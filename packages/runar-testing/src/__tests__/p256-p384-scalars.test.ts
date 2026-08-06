import { describe, it, expect } from 'vitest';
import * as nodeCrypto from 'node:crypto';
const { createECDH } = nodeCrypto;
import {
  emitMethod,
  emitP256Add, emitP256MulGen, emitVerifyECDSA_P256,
  emitP384Add, emitP384MulGen, emitVerifyECDSA_P384,
} from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * The NIST curves carried BOTH defects that were found and fixed on their
 * secp256k1 peers, because the two modules are structural copies of each other
 * and neither primitive was executed by any engine:
 *
 *  1. `p256Add` / `p384Add` could not DOUBLE. The affine chord slope
 *     (qy-py)/(qx-px) divides by zero when P == Q, and the tangent case was
 *     never written — the same bug as `ecAdd`, whose fix was never ported here.
 *
 *  2. `p256Mul` / `p384Mul` / the MulGen variants returned an ALL-ZERO point
 *     for k = 2. The ladder used incomplete Jacobian formulas over k+3n, so
 *     when the accumulator equalled the point being added the mixed-add
 *     produced (0,0,0), which then absorbed every remaining iteration — the
 *     same bug as `ecMul`.
 *
 * Both are fixed the same way as on secp256k1, except that P-256 and P-384
 * have a = -3 rather than a = 0, so the ladder uses Renes-Costello-Batina
 * Algorithms 5 and 6 (complete, a = -3) instead of 8 and 9.
 *
 * ORACLE: OpenSSL, via Node's built-in ECDH. Setting a private scalar k and
 * reading the public key yields k*G from a completely independent
 * implementation — not our codegen graded against itself.
 */

const P256_N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n;
const P384_N =
  0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973n;

/** k*G from OpenSSL, as the x||y blob the compiler emits. */
function oracle(curve: 'p256' | 'p384', k: bigint): string {
  const size = curve === 'p256' ? 32 : 48;
  const name = curve === 'p256' ? 'prime256v1' : 'secp384r1';
  const ec = createECDH(name);
  ec.setPrivateKey(Buffer.from(k.toString(16).padStart(size * 2, '0'), 'hex'));
  const pub = ec.getPublicKey(); // 0x04 || X || Y
  return pub.subarray(1).toString('hex');
}

function run(ops: StackOp[], maxOps?: number): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const vm = maxOps === undefined ? new ScriptVM() : new ScriptVM({ maxOps });
  const r = vm.executeHex(scriptHex) as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

function mulGen(curve: 'p256' | 'p384', k: bigint): string {
  const ops: StackOp[] = [{ op: 'push', value: k } as StackOp];
  (curve === 'p256' ? emitP256MulGen : emitP384MulGen)((o) => ops.push(o));
  return run(ops);
}

function add(curve: 'p256' | 'p384', a: string, b: string): string {
  const ops: StackOp[] = [
    { op: 'push', value: Uint8Array.from(Buffer.from(a, 'hex')) } as StackOp,
    { op: 'push', value: Uint8Array.from(Buffer.from(b, 'hex')) } as StackOp,
  ];
  (curve === 'p256' ? emitP256Add : emitP384Add)((o) => ops.push(o));
  return run(ops);
}

const zeroPoint = (curve: 'p256' | 'p384') => '0'.repeat(curve === 'p256' ? 128 : 192);

describe.each([
  ['p256', P256_N] as const,
  ['p384', P384_N] as const,
])('%s — scalar multiplication', (curve, N) => {
  // k = 2 is the scalar that trips the incomplete-addition exception; the
  // others are controls that passed both before and after, and prove the
  // harness itself is sound.
  for (const k of [1n, 2n, 3n, 4n, 5n]) {
    it(`${curve}MulGen(${k}) === ${k}G`, () => {
      const got = mulGen(curve, k);
      expect(got).not.toBe(zeroPoint(curve));
      expect(got).toBe(oracle(curve, k));
    }, 300_000);
  }

  it(`${curve}MulGen(n-1) matches OpenSSL`, () => {
    expect(mulGen(curve, N - 1n)).toBe(oracle(curve, N - 1n));
  }, 300_000);

  it(`${curve}MulGen(a full-width scalar) matches OpenSSL`, () => {
    const k = curve === 'p256'
      ? 0x7d3f1a95c6e2b48091a3f5d7c8e60b2419fa5c3d8e7b16490a2c5f8d3e719b4an
      : 0x3f1a95c6e2b48091a3f5d7c8e60b2419fa5c3d8e7b16490a2c5f8d3e719b4a5c6e2b48091a3f5d7c8e60b2419fa5c3dn;
    expect(mulGen(curve, k)).toBe(oracle(curve, k));
  }, 300_000);

  // Outside [1, n-1] was undefined behaviour under the old k+3n ladder; the
  // replacement reduces mod n up front, so the whole domain is defined.
  it(`${curve}MulGen(n) === the point at infinity`, () => {
    expect(mulGen(curve, N)).toBe(zeroPoint(curve));
  }, 300_000);

  it(`${curve}MulGen(n + 5) === 5G`, () => {
    expect(mulGen(curve, N + 5n)).toBe(oracle(curve, 5n));
  }, 300_000);
});

describe.each([['p256'] as const, ['p384'] as const])('%s — point addition', (curve) => {
  it(`${curve}Add(G, 2G) === 3G (distinct points, chord path)`, () => {
    expect(add(curve, oracle(curve, 1n), oracle(curve, 2n))).toBe(oracle(curve, 3n));
  }, 300_000);

  it(`${curve}Add(G, G) === 2G (DOUBLES)`, () => {
    expect(add(curve, oracle(curve, 1n), oracle(curve, 1n))).toBe(oracle(curve, 2n));
  }, 300_000);

  it(`${curve}Add(2G, 2G) === 4G (doubles a non-generator point)`, () => {
    expect(add(curve, oracle(curve, 2n), oracle(curve, 2n))).toBe(oracle(curve, 4n));
  }, 300_000);
});

// ---------------------------------------------------------------------------
// verifyECDSA is the user-facing primitive built on top of the ladder above,
// and nothing in the repo executed it — p256-wallet / p384-wallet are deploy-
// only fixtures. Since the ladder was replaced wholesale, this checks the
// composition end-to-end against real OpenSSL signatures, and pins a negative
// so an always-true verifier cannot pass.
// ---------------------------------------------------------------------------

describe.each([
  ['p256', 'prime256v1', 32] as const,
  ['p384', 'secp384r1', 48] as const,
])('%s — verifyECDSA against real OpenSSL signatures', (curve, nodeCurve, size) => {
  /** Sign with OpenSSL; return {msg, sig: r||s, pubCompressed}. */
  function signed(message: string) {
    const { generateKeyPairSync, sign: nodeSign } = nodeCrypto;
    const { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: nodeCurve });
    // raw r||s rather than DER — the emitted script splits at coordBytes
    const sig: Buffer = nodeSign('sha256', Buffer.from(message, 'utf8'), {
      key: privateKey,
      dsaEncoding: 'ieee-p1363',
    });
    const raw: Buffer = publicKey.export({ type: 'spki', format: 'der' });
    // uncompressed point is the trailing 1 + 2*size bytes of the SPKI blob
    const uncompressed = raw.subarray(raw.length - (1 + 2 * size));
    const x = uncompressed.subarray(1, 1 + size);
    const y = uncompressed.subarray(1 + size);
    const prefix = (y[y.length - 1]! & 1) === 0 ? 0x02 : 0x03;
    return {
      msg: Buffer.from(message, 'utf8'),
      sig,
      pub: Buffer.concat([Buffer.from([prefix]), x]),
    };
  }

  // ScriptVM's default 500k `maxOps` is a HARNESS-level DoS bound of ours, not
  // a consensus rule — post-Genesis BSV has no operation-count limit. Under the
  // complete a = -3 formulas these verifications execute 380,077 ops (P-256) and
  // 577,601 ops (P-384), so P-384 now crosses that default and the bound is
  // raised explicitly here rather than left to fail as if it were a script
  // error. The 3.3 MB P-384 verification script is a real cost — see the
  // size table in the commit message.
  const VM_MAX_OPS = 5_000_000;

  function verify(msg: Buffer, sig: Buffer, pub: Buffer): string {
    const ops: StackOp[] = [
      { op: 'push', value: Uint8Array.from(msg) } as StackOp,
      { op: 'push', value: Uint8Array.from(sig) } as StackOp,
      { op: 'push', value: Uint8Array.from(pub) } as StackOp,
    ];
    const emitVerify = curve === 'p256' ? emitVerifyECDSA_P256 : emitVerifyECDSA_P384;
    emitVerify((o) => ops.push(o));
    return run(ops, VM_MAX_OPS);
  }

  it(`accepts a valid ${curve} signature`, () => {
    const { msg, sig, pub } = signed('runar verifyECDSA end-to-end');
    expect(verify(msg, sig, pub)).toBe('01');
  }, 600_000);

  it(`rejects a tampered ${curve} signature`, () => {
    const { msg, sig, pub } = signed('runar verifyECDSA end-to-end');
    const bad = Buffer.from(sig);
    bad[bad.length - 1] = bad[bad.length - 1]! ^ 0x01; // flip a bit of s
    expect(verify(msg, bad, pub)).not.toBe('01');
  }, 600_000);
});
