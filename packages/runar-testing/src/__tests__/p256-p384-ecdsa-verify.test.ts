import { describe, it, expect } from 'vitest';
import { createSign, generateKeyPairSync } from 'node:crypto';
import { emitMethod, emitVerifyECDSA_P256, emitVerifyECDSA_P384 } from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * `verifyECDSA_P256` / `verifyECDSA_P384` executed through the real @bsv/sdk
 * `Spend`. Nothing in this repo had ever run these scripts: the two emitters
 * were the only EC emitters missing from `runar-compiler`'s export list, and
 * neither `p256-wallet` nor `p384-wallet` carries a real-crypto witness. They
 * were graded solely by the checked-in hex golden — i.e. against themselves.
 *
 * The oracle is OpenSSL: Node's `crypto` generates the key and produces the
 * signature; the script only ever sees (msg, r‖s, 02/03‖x).
 *
 * The rejection cases pin `decompressPubKey`'s precondition. It computes
 * y = (x³ − 3x + b)^((p+1)/4) and, before this change, never checked that
 * y² == x³ − 3x + b, nor that x < p. For an x whose RHS is a quadratic
 * non-residue the recovered point is NOT on the curve, and it went straight
 * into `cEmitMul`'s ladder — whose own soundness argument (the `c_i mod ord(P)`
 * interval in `buildJacobianAddOrDoubleInline`) is stated only for points ON
 * the curve, because cofactor 1 is what pins ord(P) = n.
 *
 * Honesty note on TDD: the rejection cases below are regression pins, NOT a
 * red-then-green proof. A pre-fix `true` cannot be constructed — every input
 * that trips the guard also fails the final `(R.x mod n) == r` comparison, and
 * making that comparison succeed with an attacker-chosen off-curve Q is
 * equivalent to forging ECDSA. So the practical exposure is an invalid-curve
 * computation on caller-supplied bytes, not a signature forgery; the guard
 * restores the precondition the ladder documents rather than closing a
 * demonstrated bypass. The genuinely new coverage is the ACCEPT case: this is
 * the first execution of either verifier by anything.
 */

const CURVES = {
  p256: {
    node: 'prime256v1',
    bytes: 32,
    hash: 'sha256',
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
    emit: emitVerifyECDSA_P256,
  },
  p384: {
    node: 'secp384r1',
    bytes: 48,
    hash: 'sha256',
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    b: 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefn,
    emit: emitVerifyECDSA_P384,
  },
} as const;

type Curve = (typeof CURVES)[keyof typeof CURVES];

const mod = (v: bigint, p: bigint) => ((v % p) + p) % p;
const blob = (hex: string) => Uint8Array.from(Buffer.from(hex, 'hex'));

function powm(base: bigint, exp: bigint, p: bigint): bigint {
  let r = 1n;
  let b = mod(base, p);
  let e = exp;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % p;
    b = (b * b) % p;
    e >>= 1n;
  }
  return r;
}

/** Is `v` a quadratic residue mod p? (p ≡ 3 mod 4 on both curves.) */
function isResidue(v: bigint, p: bigint): boolean {
  return v === 0n || powm(v, (p - 1n) / 2n, p) === 1n;
}

function rhs(c: Curve, x: bigint): bigint {
  return mod(x * x * x - 3n * x + c.b, c.p);
}

/** DER SEQUENCE { INTEGER r, INTEGER s } → fixed-width r‖s. */
function derToRaw(c: Curve, der: Buffer): string {
  let i = 0;
  if (der[i++] !== 0x30) throw new Error('not a DER sequence');
  if (der[i]! & 0x80) i += 1 + (der[i]! & 0x7f); else i += 1;
  const readInt = (): bigint => {
    if (der[i++] !== 0x02) throw new Error('not a DER integer');
    const len = der[i++]!;
    const v = BigInt('0x' + der.subarray(i, i + len).toString('hex'));
    i += len;
    return v;
  };
  const r = readInt();
  const s = readInt();
  const w = c.bytes * 2;
  return r.toString(16).padStart(w, '0') + s.toString(16).padStart(w, '0');
}

function exec(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

/** Run the curve's verifier over (msg, sig, compressed pubkey). */
function verify(c: Curve, msgHex: string, sigHex: string, pkHex: string): boolean {
  const ops: StackOp[] = [
    { op: 'push', value: blob(msgHex) } as StackOp,
    { op: 'push', value: blob(sigHex) } as StackOp,
    { op: 'push', value: blob(pkHex) } as StackOp,
  ];
  c.emit((o: StackOp) => ops.push(o));
  const top = exec(ops);
  return top !== '(empty)' && top !== '' && top !== '00';
}

for (const [name, c] of Object.entries(CURVES) as Array<[string, Curve]>) {
  const w = c.bytes * 2;
  const hx = (v: bigint) => v.toString(16).padStart(w, '0');

  describe(`${name} verifyECDSA (real Spend, OpenSSL oracle)`, () => {
    // A single keypair + signature reused by every case below, so the ONLY
    // thing that varies between accept and reject is the pubkey encoding.
    const { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: c.node });
    const pub = publicKey.export({ format: 'der', type: 'spki' }) as Buffer;
    // SPKI tail is the uncompressed point 04‖x‖y.
    const uncompressed = pub.subarray(pub.length - (1 + c.bytes * 2)).toString('hex');
    expect(uncompressed.slice(0, 2)).toBe('04');
    const qx = BigInt('0x' + uncompressed.slice(2, 2 + w));
    const qy = BigInt('0x' + uncompressed.slice(2 + w));
    const compressed = ((qy & 1n) === 0n ? '02' : '03') + hx(qx);

    const msgHex = '52c3ad6172206d657373616765'; // "Rúnar message"
    const signer = createSign(c.hash);
    signer.update(Buffer.from(msgHex, 'hex'));
    const sigHex = derToRaw(c, signer.sign(privateKey) as Buffer);

    it('the OpenSSL fixture is self-consistent', () => {
      expect(mod(qy * qy, c.p)).toBe(rhs(c, qx));
      expect(sigHex.length).toBe(w * 2);
    });

    it('accepts a genuine OpenSSL signature', () => {
      expect(verify(c, msgHex, sigHex, compressed)).toBe(true);
    });

    it('rejects the same signature under a different message', () => {
      expect(verify(c, msgHex + '00', sigHex, compressed)).toBe(false);
    });

    it('rejects the same signature under the other pubkey parity', () => {
      const flipped = (compressed.slice(0, 2) === '02' ? '03' : '02') + compressed.slice(2);
      expect(verify(c, msgHex, sigHex, flipped)).toBe(false);
    });

    // ---- decompression preconditions -------------------------------------
    it('rejects a pubkey whose x has no square root (decompression is off-curve)', () => {
      let bad = 2n;
      while (isResidue(rhs(c, bad), c.p)) bad += 1n;
      // Sanity: the recovered y really does NOT satisfy the curve equation, so
      // pre-guard this point entered the ladder.
      const yCand = powm(rhs(c, bad), (c.p + 1n) / 4n, c.p);
      expect(mod(yCand * yCand, c.p)).not.toBe(rhs(c, bad));
      expect(verify(c, msgHex, sigHex, '02' + hx(bad))).toBe(false);
    });

    it('rejects a non-canonical pubkey x ≥ p', () => {
      // Smallest on-curve x for which x + p still fits the coordinate width.
      const limit = 1n << BigInt(c.bytes * 8);
      let x = 1n;
      for (; x < 100000n; x++) {
        if (x + c.p >= limit) throw new Error('no expressible non-canonical x');
        if (isResidue(rhs(c, x), c.p)) break;
      }
      expect(mod(x + c.p, c.p)).toBe(x);
      expect(verify(c, msgHex, sigHex, '02' + hx(x + c.p))).toBe(false);
    });
  });
}
