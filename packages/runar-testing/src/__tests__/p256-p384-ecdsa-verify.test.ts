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
 * The decompression cases pin `decompressPubKey`'s precondition. It computes
 * y = (x³ − 3x + b)^((p+1)/4) and, before that change, never checked that
 * y² == x³ − 3x + b, nor that x < p. For an x whose RHS is a quadratic
 * non-residue the recovered point is NOT on the curve, and it went straight
 * into `cEmitMul`'s ladder — whose own soundness argument (the `c_i mod ord(P)`
 * interval in `buildJacobianAddOrDoubleInline`) is stated only for points ON
 * the curve, because cofactor 1 is what pins ord(P) = n.
 *
 * The `(r, s)` range cases are a different and much sharper story: they ARE a
 * red-then-green proof. Nothing validated r or s at all, and `cGroupInv` is
 * Fermat, so inv(0) = 0 rather than an error. `sig = 0x00…` therefore drove
 * w = u1 = u2 = 0, both ladders to the all-zero point, `cAffineAdd` down its
 * tangent branch with den = 0, and the final comparison to `OP_EQUAL(<>, <>)`
 * = 1 — a UNIVERSAL FORGERY against any message under any genuine pubkey.
 * See `docs/audit/2026-08-ec-degenerate-cases.md`.
 */

const CURVES = {
  p256: {
    node: 'prime256v1',
    bytes: 32,
    hash: 'sha256',
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
    n: 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n,
    emit: emitVerifyECDSA_P256,
  },
  p384: {
    node: 'secp384r1',
    bytes: 48,
    hash: 'sha256',
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    b: 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefn,
    n: 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973n,
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

/**
 * Run the curve's verifier over (msg, sig, compressed pubkey).
 *
 * Also enforces TOTALITY on every call: `verifyECDSA_*` is a boolean-valued
 * builtin that `05-stack-lower.ts#lowerVerifyECDSA` lowers as "consume 3, push
 * 1", so for ANY argument bytes it must terminate without an evaluation error
 * and leave exactly one item. That is not decoration — before the length gate,
 * a `sig` of 32..63 bytes ran `emitReverse32`'s `OP_SPLIT 1` off the end of the
 * value and aborted the script, which would make `verifyECDSA_P256(x) || alt`
 * unwritable.
 */
function verify(c: Curve, msgHex: string, sigHex: string, pkHex: string): boolean {
  const ops: StackOp[] = [
    { op: 'push', value: blob(msgHex) } as StackOp,
    { op: 'push', value: blob(sigHex) } as StackOp,
    { op: 'push', value: blob(pkHex) } as StackOp,
  ];
  c.emit((o: StackOp) => ops.push(o));
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as {
    stack: Uint8Array[];
    error?: unknown;
  };
  expect(r.error ?? null, 'verifier aborted instead of returning a boolean').toBe(null);
  expect(r.stack.length, 'verifier is specified as 3 args in, 1 boolean out').toBe(1);
  const top = Buffer.from(r.stack[0]!).toString('hex');
  return top !== '' && top !== '00';
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

    // ---- (r, s) range: SEC1 §4.1.4 step 1 / FIPS 186-5 §6.4.2 -------------
    //
    // These are the universal-forgery cases. Nothing checked 1 <= r,s <= n-1,
    // and `cGroupInv` is Fermat (a^(n-2) mod n), so inv(0) = 0 instead of an
    // error. Every all-zero-driven path therefore collapses to the all-zero
    // point and the final `(R.x mod n) == r` becomes `OP_EQUAL(<>, <>)` = 1.
    const rGenuine = sigHex.slice(0, w);
    const sGenuine = sigHex.slice(w);
    const zero = '0'.repeat(w);

    it('rejects an all-zero signature — THE universal forgery', () => {
      // No secret material, no off-curve pubkey: 64 (P-256) / 96 (P-384) zero
      // bytes plus the contract's own genuine, public key. If this returns
      // true, `verifyECDSA_*` is not a signature check at all.
      expect(verify(c, msgHex, zero + zero, compressed)).toBe(false);
    });

    it('rejects an all-zero signature under an unrelated message', () => {
      // Universal: the forged signature is not bound to the message either.
      expect(verify(c, '00', zero + zero, compressed)).toBe(false);
    });

    it('rejects r = 0 with a genuine s', () => {
      expect(verify(c, msgHex, zero + sGenuine, compressed)).toBe(false);
    });

    it('rejects s = 0 with a genuine r', () => {
      expect(verify(c, msgHex, rGenuine + zero, compressed)).toBe(false);
    });

    it('rejects r = 0, s = n — the same forgery with s out of range', () => {
      // s = n makes inv(s) = n^(n-2) mod n = 0 just as s = 0 does, so this is
      // a second spelling of the forgery that an `s != 0` check alone misses.
      expect(verify(c, msgHex, zero + hx(c.n), compressed)).toBe(false);
    });

    it('rejects r = n', () => {
      expect(verify(c, msgHex, hx(c.n) + sGenuine, compressed)).toBe(false);
    });

    it('rejects s = n', () => {
      expect(verify(c, msgHex, rGenuine + hx(c.n), compressed)).toBe(false);
    });

    it('rejects r = n + 1', () => {
      expect(verify(c, msgHex, hx(c.n + 1n) + sGenuine, compressed)).toBe(false);
    });

    it('rejects s = n + 1', () => {
      expect(verify(c, msgHex, rGenuine + hx(c.n + 1n), compressed)).toBe(false);
    });

    // ---- argument length ---------------------------------------------------
    //
    // `sig` and `pubkey` are bare `ByteString` in `runar-lang/src/builtins.ts`
    // and `03-typecheck.ts` imposes no width. The verifier split `sig` at
    // coordBytes and took EVERYTHING after as s, and peeled exactly coordBytes
    // off `pubkey` — so trailing bytes were ignored (malleability) and short
    // ones aborted (`verify` asserts non-abort on every call above).
    it('rejects a signature with trailing bytes (malleability)', () => {
      expect(verify(c, msgHex, sigHex + 'ff', compressed)).toBe(false);
    });

    it('rejects a signature with many trailing bytes', () => {
      expect(verify(c, msgHex, sigHex + 'de'.repeat(64), compressed)).toBe(false);
    });

    it('rejects a truncated signature without aborting', () => {
      // coordBytes <= len < 2*coordBytes: the length where the byte reversal
      // used to run out of input mid-loop and kill the script.
      expect(verify(c, msgHex, sigHex.slice(0, (c.bytes + 4) * 2), compressed)).toBe(false);
    });

    it('rejects an empty signature without aborting', () => {
      expect(verify(c, msgHex, '', compressed)).toBe(false);
    });

    it('rejects a pubkey with trailing bytes', () => {
      expect(verify(c, msgHex, sigHex, compressed + 'ff')).toBe(false);
    });

    it('rejects a truncated pubkey without aborting', () => {
      expect(verify(c, msgHex, sigHex, compressed.slice(0, -8))).toBe(false);
    });

    it('rejects an empty pubkey without aborting', () => {
      expect(verify(c, msgHex, sigHex, '')).toBe(false);
    });

    // ---- compressed prefix (SEC1 §2.3.4) -----------------------------------
    //
    // The parity reduction is `BIN2NUM, 2 OP_MOD`, which accepts anything.
    // 0x00/0x04/0x82 alias to "even"; 0x83 is worse — BIN2NUM(0x83) = -3 and
    // -3 mod 2 = -1 encodes as 0x81, which never matches `_dk_y_par`, so the
    // select silently returns the OTHER root.
    for (const bad of ['00', '01', '04', '82', '83', 'ff']) {
      it(`rejects pubkey prefix 0x${bad}`, () => {
        expect(verify(c, msgHex, sigHex, bad + compressed.slice(2))).toBe(false);
      });
    }
  });
}
