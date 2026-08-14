import { describe, it, expect } from 'vitest';
import { createECDH } from 'node:crypto';
import {
  emitMethod,
  emitP256Add, emitP256Mul, emitP256MulGen,
  emitP384Add, emitP384Mul, emitP384MulGen,
} from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * NIST P-256 / P-384 point arithmetic, executed through the real @bsv/sdk
 * interpreter and checked against OpenSSL (Node's `crypto.createECDH`: set the
 * scalar as the private key and the derived public key IS k·G).
 *
 * Two defects lived here undetected because `packages/runar-testing`'s ANF
 * interpreter MOCKED p256Add/p256Mul/p256MulGen to 64 zero bytes and
 * p256OnCurve to `true` — nothing on any path ever executed the emitted script:
 *
 *  1. `cAffineAdd` only ever implemented the CHORD slope (qy−py)/(qx−px),
 *     which is 0/0 when P == Q. `p256Add(G, G)` and `p384Add(G, G)` returned a
 *     wrong point. Same omission that 8a6494b4 fixed for secp256k1; it was
 *     never ported to the a = −3 curves, where the tangent is (3px²−3)/(2py).
 *  2. The scalar ladder's Jacobian mixed-add is undefined when the accumulator
 *     equals the point being added, which happens for exactly one scalar,
 *     k = 2, at the last iteration. `p256Mul(G, 2n)` / `p384Mul(G, 2n)`
 *     returned 64 / 96 zero bytes.
 */

const CURVES = {
  p256: {
    openssl: 'prime256v1',
    bytes: 32,
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    n: 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n,
    gx: 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296n,
    gy: 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5n,
    emitAdd: emitP256Add,
    emitMul: emitP256Mul,
    emitMulGen: emitP256MulGen,
  },
  p384: {
    openssl: 'secp384r1',
    bytes: 48,
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    n: 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973n,
    gx: 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7n,
    gy: 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5fn,
    emitAdd: emitP384Add,
    emitMul: emitP384Mul,
    emitMulGen: emitP384MulGen,
  },
} as const;

type Curve = (typeof CURVES)[keyof typeof CURVES];
type Aff = { x: bigint; y: bigint } | null;

// --- from-scratch double-and-add over y² = x³ − 3x + b ----------------------

function makeArith(p: bigint) {
  const m = (v: bigint) => ((v % p) + p) % p;
  const inv = (a: bigint) => {
    let r = 1n;
    let b = m(a);
    let e = p - 2n;
    while (e > 0n) {
      if (e & 1n) r = (r * b) % p;
      b = (b * b) % p;
      e >>= 1n;
    }
    return r;
  };
  const dbl = (P0: Aff): Aff => {
    if (P0 === null) return null;
    const s = m(m(3n * P0.x * P0.x - 3n) * inv(2n * P0.y));
    const x = m(s * s - 2n * P0.x);
    return { x, y: m(s * (P0.x - x) - P0.y) };
  };
  const add = (P0: Aff, Q: Aff): Aff => {
    if (P0 === null) return Q;
    if (Q === null) return P0;
    if (P0.x === Q.x) return m(P0.y + Q.y) === 0n ? null : dbl(P0);
    const s = m(m(Q.y - P0.y) * inv(m(Q.x - P0.x)));
    const x = m(s * s - P0.x - Q.x);
    return { x, y: m(s * (P0.x - x) - P0.y) };
  };
  const mul = (k: bigint, P0: Aff): Aff => {
    let r: Aff = null;
    let a = P0;
    while (k > 0n) {
      if (k & 1n) r = add(r, a);
      a = dbl(a);
      k >>= 1n;
    }
    return r;
  };
  return { add, dbl, mul };
}

// --- oracles / harness ------------------------------------------------------

function hexOf(c: Curve, pt: NonNullable<Aff>): string {
  const w = c.bytes * 2;
  return pt.x.toString(16).padStart(w, '0') + pt.y.toString(16).padStart(w, '0');
}

/** k·G according to OpenSSL, as the bare x||y blob Rúnar's `Point` uses. */
function opensslMul(c: Curve, k: bigint): string {
  const ecdh = createECDH(c.openssl);
  ecdh.setPrivateKey(Buffer.from(k.toString(16).padStart(c.bytes * 2, '0'), 'hex'));
  const pub = ecdh.getPublicKey('hex'); // 04 || x || y
  expect(pub.slice(0, 2)).toBe('04');
  return pub.slice(2);
}

function exec(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}
const blob = (hex: string) => Uint8Array.from(Buffer.from(hex, 'hex'));

function curveAdd(c: Curve, aHex: string, bHex: string): string {
  const ops: StackOp[] = [
    { op: 'push', value: blob(aHex) } as StackOp,
    { op: 'push', value: blob(bHex) } as StackOp,
  ];
  c.emitAdd((o: StackOp) => ops.push(o));
  return exec(ops);
}
function curveMul(c: Curve, pHex: string, k: bigint): string {
  const ops: StackOp[] = [
    { op: 'push', value: blob(pHex) } as StackOp,
    { op: 'push', value: k } as StackOp,
  ];
  c.emitMul((o: StackOp) => ops.push(o));
  return exec(ops);
}
function curveMulGen(c: Curve, k: bigint): string {
  const ops: StackOp[] = [{ op: 'push', value: k } as StackOp];
  c.emitMulGen((o: StackOp) => ops.push(o));
  return exec(ops);
}

for (const [name, c] of Object.entries(CURVES) as Array<[string, Curve]>) {
  const A = makeArith(c.p);
  const G: NonNullable<Aff> = { x: c.gx, y: c.gy };
  const G_HEX = hexOf(c, G);
  const ref = (k: bigint) => hexOf(c, A.mul(k, G)!);

  describe(`${name} point arithmetic`, () => {
    it('oracles agree: from-scratch double-and-add === OpenSSL', () => {
      for (const k of [1n, 2n, 3n, 4n, 5n, 12345n, c.n - 1n]) {
        expect(ref(k)).toBe(opensslMul(c, k));
      }
    });

    // ---- defect 1: affine add cannot double --------------------------------

    it(`${name}Add(G, G) === 2G (was a wrong point)`, () => {
      expect(curveAdd(c, G_HEX, G_HEX)).toBe(opensslMul(c, 2n));
    });

    it(`${name}Add(3G, 3G) === 6G — doubling a non-generator`, () => {
      expect(curveAdd(c, ref(3n), ref(3n))).toBe(opensslMul(c, 6n));
    });

    it(`control: ${name}Add(G, 2G) === 3G — the chord path still works`, () => {
      expect(curveAdd(c, G_HEX, ref(2n))).toBe(opensslMul(c, 3n));
    });

    it(`control: ${name}Add(2G, 5G) === 7G`, () => {
      expect(curveAdd(c, ref(2n), ref(5n))).toBe(opensslMul(c, 7n));
    });

    // ---- defect 2: ladder cannot double at k = 2 ---------------------------

    it(`${name}Mul(G, 2) === 2G (was all-zero bytes)`, () => {
      expect(curveMul(c, G_HEX, 2n)).toBe(opensslMul(c, 2n));
    });

    it(`${name}MulGen(2) === 2G (was all-zero bytes)`, () => {
      expect(curveMulGen(c, 2n)).toBe(opensslMul(c, 2n));
    });

    it(`${name}Mul(3G, 2) === 6G — not specific to the generator`, () => {
      expect(curveMul(c, ref(3n), 2n)).toBe(opensslMul(c, 6n));
    });

    for (const k of [1n, 3n, 4n, 7n]) {
      it(`control: ${name}Mul(G, ${k}) === ${k}G`, () => {
        expect(curveMul(c, G_HEX, k)).toBe(opensslMul(c, k));
      });
    }

    it(`control: ${name}Mul(G, n-1) === -G`, () => {
      expect(curveMul(c, G_HEX, c.n - 1n)).toBe(opensslMul(c, c.n - 1n));
    });

    it('control: pseudorandom scalar', () => {
      const k = (0xdeadbeefcafebabe1234567890abcdef0123456789abcdefn % (c.n - 1n)) + 1n;
      expect(curveMul(c, G_HEX, k)).toBe(opensslMul(c, k));
    });
  });
}
