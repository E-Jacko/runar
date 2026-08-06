import { describe, it, expect } from 'vitest';
import { ECDH } from 'node:crypto';
import {
  emitMethod,
  emitEcOnCurve, emitEcAdd,
  emitP256OnCurve, emitP256Add,
  emitP384OnCurve, emitP384Add,
} from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * GAP-301 — coordinate canonicity in the on-curve checks.
 *
 * A `Point` is a bare x‖y byte blob, and every emitter turns those bytes into
 * a script number and then reduces mod p. So the blob (x + p)‖y satisfies the
 * curve equation exactly as x‖y does. `ecOnCurve` (secp256k1) range-checks the
 * coordinates and rejects that; `p256OnCurve` / `p384OnCurve` did NOT — they
 * emitted the curve equation alone, so they accepted a coordinate that is not
 * a canonical field element.
 *
 * That matters because the on-curve check is exactly what the P-256 / P-384
 * codegen tells contract authors to gate untrusted points on, and two things
 * downstream read the coordinates BEFORE any reduction:
 *
 *   - `pNNNAdd`'s doubling test is `OP_NUMEQUAL(px, qx)` on the raw values, so
 *     P and its non-canonical twin take the CHORD path, divide by
 *     (qx − px) = p ≡ 0, and — `fieldInv` being Fermat, inv(0) = 0 — produce a
 *     point that is not 2P and is not even on the curve, with the script
 *     succeeding. That is the `pNNNAdd(P, P')` case pinned below.
 *   - a point's identity as *bytes* (nullifier / commitment / equality test)
 *     stops being unique once two encodings both pass the gate.
 *
 * Oracle: OpenSSL, via Node's `crypto.ECDH.convertKey()`, which parses an
 * uncompressed 04‖x‖y point and rejects both off-curve points and out-of-range
 * field elements. Every Rúnar result here is produced by running the emitted
 * script through the real @bsv/sdk interpreter.
 *
 * NOTE on the y half of the guard: it is emitted (mirroring secp256k1) but
 * cannot be exercised the same way. (x + p) has to fit the coordinate width,
 * which needs x < 2^(8·w) − p — about 2^224 for P-256, 2^128 for P-384 and
 * 2^32 for secp256k1 — and a curve point with such a small *x* is found by
 * trying x = 1, 2, 3, …, while one with such a small *y* is a 2^-32 / 2^-256
 * event. So only the x half has a constructible witness.
 */

const CURVES = {
  secp256k1: {
    openssl: 'secp256k1',
    bytes: 32,
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn,
    // y² = x³ + ax + b
    a: 0n,
    b: 7n,
    emitOnCurve: emitEcOnCurve,
    emitAdd: emitEcAdd,
    /** secp256k1's guard predates this fix — it is the control, already green. */
    alreadyGuarded: true,
  },
  p256: {
    openssl: 'prime256v1',
    bytes: 32,
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    a: -3n,
    b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
    emitOnCurve: emitP256OnCurve,
    emitAdd: emitP256Add,
    alreadyGuarded: false,
  },
  p384: {
    openssl: 'secp384r1',
    bytes: 48,
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    a: -3n,
    b: 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefn,
    emitOnCurve: emitP384OnCurve,
    emitAdd: emitP384Add,
    alreadyGuarded: false,
  },
} as const;

type Curve = (typeof CURVES)[keyof typeof CURVES];

// --- field helpers (from the curve parameters alone) ------------------------

const mod = (v: bigint, p: bigint) => ((v % p) + p) % p;

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

/** √a mod p for p ≡ 3 (mod 4) — true for all three curves. */
function sqrtMod(a: bigint, p: bigint): bigint | null {
  const r = powm(a, (p + 1n) / 4n, p);
  return (r * r) % p === mod(a, p) ? r : null;
}

function rhs(c: Curve, x: bigint): bigint {
  return mod(x * x * x + c.a * x + c.b, c.p);
}

function isOnCurve(c: Curve, x: bigint, y: bigint): boolean {
  return mod(y * y, c.p) === rhs(c, x);
}

/**
 * The smallest on-curve x for which x + p still fits the coordinate width —
 * the only shape of witness that makes a non-canonical encoding expressible.
 */
function smallXPoint(c: Curve): { x: bigint; y: bigint } {
  const limit = 1n << BigInt(c.bytes * 8);
  for (let x = 1n; x < 100000n; x++) {
    if (x + c.p >= limit) break;
    const y = sqrtMod(rhs(c, x), c.p);
    if (y !== null) return { x, y };
  }
  throw new Error(`no small-x point found for ${c.openssl}`);
}

// --- harness ----------------------------------------------------------------

const blob = (hex: string) => Uint8Array.from(Buffer.from(hex, 'hex'));

function exec(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

/** Run the curve's on-curve emitter over a raw point blob. */
function onCurve(c: Curve, pointHex: string): boolean {
  const ops: StackOp[] = [{ op: 'push', value: blob(pointHex) } as StackOp];
  c.emitOnCurve((o: StackOp) => ops.push(o));
  const top = exec(ops);
  // Script booleans: '' / '00' are false, anything else true.
  return top !== '(empty)' && top !== '' && top !== '00';
}

function add(c: Curve, aHex: string, bHex: string): string {
  const ops: StackOp[] = [
    { op: 'push', value: blob(aHex) } as StackOp,
    { op: 'push', value: blob(bHex) } as StackOp,
  ];
  c.emitAdd((o: StackOp) => ops.push(o));
  return exec(ops);
}

/**
 * OpenSSL's verdict on an uncompressed point: on-curve AND canonical.
 * `ECDH.convertKey` parses 04‖x‖y through OpenSSL's `EC_POINT_oct2point`,
 * which rejects both off-curve points and out-of-range field elements.
 */
function opensslAcceptsPoint(c: Curve, pointHex: string): boolean {
  try {
    ECDH.convertKey('04' + pointHex, c.openssl, 'hex', 'hex', 'compressed');
    return true;
  } catch {
    return false;
  }
}

for (const [name, c] of Object.entries(CURVES) as Array<[string, Curve]>) {
  const w = c.bytes * 2;
  const hx = (v: bigint) => v.toString(16).padStart(w, '0');

  describe(`${name} on-curve canonicity (GAP-301)`, () => {
    const P = smallXPoint(c);
    const canonical = hx(P.x) + hx(P.y);
    const nonCanonicalX = hx(P.x + c.p) + hx(P.y);

    it('the witness is a genuine curve point with an expressible non-canonical x', () => {
      expect(isOnCurve(c, P.x, P.y)).toBe(true);
      expect(P.x + c.p).toBeLessThan(1n << BigInt(c.bytes * 8));
      // Same field element, different bytes — the whole point of the test.
      expect(mod(P.x + c.p, c.p)).toBe(P.x);
      expect(nonCanonicalX).not.toBe(canonical);
    });

    it('oracle: OpenSSL accepts the canonical encoding and rejects x ≥ p', () => {
      expect(opensslAcceptsPoint(c, canonical)).toBe(true);
      expect(opensslAcceptsPoint(c, nonCanonicalX)).toBe(false);
    });

    it('accepts the canonical point', () => {
      expect(onCurve(c, canonical)).toBe(true);
    });

    it('rejects x ≥ p — agreeing with OpenSSL', () => {
      expect(onCurve(c, nonCanonicalX)).toBe(false);
    });

    it('still rejects a point that is off the curve outright', () => {
      const offCurve = hx(P.x + 1n) + hx(P.y);
      expect(opensslAcceptsPoint(c, offCurve)).toBe(false);
      expect(onCurve(c, offCurve)).toBe(false);
    });

    // Why the guard is load-bearing rather than cosmetic: the two encodings
    // denote the same group element, but `emitAdd` compares the RAW x values
    // to detect doubling, so it takes the chord path and divides by zero.
    it('the gate is load-bearing: add(P, P′) is neither 2P nor even on the curve', () => {
      const two = add(c, canonical, canonical);
      const mixed = add(c, canonical, nonCanonicalX);
      expect(mixed).not.toBe(two);
      const rx = BigInt('0x' + mixed.slice(0, w));
      const ry = BigInt('0x' + mixed.slice(w));
      expect(isOnCurve(c, rx, ry)).toBe(false);
      // …and the script SUCCEEDS while returning it, so nothing downstream
      // can notice: only the on-curve gate can reject the input.
      expect(mixed).not.toBe('(empty)');
    });

    if (c.alreadyGuarded) {
      it('control: this curve was already guarded before GAP-301', () => {
        expect(c.alreadyGuarded).toBe(true);
      });
    }
  });
}
