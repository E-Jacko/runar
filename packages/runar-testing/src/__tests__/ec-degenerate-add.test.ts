import { describe, it, expect } from 'vitest';
import { ECDH } from 'node:crypto';
import {
  emitMethod,
  emitEcAdd, emitEcNegate, emitEcOnCurve,
  emitP256Add, emitP256Negate, emitP256OnCurve,
  emitP384Add, emitP384Negate, emitP384OnCurve,
} from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM, TestContract } from '../index.js';

/**
 * `ecAdd(P, −P)` — the one affine-addition case that has no affine answer.
 *
 * 03f50d48 gave the affine adders a tangent path selected on `cond = (px == qx)`
 * ALONE. For Q = −P that condition is 1, so the emitter took the tangent and
 * returned 2P: an on-curve, perfectly plausible, WRONG point. Before that
 * commit the chord path ran, divided by zero (`fieldInv` is Fermat, so
 * inv(0) = 0), and produced (−2px mod p, −py mod p) — an off-curve blob that
 * `ecOnCurve` rejected. So the fix for doubling silently disarmed the only
 * guard that had been catching P + (−P), against exactly the idiom the
 * codegen's own comments tell authors to write:
 *
 *     const r = p384Add(a, b);
 *     assert(p384OnCurve(r));      // rejected before 03f50d48, ACCEPTED after
 *
 * The semantics pinned here: P + (−P) is the point at infinity, and this
 * codegen represents O as the ALL-ZERO blob — the same thing `ecMul(P, 0n)`
 * already returns, and the same thing the `ec-mulgen-linear` rewrite in
 * `optimizer/ec-rules.json` produces when k1 + k2 ≡ 0 (mod n). O is not on the
 * curve (0² ≠ 0³ + b for every b ≠ 0), so `ecOnCurve` rejects it and the guard
 * above works again.
 *
 * Both halves are pinned together on purpose. The script is executed through
 * the real @bsv/sdk `Spend`; the interpreter is driven through `TestContract`.
 * `conformance/witnesses/real-crypto-execution.test.ts` asserts
 * `interpreterAccepted === vmAccepted`, so any drift between the two is a
 * conformance failure — and "fix the interpreter to match the script" would
 * have cemented the wrong answer.
 */

const blob = (hex: string) => Uint8Array.from(Buffer.from(hex, 'hex'));

function exec(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

const CURVES = {
  secp256k1: {
    openssl: 'secp256k1',
    bytes: 32,
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn,
    a: 0n,
    b: 7n,
    gx: 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n,
    gy: 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n,
    emitAdd: emitEcAdd,
    emitNegate: emitEcNegate,
    emitOnCurve: emitEcOnCurve,
    /** Rúnar source names for the same three primitives. */
    fnAdd: 'ecAdd', fnNegate: 'ecNegate', fnOnCurve: 'ecOnCurve', pointType: 'Point',
  },
  p256: {
    openssl: 'prime256v1',
    bytes: 32,
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    a: -3n,
    b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
    gx: 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296n,
    gy: 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5n,
    emitAdd: emitP256Add,
    emitNegate: emitP256Negate,
    emitOnCurve: emitP256OnCurve,
    fnAdd: 'p256Add', fnNegate: 'p256Negate', fnOnCurve: 'p256OnCurve', pointType: 'P256Point',
  },
  p384: {
    openssl: 'secp384r1',
    bytes: 48,
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    a: -3n,
    b: 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefn,
    gx: 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7n,
    gy: 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5fn,
    emitAdd: emitP384Add,
    emitNegate: emitP384Negate,
    emitOnCurve: emitP384OnCurve,
    fnAdd: 'p384Add', fnNegate: 'p384Negate', fnOnCurve: 'p384OnCurve', pointType: 'P384Point',
  },
} as const;

type Curve = (typeof CURVES)[keyof typeof CURVES];

const mod = (v: bigint, p: bigint) => ((v % p) + p) % p;

/** Independent affine addition from the curve parameters alone. `null` = O. */
type Aff = { x: bigint; y: bigint } | null;
function refArith(c: Curve) {
  const p = c.p;
  const inv = (a: bigint) => {
    let r = 1n;
    let b = mod(a, p);
    let e = p - 2n;
    while (e > 0n) {
      if (e & 1n) r = (r * b) % p;
      b = (b * b) % p;
      e >>= 1n;
    }
    return r;
  };
  const dbl = (P: Aff): Aff => {
    if (P === null) return null;
    const s = mod(mod(3n * P.x * P.x + c.a, p) * inv(2n * P.y), p);
    const x = mod(s * s - 2n * P.x, p);
    return { x, y: mod(s * (P.x - x) - P.y, p) };
  };
  const add = (P: Aff, Q: Aff): Aff => {
    if (P === null) return Q;
    if (Q === null) return P;
    if (P.x === Q.x) return mod(P.y + Q.y, p) === 0n ? null : dbl(P);
    const s = mod(mod(Q.y - P.y, p) * inv(mod(Q.x - P.x, p)), p);
    const x = mod(s * s - P.x - Q.x, p);
    return { x, y: mod(s * (P.x - x) - P.y, p) };
  };
  return { add, dbl };
}

for (const [name, c] of Object.entries(CURVES) as Array<[string, Curve]>) {
  const w = c.bytes * 2;
  const hx = (v: bigint) => v.toString(16).padStart(w, '0');
  const G = { x: c.gx, y: c.gy };
  const G_HEX = hx(G.x) + hx(G.y);
  const NEG_G_HEX = hx(G.x) + hx(mod(c.p - G.y, c.p));
  const ZERO_POINT = '0'.repeat(w * 2);

  function add(aHex: string, bHex: string): string {
    const ops: StackOp[] = [
      { op: 'push', value: blob(aHex) } as StackOp,
      { op: 'push', value: blob(bHex) } as StackOp,
    ];
    c.emitAdd((o: StackOp) => ops.push(o));
    return exec(ops);
  }
  function negate(aHex: string): string {
    const ops: StackOp[] = [{ op: 'push', value: blob(aHex) } as StackOp];
    c.emitNegate((o: StackOp) => ops.push(o));
    return exec(ops);
  }
  function onCurve(aHex: string): boolean {
    const ops: StackOp[] = [{ op: 'push', value: blob(aHex) } as StackOp];
    c.emitOnCurve((o: StackOp) => ops.push(o));
    const top = exec(ops);
    return top !== '(empty)' && top !== '' && top !== '00';
  }

  describe(`${name} — ecAdd(P, −P) is the point at infinity`, () => {
    it('the witness really is −P (independent of the emitter)', () => {
      expect(negate(G_HEX)).toBe(NEG_G_HEX);
      // OpenSSL agrees both are genuine curve points.
      for (const pt of [G_HEX, NEG_G_HEX]) {
        expect(() => ECDH.convertKey('04' + pt, c.openssl, 'hex', 'hex', 'compressed')).not.toThrow();
      }
    });

    it('script: add(P, −P) is the all-zero point, NOT 2P', () => {
      const twoP = refArith(c).dbl(G)!;
      const got = add(G_HEX, NEG_G_HEX);
      expect(got).not.toBe(hx(twoP.x) + hx(twoP.y));
      expect(got).toBe(ZERO_POINT);
    });

    it('script: the on-curve gate rejects it — the assert(onCurve(add(a,b))) idiom works', () => {
      expect(onCurve(add(G_HEX, NEG_G_HEX))).toBe(false);
      // the reference agrees the true answer is O
      expect(refArith(c).add(G, { x: G.x, y: mod(c.p - G.y, c.p) })).toBeNull();
    });

    it('script control: doubling and generic addition are untouched', () => {
      const r = refArith(c);
      const twoP = r.dbl(G)!;
      const threeP = r.add(twoP, G)!;
      expect(add(G_HEX, G_HEX)).toBe(hx(twoP.x) + hx(twoP.y));
      expect(add(hx(twoP.x) + hx(twoP.y), G_HEX)).toBe(hx(threeP.x) + hx(threeP.y));
    });
  });

  // ---- interpreter must give the SAME answer as the script ------------------
  const SOURCE = `
class DegenAdd extends SmartContract {
  readonly pt: ${c.pointType};
  constructor(pt: ${c.pointType}) { super(pt); this.pt = pt; }

  public sumEquals(expected: ${c.pointType}) {
    assert(${c.fnAdd}(this.pt, ${c.fnNegate}(this.pt)) == expected);
  }

  public sumOnCurve() {
    assert(${c.fnOnCurve}(${c.fnAdd}(this.pt, ${c.fnNegate}(this.pt))));
  }
}
`;

  describe(`${name} — interpreter and script agree on P + (−P)`, () => {
    it('interpreter: add(P, −P) is the all-zero point', () => {
      const k = TestContract.fromSource(SOURCE, { pt: G_HEX });
      expect(k.call('sumEquals', { expected: ZERO_POINT }).success).toBe(true);
    });

    it('interpreter: the on-curve gate rejects it', () => {
      const k = TestContract.fromSource(SOURCE, { pt: G_HEX });
      expect(k.call('sumOnCurve').success).toBe(false);
    });

    it('the two agree byte-for-byte', () => {
      const k = TestContract.fromSource(SOURCE, { pt: G_HEX });
      const scriptResult = add(G_HEX, NEG_G_HEX);
      expect(k.call('sumEquals', { expected: scriptResult }).success).toBe(true);
    });
  });
}
