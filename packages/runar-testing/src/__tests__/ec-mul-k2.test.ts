import { describe, it, expect } from 'vitest';
import { Point as BsvPoint, BigNumber } from '@bsv/sdk';
import { emitEcMul, emitEcMulGen, emitMethod } from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * `ecMul` / `ecMulGen` must be correct for the scalar k = 2.
 *
 * The emitted ladder is MSB-first double-and-add over k' = k + 3n with the
 * accumulator initialised to P. At step i the accumulator holds c_i·P where
 * c_i = k' >> i, and the conditional step adds the affine P to (c_i − 1)·P.
 * The Jacobian mixed-add is undefined when the two operands are equal:
 * H = U2 − X1 = 0 makes Z3 = Z1·H = 0, and `fieldInv` is Fermat, so
 * fieldInv(0) = 0 and the final Jacobian→affine conversion yields the
 * ALL-ZERO point rather than 2P.
 *
 * c_i ≡ 2 (mod n) with bit i of k' set happens for exactly one scalar in the
 * whole domain — k = 2, at the last iteration — so `ecMul(P, 2n)` and
 * `ecMulGen(2n)` returned 64 zero bytes while every other scalar was right.
 * Any contract multiplying by 2 deployed an UNSPENDABLE script, byte-identical
 * across all seven tiers.
 *
 * Every expectation here is executed through the real @bsv/sdk `Spend`
 * interpreter and compared against @bsv/sdk's own secp256k1 implementation —
 * never against the Rúnar interpreter, which computes EC natively and so
 * agreed with itself while the emitted script was wrong.
 */

const GX = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n;
const GY = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n;
const P = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn;
const N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;

const G_BSV = new BsvPoint(GX.toString(16), GY.toString(16));

// --- a from-scratch double-and-add, sharing no code with the compiler -------

type Aff = { x: bigint; y: bigint } | null;

function inv(a: bigint): bigint {
  let [r, b, e] = [1n, ((a % P) + P) % P, P - 2n];
  while (e > 0n) {
    if (e & 1n) r = (r * b) % P;
    b = (b * b) % P;
    e >>= 1n;
  }
  return r;
}
function dbl(p: Aff): Aff {
  if (p === null) return null;
  const s = (3n * p.x * p.x % P) * inv(2n * p.y) % P;
  const x = ((s * s - 2n * p.x) % P + P) % P;
  return { x, y: ((s * (p.x - x) - p.y) % P + P) % P };
}
function add(p: Aff, q: Aff): Aff {
  if (p === null) return q;
  if (q === null) return p;
  if (p.x === q.x) return (p.y + q.y) % P === 0n ? null : dbl(p);
  const s = (((q.y - p.y) % P + P) % P) * inv(q.x - p.x) % P;
  const x = ((s * s - p.x - q.x) % P + P) % P;
  return { x, y: ((s * (p.x - x) - p.y) % P + P) % P };
}
/** k·P computed from the curve parameters alone. */
function refMul(k: bigint, p: Aff): Aff {
  let r: Aff = null;
  let a = p;
  while (k > 0n) {
    if (k & 1n) r = add(r, a);
    a = dbl(a);
    k >>= 1n;
  }
  return r;
}

// --- harness ---------------------------------------------------------------

function pointHex(p: NonNullable<Aff>): string {
  return p.x.toString(16).padStart(64, '0') + p.y.toString(16).padStart(64, '0');
}
function blob(hex: string): Uint8Array {
  return Uint8Array.from(Buffer.from(hex, 'hex'));
}
/** Execute the ops through the real @bsv/sdk interpreter, return TOS hex. */
function exec(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as never as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}
function ecMul(pHex: string, k: bigint): string {
  const ops: StackOp[] = [
    { op: 'push', value: blob(pHex) } as StackOp,
    { op: 'push', value: k } as StackOp,
  ];
  emitEcMul((o) => ops.push(o));
  return exec(ops);
}
function ecMulGen(k: bigint): string {
  const ops: StackOp[] = [{ op: 'push', value: k } as StackOp];
  emitEcMulGen((o) => ops.push(o));
  return exec(ops);
}
/** k·G according to @bsv/sdk. */
function bsvMul(k: bigint): string {
  const r = G_BSV.mul(new BigNumber(k.toString(16), 16));
  return r.getX().toHex(32) + r.getY().toHex(32);
}

const G_HEX = pointHex({ x: GX, y: GY });

describe('emitEcMul / emitEcMulGen', () => {
  it('oracles agree: from-scratch double-and-add === @bsv/sdk', () => {
    for (const k of [1n, 2n, 3n, 4n, 5n, 12345n, N - 1n]) {
      expect(pointHex(refMul(k, { x: GX, y: GY })!)).toBe(bsvMul(k));
    }
  });

  // k = 2 is the whole defect: the single scalar in [1, n-1] at which the
  // ladder's mixed-add is handed two equal operands.
  it('ecMul(G, 2) === 2G (was 64 zero bytes)', () => {
    expect(ecMul(G_HEX, 2n)).toBe(bsvMul(2n));
  });

  it('ecMulGen(2) === 2G (was 64 zero bytes)', () => {
    expect(ecMulGen(2n)).toBe(bsvMul(2n));
  });

  it('ecMul(3G, 2) === 6G — the exception is not specific to the generator', () => {
    const p3 = refMul(3n, { x: GX, y: GY })!;
    expect(ecMul(pointHex(p3), 2n)).toBe(pointHex(refMul(6n, { x: GX, y: GY })!));
  });

  // Controls: the scalars that already worked must keep working, so the fix
  // cannot have been a blanket "always double".
  for (const k of [1n, 3n, 4n, 5n, 7n, 12345n]) {
    it(`control: ecMul(G, ${k}) === ${k}G`, () => {
      expect(ecMul(G_HEX, k)).toBe(bsvMul(k));
    });
  }

  it('control: ecMul(G, n-1) === -G', () => {
    expect(ecMul(G_HEX, N - 1n)).toBe(bsvMul(N - 1n));
  });

  it('control: pseudorandom scalars', () => {
    const ks = [
      0xdeadbeefcafebabe1234567890abcdefn,
      0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0n,
      N / 2n,
    ];
    for (const k of ks) expect(ecMul(G_HEX, k)).toBe(bsvMul(k));
  });
});
