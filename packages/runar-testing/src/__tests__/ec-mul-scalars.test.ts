import { describe, it, expect } from 'vitest';
import { emitEcMul, emitEcMulGen, emitMethod } from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { BigNumber, Curve } from '@bsv/sdk';
import { ScriptVM } from '../index.js';

/**
 * `ecMul` / `ecMulGen` must be correct for EVERY scalar, not just the ones a
 * happy-path test reaches for.
 *
 * The Jacobian mixed-add used by the scalar ladder is an INCOMPLETE addition
 * formula: it computes H = U2 - X1 and R = S2 - Y1, so when the accumulator
 * equals the point being added both go to zero and it yields (0, 0, 0) — the
 * zero point — which then propagates through every remaining iteration. The
 * ladder hits that case for k = 2 exactly, so `ecMul(P, 2n)` and `ecMulGen(2n)`
 * returned an all-zero point while k = 1, 3, 4 were fine.
 *
 * That is the same defect class as the `ecAdd` doubling bug (see
 * ec-add-doubling.test.ts), one level down. It is NOT a k=2 special case: the
 * point operand is contract input, so an attacker who can choose P and k can
 * steer the accumulator into the exceptional case deliberately. The fix is to
 * use addition formulas that have no exceptional cases at all.
 *
 * Oracle is @bsv/sdk's own secp256k1 implementation — an independent
 * implementation, not our codegen graded against itself.
 */

const curve = new Curve();
const CURVE_N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;

/** Independent oracle: k*G via @bsv/sdk, as the 64-byte Point blob we emit. */
function oracleMulGen(k: bigint): string {
  const P = curve.g.mul(new BigNumber(k.toString(10), 10));
  return P.getX().toString(16).padStart(64, '0') + P.getY().toString(16).padStart(64, '0');
}

/** Run an op list on the real @bsv/sdk interpreter; return top of stack as hex. */
function run(ops: StackOp[]): string {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  const r = new ScriptVM().executeHex(scriptHex) as { stack: Uint8Array[] };
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

function mulGen(k: bigint): string {
  const ops: StackOp[] = [{ op: 'push', value: k } as StackOp];
  emitEcMulGen((o) => ops.push(o));
  return run(ops);
}

function mul(pointBlobHex: string, k: bigint): string {
  const ops: StackOp[] = [
    { op: 'push', value: Uint8Array.from(Buffer.from(pointBlobHex, 'hex')) } as StackOp,
    { op: 'push', value: k } as StackOp,
  ];
  emitEcMul((o) => ops.push(o));
  return run(ops);
}

const ZERO_POINT = '0'.repeat(128);

describe('emitEcMulGen — scalar coverage', () => {
  // k = 2 is the scalar that trips the incomplete-addition exception.
  // k = 1, 3, 4 pass both before and after the fix; they are the controls that
  // prove the harness itself is sound.
  for (const k of [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n]) {
    it(`ecMulGen(${k}) === ${k}G`, () => {
      const got = mulGen(k);
      expect(got).not.toBe(ZERO_POINT);
      expect(got).toBe(oracleMulGen(k));
    }, 120_000);
  }

  for (const [label, k] of [
    ['2^128', 1n << 128n],
    ['2^255', 1n << 255n],
    ['n-1', CURVE_N - 1n],
    ['a full-width 256-bit scalar', 0x9f3c2a1de4b5768900112233445566778899aabbccddeeff0f1e2d3c4b5a6978n],
  ] as Array<[string, bigint]>) {
    it(`ecMulGen(${label}) matches the @bsv/sdk oracle`, () => {
      expect(mulGen(k)).toBe(oracleMulGen(k));
    }, 120_000);
  }

  // Scalars outside [1, n-1] were undefined behaviour under the old ladder,
  // which added 3n and assumed the sum stayed inside a fixed 258-bit window.
  // The replacement reduces k mod n up front, so the whole domain is defined.
  it('ecMulGen(n) === the point at infinity, encoded as all-zero', () => {
    expect(mulGen(CURVE_N)).toBe(ZERO_POINT);
  }, 120_000);

  it('ecMulGen(0) === the point at infinity, encoded as all-zero', () => {
    expect(mulGen(0n)).toBe(ZERO_POINT);
  }, 120_000);

  it('ecMulGen(n + 5) === 5G (scalar reduced mod n)', () => {
    expect(mulGen(CURVE_N + 5n)).toBe(oracleMulGen(5n));
  }, 120_000);

  it('ecMulGen(-1) === (n-1)G (negative scalar reduced into range)', () => {
    expect(mulGen(-1n)).toBe(oracleMulGen(CURVE_N - 1n));
  }, 120_000);
});

describe('emitEcMul — scalar coverage on a non-generator base', () => {
  // Base point = 2G, so results are (2k)G and can be checked with the same oracle.
  const base = oracleMulGen(2n);

  for (const k of [1n, 2n, 3n, 5n]) {
    it(`ecMul(2G, ${k}) === ${2n * k}G`, () => {
      const got = mul(base, k);
      expect(got).not.toBe(ZERO_POINT);
      expect(got).toBe(oracleMulGen(2n * k));
    }, 120_000);
  }
});

// ---------------------------------------------------------------------------
// End-to-end: the fixture that exposed the bug must now SPEND.
//
// `ec-unit` calls `ecMul(g, 2n)` and then `assert(ecOnCurve(doubled))`. With
// the incomplete mixed-add, `doubled` was the all-zero point, which is not on
// the curve, so the assert failed and the deployed script was UNSPENDABLE —
// byte-identically across all seven tiers. That is how the bug was found: by
// trying to spend the fixture on a live regtest node, where it was rejected
// with "Script failed an OP_VERIFY operation".
//
// This runs the real @bsv/sdk Spend engine under consensus rules (clean-stack,
// push-only unlocking, minimal-push) via the real-crypto oracle, and also
// cross-checks the ANF interpreter, so source semantics and emitted script
// have to agree.
// ---------------------------------------------------------------------------

describe('ec-unit fixture spends end-to-end', () => {
  it('ECUnit.testOps() is accepted by the real Spend engine', async () => {
    const { readFileSync } = await import('node:fs');
    const { resolve } = await import('node:path');
    const { runStatelessSigned, testKey } = await import('../index.js');

    const file = resolve(__dirname, '../../../../examples/ts/ec-unit/ECUnit.runar.ts');
    const source = readFileSync(file, 'utf8');

    const res = runStatelessSigned({
      source,
      fileName: 'ECUnit.runar.ts',
      method: 'testOps',
      args: [],
      constructorArgs: { pubKey: testKey('alice').pubKey },
    });

    expect(res.reachedEngine).toBe(true);
    expect(res.vmError).toBeUndefined();
    expect(res.vmAccepted).toBe(true);
    expect(res.interpreterAccepted).toBe(true);
  }, 300_000);
});
