import { describe, it, expect } from 'vitest';
import {
  emitP256Add,
  emitP256Mul,
  emitP256MulGen,
  emitP256Negate,
  emitP256OnCurve,
  emitP256EncodeCompressed,
  emitVerifyECDSA_P256,
  emitP384Add,
  emitP384Mul,
  emitP384MulGen,
  emitP384Negate,
  emitP384OnCurve,
  emitP384EncodeCompressed,
  emitVerifyECDSA_P384,
} from '../passes/p256-p384-codegen.js';
import type { StackOp } from '../ir/index.js';

// ---------------------------------------------------------------------------
// Op-count goldens for the NIST P-256 / P-384 emitters (T-006).
//
// The p256-primitives / p256-wallet / p384-primitives / p384-wallet
// conformance fixtures exercise these builtins end-to-end across all 7 tiers,
// but the TS tier had no *localized* unit test pinning the emit output — a
// TS-side codegen regression would only surface as a whole-suite conformance
// hex mismatch. These goldens lock the exact size of each emitter's op TREE —
// `if` bodies included, see countOpTree — so a regression fails here, naming
// the emitter. They match the Go peer goldens in
// compilers/go/codegen/crypto_codegen_test.go (same constant templates).
// Update them only alongside a deliberate codegen change.
// ---------------------------------------------------------------------------

/**
 * Total number of StackOps in `ops`, INCLUDING the bodies of `if` ops.
 *
 * A flat `ops.length` cannot see inside a branch, so any emitter whose work
 * sits in an `if` body — the scalar ladders emit 257 / 385 conditional
 * additions, WOTS+ and SLH-DSA are almost entirely conditional — reports a
 * count that barely moves no matter what the branch contains. Adding +1.3 KB
 * of script inside the ladder's last step left the `p256Mul` / `p384Mul`
 * goldens byte-identical. Recursing is what makes the golden a gate.
 */
function countOpTree(ops: StackOp[]): number {
  let total = 0;
  for (const op of ops) {
    total++;
    if (op.op === 'if') {
      total += countOpTree(op.then);
      total += countOpTree(op.else ?? []);
    }
  }
  return total;
}

function countOps(fn: (emit: (op: StackOp) => void) => void): number {
  const ops: StackOp[] = [];
  fn((op: StackOp) => ops.push(op));
  return countOpTree(ops);
}

describe('NIST P-256 / P-384 codegen — op-count goldens (T-006)', () => {
  // Deltas from the P == -Q fix and the decompression guard, decomposed so a
  // future reader can tell a port bug from an expected move:
  //
  //   pNNNAdd            +21 ops — the (py == qy) conjunct and the notinf mask.
  //   verifyECDSA_P256   +85 ops = 52 + 33
  //   verifyECDSA_P384  +339 ops = 52 + 287
  //
  //   52 is curve-INDEPENDENT: 21 for the affine-add mask (verifyECDSA calls
  //   cAffineAdd once, for R1 + R2), plus the residue check, the x < p check,
  //   the altstack stash and the closing OP_BOOLAND. Both curves pay exactly
  //   52, which is what makes it structural.
  //
  //   The remainder is one op per SET BIT of (p+1)/4, minus the MSB that seeds
  //   the loop rather than stepping it: popcount is 34 on P-256 and 288 on
  //   P-384, giving 33 and 287. Cause: `_dk_y2_keep` now sits under `_dk_y2`
  //   for the whole of cFieldPow, pushing that loop's copyToTop(base) from
  //   depth 1 (a 1-op OP_OVER) to depth 2 (push + OP_PICK).
  //
  // In BYTES there are two figures, and they differ by 3 — do not treat either
  // as wrong. Emitting the primitive STANDALONE through emitMethod costs
  // +151 (P-256) / +437 (P-384). One call site inside a compiled contract costs
  // +148 / +434, because the peephole optimizer folds three more bytes at the
  // boundary with the surrounding contract code; that is what the p256-wallet
  // and p384-wallet golden deltas show. Either way it is +0.015% / +0.022% of a
  // 0.96 MB / 1.96 MB script, so the simple `_dk_y2_keep` placement was kept
  // over stashing the copy on the altstack to avoid the depth shift.
  //
  // See the Zig-divergence note in ec.test.ts: these are pre-peephole OP
  // counts, not bytes, and the Zig peer's goldens legitimately differ.
  //
  // Second move, the argument-validation fix (universal forgery — see
  // cEmitSigRangeGate and docs/audit/2026-08-ec-degenerate-cases.md):
  //
  //   verifyECDSA_P256  +58 ops
  //   verifyECDSA_P384  +58 ops
  //
  //   +58 is curve-INDEPENDENT because every added op is a fixed-shape gate,
  //   not a per-bit loop: 2 x 10 for the `_sig` / `_pk` length clamps, 1 for
  //   their OP_BOOLAND, 26 for the (r, s) range gate (2 x {OP_0NOTEQUAL, a
  //   copy, an n push, OP_LESSTHAN, OP_BOOLAND} plus roll/pick bookkeeping and
  //   the joining OP_BOOLAND), 8 for the SEC1 prefix test and its fold-in, and
  //   4 for collapsing the three verdicts into `_input_ok`. The two curves
  //   differ only in the SIZE of the constants pushed, which op counts cannot
  //   see. In bytes it is +225 (P-256) / +306 (P-384) standalone, the gap being
  //   the wider n pushes (2 x 48 vs 2 x 32 bytes) and the wider clamp pads
  //   (96 + 49 vs 64 + 33) — 0.023% / 0.015% of the whole script.
  const goldens: Array<[name: string, fn: (emit: (op: StackOp) => void) => void, expected: number]> = [
    ['p256Add',               emitP256Add,                6663],
    ['p256Mul',               emitP256Mul,              140036],
    ['p256MulGen',            emitP256MulGen,           140038],
    ['p256Negate',            emitP256Negate,              945],
    ['p256OnCurve',           emitP256OnCurve,             559],
    ['p256EncodeCompressed',  emitP256EncodeCompressed,     16],
    ['verifyECDSA_P256',      emitVerifyECDSA_P256,     297331],
    ['p384Add',               emitP384Add,               11469],
    ['p384Mul',               emitP384Mul,              211178],
    ['p384MulGen',            emitP384MulGen,           211180],
    ['p384Negate',            emitP384Negate,             1393],
    ['p384OnCurve',           emitP384OnCurve,             783],
    ['p384EncodeCompressed',  emitP384EncodeCompressed,     16],
    ['verifyECDSA_P384',      emitVerifyECDSA_P384,     453307],
  ];

  for (const [name, fn, expected] of goldens) {
    it(`${name} op count is ${expected}`, () => {
      expect(countOps(fn)).toBe(expected);
    });
  }

  it('every emitted op is well-formed (non-empty op kind)', () => {
    const ops: StackOp[] = [];
    emitP256Add((op: StackOp) => ops.push(op));
    expect(ops.length).toBeGreaterThan(0);
    for (const op of ops) {
      expect((op as { op: string }).op).toBeTruthy();
    }
  });
});
