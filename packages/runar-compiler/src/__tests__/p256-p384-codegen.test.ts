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
  const goldens: Array<[name: string, fn: (emit: (op: StackOp) => void) => void, expected: number]> = [
    ['p256Add',               emitP256Add,                6642],
    ['p256Mul',               emitP256Mul,              140036],
    ['p256MulGen',            emitP256MulGen,           140038],
    ['p256Negate',            emitP256Negate,              945],
    ['p256OnCurve',           emitP256OnCurve,             559],
    ['p256EncodeCompressed',  emitP256EncodeCompressed,     16],
    ['verifyECDSA_P256',      emitVerifyECDSA_P256,     297188],
    ['p384Add',               emitP384Add,               11448],
    ['p384Mul',               emitP384Mul,              211178],
    ['p384MulGen',            emitP384MulGen,           211180],
    ['p384Negate',            emitP384Negate,             1393],
    ['p384OnCurve',           emitP384OnCurve,             783],
    ['p384EncodeCompressed',  emitP384EncodeCompressed,     16],
    ['verifyECDSA_P384',      emitVerifyECDSA_P384,     452910],
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
