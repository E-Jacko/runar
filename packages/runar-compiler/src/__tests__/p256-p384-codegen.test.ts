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
// hex mismatch. These goldens lock the exact op count for each emitter so a
// regression fails here, naming the emitter. They match the Go peer goldens
// in compilers/go/codegen/crypto_codegen_test.go (same constant templates).
// Update them only alongside a deliberate codegen change.
// ---------------------------------------------------------------------------

function countOps(fn: (emit: (op: StackOp) => void) => void): number {
  const ops: StackOp[] = [];
  fn((op: StackOp) => ops.push(op));
  return ops.length;
}

describe('NIST P-256 / P-384 codegen — op-count goldens (T-006)', () => {
  const goldens: Array<[name: string, fn: (emit: (op: StackOp) => void) => void, expected: number]> = [
    ['p256Add',               emitP256Add,                6642],
    ['p256Mul',               emitP256Mul,               107579],
    ['p256MulGen',            emitP256MulGen,            107581],
    ['p256Negate',            emitP256Negate,              945],
    ['p256OnCurve',           emitP256OnCurve,             546],
    ['p256EncodeCompressed',  emitP256EncodeCompressed,     14],
    ['verifyECDSA_P256',      emitVerifyECDSA_P256,     232272],
    ['p384Add',               emitP384Add,               11448],
    ['p384Mul',               emitP384Mul,              162977],
    ['p384MulGen',            emitP384MulGen,           162979],
    ['p384Negate',            emitP384Negate,             1393],
    ['p384OnCurve',           emitP384OnCurve,             770],
    ['p384EncodeCompressed',  emitP384EncodeCompressed,     14],
    ['verifyECDSA_P384',      emitVerifyECDSA_P384,     356506],
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
