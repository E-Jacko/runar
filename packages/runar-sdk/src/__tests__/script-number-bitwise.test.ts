import { describe, it, expect } from 'vitest';
import { computeNewState } from '../anf-interpreter.js';
import type { ANFProgram } from 'runar-ir-schema';

// ---------------------------------------------------------------------------
// Bitwise/shift script-number semantics (regression anchors)
// ---------------------------------------------------------------------------
//
// `& | ^ ~ << >>` on bigint compile to OP_AND/OP_OR/OP_XOR/OP_INVERT/
// OP_LSHIFT/OP_RSHIFT, which operate on the operands' minimal script-number
// BYTES, not their numeric value (spec/opcodes.md). These tests drive the
// interpreter's bin_op/unary_op evaluation through the public
// `computeNewState` API and pin it to that byte-array semantic — mirroring
// the reference fix already landed for the runar-testing interpreter
// (packages/runar-testing/src/__tests__/script-number-bitwise.test.ts) — so
// the SDK's off-chain state derivation never disagrees with the deployed
// script for these operators.

function makeANF(overrides: Partial<ANFProgram> = {}): ANFProgram {
  return {
    contractName: 'Test',
    properties: [],
    methods: [],
    ...overrides,
  };
}

function makeBinOpANF(op: string): ANFProgram {
  return makeANF({
    properties: [{ name: 'result', type: 'bigint', readonly: false }],
    methods: [{
      name: 'compute',
      params: [
        { name: 'a', type: 'bigint' },
        { name: 'b', type: 'bigint' },
      ],
      body: [
        { name: 't0', value: { kind: 'load_param', name: 'a' } },
        { name: 't1', value: { kind: 'load_param', name: 'b' } },
        { name: 't2', value: { kind: 'bin_op', op, left: 't0', right: 't1' } },
        { name: 't3', value: { kind: 'update_prop', name: 'result', value: 't2' } },
      ],
      isPublic: true,
    }],
  });
}

function makeUnaryOpANF(op: string): ANFProgram {
  return makeANF({
    properties: [{ name: 'result', type: 'bigint', readonly: false }],
    methods: [{
      name: 'compute',
      params: [{ name: 'a', type: 'bigint' }],
      body: [
        { name: 't0', value: { kind: 'load_param', name: 'a' } },
        { name: 't1', value: { kind: 'unary_op', op, operand: 't0' } },
        { name: 't2', value: { kind: 'update_prop', name: 'result', value: 't1' } },
      ],
      isPublic: true,
    }],
  });
}

function binOp(op: string, a: bigint, b: bigint): unknown {
  return computeNewState(makeBinOpANF(op), 'compute', { result: 0n }, { a, b }).result;
}

function unaryOp(op: string, a: bigint): unknown {
  return computeNewState(makeUnaryOpANF(op), 'compute', { result: 0n }, { a }).result;
}

describe('ANF interpreter: script-number bitwise/shift semantics (regression anchors)', () => {
  it('shifts match the byte-array truncation, not native bigint', () => {
    expect(binOp('<<', 255n, 1n)).toBe(254n); // native would be 510
    expect(binOp('<<', 256n, 1n)).toBe(512n);
    expect(binOp('<<', 5n, 3n)).toBe(40n);
    expect(binOp('>>', 32n, 3n)).toBe(4n);
    expect(binOp('>>', 255n, 1n)).toBe(-127n); // native would be 127
  });

  it('OP_INVERT flips the operand bytes, not native ~n', () => {
    expect(unaryOp('~', 5n)).toBe(-122n); // native ~5 would be -6
    expect(unaryOp('~', 255n)).toBe(-32512n);
    expect(unaryOp('~', 0n)).toBe(0n);
  });

  it('AND/OR/XOR operate on script-number bytes, not native bigint', () => {
    expect(binOp('&', 5n, 3n)).toBe(1n);
    expect(binOp('&', -1n, 5n)).toBe(1n); // native would be 5
  });

  it('AND/OR require equal operand byte length (abort otherwise)', () => {
    expect(() => binOp('&', 255n, 1n)).toThrow(/same length/);
    expect(() => binOp('|', 7n, 0n)).toThrow(/same length/);
  });

  it('negative shift counts abort', () => {
    expect(() => binOp('<<', 5n, -1n)).toThrow(/negative shift/);
  });
});
