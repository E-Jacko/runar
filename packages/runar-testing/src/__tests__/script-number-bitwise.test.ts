import { describe, it, expect } from 'vitest';
import { ScriptVM } from '../vm/script-vm.js';
import {
  decodeScriptNumber,
  scriptNumberBitwise,
  scriptNumberInvert,
  scriptNumberShift,
} from '../vm/utils.js';
import { buildWitness } from '../oracle/witness.js';

// The interpreter models values as bigint; the deployed script runs
// OP_AND/OP_OR/OP_XOR/OP_INVERT/OP_LSHIFT/OP_RSHIFT on the operands' raw
// script-number bytes. These tests pin the interpreter's scriptNumber* helpers
// to the ScriptVM (the on-chain reference), so TestContract can never again
// report a different result than the deployed script for these operators.

const OP: Record<string, number> = { '&': 0x84, '|': 0x85, '^': 0x86, '<<': 0x98, '>>': 0x99 };
const OP_INVERT = 0x83;

type VmResult = { threw: boolean; value?: bigint; error?: string };

function vmBinary(a: bigint, b: bigint, opByte: number): VmResult {
  const locking = new Uint8Array([...buildWitness([a, b]), opByte]);
  const r = new ScriptVM().execute(new Uint8Array([]), locking);
  if (!r.success && r.error) return { threw: true, error: r.error };
  const top = r.stack[r.stack.length - 1];
  return { threw: false, value: top ? decodeScriptNumber(top) : 0n };
}
function vmUnary(a: bigint, opByte: number): VmResult {
  const locking = new Uint8Array([...buildWitness([a]), opByte]);
  const r = new ScriptVM().execute(new Uint8Array([]), locking);
  if (!r.success && r.error) return { threw: true, error: r.error };
  const top = r.stack[r.stack.length - 1];
  return { threw: false, value: top ? decodeScriptNumber(top) : 0n };
}

describe('script-number bitwise/shift semantics (regression anchors)', () => {
  it('shifts match the byte-array truncation, not native bigint', () => {
    expect(scriptNumberShift('<<', 255n, 1n)).toBe(254n); // native would be 510
    expect(scriptNumberShift('<<', 256n, 1n)).toBe(512n);
    expect(scriptNumberShift('<<', 5n, 3n)).toBe(40n);
    expect(scriptNumberShift('>>', 32n, 3n)).toBe(4n);
    expect(scriptNumberShift('>>', 255n, 1n)).toBe(-127n); // native would be 127
  });
  it('OP_INVERT flips the operand bytes, not native ~n', () => {
    expect(scriptNumberInvert(5n)).toBe(-122n); // native ~5 would be -6
    expect(scriptNumberInvert(255n)).toBe(-32512n);
    expect(scriptNumberInvert(0n)).toBe(0n);
  });
  it('AND/OR/XOR require equal operand byte length (abort otherwise)', () => {
    expect(() => scriptNumberBitwise('&', 255n, 1n)).toThrow(/same length/);
    expect(() => scriptNumberBitwise('|', 7n, 0n)).toThrow(/same length/);
    expect(scriptNumberBitwise('&', 5n, 3n)).toBe(1n);
    expect(scriptNumberBitwise('&', -1n, 5n)).toBe(1n); // native would be 5
  });
  it('negative shift counts abort', () => {
    expect(() => scriptNumberShift('<<', 5n, -1n)).toThrow(/negative shift/);
    expect(() => scriptNumberShift('>>', 5n, -1n)).toThrow(/negative shift/);
  });
});

describe('script-number helpers agree with ScriptVM over a fuzz', () => {
  // Seeded LCG — deterministic, no Math.random.
  let seed = 0x9e3779b9 >>> 0;
  const rand = () => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed;
  };
  const randVal = () => {
    const mag = BigInt(rand() % 70000);
    return (rand() & 1) === 0 ? mag : -mag;
  };

  it('binary & | ^ << >> match the VM (value + abort) for 3000 random cases', () => {
    for (let i = 0; i < 3000; i++) {
      const a = randVal();
      // shift counts stay small & sometimes negative; logical operands arbitrary.
      for (const sym of ['&', '|', '^', '<<', '>>'] as const) {
        const b = sym === '<<' || sym === '>>' ? BigInt((rand() % 20) - 2) : randVal();
        let helperThrew = false;
        let helperVal: bigint | undefined;
        try {
          helperVal = sym === '<<' || sym === '>>'
            ? scriptNumberShift(sym, a, b)
            : scriptNumberBitwise(sym, a, b);
        } catch { helperThrew = true; }
        const vm = vmBinary(a, b, OP[sym]!);
        if (helperThrew) {
          expect(vm.threw, `${a} ${sym} ${b}: helper threw, VM did not (val=${vm.value})`).toBe(true);
        } else {
          expect(vm.threw, `${a} ${sym} ${b}: VM threw (${vm.error}), helper=${helperVal}`).toBe(false);
          expect(vm.value, `${a} ${sym} ${b}`).toBe(helperVal);
        }
      }
    }
  });

  it('unary ~ matches the VM for random operands', () => {
    for (let i = 0; i < 1500; i++) {
      const a = randVal();
      const helperVal = scriptNumberInvert(a);
      const vm = vmUnary(a, OP_INVERT);
      expect(vm.threw, `~${a}: VM threw ${vm.error}`).toBe(false);
      expect(vm.value, `~${a}`).toBe(helperVal);
    }
  });
});
