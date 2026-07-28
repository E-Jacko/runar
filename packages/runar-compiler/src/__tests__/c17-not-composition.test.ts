/**
 * C17 — `OP_NOT` composition residual after `push0-numequal-to-not`.
 *
 * `push0-numequal-to-not` rewrites `PUSH 0; OP_NUMEQUAL` → `OP_NOT`. Taken in
 * isolation that rewrite is value-exact: both compute `x == 0` and both leave a
 * canonical `{0,1}` on the stack.
 *
 * The bug is what it ENABLES. The synthesized `OP_NOT` sits directly on top of
 * an ARBITRARY script number `x`, not on a canonical boolean. `not-not-elim`
 * (`OP_NOT; OP_NOT` → `[]`) is only sound when the value beneath the first
 * `OP_NOT` is already a canonical boolean — its own spec comment says so. Once
 * the rewrite fires, the two rules compose into `PUSH 0; OP_NUMEQUAL; OP_NOT`
 * → `OP_NOT; OP_NOT` → `[]`, i.e. the optimizer deletes the comparison and
 * leaves the raw operand behind.
 *
 * That sequence is exactly what the stack lowerer emits for `x !== 0n`
 * (`05-stack-lower.ts`: `'!==': ['OP_NUMEQUAL', 'OP_NOT']`) on a `bigint`. So
 * `x !== 0n` currently compiles to `x`. Truthiness survives (any non-zero x is
 * truthy), which is why `assert(x !== 0n)` still passes — but the VALUE does
 * not: for `x = 5` the program must leave `1`, the optimized program leaves
 * `5`. Any consumer of that value (a `=== true` comparison, arithmetic, or a
 * stateful continuation that serialises the boolean) diverges.
 *
 * The mirrored composition `OP_NOT; PUSH 0; OP_NUMEQUAL` (`(!b) === false`)
 * collapses the same way.
 */

import { describe, it, expect } from 'vitest';
// @ts-expect-error vitest resolves this via alias (runar-testing is not a tsc dep of runar-compiler)
import { ScriptVM, bytesToHex } from 'runar-testing';
import type { StackOp } from '../ir/index.js';
import { emitMethod } from '../passes/06-emit.js';
import { optimizeStackIR } from '../optimizer/peephole.js';
import { compile } from '../index.js';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const opc = (code: string): StackOp => ({ op: 'opcode', code });
const push = (value: bigint): StackOp => ({ op: 'push', value });

function emitOps(ops: StackOp[]): string {
  return emitMethod({ name: 'c17', ops, maxStackDepth: 0 }).scriptHex;
}

interface Effect {
  success: boolean;
  stack: string[];
}

function effect(ops: StackOp[]): Effect {
  const r = new ScriptVM().executeHex(emitOps(ops));
  return { success: r.success, stack: r.stack.map(bytesToHex) };
}

function hexToBytes(hex: string): Uint8Array {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  return out;
}

/** Run `unlockHex` then `lockingHex` on the VM. */
function runScript(unlockHex: string, lockingHex: string): { success: boolean } {
  const vm = new ScriptVM();
  const r = vm.execute(hexToBytes(unlockHex), hexToBytes(lockingHex));
  return { success: r.success };
}

// ---------------------------------------------------------------------------
// Stack-IR level: the peephole must preserve the VALUE, not just truthiness
// ---------------------------------------------------------------------------

describe('C17: OP_NOT composition after push0-numequal-to-not', () => {
  // `x !== 0n` on a bigint: PUSH x; PUSH 0; OP_NUMEQUAL; OP_NOT
  const xNotEqualZero = (x: bigint): StackOp[] => [
    push(x),
    push(0n),
    opc('OP_NUMEQUAL'),
    opc('OP_NOT'),
  ];

  it('preserves the full stack effect of `x !== 0` for every numeric edge value', () => {
    for (const x of [0n, 1n, 2n, 5n, -1n, 127n, 128n, -128n, 65535n, 2147483647n]) {
      const ops = xNotEqualZero(x);
      expect(effect(optimizeStackIR(ops)), `x = ${x}`).toEqual(effect(ops));
    }
  });

  it('preserves the OUTCOME of `(x !== 0) === true` (success flag diverges, not just bytes)', () => {
    // `(x !== 0) === true` — the boolean is consumed by a numeric comparison,
    // so a non-canonical residual flips the script from accept to reject.
    const ops = [...xNotEqualZero(5n), push(1n), opc('OP_NUMEQUAL')];
    const unoptimized = effect(ops);
    // Sanity: unoptimized answer is "true".
    expect(unoptimized).toEqual({ success: true, stack: ['01'] });
    expect(effect(optimizeStackIR(ops))).toEqual(unoptimized);
  });

  it('preserves the mirrored composition `(!b) === false` (OP_NOT; PUSH 0; OP_NUMEQUAL)', () => {
    for (const b of [0n, 1n, 5n, -1n, 128n]) {
      const ops = [push(b), opc('OP_NOT'), push(0n), opc('OP_NUMEQUAL')];
      expect(effect(optimizeStackIR(ops)), `b = ${b}`).toEqual(effect(ops));
    }
  });

  it('does not delete `PUSH 0; OP_NUMEQUAL; OP_NOT` outright', () => {
    const ops = [push(0n), opc('OP_NUMEQUAL'), opc('OP_NOT')];
    expect(optimizeStackIR(ops).length).toBeGreaterThan(0);
  });
});

// ---------------------------------------------------------------------------
// Source level: peephole ON must agree with peephole OFF
// ---------------------------------------------------------------------------

const SOURCE = `
import { SmartContract, assert } from 'runar-lang';

export class NotComposition extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint): void {
    const nonZero: boolean = x !== 0n;
    assert(nonZero === true);
  }
}
`;

describe('C17: compiled contract — peephole ON must match peephole OFF', () => {
  it('`(x !== 0n) === true` accepts a non-zero witness with the peephole enabled', () => {
    const on = compile(SOURCE, { fileName: 'NotComposition.runar.ts' });
    const off = compile(SOURCE, { fileName: 'NotComposition.runar.ts', disablePeephole: true });
    expect(on.success).toBe(true);
    expect(off.success).toBe(true);

    // witness: x = 5  (OP_5)
    const witness = '55';
    const expected = runScript(witness, off.scriptHex!);
    expect(expected).toEqual({ success: true });
    expect(runScript(witness, on.scriptHex!)).toEqual(expected);
  });

  it('`(x !== 0n) === true` rejects a zero witness identically with and without the peephole', () => {
    const on = compile(SOURCE, { fileName: 'NotComposition.runar.ts' });
    const off = compile(SOURCE, { fileName: 'NotComposition.runar.ts', disablePeephole: true });
    const witness = '00'; // OP_0
    expect(runScript(witness, on.scriptHex!).success).toBe(
      runScript(witness, off.scriptHex!).success,
    );
  });
});
