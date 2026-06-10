/**
 * Repeated-operand consume bug (issue: hand-written ANF via compileFromANF).
 *
 * `bringToTop(ref, consume=true)` is a pure no-op when the ref is already on
 * top of the stack — the value is left in place for the consumer opcode. When
 * a SINGLE ANF value reads the SAME ref in more than one operand position
 * (e.g. `t := x + x`, `t := min(x, x)`), every load used to make an
 * independent consume decision via `isLastUse`. If the binding is the ref's
 * last use, all loads become consume-mode, so only ONE stack slot backs TWO
 * (or more) operand positions and the emitted opcode underflows (or, when the
 * ref is buried below other live slots, silently pairs the wrong slot).
 *
 * This is unreachable from the language frontend (pass 04 gives every operand
 * a fresh temp), but fully reachable through `compileFromANF` / CLI `--ir`.
 *
 * The rule under test (the canonical fix, ported to all 7 compilers):
 * an operand load may consume (ROLL / move) its ref only when this binding is
 * the ref's last use AND the ref does not occur at any OTHER operand position
 * of the same ANF value. Repeated refs always copy (PICK / DUP).
 *
 * These tests execute the emitted script on the runar-testing ScriptVM so
 * they verify semantics, not byte shapes.
 */

import { describe, it, expect } from 'vitest';
// @ts-expect-error vitest resolves this via alias
import { ScriptVM } from 'runar-testing';
import { compile, compileFromANF } from '../index.js';
import type { ANFProgram, ANFBinding } from '../ir/index.js';

/** Build a stateless single-method ANF program (target: bigint property). */
function program(params: string[], body: ANFBinding[]): ANFProgram {
  return {
    contractName: 'Repeat',
    properties: [{ name: 'target', type: 'bigint', readonly: true }],
    methods: [
      {
        name: 'unlock',
        params: params.map(name => ({ name, type: 'bigint' })),
        body,
        isPublic: true,
      },
    ],
  };
}

/** Minimal-push unlocking script for small non-negative integers (0..16). */
function pushSmallInts(values: number[]): Uint8Array {
  return new Uint8Array(values.map(v => {
    if (v === 0) return 0x00; // OP_0
    if (v >= 1 && v <= 16) return 0x50 + v; // OP_1..OP_16
    throw new Error(`pushSmallInts only supports 0..16, got ${v}`);
  }));
}

function hexToBytes(hex: string): Uint8Array {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
  return out;
}

function runScript(unlockArgs: number[], lockingHex: string): { success: boolean; error?: string } {
  const vm = new ScriptVM();
  const result = vm.execute(pushSmallInts(unlockArgs), hexToBytes(lockingHex));
  return { success: result.success, error: result.error };
}

describe('repeated ref in one ANF value (compileFromANF / --ir path)', () => {
  it('bin_op with the same ref twice: t := x + x executes correctly', () => {
    // unlock(x) { assert(x + x === target) }  with target baked to 10
    const anf = program(['x'], [
      { name: 't0', value: { kind: 'bin_op', op: '+', left: 'x', right: 'x' } },
      { name: 't1', value: { kind: 'load_prop', name: 'target' } },
      { name: 't2', value: { kind: 'bin_op', op: '===', left: 't0', right: 't1' } },
      { name: 't3', value: { kind: 'assert', value: 't2' } },
    ]);
    const { scriptHex, scriptAsm } = compileFromANF(anf, {
      constructorArgs: { target: 10n },
      disableConstantFolding: true,
    });

    // The emitted script must duplicate x before the ADD so OP_ADD has two
    // stack items to pop.
    expect(scriptAsm).toMatch(/OP_DUP(?: OP_\w+)*? OP_ADD/);

    // 5 + 5 === 10 → spendable.
    expect(runScript([5], scriptHex)).toEqual({ success: true });
    // 4 + 4 === 8 ≠ 10 → script evaluates to false (NOT a stack underflow).
    const wrong = runScript([4], scriptHex);
    expect(wrong.success).toBe(false);
    expect(wrong.error ?? '').not.toMatch(/underflow/i);
  });

  it('call with the same ref in two argument positions: min(x, x)', () => {
    // unlock(x) { assert(min(x, x) === target) }  with target baked to 5
    const anf = program(['x'], [
      { name: 't0', value: { kind: 'call', func: 'min', args: ['x', 'x'] } },
      { name: 't1', value: { kind: 'load_prop', name: 'target' } },
      { name: 't2', value: { kind: 'bin_op', op: '===', left: 't0', right: 't1' } },
      { name: 't3', value: { kind: 'assert', value: 't2' } },
    ]);
    const { scriptHex } = compileFromANF(anf, {
      constructorArgs: { target: 5n },
      disableConstantFolding: true,
    });

    expect(runScript([5], scriptHex)).toEqual({ success: true });
    expect(runScript([6], scriptHex).success).toBe(false);
  });

  it('repeated ref buried below another live slot: t := x + x with y on top', () => {
    // unlock(x, y) { assert(x + x + y === target) }  with target baked to 13.
    // At t0 the stack is [x, y] (y on top): x sits at depth 1, so a naive
    // "last occurrence may still consume" rule pairs the wrong slot
    // (computes x + y) instead of duplicating x.
    const anf = program(['x', 'y'], [
      { name: 't0', value: { kind: 'bin_op', op: '+', left: 'x', right: 'x' } },
      { name: 't1', value: { kind: 'bin_op', op: '+', left: 't0', right: 'y' } },
      { name: 't2', value: { kind: 'load_prop', name: 'target' } },
      { name: 't3', value: { kind: 'bin_op', op: '===', left: 't1', right: 't2' } },
      { name: 't4', value: { kind: 'assert', value: 't3' } },
    ]);
    const { scriptHex } = compileFromANF(anf, {
      constructorArgs: { target: 13n },
      disableConstantFolding: true,
    });

    // x=5, y=3: 5 + 5 + 3 = 13 → spendable.
    expect(runScript([5, 3], scriptHex)).toEqual({ success: true });
    // The buggy pairing computes x + y + y = 11 ≠ 13; also reject a plain miss.
    expect(runScript([4, 3], scriptHex).success).toBe(false);
  });

  it('bin_op with distinct refs is unchanged (frontend canonical Dbl)', () => {
    // The frontend path gives every operand a fresh temp; its output must not
    // shift under the repeated-operand rule (no ref repeats within a value).
    const source = `
import { SmartContract, assert } from 'runar-lang';
export class Dbl extends SmartContract {
  readonly target: bigint;
  constructor(target: bigint) { super(target); this.target = target; }
  public unlock(x: bigint) { assert(x + x === this.target); }
}
`;
    const result = compile(source, { fileName: 'Dbl.runar.ts', disableConstantFolding: true });
    expect(result.success).toBe(true);
    // DUP SWAP ADD <target-placeholder> NUMEQUAL
    expect(result.scriptHex).toBe('767c93009c');
  });
});
