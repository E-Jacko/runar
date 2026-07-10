/**
 * Issue #121 — non-zero-start and countdown for-loops.
 *
 * The ANF `loop` node historically carried only an iteration `count` and
 * always lowered the iterator as i = 0..count-1. Source-level loops that start
 * at a non-zero value (`for (let i = 1n; i <= 3n; i++)`) or count down
 * (`for (let i = 3n; i > 0n; i--)`) therefore diverged from the interpreter's
 * true semantics. The compiler front-end had been guarding this by REJECTING
 * such loops outright; issue #121 asks for them to compile correctly instead.
 *
 * These tests use the source-vs-script differential oracle: the ANF
 * interpreter (true semantics) and the compiled Bitcoin Script must agree.
 */
import { describe, it, expect } from 'vitest';
import { runDifferentialExecution } from '../oracle/index.js';

// sum of i over the loop must equal the witness `expected`.
function src(loopHeader: string): string {
  return `
import { SmartContract, assert } from 'runar-lang';

export class SumLoop extends SmartContract {
  readonly tag: bigint;
  constructor(tag: bigint) { super(tag); this.tag = tag; }
  public verify(expected: bigint): void {
    let sum: bigint = 0n;
    ${loopHeader} {
      sum = sum + i;
    }
    assert(sum === expected);
  }
}
`;
}

describe('issue #121 — non-zero-start / countdown loops', () => {
  it('control: zero-start counting-up loop agrees (sum 0+1+2+3 === 6)', () => {
    const r = runDifferentialExecution({
      source: src('for (let i: bigint = 0n; i <= 3n; i++)'),
      fileName: 'SumLoop.runar.ts',
      method: 'verify',
      args: [6n],
      constructorArgs: { tag: 0n },
    });
    expect(r.interpreterAccepted).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.agrees).toBe(true);
  });

  it('non-zero start: for (i=1; i<=3; i++) yields 1+2+3 === 6', () => {
    const r = runDifferentialExecution({
      source: src('for (let i: bigint = 1n; i <= 3n; i++)'),
      fileName: 'SumLoop.runar.ts',
      method: 'verify',
      args: [6n],
      constructorArgs: { tag: 0n },
    });
    expect(r.interpreterAccepted).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.agrees).toBe(true);
  });

  it('countdown: for (i=3; i>0; i--) yields 3+2+1 === 6', () => {
    const r = runDifferentialExecution({
      source: src('for (let i: bigint = 3n; i > 0n; i--)'),
      fileName: 'SumLoop.runar.ts',
      method: 'verify',
      args: [6n],
      constructorArgs: { tag: 0n },
    });
    expect(r.interpreterAccepted).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.agrees).toBe(true);
  });

  it('countdown inclusive: for (i=3; i>=1; i--) yields 3+2+1 === 6', () => {
    const r = runDifferentialExecution({
      source: src('for (let i: bigint = 3n; i >= 1n; i--)'),
      fileName: 'SumLoop.runar.ts',
      method: 'verify',
      args: [6n],
      constructorArgs: { tag: 0n },
    });
    expect(r.interpreterAccepted).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.agrees).toBe(true);
  });
});
