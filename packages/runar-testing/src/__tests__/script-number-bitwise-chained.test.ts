import { describe, it, expect } from 'vitest';
import { runDifferentialExecution } from '../oracle/differential-execution.js';

// Chained byte-array-op parity (interpreter vs deployed script).
//
// A SINGLE `<< >> & | ^ ~` on minimal operands was already faithful. But a
// CHAINED expression — where a shift/bitwise RESULT (which on-chain is a
// fixed-length, possibly NON-minimal byte array) feeds another length-sensitive
// `& | ^`/shift — diverged: the interpreter modelled results as bigint and
// re-minimised, losing the real length. Confirmed both directions before the
// byte-threading fix:
//   - over-reject: `(2<<8)|5` — interpreter THREW (OP_OR length mismatch) while
//     the deployed OP_LSHIFT leaves a 1-byte 0x00 and OP_OR([0x00],[0x05])=[0x05]
//     spends.
//   - FUNDS-LOSS: `((1<<8)&0)==0` — interpreter returned 0 (assert passes, spend
//     accepted) while on-chain OP_AND([0x00],[]) ABORTS (length mismatch), so the
//     UTXO is un-spendable. TestContract green, chain rejects.
// The interpreter now threads the exact stack bytes for byte-op results, so both
// directions agree with the deployed script. This suite is the RED→GREEN anchor.

const ctorNone = {};

function diff(source: string, method: string, args: bigint[]) {
  return runDifferentialExecution({
    source,
    fileName: 'Chain.runar.ts',
    method,
    args,
    constructorArgs: ctorNone,
  });
}

describe('chained byte-array-op parity (interpreter vs deployed script)', () => {
  // (x << 8) | y  === 5 . For x=2,y=5 the on-chain value is 5 (OP_LSHIFT leaves a
  // 1-byte 0x00; OP_OR with 0x05 = 0x05), so the script SPENDS. Pre-fix the
  // interpreter threw at OP_OR -> rejected -> divergence.
  const orSource = `
class Chain extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint, y: bigint): void {
    assert(((x << 8n) | y) === 5n);
  }
}`;

  it('over-reject case: (2<<8)|5 === 5 — interpreter and script both ACCEPT', () => {
    const r = diff(orSource, 'unlock', [2n, 5n]);
    expect(r.agrees).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.interpreterAccepted).toBe(true);
  });

  // ((x << 8) & y) === 0 . For x=1,y=0 the on-chain OP_AND([0x00],[]) ABORTS
  // (length mismatch) so the script REJECTS. Pre-fix the interpreter computed
  // 0 & 0 = 0, the assert passed, and TestContract reported the spend as VALID —
  // the funds-loss direction.
  const andSource = `
class Chain extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint, y: bigint): void {
    assert(((x << 8n) & y) === 0n);
  }
}`;

  it('funds-loss case: ((1<<8)&0)===0 — interpreter and script both REJECT', () => {
    const r = diff(andSource, 'unlock', [1n, 0n]);
    expect(r.agrees).toBe(true);
    expect(r.vmAccepted).toBe(false);
    expect(r.interpreterAccepted).toBe(false);
  });

  // Chained invert of a non-minimal shift result.
  const invSource = `
class Chain extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint): void {
    assert((~(x << 8n)) === -1n);
  }
}`;

  it('chained invert: ~(2<<8) matches the deployed OP_INVERT of [0x00]', () => {
    // OP_LSHIFT leaves [0x00]; OP_INVERT -> [0xff] -> decode -127. So ~(2<<8) is
    // -127, not -1; the assert fails on BOTH engines (they must agree either way).
    const r = diff(invSource, 'unlock', [2n]);
    expect(r.agrees).toBe(true);
  });

  it('mini-fuzz: (x<<8)&y and (x<<8)|y agree with the deployed script for many inputs', () => {
    // Deterministic sweep (no RNG): mixes values whose shift result is a 1-byte
    // 0x00 (non-minimal) against minimal operands of assorted lengths, so the
    // length-mismatch path is exercised in both the abort and non-abort case.
    const xs = [0n, 1n, 2n, 5n, 127n, 128n, 255n, 256n, 300n];
    const ys = [0n, 1n, 5n, 127n, 128n, 255n, 256n];
    let checked = 0;
    for (const x of xs) {
      for (const y of ys) {
        for (const src of [orSource, andSource]) {
          const r = diff(src, 'unlock', [x, y]);
          expect(
            r.agrees,
            `divergence for x=${x} y=${y}: interp=${r.interpreterAccepted} vm=${r.vmAccepted} (${r.interpreterError ?? r.vmError ?? ''})`,
          ).toBe(true);
          checked++;
        }
      }
    }
    expect(checked).toBe(xs.length * ys.length * 2);
  });
});
