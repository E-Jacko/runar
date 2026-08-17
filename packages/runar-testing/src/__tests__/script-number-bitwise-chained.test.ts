import { describe, it, expect } from 'vitest';
import { runTriModalExecution } from '../oracle/tri-modal-execution.js';

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

// ORACLE (changed 2026-08-17): compare against the CONSENSUS verdict
// (`Spend.validate()`), not the bare `ScriptVM`.
//
// `ScriptVM.success` is "no evaluation error and truthy top of stack" — it does
// NOT apply the consensus wrappers, so it does not enforce MINIMAL ENCODING.
// A chained byte op can leave a non-minimal result (`1 << 8` = [0x00]), and a
// real node ABORTS when a numeric op consumes it while the bare VM happily
// accepts. Asserting against `vmAccepted` therefore pinned the interpreter to a
// weaker oracle than the chain, which is the opposite of this suite's stated
// purpose ("TestContract green, chain rejects").
//
// Measured over this file's own 126-case sweep after the minimal-encoding fix
// in `interpreter.ts`: interpreter vs consensus `Spend` = 0 mismatches;
// interpreter vs bare `ScriptVM` = 22 mismatches, every one a case where the
// bare VM omits the minimal-encoding rule.
const ctorNone = {};

function diff(source: string, method: string, args: bigint[]) {
  const r = runTriModalExecution({
    source,
    fileName: 'Chain.runar.ts',
    method,
    args,
    constructorArgs: ctorNone,
  });
  // Re-key `agrees` onto the consensus verdict.
  return {
    ...r,
    vmAccepted: r.spendAccepted,
    agrees: r.interpreterAccepted === r.spendAccepted,
  };
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
