import { SmartContract, assert } from 'runar-lang';

/**
 * Regression reproducer — a shift whose RESULT is a non-minimal ZERO, then
 * consumed NUMERICALLY.
 *
 * `OP_RSHIFT` preserves the operand's byte length, so `1 >> 1` leaves the
 * 1-byte array [0x00]. The minimal encoding of zero is the EMPTY array, so
 * [0x00] is non-minimal. `=== 0n` lowers to `OP_NOT`, a NUMERIC op, and every
 * numeric op on chain decodes with fRequireMinimal=true and ABORTS.
 *
 * The buggy interpreter threaded scriptBytes through the shift but then read
 * only the decoded value in the comparison, re-minimising [0x00] to 0 and
 * ACCEPTING. `TestContract` went green and the deployed UTXO was unspendable —
 * the funds-locking direction, and the mirror of
 * `2026-07-14-chained-shift-or-nonminimal` (which pins the interpreter wrongly
 * REJECTING). That entry's note says it exists so a one-sided fix cannot pass;
 * this entry is the side it does not reach.
 *
 * Correct behaviour: BOTH engines REJECT.
 */
export class ShiftNonMinimalZero extends SmartContract {
  readonly n: bigint;

  constructor(n: bigint) {
    super(n);
    this.n = n;
  }

  public spend(): void {
    assert((this.n >> 1n) === 0n);
  }
}
