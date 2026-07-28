import { SmartContract, assert } from 'runar-lang';

/**
 * Regression reproducer — the FUNDS-LOSS direction of the chained shift/bitwise
 * divergence (commit 694c891b).
 *
 * `x << 8` with x = 1 leaves a 1-byte, NON-MINIMAL 0x00 on the stack: OP_LSHIFT
 * preserves the operand's byte length, so [0x01] shifted 8 bits becomes [0x00].
 * The literal `0` is the EMPTY byte array. OP_AND requires equal-length
 * operands, so the deployed script ABORTS and the UTXO is un-spendable.
 *
 * The buggy interpreters re-minimised each intermediate result to a bare
 * integer, so `1 << 8` became numeric 0 -> empty byte array, `& 0` succeeded,
 * `=== 0` was true, and TestContract reported the spend VALID. A developer
 * would have deployed against that verdict and lost the funds.
 *
 * Correct behaviour: BOTH engines reject. This entry pins reject/reject.
 */
export class ChainedShiftAnd extends SmartContract {
  constructor() {
    super();
  }

  public testChainedAnd(x: bigint): void {
    assert(((x << 8n) & 0n) === 0n);
  }
}
