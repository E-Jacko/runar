import { SmartContract, assert } from 'runar-lang';

/**
 * Regression reproducer — the ACCEPT direction of the chained shift/bitwise
 * divergence (commit 694c891b), the mirror image of
 * `2026-07-14-chained-shift-and-length-mismatch`.
 *
 * `x << 8` with x = 2 leaves a 1-byte, non-minimal 0x00 (OP_LSHIFT preserves
 * byte length). The literal 5 is the 1-byte [0x05]. Lengths MATCH, so OP_OR
 * succeeds and yields [0x05] = 5 — the spend is valid.
 *
 * The buggy interpreters re-minimised `2 << 8` to numeric 0 -> EMPTY byte
 * array, then hit a length mismatch against [0x05] and rejected a spend the
 * deployed script accepts. Same root cause, opposite verdict, so this entry
 * catches a one-sided "fix" that only handles the abort direction.
 *
 * Correct behaviour: BOTH engines accept. This entry pins accept/accept.
 */
export class ChainedShiftOr extends SmartContract {
  constructor() {
    super();
  }

  public testChainedOr(x: bigint): void {
    assert(((x << 8n) | 5n) === 5n);
  }
}
