import { StatefulSmartContract } from 'runar-lang';

/**
 * BranchMergedLocals -- regression fixture for the branch-merged-local
 * miscompilation reported privately on 2026-08-03.
 *
 * Two locals are initialised from state fields and the arms of an `if`
 * reassign DIFFERENT ones, then both feed the continuation. An `if` carries a
 * single value, so ANF lowering could only rewire post-branch references for
 * ONE merged local; with two, every later reference still named the dead
 * pre-branch binding, and stack lowering registered one stack-map slot for two
 * physical results and resolved every later operand one slot off. The script
 * compiled cleanly, passed the ANF-interpreter tests, and was rejected by the
 * real Script interpreter -- a permanently unspendable contract from idiomatic
 * source.
 *
 * Both arms now end with the same canonical result block, so the merged values
 * survive whichever branch runs. See
 * packages/runar-testing/src/__tests__/branch-merged-locals-vm.test.ts for the
 * real-Script-VM proof.
 */
class BranchMergedLocals extends StatefulSmartContract {
  a: bigint;
  b: bigint;

  constructor(a: bigint, b: bigint) {
    super(a, b);
    this.a = a;
    this.b = b;
  }

  public bid(amount: bigint, toFirst: bigint) {
    let na = this.a;
    let nb = this.b;
    if (toFirst > 0n) {
      na = amount;
    } else {
      nb = amount;
    }
    this.addOutput(1000n, na, nb);
  }
}
