import { StatefulSmartContract } from 'runar-lang';

/**
 * LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
 * the enclosing scope, which is what an `if` inside a loop body always makes
 * them. Construct-ledger row `loop-carried-locals-k2`, the member that was
 * still open after the nested-loop fix.
 *
 * `conformance/tests/merge-locals-shapes` pins the branch-merge arities with
 * the merged locals LIVE after the `if` (the enclosing scope reads them), and
 * `conformance/tests/bounded-loop` pins a loop with no branch in it. Neither
 * covers their intersection, and the intersection is where the merge block's
 * premise fails: a loop body's last-use map ends AT the `if`, so no merged
 * local is live after it.
 *
 *   guarded -- K=2 merged locals reassigned inside an `if` WITHOUT an `else`
 *              inside a bounded loop. Pre-fix, all seven tiers registered ONE
 *              stackMap name for the two physical results and the continuation
 *              committed `nb = x` where the source says `3x` -- silently, and
 *              as a permanently unspendable UTXO.
 *   afterIf -- the K=1 arity of the same gap: the local is rebound inside the
 *              `if` and read AFTER it but still inside the loop body. Pre-fix
 *              this was REJECTED outright with `Value 'na' not found on stack`.
 */
class LoopIfMergedLocals extends StatefulSmartContract {
  a: bigint;
  b: bigint;
  c: bigint;

  constructor(a: bigint, b: bigint, c: bigint) {
    super(a, b, c);
    this.a = a;
    this.b = b;
    this.c = c;
  }

  public guarded(x: bigint, limit: bigint) {
    let na: bigint = 0n;
    let nb: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < limit) {
        na = na + x;
        nb = nb + na;
      }
    }
    this.addOutput(1000n, na, nb, this.c);
  }

  public afterIf(x: bigint, limit: bigint) {
    let na: bigint = 0n;
    let nb: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < limit) {
        na = na + x;
      }
      nb = nb + na;
    }
    this.addOutput(1000n, na, nb, this.c);
  }
}
