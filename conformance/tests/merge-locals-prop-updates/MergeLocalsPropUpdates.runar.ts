import { StatefulSmartContract } from 'runar-lang';

/**
 * MergeLocalsPropUpdates -- construct-ledger row
 * `merge-locals-with-prop-updates`.
 *
 * The PALMER-1 branch-merge shape crossed with property mutation: one method
 * that BOTH merges two locals across an `if` AND writes contract properties
 * (`this.x = ...`) from the merged results. Property writes and merged locals
 * both contend for the continuation's state slots, so they interact -- yet
 * before this fixture a method-scoped scan of every `.runar.ts` under
 * `examples/` and `conformance/` found ZERO contracts doing both:
 * branch-merged-locals merges but writes properties only in its constructor,
 * cond-write-multi-field and tic-tac-toe mutate properties inside an `if` but
 * declare no locals at all.
 *
 * `total` is derived from BOTH merged locals, so a merge that resurrects a
 * dead pre-branch binding shows up as a wrong committed value rather than a
 * rejected spend -- pinned by `expectedState` in
 * conformance/witnesses/real-crypto/merge-locals-prop-updates.json.
 */
class MergeLocalsPropUpdates extends StatefulSmartContract {
  a: bigint;
  b: bigint;
  total: bigint;

  constructor(a: bigint, b: bigint, total: bigint) {
    super(a, b, total);
    this.a = a;
    this.b = b;
    this.total = total;
  }

  public settle(amount: bigint, toFirst: bigint) {
    let na: bigint = this.a;
    let nb: bigint = this.b;
    if (toFirst > 0n) {
      na = na + amount;
    } else {
      nb = nb + amount;
    }
    this.a = na;
    this.b = nb;
    this.total = na + nb;
    this.addOutput(1000n, this.a, this.b, this.total);
  }
}
