import { StatefulSmartContract, assert } from 'runar-lang';

/**
 * AssertFalseGuard -- the `assert(false)`-else guard, in the two positions the
 * multi-result branch node originally missed. Both produced a permanently
 * unspendable UTXO from source that reads as plainly correct, and both were
 * completely unfixtured: `selector` covers the LIFTED chain, `cond-write-multi-field`
 * covers an `if` WITHOUT an else, and neither covers these.
 *
 * `bump` -- a single property written under a guard whose else is the dead
 * `assert(false)`. `collectUpdateBranches` recognises this as a ONE-branch
 * chain, which excluded it from declaring its result; `liftBranchUpdateProps`
 * only rewrites chains of TWO OR MORE, so nothing rewrote it either. It fell
 * through both, the arm's `update_prop` kept the property's stale slot, and the
 * state continuation committed the PRE-call value.
 *
 * `dispatch` -- `selector`'s exact chain, one `for` deeper.
 * `liftBranchUpdateProps` walks `method.body` and does not recurse, so a chain
 * inside a loop body is recognised at every nesting depth but rewritten at
 * none. Two arms writing DIFFERENT property sets is precisely the shape the
 * multi-result node exists to fix; nesting it put it back out of reach.
 */
class AssertFalseGuard extends StatefulSmartContract {
  count: bigint;
  a: bigint;
  b: bigint;

  constructor(count: bigint, a: bigint, b: bigint) {
    super(count, a, b);
    this.count = count;
    this.a = a;
    this.b = b;
  }

  public bump(n: bigint) {
    if (n > 0n) {
      this.count = this.count + n;
    } else {
      assert(false);
    }
  }

  public dispatch(sel: bigint, v: bigint) {
    for (let i = 0n; i < 2n; i++) {
      if (sel == 0n) {
        this.a = v;
      } else if (sel == 1n) {
        this.b = v;
      } else {
        assert(false);
      }
    }
  }
}
