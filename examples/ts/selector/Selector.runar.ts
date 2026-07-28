import { StatefulSmartContract, assert } from 'runar-lang';

/**
 * Selector -- regression fixture for deep-review finding C20.
 *
 * A dispatch method whose branches each end in a single `update_prop` and
 * whose terminal `else` is `assert(false)`. The pre-fix ANF lowering
 * (`liftBranchUpdateProps`) dropped that abort, so a selector value matching
 * NO branch produced a spendable NO-OP state continuation instead of failing
 * the script — a funds-safety bug. The compiler now re-emits
 * `assert(cond0 || cond1)` so an out-of-range selector aborts on-chain.
 */
class Selector extends StatefulSmartContract {
  a: bigint;
  b: bigint;

  constructor(a: bigint, b: bigint) {
    super(a, b);
    this.a = a;
    this.b = b;
  }

  public set(i: bigint, v: bigint) {
    if (i == 0n) {
      this.a = v;
    } else if (i == 1n) {
      this.b = v;
    } else {
      assert(false);
    }
  }
}
