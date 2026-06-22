import { StatefulSmartContract } from 'runar-lang';

/**
 * CondWriteMultiField -- regression fixture for GitHub issue #99.
 *
 * A conditional write of TWO mutable state fields in an `if` WITHOUT an
 * `else`. The then-branch leaves two result values on the stack; the empty
 * else-branch must preserve two old values. The pre-fix stack lowering only
 * balanced a single item, leaving the IF/ELSE arms imbalanced by (N-1) and
 * the update branch unspendable. The compiler now reconciles the full depth
 * difference and asserts branch balance (invariant B).
 */
class CondWriteMultiField extends StatefulSmartContract {
  a: bigint;
  b: bigint;

  constructor(a: bigint, b: bigint) {
    super(a, b);
    this.a = a;
    this.b = b;
  }

  public bump(flag: bigint) {
    if (flag > 0n) {
      this.a = this.a + 1n;
      this.b = this.b + 2n;
    }
    this.addOutput(1000n, this.a, this.b);
  }
}
