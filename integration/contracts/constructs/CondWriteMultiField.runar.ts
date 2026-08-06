// TEST-ONLY — not a user example.
// Issue #99 regression: conditional write of TWO mutable fields in an if
// WITHOUT else. Then-branch leaves two stack results; empty else must
// preserve two old values (branch-balance invariant B).
import { StatefulSmartContract } from 'runar-lang';

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
