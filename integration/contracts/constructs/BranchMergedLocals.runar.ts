// TEST-ONLY — not a user example.
// Palmer-1 regression: ≥2 locals asymmetrically reassigned through if/else,
// then both feed the state continuation. Must deploy + spend on regtest with
// correct post-state (not just accept/reject).
import { StatefulSmartContract } from 'runar-lang';

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
