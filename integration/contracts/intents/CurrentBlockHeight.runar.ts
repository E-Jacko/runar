// TEST-ONLY — not a user example.
import { StatefulSmartContract, assert, currentBlockHeight } from 'runar-lang';

class CurrentBlockHeight extends StatefulSmartContract {
  readonly deadline: bigint;
  count: bigint;

  constructor(deadline: bigint, count: bigint) {
    super(deadline, count);
    this.deadline = deadline;
    this.count = count;
  }

  public spend() {
    const h = currentBlockHeight();
    assert(h <= this.deadline);
    this.count = this.count + 1n;
  }
}
