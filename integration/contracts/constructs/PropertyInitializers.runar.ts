// TEST-ONLY — not a user example.
import { StatefulSmartContract, assert } from 'runar-lang';

class PropertyInitializers extends StatefulSmartContract {
  count: bigint = 0n;
  readonly maxCount: bigint;
  readonly active: boolean = true;

  constructor(maxCount: bigint) {
    super(maxCount);
    this.maxCount = maxCount;
  }

  public increment(amount: bigint) {
    assert(this.active);
    this.count = this.count + amount;
    assert(this.count <= this.maxCount);
  }
}
