// TEST-ONLY — not a user example.
import { SmartContract, assert } from 'runar-lang';

class BooleanLogic extends SmartContract {
  readonly threshold: bigint;
  constructor(threshold: bigint) {
    super(threshold);
    this.threshold = threshold;
  }
  public verify(a: bigint, b: bigint, flag: boolean): void {
    const aAbove = a > this.threshold;
    const bAbove = b > this.threshold;
    const both = aAbove && bAbove;
    const either = aAbove || bAbove;
    const notFlag = !flag;
    assert(both || (either && notFlag));
  }
}
