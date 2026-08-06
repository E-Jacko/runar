// TEST-ONLY — not a user example.
import { SmartContract, assert } from 'runar-lang';

class TernaryOps extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) {
    super(expected);
    this.expected = expected;
  }
  public verify(flag: boolean, a: bigint, b: bigint): void {
    const v = flag ? a : b;
    assert(v === this.expected);
  }
}
