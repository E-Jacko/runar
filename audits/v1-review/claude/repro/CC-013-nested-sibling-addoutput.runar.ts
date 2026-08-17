import { StatefulSmartContract, assert } from 'runar-lang';
import type { PubKey } from 'runar-lang';

class Shape9 extends StatefulSmartContract {
  readonly s0: bigint;
  readonly s1: PubKey;
  f0: bigint;
  f1: PubKey;

  constructor(s0: bigint, s1: PubKey, f0: bigint, f1: PubKey) {
    super(s0, s1, f0, f1);
    this.s0 = s0;
    this.s1 = s1;
    this.f0 = f0;
    this.f1 = f1;
  }

  public step(p0: bigint, p1: PubKey) {
    assert(p0 >= 1065n);
    assert(this.s0 == 7n);
    assert(this.s1 == '02a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1');
    let l0: bigint = this.f0;
    let l1: PubKey = this.f1;
    if (p0 > 0n) {
      if (p0 > 2000n) {
        l0 = 127n;
      } else {
        l0 = 17n;
      }
    }
    this.addOutput(1000n, l0, l1);
  }
}
