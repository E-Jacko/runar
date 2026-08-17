import { StatefulSmartContract, assert } from 'runar-lang';
export class N10 extends StatefulSmartContract {
  p: bigint = 1n + 2n;
  constructor(seed: bigint) { super(seed); this.p = seed; }
  public go(x: bigint) { this.p = x; assert(x > 0n); }
}
