import { SmartContract, assert } from 'runar-lang';

export class Issue149 extends SmartContract {
  p: bigint;

  constructor(p: bigint) {
    super(p);
    this.p = p;
  }

  public go(x: bigint, c1: bigint, c2: bigint) {
    let a: bigint = 1n;
    let y: bigint = x + 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 5n; } else { a = 6n; }
    }
    assert(a + y > 0n);
    this.p = a * 10n + y;
  }
}
