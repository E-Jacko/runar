import { StatefulSmartContract, assert } from 'runar-lang';
export class P01 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }
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
// Call: go(3,1,0) expect p=65; go(3,1,1) expect p=55; go(3,0,0) expect p=15
