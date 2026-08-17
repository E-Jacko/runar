import { StatefulSmartContract, assert } from 'runar-lang';
export class P45 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(p: bigint) { super(p); this.p = p; }
  public go(c1: bigint, c2: bigint) {
    let a: bigint = 1n; let b: bigint = 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 3n; b = 4n; } else { a = 5n; b = 6n; }
      this.p = a + b;
    } else {
      this.p = 0n;
    }
  }
}
