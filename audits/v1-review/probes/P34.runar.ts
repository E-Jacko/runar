import { StatefulSmartContract, assert } from 'runar-lang';
export class P34 extends StatefulSmartContract {
  s: bigint = 0n;
  constructor(s: bigint) { super(s); this.s = s; }
  public go() {
    let a: bigint = 0n; let b: bigint = 1n;
    for (let i: bigint = 0n; i < 3n; i++) {
      if (i > 1n) { a = a + 1n; b = b + 1n; } else { a = a + 2n; }
    }
    this.s = a + b;
  }
}
