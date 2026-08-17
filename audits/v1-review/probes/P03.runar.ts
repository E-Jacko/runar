import { StatefulSmartContract, assert } from 'runar-lang';
export class P03 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public step(flag: bigint) {
    let x: bigint = this.a;
    let y: bigint = this.b;
    if (flag > 0n) { x = x + 1n; this.a = x; } else { y = y + 1n; }
    assert(x + y > 0n);
    this.b = y;
  }
}
