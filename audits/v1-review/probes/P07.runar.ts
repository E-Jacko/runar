import { StatefulSmartContract, assert } from 'runar-lang';
export class P07 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public go(flag: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    for (let i: bigint = 0n; i < 3n; i++) { x = x + 1n; }
    if (flag > 0n) { y = y + x; } else { y = y - 1n; }
    this.a = x; this.b = y;
  }
}
