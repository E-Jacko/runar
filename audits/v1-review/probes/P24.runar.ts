import { StatefulSmartContract, assert } from 'runar-lang';
export class P24 extends StatefulSmartContract {
  a: bigint = 7n;
  b: bigint = 8n;
  constructor() { super(); }
  public go(flag: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    if (flag > 0n) { x = 1n; y = 2n; } else { x = 3n; y = 4n; }
    this.a = x; this.b = y;
  }
}
