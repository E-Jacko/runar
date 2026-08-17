import { StatefulSmartContract, assert } from 'runar-lang';
export class P26 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n; c: bigint = 0n;
  constructor(a: bigint, b: bigint, c: bigint) {
    super(a, b, c); this.a = a; this.b = b; this.c = c;
  }
  public go(flag: bigint, sats: bigint) {
    if (flag > 0n) { this.a = this.a + 1n; }
    this.addOutput(sats, this.a, this.b, this.c);
  }
}
