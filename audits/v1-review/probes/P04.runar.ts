import { StatefulSmartContract, assert, toByteString } from 'runar-lang';
export class P04 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public go(flag: bigint, sats: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    if (flag > 0n) {
      x = x + 1n; y = y + 2n;
      this.addRawOutput(sats, toByteString('76a914') /* probe: use valid short script in harness */);
    } else { x = x + 3n; }
    this.a = x; this.b = y;
  }
}
