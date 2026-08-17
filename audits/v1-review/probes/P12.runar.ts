import { StatefulSmartContract, assert } from 'runar-lang';
export class P12 extends StatefulSmartContract {
  v: bigint = 0n;
  constructor(v: bigint) { super(v); this.v = v; }
  public go(flag: bigint) {
    let x: bigint = this.v;
    if (flag > 0n) { x = -1n; } else { x = -256n; }
    this.v = x;
  }
}
// Deploy with v=-128; call both flags
