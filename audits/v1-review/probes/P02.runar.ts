import { StatefulSmartContract, assert } from 'runar-lang';
export class P02 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(s: bigint) { super(s); this.p = s; }
  public go(a: bigint, b: bigint, c: bigint) {
    let x: bigint = 1n;
    let y: bigint = 2n;
    let z: bigint = 3n;
    if (a > 0n) {
      if (b > 0n) {
        if (c > 0n) { x = 9n; } else { y = 8n; }
      } else { z = 7n; }
    }
    assert(x + y + z > 0n);
    this.p = x * 100n + y * 10n + z;
  }
}
