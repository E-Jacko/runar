import { SmartContract, assert } from 'runar-lang';
export class P32 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    let x: bigint = this.n;
    if (x > 0n) {
      if (x > 1n) {
        if (x > 2n) {
          if (x > 3n) { x = x - 1n; } else { x = x + 1n; }
        } else { x = x + 2n; }
      } else { x = x + 3n; }
    } else { x = 0n; }
    assert(x >= 0n);
  }
}
