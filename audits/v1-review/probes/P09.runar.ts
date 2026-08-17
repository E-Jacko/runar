import { StatefulSmartContract, assert } from 'runar-lang';
export class P09 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n; c: bigint = 0n; d: bigint = 0n;
  constructor(a: bigint, b: bigint, c: bigint, d: bigint) {
    super(a, b, c, d); this.a = a; this.b = b; this.c = c; this.d = d;
  }
  public go(flag: bigint) {
    if (flag > 0n) { this.a = this.a + 1n; this.c = this.c + 1n; }
    else { this.b = this.b + 1n; }
    assert(this.a + this.b + this.c + this.d >= 0n);
  }
}
