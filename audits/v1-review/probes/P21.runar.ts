import { SmartContract, assert } from 'runar-lang';
export class P21 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  private step(flag: bigint): bigint {
    let x: bigint = this.n; let y: bigint = 1n;
    if (flag > 0n) { x = x + 1n; y = y + 1n; } else { y = y + 2n; }
    return x + y;
  }
  public f(flag: bigint) { assert(this.step(flag) > 0n); }
}
