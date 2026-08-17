import { SmartContract, assert } from 'runar-lang';
export class P29 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint) {
    let a: bigint = 1n; let b: bigint = 2n; let c: bigint = 3n;
    if (flag > 0n) { a = 4n; b = 5n; c = 6n; } else { a = 7n; b = 8n; c = 9n; }
    assert(a > 0n); // b,c dead after
  }
}
