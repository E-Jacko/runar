import { SmartContract } from 'runar-lang';
export class P37 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() { this.n = 1n; }
}
