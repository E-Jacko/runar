import { SmartContract, assert } from 'runar-lang';
export class N09 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { let s: bigint = 0n; for (let i: bigint = 0n; i < x; i++) { s = s + i; } assert(s > 0n); }
}
