import { SmartContract, assert } from 'runar-lang';
export class P31 extends SmartContract {
  public f() {
    const a: bigint = 2147483647n;
    const b: bigint = 2147483648n;
    const c: bigint = 4294967296n;
    assert(a + 1n === b);
    assert(b + b === c);
  }
}
