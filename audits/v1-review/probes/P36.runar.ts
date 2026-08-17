import { SmartContract, assert } from 'runar-lang';
export class P36 extends SmartContract {
  public f(n: bigint) { assert(Math.floor(Number(n)) > 0); }
}
