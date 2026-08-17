import { SmartContract, assert } from 'runar-lang';

class ExecFuzz9989 extends SmartContract {

  constructor() {
    super();
  }

  public run0(param1: bigint): void {
    let acc: bigint = (param1 + param1);
    let br0: bigint = (param1 + 0n);
    const sib0: bigint = (param1 + param1);
    if ((param1 !== 0n)) {
      if ((param1 === 0n)) {
        br0 = (param1 + 0n);
      } else {
        br0 = param1;
      }
    }
    assert((((param1 === ((acc + acc) + 0n)) || (((acc + acc) * acc) >= 0n)) && (((br0 + acc) > -1000000n) && (br0 < sib0))));
  }
}
