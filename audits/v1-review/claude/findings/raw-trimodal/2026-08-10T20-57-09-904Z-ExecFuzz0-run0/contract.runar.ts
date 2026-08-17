import { SmartContract, assert } from 'runar-lang';

class ExecFuzz0 extends SmartContract {

  constructor() {
    super();
  }

  public run0(param0: bigint): void {
    let acc: bigint = param0;
    let br0: bigint = 0n;
    const sib0: bigint = (param0 - param0);
    if ((param0 < 0n)) {
      if ((param0 === 0n)) {
        br0 = param0;
      } else {
        br0 = (param0 + param0);
      }
    }
    assert((((param0 === ((acc + acc) + 0n)) || (acc > ((acc + acc) + 0n))) && (((br0 + acc) > -1000000n) && (br0 < sib0))));
  }
}
