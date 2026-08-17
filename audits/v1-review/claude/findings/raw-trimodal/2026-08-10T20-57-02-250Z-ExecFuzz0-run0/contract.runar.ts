import { SmartContract, assert } from 'runar-lang';

class ExecFuzz0 extends SmartContract {
  readonly prop0: bigint;

  constructor(prop0: bigint) {
    super(prop0);
    this.prop0 = prop0;
  }

  public run0(param0: bigint): void {
    let acc: bigint = (this.prop0 + this.prop0);
    let br0: bigint = (this.prop0 + this.prop0);
    const sib0: bigint = (this.prop0 + 0n);
    if ((param0 >= 0n)) {
      if ((param0 === 0n)) {
        br0 = (this.prop0 + 0n);
      } else {
        br0 = (0n + 0n);
      }
    }
    assert(((param0 > (acc + acc)) && (((br0 + acc) > -1000000n) && (br0 < sib0))));
  }
}
