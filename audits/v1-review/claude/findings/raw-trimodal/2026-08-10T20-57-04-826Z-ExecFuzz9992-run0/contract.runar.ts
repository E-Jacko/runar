import { SmartContract, assert } from 'runar-lang';

class ExecFuzz9992 extends SmartContract {
  readonly prop1: bigint;
  readonly prop1X: bigint;

  constructor(prop1: bigint, prop1X: bigint) {
    super(prop1, prop1X);
    this.prop1 = prop1;
    this.prop1X = prop1X;
  }

  public run0(param0: boolean, param3: bigint): void {
    let acc: bigint = (2n + this.prop1X);
    let wacc: bigint = (-4n - 3n);
    for (let k: bigint = 4n; k > 2n; k--) {
      for (let k2: bigint = 8n; k2 > 6n; k2--) {
        acc = (acc + (this.prop1X - k));
      }
      wacc = (wacc - acc);
    }
    let br0: bigint = 2n;
    const sib0: bigint = (4n - this.prop1X);
    if ((param3 !== -6n)) {
      if ((param3 >= -2n)) {
        br0 = param3;
      } else {
        br0 = 4n;
      }
    }
    assert(((!(param0) && ((acc <= -2n) && (wacc >= -4n))) && (((br0 + acc) > -1000000n) && (br0 > sib0))));
  }
}
