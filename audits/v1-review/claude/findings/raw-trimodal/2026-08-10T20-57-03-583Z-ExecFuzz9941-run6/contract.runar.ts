import { SmartContract, assert } from 'runar-lang';

class ExecFuzz9941 extends SmartContract {
  readonly prop1: bigint;
  readonly prop6: bigint;

  constructor(prop1: bigint, prop6: bigint) {
    super(prop1, prop6);
    this.prop1 = prop1;
    this.prop6 = prop6;
  }

  public run6(param9: bigint, param5: bigint, param1: boolean): void {
    let acc: bigint = (0n + param9);
    let br0: bigint = (param9 - param5);
    const sib0: bigint = (this.prop6 - param5);
    if ((param9 < -1n)) {
      if ((param9 === -3n)) {
        br0 = (0n + 4n);
      } else {
        br0 = -4n;
      }
    }
    assert(((param1 || (0n > (-1n - acc))) && (((br0 + acc) > -1000000n) && (br0 < sib0))));
  }
}
