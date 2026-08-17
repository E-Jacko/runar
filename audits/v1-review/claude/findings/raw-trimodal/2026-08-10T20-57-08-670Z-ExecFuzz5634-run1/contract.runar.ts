import { SmartContract, assert, cat, toByteString } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ExecFuzz5634 extends SmartContract {
  readonly prop0: ByteString;

  constructor(prop0: ByteString) {
    super(prop0);
    this.prop0 = prop0;
  }

  public run1(param1: bigint, param3: ByteString): void {
    let acc: bigint = (-3n + 2n);
    const b0: ByteString = cat(this.prop0, this.prop0);
    let br0: bigint = (param1 + -1n);
    const sib0: bigint = (param1 + -2n);
    if ((param1 >= -3n)) {
      if ((param1 === 0n)) {
        br0 = 2n;
      } else {
        br0 = -1n;
      }
    }
    assert((((param1 <= 3n) || (((param1 - acc) * -1n) < (acc + 0n))) && (((br0 + acc) > -1000000n) && (br0 !== sib0))));
  }
}
