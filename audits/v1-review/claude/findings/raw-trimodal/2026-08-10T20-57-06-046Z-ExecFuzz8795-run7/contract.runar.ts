import { SmartContract, assert, toByteString } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ExecFuzz8795 extends SmartContract {
  readonly prop0: ByteString;

  constructor(prop0: ByteString) {
    super(prop0);
    this.prop0 = prop0;
  }

  public run7(param4: bigint): void {
    let acc: bigint = param4;
    let br0: bigint = -1n;
    const sib0: bigint = param4;
    if ((param4 !== 7n)) {
      if ((param4 < -2n)) {
        br0 = param4;
      } else {
        br0 = (-2n + -1n);
      }
    }
    assert(((param4 !== (acc + acc)) && (((br0 + acc) > -1000000n) && (br0 > sib0))));
  }
}
