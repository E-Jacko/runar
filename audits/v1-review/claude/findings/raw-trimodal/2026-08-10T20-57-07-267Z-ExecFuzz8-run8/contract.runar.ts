import { SmartContract, assert, toByteString } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ExecFuzz8 extends SmartContract {
  readonly prop8: ByteString;
  readonly prop8X: ByteString;

  constructor(prop8: ByteString, prop8X: ByteString) {
    super(prop8, prop8X);
    this.prop8 = prop8;
    this.prop8X = prop8X;
  }

  public run8(param0: ByteString, param8: bigint, param7: ByteString): void {
    let acc: bigint = -3n;
    let br0: bigint = (param8 - -1n);
    const sib0: bigint = 3n;
    if ((param8 >= 4n)) {
      if ((param8 !== -1n)) {
        br0 = param8;
      } else {
        br0 = (param8 + 4n);
      }
    } else {
      br0 = (param8 - 3n);
    }
    assert(((param8 !== ((1n + param8) + acc)) && (((br0 + acc) > -1000000n) && (br0 <= sib0))));
  }
}
