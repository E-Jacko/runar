import { SmartContract, assert, toByteString } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ExecFuzz1253 extends SmartContract {
  readonly prop0: ByteString;
  readonly prop2: ByteString;

  constructor(prop0: ByteString, prop2: ByteString) {
    super(prop0, prop2);
    this.prop0 = prop0;
    this.prop2 = prop2;
  }

  public run5(param2: bigint, param8: ByteString): void {
    let acc: bigint = param2;
    let br0: bigint = (0n + param2);
    const sib0: bigint = param2;
    if ((param2 > -8n)) {
      if ((param2 <= 0n)) {
        br0 = (param2 - param2);
      } else {
        br0 = (param2 + param2);
      }
    }
    assert((((param2 === ((0n + acc) + acc)) || (acc <= 0n)) && (((br0 + acc) > -1000000n) && (br0 < sib0))));
  }
}
