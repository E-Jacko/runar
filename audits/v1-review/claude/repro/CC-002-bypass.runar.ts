import { SmartContract, assert } from 'runar-lang';

export class Bypass extends SmartContract {
  readonly q: bigint;
  constructor(q: bigint) { super(q); this.q = q; }

  public run5(param2: bigint): void {
    let br0: bigint = param2;
    const sib0: bigint = param2;
    if (param2 > -8n) {
      if (param2 <= 0n) { br0 = 0n; } else { br0 = 1n; }
    }
    assert(br0 < sib0);
  }
}
