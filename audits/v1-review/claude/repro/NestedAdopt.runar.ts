import { StatefulSmartContract } from 'runar-lang';

export class NestedAdopt extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }

  public go(x: bigint, c1: bigint, c2: bigint) {
    let a: bigint = 1n;
    let y: bigint = x + 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 5n; } else { a = 6n; }
    }
    assert(a + y > 0n);
    this.p = a * 10n + y;
  }
}
