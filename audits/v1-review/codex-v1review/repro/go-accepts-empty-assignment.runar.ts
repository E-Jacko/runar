import { StatefulSmartContract, assert } from 'runar-lang';

class EmptyAssignment extends StatefulSmartContract {
  value: bigint;

  constructor(value: bigint) {
    super(value);
    this.value = value;
  }

  public set(next: bigint) {
    this.value = ;
    this.value = next;
    assert(true);
  }
}
