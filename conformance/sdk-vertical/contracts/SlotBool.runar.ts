import { SmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig } from 'runar-lang';

/**
 * SlotBool — vertical-pin fixture for the `bool` constructor-slot value class
 * (remediation plan Phase C3 / C1 matrix).
 *
 * `valueEncoding: 'bool'` is a SINGLE-OPCODE encoding: `true` → `OP_TRUE`
 * (0x51), `false` → `OP_0` (0x00). It has no push header, so a splice that
 * assumes "header + value" for every slot mis-measures it — and `false`
 * happens to encode to the very same `0x00` byte as the untouched template
 * placeholder, which is why a bool slot that is silently never spliced looks
 * byte-identical to a correct one for exactly one of its two values.
 */
class SlotBool extends SmartContract {
  readonly flag: boolean;
  readonly owner: PubKey;

  constructor(flag: boolean, owner: PubKey) {
    super(flag, owner);
    this.flag = flag;
    this.owner = owner;
  }

  public unlock(sig: Sig, expected: boolean) {
    assert(this.flag === expected);
    assert(checkSig(sig, this.owner));
  }
}
