import { SmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig, ByteString } from 'runar-lang';

/**
 * SlotMatrix — vertical-pin fixture for `constructorSlots` / constructor-arg
 * splicing (remediation plan Phase C3).
 *
 * Stateless on purpose: every readonly property becomes a CODE-part
 * constructor slot (an `OP_0` placeholder the SDK splices a deploy-time value
 * over), so a single compiled template can be redeployed across the whole C1
 * value-class matrix by varying only `constructorArgs`.
 *
 * Three slot kinds in one script, in declaration order:
 *   - `count`  bigint     → `valueEncoding: 'scriptnum'` (OP_0 / OP_N /
 *                           OP_1NEGATE / sign-magnitude push)
 *   - `tag`    ByteString → `valueEncoding: 'data'`, VARIABLE length: the
 *                           class where a 1-byte OP_1..OP_16 / 0x81 payload
 *                           collapses to a single opcode with no push header
 *   - `owner`  PubKey     → `valueEncoding: 'data'`, FIXED 1 + 33 bytes
 *
 * `tag` is referenced twice so the template carries two slots for the same
 * `paramIndex` — a splice that resolves offsets in the wrong order, or that
 * fails to account for an earlier slot's expansion, desynchronises the second
 * one.
 */
class SlotMatrix extends SmartContract {
  readonly count: bigint;
  readonly tag: ByteString;
  readonly owner: PubKey;

  constructor(count: bigint, tag: ByteString, owner: PubKey) {
    super(count, tag, owner);
    this.count = count;
    this.tag = tag;
    this.owner = owner;
  }

  public unlock(sig: Sig, witness: ByteString, n: bigint) {
    assert(this.tag === witness);
    assert(this.count === n);
    assert(this.tag !== this.owner);
    assert(checkSig(sig, this.owner));
  }
}
