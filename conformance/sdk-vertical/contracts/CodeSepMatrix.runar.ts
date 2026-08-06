import { StatefulSmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig, ByteString } from 'runar-lang';

/**
 * CodeSepMatrix — vertical-pin fixture for `codeSeparatorIndex` /
 * `codeSeparatorIndices` (remediation plan Phase C4).
 *
 * Stateful with TWO public methods, so the compiler emits more than one
 * `OP_CODESEPARATOR` and the artifact carries a multi-entry
 * `codeSeparatorIndices` list plus `codeSepIndexSlots` (the OP_0 placeholders
 * each SDK replaces with the DEPLOY-TIME-adjusted codesep byte offset).
 *
 * The readonly `tag` is a VARIABLE-length ByteString slot that sits inside the
 * script, so the deployed codesep offsets shift by an amount that depends on
 * the constructor VALUE. That is the C3xC4 interaction the matrix exists for:
 * a 1-byte `0x05` tag encodes to one byte (`OP_5`) while a 1-byte `0x00` tag
 * encodes to two (`01 00`), so the two deployments must bake DIFFERENT codesep
 * indices from the SAME template. A tier that hardcodes the template-relative
 * index, or that computes the shift from the declared type instead of the
 * encoded bytes, produces a signature over the wrong subscript — a green
 * compile and an unspendable output.
 */
class CodeSepMatrix extends StatefulSmartContract {
  note: ByteString;
  readonly tag: ByteString;
  readonly owner: PubKey;

  constructor(note: ByteString, tag: ByteString, owner: PubKey) {
    super(note, tag, owner);
    this.note = note;
    this.tag = tag;
    this.owner = owner;
  }

  public bump(witness: ByteString) {
    assert(this.tag === witness);
    assert(this.note !== witness);
    this.note = witness;
  }

  /**
   * Non-terminal (usesCodePart, like `bump`) but declared AFTER `bump` and
   * referencing no readonly ctor property of its own, so it exists purely to
   * carry a SECOND `codeSepIndexSlot` whose own OP_CODESEPARATOR sits after
   * the `tag` ctor slot (remediation plan P0-1). `bump`'s own slot always
   * targets template offset 6 — before every ctor slot — so its baked value
   * never shifts; this one's does, by exactly `tag`'s encoded-length delta.
   */
  public reseal(witness: ByteString) {
    assert(this.note !== witness);
    this.note = witness;
  }

  public close(sig: Sig) {
    assert(checkSig(sig, this.owner));
  }
}
