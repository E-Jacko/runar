import { StatefulSmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig, ByteString } from 'runar-lang';

/**
 * AttributedToken -- a token whose immutable ATTRIBUTES are baked into the
 * code part of its locking script, so a later covenant can verify them by
 * inspecting the token's parent transaction in Bitcoin Script.
 *
 * This is the token half of the "Verified Companion Inputs" example pair
 * (see CompanionVerifier.runar.ts for the verifier half): cross-contract
 * composition where one covenant input verifies attributes of ANOTHER input
 * in the same spending transaction -- no oracle, no indexer, no coordinator.
 *
 * Design rules that make the attributes verifiable:
 *
 *  - **Attributes travel in the code part.** `attestor`, `category`, and
 *    `batchId` are readonly and baked at deploy; every child produced by a
 *    split inherits them byte-for-byte because the children reuse the same
 *    code part.
 *  - **An attribute only exists on-chain if the contract references it.**
 *    Unreferenced readonly props are eliminated by the compiler. `revoke`
 *    references `attestor` (checkSig) and `category` (enum floor assert)
 *    precisely so both become constructorSlots a downstream verifier can
 *    extract. This is the load-bearing rule of the whole pattern.
 *  - **Amount is divisible; attribution is not.** `split` conserves `amount`
 *    across children; the attribute slots are indivisible provenance.
 *
 * ATTRIBUTE SLOT ENCODING (fixed-layout template requirement):
 *  - `attestor` is a 33-byte pubkey push -- a fixed-width 33-byte slot.
 *  - `category` is constrained to 1..16 so it always bakes as a SINGLE OP_N
 *    opcode byte (0x51..0x60). 0 would bake as OP_0 (indistinguishable from
 *    an unbaked placeholder); 17+ bakes as a 2-byte push, shifting every
 *    offset after the slot. Fixed-width slots keep the verifier's offsets
 *    compile-time constants.
 *
 * The verifier derives those offsets mechanically from the artifact's
 * verification descriptors (`resolveSlotLayout` / `computeTemplateHash` in
 * runar-sdk) -- see the test file for the derivation.
 *
 * State model (UTXO): mutable state (owner, amount, status) rides in an
 * OP_RETURN tail; spending with the same code part = transfer/split.
 * Status: 1 = Active, 3 = Retired (consumed), 4 = Revoked (attestor recall).
 */
class AttributedToken extends StatefulSmartContract {
  /** Current holder. Mutable -- updated on transfer/split. */
  owner: PubKey;
  /** Divisible quantity. Mutable -- divided on split, conserved across children. */
  amount: bigint;
  /** Lifecycle status: 1 = Active, 3 = Retired, 4 = Revoked. Mutable. */
  status: bigint;

  /** ATTRIBUTE SLOT #1: who attested/minted this token. Readonly, baked into
   *  the code part -- the field a downstream CompanionVerifier extracts and
   *  checks against its allowlist. */
  readonly attestor: PubKey;
  /** ATTRIBUTE SLOT #2: category enum (1..16 ONLY -- see encoding note above).
   *  Readonly, baked as a single OP_N opcode byte. */
  readonly category: bigint;
  /** Batch identity -- hash of genesis metadata. Readonly, inherited by all children. */
  readonly batchId: ByteString;

  constructor(
    owner: PubKey,
    amount: bigint,
    status: bigint,
    attestor: PubKey,
    category: bigint,
    batchId: ByteString,
  ) {
    super(owner, amount, status, attestor, category, batchId);
    this.owner = owner;
    this.amount = amount;
    this.status = status;
    this.attestor = attestor;
    this.category = category;
    this.batchId = batchId;
  }

  /** Full transfer: 1 UTXO -> 1 UTXO. Whole amount to a new owner. */
  public transfer(sig: Sig, to: PubKey, outputSatoshis: bigint) {
    assert(checkSig(sig, this.owner));
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);

    this.addOutput(outputSatoshis, to, this.amount, this.status);
  }

  /**
   * Split: 1 UTXO -> 2 UTXOs. Recipient gets `splitAmount`, owner keeps the
   * remainder. Amount is conserved; attestor/category/batchId are inherited
   * automatically because both children reuse this same code part.
   */
  public split(sig: Sig, to: PubKey, splitAmount: bigint, outputSatoshis: bigint) {
    assert(checkSig(sig, this.owner));
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);
    assert(splitAmount > 0n);
    assert(splitAmount < this.amount);

    this.addOutput(outputSatoshis, to, splitAmount, this.status);
    this.addOutput(outputSatoshis, this.owner, this.amount - splitAmount, this.status);
  }

  /** Retire: mark the token consumed. Active -> Retired. Amount and owner
   *  preserved as the permanent record. */
  public retire(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.owner));
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);

    this.addOutput(outputSatoshis, this.owner, this.amount, 3n);
  }

  /**
   * Revoke: attestor-only error correction. Active -> Revoked (status 4).
   *
   * Beyond its business meaning, this method is what forces BOTH attribute
   * slots on-chain: `checkSig(sig, this.attestor)` bakes the attestor pubkey
   * as a constructorSlot, and the `category` floor assert bakes the category
   * opcode. Attributes you can verify in Script exist only because the
   * contract itself commits to them.
   */
  public revoke(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.attestor));
    // On-chain anchor for `category` + enum floor (0 would bake as an OP_0
    // placeholder-lookalike -- see the encoding note on the property).
    assert(this.category >= 1n);
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);

    this.addOutput(outputSatoshis, this.owner, this.amount, 4n);
  }
}
