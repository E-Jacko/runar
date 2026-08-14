import { StatefulSmartContract } from 'runar-lang';

/**
 * StateBigintEdges -- construct-ledger row `state-bigint-edges`.
 *
 * A bigint state field is written as a FIXED 8-byte little-endian
 * SIGN-MAGNITUDE word (OP_NUM2BIN semantics): the magnitude occupies bytes
 * 0..6 little-endian and the sign lives in bit 0x80 of byte 7. It is NOT
 * two's complement -- `-1` is `01 00 00 00 00 00 00 80`, not `ff..ff`.
 *
 * Every existing pin stopped short of the sign bit. `state.test.ts` covers
 * negatives only as `deserializeState(serializeState(x)) === x`, which any
 * self-consistent framing satisfies -- including a wrong one. The seven-SDK
 * `sdk-output` goldens pin bigint state values 0, 100, 1000, 10000 and
 * 1000000: all small and all NON-NEGATIVE. No golden anywhere exercised the
 * sign bit, and no real-crypto witness pinned a negative `expectedState`.
 *
 * `shift` moves the two fields in OPPOSITE directions so a single spend
 * crosses the sign boundary in both senses, and the continuation is rebuilt
 * on-chain by the COMPILER's own state framing while the deployed script was
 * written by the SDK's serializer -- so a disagreement between the two shows
 * up as an unspendable UTXO on the real Spend engine, not as a round-trip that
 * agrees with itself.
 */
class StateBigintEdges extends StatefulSmartContract {
  lo: bigint;
  hi: bigint;

  constructor(lo: bigint, hi: bigint) {
    super(lo, hi);
    this.lo = lo;
    this.hi = hi;
  }

  public shift(delta: bigint) {
    this.lo = this.lo - delta;
    this.hi = this.hi + delta;
    this.addOutput(1000n, this.lo, this.hi);
  }
}
