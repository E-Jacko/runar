import { StatefulSmartContract } from 'runar-lang';

/**
 * OversizeBigintShift -- a length-sensitive byte op whose operand is a bigint
 * const too large for a JSON number (NEW-008).
 *
 * `runar-cli compile` serialises every ANF bigint as a `"<n>n"` STRING, and
 * that artifact is what every SDK loads off disk. `conformance/runner` narrows
 * the SAFE-INTEGER ones back to JSON numbers when it stamps `expected-ir.json`,
 * so before this fixture only ONE of 71 goldens carried an `n`-string at all --
 * and that one has no byte ops. The result: nothing on disk ever fed a
 * `"<n>n"` const into `<<`, `>>`, `&`, `|`, `^` or `~`, and four of the seven
 * SDK ANF interpreters silently took the ByteString path for such an operand.
 *
 * `9007199254740993n` (2^53 + 1) is deliberately one past
 * `Number.MAX_SAFE_INTEGER`, so it survives the runner's narrowing and the
 * golden below really does pin the string form.
 *
 * On chain: `9007199254740993` is the 7-byte script number
 * `01 00 00 00 00 00 20`; `OP_LSHIFT 8` is LENGTH-PRESERVING, leaving
 * `00 00 00 00 00 20 00` (a NON-minimal 7-byte encoding of 2^45), and
 * `OP_INVERT` then flips all seven bytes to `ff ff ff ff ff df ff` =
 * -35993612646875135. An interpreter that re-minimises anywhere along that
 * chain disagrees with the deployed script and the continuation it builds is
 * unspendable.
 */
class OversizeBigintShift extends StatefulSmartContract {
  out: bigint;

  constructor(out: bigint) {
    super(out);
    this.out = out;
  }

  public shift(): void {
    this.out = ~(9007199254740993n << 8n);
  }
}
