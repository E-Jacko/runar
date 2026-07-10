/**
 * Tri-modal source-vs-script differential-execution oracle (issue #124).
 *
 * Extends the bi-modal {@link runDifferentialExecution} (ANF `RunarInterpreter`
 * vs. the repo's hand-rolled `ScriptVM`) with a THIRD, fully independent
 * execution engine: the upstream `@bsv/sdk` `Spend` interpreter. The three
 * engines have three separate provenances:
 *
 *   1. interpreter — the ANF `RunarInterpreter` (source semantics, our code).
 *   2. ScriptVM   — the repo's hand-rolled Bitcoin Script VM (our code).
 *   3. Spend      — the upstream `@bsv/sdk` production Script interpreter
 *                   (third-party code, the same engine that validates real
 *                   BSV transactions).
 *
 * Because engines (1) and (2) are both maintained in this repo, a shared-design
 * mistake could be mirrored in both and slip past the bi-modal oracle. Engine
 * (3) is written by a different team against the consensus rules, so a
 * disagreement between it and the other two is a strong signal of a real
 * miscompile. `Spend` additionally enforces the consensus **clean-stack** rule
 * (exactly one truthy item must remain) and the **push-only unlocking** rule,
 * which the hand-rolled ScriptVM does not — so it catches a strictly larger
 * class of script-shape bugs.
 *
 * Scope matches the bi-modal oracle: STATELESS, non-crypto contracts (no
 * `checkSig`, no sighash, no state continuation). For those, `Spend` never needs
 * a real transaction context, so we drive it with a synthetic single-input
 * spend built directly from the compiled locking script + the generated witness.
 */
import { Spend, LockingScript, UnlockingScript } from '@bsv/sdk';
import {
  runDifferentialExecution,
  type DiffExecOptions,
  type DiffExecResult,
} from './differential-execution.js';

export interface TriModalExecResult extends DiffExecResult {
  /** Did the compiled script verify on the upstream @bsv/sdk `Spend` engine? */
  spendAccepted: boolean;
  /** `Spend` rejection / throw message, when it did not accept. */
  spendError?: string;
  /** interpreter === ScriptVM === Spend (all three agree on accept/reject). */
  agrees: boolean;
}

/**
 * Run the compiled locking script + witness through the upstream `@bsv/sdk`
 * `Spend` interpreter. `Spend.validate()` returns `true` on success and THROWS
 * (a `ScriptEvaluationError`) on any failure — including the clean-stack and
 * push-only consensus rules — so a throw is mapped to a reject.
 */
function runSpendEngine(
  lockingHex: string,
  witnessHex: string,
): { accepted: boolean; error?: string } {
  try {
    const spend = new Spend({
      sourceTXID: '00'.repeat(32),
      sourceOutputIndex: 0,
      sourceSatoshis: 1,
      lockingScript: LockingScript.fromHex(lockingHex),
      transactionVersion: 1,
      otherInputs: [],
      outputs: [],
      inputIndex: 0,
      unlockingScript: UnlockingScript.fromHex(witnessHex),
      inputSequence: 0xffffffff,
      lockTime: 0,
    });
    const ok = spend.validate();
    return { accepted: ok === true };
  } catch (e) {
    return { accepted: false, error: e instanceof Error ? e.message : String(e) };
  }
}

/**
 * Compile a generated (contract, args) once, then run the SAME deployed bytes
 * and witness through all three engines and report whether they agree on
 * accept/reject. Reuses {@link runDifferentialExecution} for the compile +
 * witness build + interpreter + ScriptVM legs, then layers the `Spend` engine
 * on the exact `lockingHex` / `witnessHex` it produced (no re-compile).
 */
export function runTriModalExecution(opts: DiffExecOptions): TriModalExecResult {
  const bi = runDifferentialExecution(opts);
  const spend = runSpendEngine(bi.lockingHex, bi.witnessHex);
  const agrees =
    bi.interpreterAccepted === bi.vmAccepted &&
    bi.vmAccepted === spend.accepted;
  return {
    ...bi,
    spendAccepted: spend.accepted,
    spendError: spend.error,
    agrees,
  };
}
