/**
 * Pure decision function for whether an early-stopped fuzz run must FAIL the
 * gate (C5, deep-review finding).
 *
 * Both the ANF (`--anf`) and execution-oracle (`--execute`) differential
 * harnesses accept a `--time-budget-ms` wall-clock budget and set
 * `earlyStop: true` on the returned report when the budget is hit before the
 * full generated corpus finished running (see `anf-differential.ts` /
 * `execute-differential.ts`). Before this fix, `index.ts` only ever failed the
 * CLI exit code on `mismatchCount > 0` / `divergenceCount > 0`: an
 * early-stopped nightly run that simply hadn't hit a mismatch YET (because
 * most of the corpus never ran) reported `exit 0` — a silent, unqualified
 * PASS over an incomplete oracle run. PR gates omit `--time-budget-ms`, so
 * they were unaffected; the nightly gates (which DO pass a budget) were the
 * ones exposed.
 */

export interface RunCompletion {
  /** Did the harness stop before exhausting the generated corpus? */
  earlyStop: boolean;
  /** Number of corpus items (programs / contracts) actually run. */
  completed: number;
  /** Total corpus size generated for this run. */
  total: number;
}

export interface ShouldFailRunOptions {
  /**
   * Minimum fraction (0, 1] of the corpus that must have run even when the
   * harness stopped early on its time budget. Default 1 — ANY early-stopped
   * run that didn't finish the whole corpus fails. Lower it to tolerate a
   * partial run (e.g. 0.9 = fail only if less than 90% completed).
   */
  minCompleteFraction?: number;
}

/** True when an early-stopped, incomplete run must fail the gate. */
export function shouldFailRun(
  run: RunCompletion,
  options: ShouldFailRunOptions = {},
): boolean {
  if (!run.earlyStop) return false;
  if (run.total <= 0) return false; // nothing was ever supposed to run
  const minFraction = options.minCompleteFraction ?? 1;
  return run.completed / run.total < minFraction;
}
