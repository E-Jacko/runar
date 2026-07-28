import { describe, it, expect } from 'vitest';
import { shouldFailRun } from '../run-policy.js';

// C5 (deep-review finding, P1 "serious test blindness"): the fuzzer's
// time-budget `earlyStop` used to exit green with an incomplete corpus —
// index.ts only ever failed the CLI exit code on mismatchCount/
// divergenceCount, never on "did we actually run the whole generated
// corpus". `shouldFailRun` is the pure decision function pulled out of
// index.ts's per-mode (`--anf` / `--execute`) exit-code logic so it can be
// driven directly with synthetic report shapes instead of the full
// generate-and-compile pipeline.
describe('shouldFailRun (C5 — early-stop must not silently pass an incomplete run)', () => {
  it('FAILS when the run stopped early before covering the full corpus', () => {
    expect(shouldFailRun({ earlyStop: true, completed: 40, total: 100 })).toBe(true);
  });

  it('PASSES a run that stopped early but happened to finish exactly at the last item', () => {
    expect(shouldFailRun({ earlyStop: true, completed: 100, total: 100 })).toBe(false);
  });

  it('PASSES a complete run that never hit the time budget', () => {
    expect(shouldFailRun({ earlyStop: false, completed: 40, total: 100 })).toBe(false);
  });

  it('PASSES a complete run with no time budget at all (earlyStop always false, completed === total)', () => {
    expect(shouldFailRun({ earlyStop: false, completed: 100, total: 100 })).toBe(false);
  });

  it('honors an explicit minimum-fraction threshold', () => {
    const run = { earlyStop: true, completed: 91, total: 100 };
    expect(shouldFailRun(run)).toBe(true); // default: must be 100% complete
    expect(shouldFailRun(run, { minCompleteFraction: 0.9 })).toBe(false);
    expect(shouldFailRun(run, { minCompleteFraction: 0.95 })).toBe(true);
  });

  it('does not divide by zero when total is 0 (nothing was ever supposed to run)', () => {
    expect(shouldFailRun({ earlyStop: true, completed: 0, total: 0 })).toBe(false);
  });
});
