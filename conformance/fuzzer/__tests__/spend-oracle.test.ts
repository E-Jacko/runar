import { describe, it, expect } from 'vitest';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runSpendOracle } from '../spend-oracle.js';
import { REQUIRED_CASE_COUNT, REQUIRED_TAGS } from '../spend-shapes.js';

/**
 * Smoke gate for the Phase E3 Spend-oracle fuzzer. Everything is deterministic
 * on a fixed seed: the corpus, the args, the signing key, the fee rate, and
 * therefore the transactions and the engine verdicts.
 *
 * The assertions below are the ones that make a GREEN run mean something:
 * the corpus must have reached every fund-critical construct, real script must
 * actually have run (`validatedInputs > 0` — otherwise the pass is vacuous),
 * and both an accept and a reject verdict must have been produced (a corpus
 * that only ever rejects would pass a naive "no accepted-when-reject" check).
 */
describe('runSpendOracle (Phase E3 — absolute Spend oracle over stateful spends)', () => {
  it('is clean on a fixed-seed construct-biased corpus, and not vacuously so', async () => {
    // One case per construct family: the corpus draws families round-robin, so
    // a smaller run silently skips the tail families.
    const report = await runSpendOracle({
      numCases: REQUIRED_CASE_COUNT,
      seed: 424242,
      findingsDir: join(tmpdir(), 'runar-spend-oracle-smoke'),
    });

    expect(report.casesRun).toBe(REQUIRED_CASE_COUNT);
    expect(report.failureCount, JSON.stringify(report.byKind)).toBe(0);

    // Not vacuous: real script really ran on the real engine.
    expect(report.validatedInputs).toBeGreaterThan(0);

    // Not vacuous: the corpus exercises BOTH verdicts.
    expect(report.acceptCount).toBeGreaterThan(0);
    expect(report.rejectCount).toBeGreaterThan(0);

    // Not vacuous: every fund-critical construct was reached.
    expect(REQUIRED_TAGS.filter((t) => !report.tagsCovered.includes(t))).toEqual([]);
  }, 120_000);

  it('reproduces exactly on the same seed', async () => {
    const opts = { numCases: 6, seed: 20260803, findingsDir: join(tmpdir(), 'runar-spend-oracle-repeat') };
    const a = await runSpendOracle(opts);
    const b = await runSpendOracle(opts);
    expect(b.acceptCount).toBe(a.acceptCount);
    expect(b.rejectCount).toBe(a.rejectCount);
    expect(b.failureCount).toBe(a.failureCount);
    expect(b.tagsCovered).toEqual(a.tagsCovered);
    expect(b.validatedInputs).toBe(a.validatedInputs);
  }, 120_000);

  it('(E4) metamorphic variants preserve verdict and expectedState', async () => {
    const report = await runSpendOracle({
      numCases: 12,
      seed: 424242,
      metamorphic: true,
      findingsDir: join(tmpdir(), 'runar-spend-oracle-metamorphic'),
    });
    expect(report.failureCount, JSON.stringify(report.byKind)).toBe(0);
    // Variants run through the same engine, so a metamorphic run validates
    // strictly more inputs than the base run over the same corpus.
    const base = await runSpendOracle({
      numCases: 12,
      seed: 424242,
      findingsDir: join(tmpdir(), 'runar-spend-oracle-metamorphic-base'),
    });
    expect(report.validatedInputs).toBeGreaterThan(base.validatedInputs);
  }, 180_000);
});
