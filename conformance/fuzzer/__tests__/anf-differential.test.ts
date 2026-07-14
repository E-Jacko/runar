import { describe, it, expect } from 'vitest';
import { classifyTierResults, classifyUnavailableTier } from '../anf-differential.js';

describe('classifyUnavailableTier (finding #18 — requested tier silently dropped)', () => {
  it('DEFAULT: a requested tier with no binary FAILS (not silently skipped)', () => {
    // skipMissingTiers unset — the CI gates never pass it, so the old default
    // silently skipped a missing tier, hiding cross-tier divergences.
    expect(classifyUnavailableTier(false, undefined)).toBe('failed');
    expect(classifyUnavailableTier(false, false)).toBe('failed');
  });
  it('only an EXPLICIT skipMissingTiers:true downgrades a missing tier to a skip', () => {
    expect(classifyUnavailableTier(false, true)).toBe('skipped');
  });
  it('an AVAILABLE tier that produced null = ran-and-rejected = failure', () => {
    expect(classifyUnavailableTier(true, undefined)).toBe('failed');
    expect(classifyUnavailableTier(true, true)).toBe('failed');
    expect(classifyUnavailableTier(undefined, true)).toBe('failed');
  });
});

// Finding #16 — the ANF differential harness's own docstring (anf-differential.ts
// header) promises it "fails the job on ... any compiler crash that doesn't
// reproduce on every other tier." `classifyTierResults` is the pure decision
// function pulled out of `runAnfDifferential`'s per-program loop; these tests
// drive it directly with synthetic tier outputs instead of the full
// generate-and-compile pipeline.
describe('classifyTierResults (finding #16 — silent single-tier crash)', () => {
  it('is a mismatch when >=2 tiers agree but a requested tier crashed/rejected', () => {
    // Six tiers agree on identical hex; `java` has an installed binary that
    // rejected the (valid) program. Before the fix this was NEVER checked
    // once >=2 outputs existed, so the crash was silently dropped.
    const outputs = {
      ts: 'aabbcc',
      go: 'aabbcc',
      rust: 'aabbcc',
      python: 'aabbcc',
      zig: 'aabbcc',
      ruby: 'aabbcc',
    };
    const result = classifyTierResults(outputs, ['java']);
    expect(result.status).toBe('mismatch');
    if (result.status === 'mismatch') {
      expect(result.reason).toContain('java');
    }
  });

  it('is ok when all producing tiers agree and nothing failed', () => {
    const outputs = { ts: 'aabbcc', go: 'aabbcc', rust: 'aabbcc' };
    const result = classifyTierResults(outputs, []);
    expect(result.status).toBe('ok');
  });

  it('is still a mismatch on plain hex divergence (existing behavior preserved)', () => {
    const outputs = { ts: 'aabbcc', go: 'ddeeff' };
    const result = classifyTierResults(outputs, []);
    expect(result.status).toBe('mismatch');
    if (result.status === 'mismatch') {
      expect(result.reason).toContain('hex divergence');
    }
  });

  it('reports BOTH hex divergence and a tier crash when both occur together', () => {
    const outputs = { ts: 'aabbcc', go: 'ddeeff' };
    const result = classifyTierResults(outputs, ['java']);
    expect(result.status).toBe('mismatch');
    if (result.status === 'mismatch') {
      expect(result.reason).toContain('hex divergence');
      expect(result.reason).toContain('java');
    }
  });

  it('is a mismatch when fewer than 2 tiers produced output and one failed (pre-existing behavior)', () => {
    const outputs = { ts: 'aabbcc' };
    const result = classifyTierResults(outputs, ['go']);
    expect(result.status).toBe('mismatch');
    if (result.status === 'mismatch') {
      expect(result.reason).toContain('go');
    }
  });

  it('is insufficient (skip, not mismatch) when fewer than 2 tiers ran and none failed', () => {
    const outputs = { ts: 'aabbcc' };
    const result = classifyTierResults(outputs, []);
    expect(result.status).toBe('insufficient');
  });
});
