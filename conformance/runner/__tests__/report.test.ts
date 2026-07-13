import { describe, it, expect } from 'vitest';
import { generateReport } from '../report.js';
import type { ConformanceResult } from '../runner.js';

// generateReport decides each fixture's pass/fail/skip status, and the CLI exits
// non-zero on report.failed > 0 (runner/index.ts). So a real failure that is
// mislabeled 'skip' silently passes CI (audit #17).

const out = (success: boolean, error = '', durationMs = 1) => ({
  irJson: '',
  scriptHex: '',
  scriptAsm: '',
  success,
  error,
  durationMs,
});

const base = (over: Partial<ConformanceResult>): ConformanceResult => ({
  testName: 'demo',
  tsCompiler: out(true),
  irMatch: true,
  scriptMatch: true,
  errors: [],
  ...over,
});

describe('generateReport status (audit #17)', () => {
  it('a fixture where EVERY tier failed is FAILED, not skipped', () => {
    // TS ran and failed with a real compile error; no other tier ran; the
    // parity comparison found a mismatch. The old code marked this 'skip'.
    const r = generateReport([
      base({
        tsCompiler: out(false, 'compile error: bad thing'),
        irMatch: false,
        scriptMatch: false,
        errors: ['TS compiler failed'],
      }),
    ]);
    expect(r.results[0]!.status).toBe('fail');
    expect(r.failed).toBe(1);
    expect(r.skipped).toBe(0);
  });

  it('a mismatch is always a failure even if the all-skipped heuristic would fire', () => {
    const r = generateReport([
      base({ tsCompiler: out(false, 'nope'), irMatch: false, scriptMatch: false }),
    ]);
    expect(r.results[0]!.status).toBe('fail');
  });

  it('a genuinely un-evaluated fixture (source not found, no tiers) is skipped', () => {
    const r = generateReport([
      base({
        tsCompiler: out(false, 'Source file not found: X.runar.ts'),
        irMatch: true,
        scriptMatch: true,
        errors: [],
      }),
    ]);
    expect(r.results[0]!.status).toBe('skip');
    expect(r.skipped).toBe(1);
    expect(r.failed).toBe(0);
  });

  it('a clean multi-tier match is a pass', () => {
    const r = generateReport([base({ goCompiler: out(true), javaCompiler: out(true) })]);
    expect(r.results[0]!.status).toBe('pass');
  });

  it('includes the Java timing (previously omitted)', () => {
    const r = generateReport([base({ javaCompiler: out(true, '', 42) })]);
    expect(r.results[0]!.timings.java).toBe(42);
  });
});
