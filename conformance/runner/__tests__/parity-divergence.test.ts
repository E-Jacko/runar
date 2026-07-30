import { describe, expect, it } from 'vitest';

import { compareIR, compareScript, type CompilerOutput } from '../runner.js';

// A cross-tier parity gate that reports "IR mismatch between compilers" without
// naming WHICH tier diverged is not actionable: the operator has to re-run the
// suite by hand, per tier, to find out. That is exactly what happened chasing
// the intermittent add-data-output / add-raw-output failure — the gate fired and
// told us nothing. These tests pin the diagnostic, not just the verdict.

function out(over: Partial<CompilerOutput> = {}): CompilerOutput {
  return {
    irJson: '{"a":1}',
    scriptHex: 'deadbeef',
    scriptAsm: '',
    success: true,
    durationMs: 1,
    ...over,
  };
}

/** ts, go, rust, python, zig, ruby, java — the fixed slot order both callers use. */
function allSeven(over: Partial<Record<number, CompilerOutput | undefined>> = {}) {
  const base = Array.from({ length: 7 }, () => out());
  for (const [i, v] of Object.entries(over)) base[Number(i)] = v as CompilerOutput;
  return base;
}

describe('compareIR divergence reporting', () => {
  it('agrees across all seven tiers', () => {
    const r = compareIR(allSeven(), 7);
    expect(r.ok).toBe(true);
    expect(r.detail).toBeUndefined();
  });

  it('names the single divergent tier and the majority it disagrees with', () => {
    // zig (slot 4) emits different IR from the other six.
    const r = compareIR(allSeven({ 4: out({ irJson: '{"a":2}' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toBeDefined();
    expect(r.detail).toContain('zig');
    // The six agreeing tiers must be identified as the majority, so the reader
    // knows zig is the odd one out rather than "seven tiers all disagree".
    expect(r.detail).toMatch(/ts, go, rust, python, ruby, java/);
  });

  it('reports the offset of the first differing character', () => {
    const r = compareIR(allSeven({ 1: out({ irJson: '{"a":9}' }) }), 7);
    expect(r.ok).toBe(false);
    // '{"a":' is 5 chars, so index 5 is the first divergence.
    expect(r.detail).toContain('offset 5');
  });

  it('reports every group when tiers split more than two ways', () => {
    const r = compareIR(allSeven({ 1: out({ irJson: '{"a":2}' }), 5: out({ irJson: '{"a":3}' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('go');
    expect(r.detail).toContain('ruby');
  });

  it('names the tier that reported success with empty IR', () => {
    const r = compareIR(allSeven({ 3: out({ irJson: '' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('python');
    expect(r.detail).toContain('empty');
  });

  it('names which tiers were present when too few produced IR to cross-validate', () => {
    const outputs: (CompilerOutput | undefined)[] = Array.from({ length: 7 }, () => undefined);
    outputs[2] = out();
    const r = compareIR(outputs, 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('rust');
  });

  it('treats a single-tier fixture as a trivial match', () => {
    const outputs: (CompilerOutput | undefined)[] = Array.from({ length: 7 }, () => undefined);
    outputs[1] = out();
    expect(compareIR(outputs, 1).ok).toBe(true);
  });
});

describe('compareScript divergence reporting', () => {
  it('agrees across all seven tiers', () => {
    expect(compareScript(allSeven(), 7).ok).toBe(true);
  });

  it('names the divergent tier and the first differing byte offset', () => {
    const r = compareScript(allSeven({ 6: out({ scriptHex: 'deadbfef' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('java');
    // 'deadbeef' vs 'deadbfef' first differs in the 3rd byte (index 2).
    expect(r.detail).toContain('byte 2');
  });

  it('reports a length difference rather than a byte offset when one side is a prefix', () => {
    const r = compareScript(allSeven({ 0: out({ scriptHex: 'deadbeefcc' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('ts');
    expect(r.detail).toMatch(/5 bytes|length/);
  });

  it('is insensitive to case and whitespace, as the comparison itself is', () => {
    const r = compareScript(allSeven({ 2: out({ scriptHex: 'DE AD BE EF' }) }), 7);
    expect(r.ok).toBe(true);
  });

  it('names the tier that reported success with empty hex', () => {
    const r = compareScript(allSeven({ 5: out({ scriptHex: '' }) }), 7);
    expect(r.ok).toBe(false);
    expect(r.detail).toContain('ruby');
    expect(r.detail).toContain('empty');
  });
});
