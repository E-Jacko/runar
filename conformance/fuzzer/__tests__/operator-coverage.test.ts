import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import {
  arbGeneratedContract,
  arbArithmeticContract,
  arbStatelessContract,
  renderTypeScript,
} from '../../../packages/runar-testing/src/fuzzer/index.js';

// Operator coverage gap (audit findings #P0-2, #10): `/` and `%` must appear
// in the generated corpus of BOTH generators that feed a real EXECUTION
// oracle (interpreter vs @bsv/sdk Spend on synthesized witnesses):
//   - arbGeneratedContract               -> execute-differential.ts / ir-differential.ts
//   - arbArithmeticContract / arbStatelessContract -> metamorphic-fuzz.ts
//
// Shift/bitwise ops (`<<`/`>>`/`&`/`|`/`^`) are covered separately, only in
// the byte-parity-only `anf-differential.ts` generator (see
// conformance/fuzzer/__tests__/anf-differential.test.ts and
// conformance/fuzzer/anf-differential.ts). They are deliberately NOT added to
// these two execution-oracle generators: `<<`/`>>`/`&`/`|`/`^` on bigint have
// a CONFIRMED interpreter-vs-script divergence (raw-byte-width truncation /
// sign-magnitude vs two's-complement mismatch — see task report), and both
// `arbGeneratedContract` and `arbArithmeticContract` back FIXED-SEED PR merge
// gates (`fuzz:execute:gate`, `fuzz-metamorphic` in
// .github/workflows/fuzzer-nightly.yml). Enabling them here would turn every
// future PR red on an already-known, already-reported issue rather than
// catching a new regression.
describe('Operator coverage: division / modulo reach the execution-oracle generators', () => {
  it('arbGeneratedContract renders `/` and `%` across a large sample', () => {
    const contracts = fc.sample(arbGeneratedContract, { numRuns: 300, seed: 20260712 });
    const sources = contracts.map((c) => renderTypeScript(c));
    const hasDiv = sources.some((s) => / \/ /.test(s));
    const hasMod = sources.some((s) => / % /.test(s));
    expect(hasDiv).toBe(true);
    expect(hasMod).toBe(true);
  });

  it('arbArithmeticContract source strings contain `/` and `%` across a large sample', () => {
    const sources = fc.sample(arbArithmeticContract, { numRuns: 300, seed: 20260712 });
    const hasDiv = sources.some((s) => / \/ /.test(s));
    const hasMod = sources.some((s) => / % /.test(s));
    expect(hasDiv).toBe(true);
    expect(hasMod).toBe(true);
  });

  it('arbStatelessContract source strings contain `/` and `%` across a large sample', () => {
    const sources = fc.sample(arbStatelessContract, { numRuns: 300, seed: 20260712 });
    const hasDiv = sources.some((s) => / \/ /.test(s));
    const hasMod = sources.some((s) => / % /.test(s));
    expect(hasDiv).toBe(true);
    expect(hasMod).toBe(true);
  });

  it('never generates a literal-0 divisor (division-by-zero guard)', () => {
    const contracts = fc.sample(arbGeneratedContract, { numRuns: 300, seed: 20260712 });
    const sources = contracts.map((c) => renderTypeScript(c));
    for (const s of sources) {
      expect(s).not.toMatch(/[/%] 0n\)/);
    }
    const stringSources = [
      ...fc.sample(arbArithmeticContract, { numRuns: 300, seed: 20260712 }),
      ...fc.sample(arbStatelessContract, { numRuns: 300, seed: 20260712 }),
    ];
    for (const s of stringSources) {
      expect(s).not.toMatch(/[/%] 0n\)/);
    }
  });
});
