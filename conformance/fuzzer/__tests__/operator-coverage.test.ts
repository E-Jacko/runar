import { describe, it, expect } from 'vitest';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import fc from 'fast-check';
import {
  arbGeneratedContract,
  arbArithmeticContract,
  arbStatelessContract,
  renderTypeScript,
} from '../../../packages/runar-testing/src/fuzzer/index.js';
import { runExecuteDifferential } from '../execute-differential.js';

// Operator coverage gap (audit findings #P0-2, #10): `/` and `%` must appear
// in the generated corpus of BOTH generators that feed a real EXECUTION
// oracle (interpreter vs @bsv/sdk Spend on synthesized witnesses):
//   - arbGeneratedContract               -> execute-differential.ts / ir-differential.ts
//   - arbArithmeticContract / arbStatelessContract -> metamorphic-fuzz.ts
//
// Shift/bitwise ops (`<<`/`>>`/`&`/`|`/`^`) were ALSO withheld from these two
// execution-oracle generators for the same reason: the interpreter used to
// diverge from the deployed script's raw-byte-width semantics (audit #10,
// fixed in #141 — "fix/shift-bitwise-semantics"). Commit 0e92d9fe re-enabled
// them in `arbArithExpr` (the string-based generator behind
// `arbArithmeticContract` / `arbStatelessContract`) once the interpreter fix
// landed, but never ported the same change to `arbBigintExprIR` (the IR-based
// generator behind `arbGeneratedContract`), and this comment was never
// updated — leaving `arbGeneratedContract` (and therefore
// `execute-differential.ts`'s randomized PR/nightly gate) blind to a
// regression in exactly the opcodes #141 fixed. C6 (deep-review finding)
// closes that gap: shift/bitwise now reach `arbGeneratedContract` too, with
// operand magnitudes that can exceed the single-byte scriptnum range (the
// #141 bug only manifested once an operand needed >1 script-number byte).
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

// C6 (deep-review finding, P1 "serious test blindness"): the randomized
// execution-oracle generator (`arbGeneratedContract`, feeding
// `execute-differential.ts`'s PR/nightly gate) excluded shift/bitwise ops
// entirely and only ever synthesized single-byte-magnitude operands
// (`INPUT_MAG = 100`), so it could never re-catch a #141-shaped regression.
describe('Operator coverage: shift/bitwise reach arbGeneratedContract (C6 / #141 regression)', () => {
  it('arbGeneratedContract renders `<< >> & | ^` across a large sample', () => {
    const contracts = fc.sample(arbGeneratedContract, { numRuns: 300, seed: 20260712 });
    const sources = contracts.map((c) => renderTypeScript(c));
    expect(sources.some((s) => / << /.test(s))).toBe(true);
    expect(sources.some((s) => / >> /.test(s))).toBe(true);
    expect(sources.some((s) => / & /.test(s))).toBe(true);
    expect(sources.some((s) => / \| /.test(s))).toBe(true);
    expect(sources.some((s) => / \^ /.test(s))).toBe(true);
  });

  it('arbGeneratedContract operand magnitudes can exceed the single-byte scriptnum range', () => {
    // Bitcoin script numbers are minimally-encoded sign-magnitude: a value
    // needs a second byte once |value| > 127 (the sign bit no longer fits in
    // one byte). #141 was specifically a byte-array-truncation bug that only
    // manifests once an operand crosses that boundary — a corpus confined to
    // [-100, 100] can never reach it.
    const contracts = fc.sample(arbGeneratedContract, { numRuns: 300, seed: 20260712 });
    const sources = contracts.map((c) => renderTypeScript(c));
    const literalRe = /(-?\d+)n\b/g;
    let sawMultiByte = false;
    outer: for (const s of sources) {
      for (const m of s.matchAll(literalRe)) {
        if (Math.abs(Number(m[1])) > 127) {
          sawMultiByte = true;
          break outer;
        }
      }
    }
    expect(sawMultiByte).toBe(true);
  });

  it('the widened corpus (shift/bitwise + multi-byte operands) still agrees end-to-end on the execution oracle', async () => {
    // Confirms the widened domain does not itself introduce false-positive
    // fuzz failures: re-derive the SAME seeded corpus the oracle runs and
    // assert it actually contains shift/bitwise ops (the coverage claim is
    // not vacuous), then run the real interpreter-vs-script oracle over it
    // and require zero divergences / zero errors.
    const numContracts = 80;
    const seed = 424242;
    const contracts = fc.sample(arbGeneratedContract, { numRuns: numContracts, seed });
    const sources = contracts.map((c) => renderTypeScript(c));
    const hasShiftOrBitwise = sources.some(
      (s) => / << /.test(s) || / >> /.test(s) || / & /.test(s) || / \| /.test(s) || / \^ /.test(s),
    );
    expect(hasShiftOrBitwise).toBe(true);

    const report = await runExecuteDifferential({
      numContracts,
      seed,
      inputsPerMethod: 6,
      findingsDir: join(tmpdir(), 'runar-exec-fuzz-operator-coverage'),
    });
    expect(report.casesRun).toBeGreaterThan(0);
    expect(report.divergenceCount).toBe(0);
    expect(report.errorCount).toBe(0);
  });
});
