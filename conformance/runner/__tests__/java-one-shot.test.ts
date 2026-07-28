// ---------------------------------------------------------------------------
// C23 — the Java one-shot path must not report an "empty success".
//
// `buildJavaOneShotOutput` is exactly what `runJavaCompiler` returns when the
// daemon is disabled (`RUNAR_JAVA_DAEMON=0`). The failure mode this pins down:
// the jar exits 0 but writes nothing to stdout (crashed after the exit-code
// path, wrong flag, redirected output, truncated pipe). The old inline code
// returned `success: true` with `irJson: ''` / `scriptHex: ''`, and the
// golden-file gate is written as `javaResult?.success && javaResult.scriptHex`
// — falsy hex ⇒ Java silently skipped the golden comparison while still being
// counted as a tested tier.
// ---------------------------------------------------------------------------

import { describe, it, expect } from 'vitest';
import { buildJavaOneShotOutput } from '../runner.js';

/** A minimal, valid ANF IR document — enough for canonicalizeJson to chew on. */
const IR_JSON = JSON.stringify({ contract: 'Counter', bindings: [] });
const HEX = 'aabbccdd';

const ok = (stdout: string) => ({ stdout, stderr: '', code: 0 });
const err = (code: number, stderr: string) => ({ stdout: '', stderr, code });

describe('buildJavaOneShotOutput (C23)', () => {
  it('treats exit-0-with-empty-stdout on BOTH legs as a failure', () => {
    const out = buildJavaOneShotOutput(ok(''), ok(''), 12);
    expect(out.success).toBe(false);
    expect(out.error).toMatch(/no IR and no script hex/);
    expect(out.error).toMatch(/exit 0, empty stdout/);
    expect(out.irJson).toBe('');
    expect(out.scriptHex).toBe('');
    expect(out.durationMs).toBe(12);
  });

  it('treats exit-0 with empty --emit-ir stdout as a failure', () => {
    const out = buildJavaOneShotOutput(ok('   \n'), ok(HEX), 1);
    expect(out.success).toBe(false);
    expect(out.error).toMatch(/empty IR/);
  });

  it('treats exit-0 with empty --hex stdout as a failure', () => {
    const out = buildJavaOneShotOutput(ok(IR_JSON), ok('  \n '), 1);
    expect(out.success).toBe(false);
    expect(out.error).toMatch(/empty script hex/);
  });

  it('treats a non-zero --hex exit as a failure instead of silently emptying hex', () => {
    const out = buildJavaOneShotOutput(ok(IR_JSON), err(1, 'codegen: unsupported builtin'), 1);
    expect(out.success).toBe(false);
    expect(out.error).toMatch(/java --hex exit 1/);
    expect(out.error).toMatch(/unsupported builtin/);
    expect(out.scriptHex).toBe('');
  });

  it('reports a non-zero --emit-ir exit', () => {
    const out = buildJavaOneShotOutput(err(2, 'parse error at line 3'), ok(''), 1);
    expect(out.success).toBe(false);
    expect(out.error).toMatch(/java --emit-ir exit 2/);
    expect(out.error).toMatch(/parse error at line 3/);
  });

  it('keeps a genuinely successful run passing', () => {
    const out = buildJavaOneShotOutput(ok(`${IR_JSON}\n`), ok(`${HEX}\n`), 42);
    expect(out.success).toBe(true);
    expect(out.error).toBeUndefined();
    expect(out.scriptHex).toBe(HEX);
    // canonicalizeJson pretty-prints with sorted keys; just assert it survived.
    expect(JSON.parse(out.irJson)).toEqual({ bindings: [], contract: 'Counter' });
    expect(out.durationMs).toBe(42);
  });
});
