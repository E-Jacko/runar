// INTERPRETER-ONLY: spendability covered by conformance/script_execution_test.go
// (TestRawOutput_ScriptExecution_Accept / _Reject_RawOutputAbsent hand-build the exact
//  3-output tx [rawOutput, continuation, change] this method requires and run the compiled
//  bytes on the go-sdk engine). There is deliberately NO real-crypto witness: the SDK
//  deploy->call path funds a single continuation output and cannot compose the separate
//  1000-sat raw output, so it would reject a valid spend. See
//  conformance/witnesses/coverage-ledger.json entry "add-raw-output".
import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { TestContract } from 'runar-testing';

const __dirname = dirname(fileURLToPath(import.meta.url));
const source = readFileSync(join(__dirname, 'RawOutputTest.runar.ts'), 'utf8');

describe('RawOutputTest', () => {
  it('compiles via TestContract.fromSource', () => {
    const c = TestContract.fromSource(source, { count: 0n });
    expect(c.state.count).toBe(0n);
  });

  it('sendToScript emits a raw output and bumps count', () => {
    const c = TestContract.fromSource(source, { count: 0n });
    const r = c.call('sendToScript', {
      // P2PKH-shaped raw script: 76a914 <20 bytes> 88ac
      scriptBytes: '76a914' + '00'.repeat(20) + '88ac',
    });
    expect(r.success).toBe(true);
    expect(c.state.count).toBe(1n);
    expect(r.outputs!.some((o) => '_rawScript' in (o as object))).toBe(true);
  });
});
