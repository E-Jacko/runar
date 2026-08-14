/**
 * Testing-gap remediation, reviewer finding P1-3: `newAlwaysAckMockProvider`
 * (a `MockProvider` factory whose entire purpose is "never validate a
 * broadcast") was re-exported from both public barrels (`src/index.ts` and
 * `src/providers/index.ts`). The machine-checked always-ack allowlist
 * (`always-ack-allowlist.test.ts`) only scans `src/**\/*.{test,spec}.ts` in
 * THIS package, so any other package or downstream consumer could import the
 * never-validate factory through the public `runar-sdk` entry point
 * completely ungated.
 *
 * Fix: drop it from both barrels. It stays exported from
 * `providers/mock.ts` (a non-public module) so this package's own
 * allowlisted tests can still import it directly.
 */
import { describe, it, expect } from 'vitest';
import * as sdkIndex from '../index.js';
import * as providersIndex from '../providers/index.js';

describe('newAlwaysAckMockProvider is not public SDK surface (P1-3)', () => {
  it('is not exported from the package root barrel (src/index.ts)', () => {
    expect((sdkIndex as Record<string, unknown>).newAlwaysAckMockProvider).toBeUndefined();
  });

  it('is not exported from the providers barrel (src/providers/index.ts)', () => {
    expect((providersIndex as Record<string, unknown>).newAlwaysAckMockProvider).toBeUndefined();
  });
});
