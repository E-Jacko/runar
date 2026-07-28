import { describe, it, expect, afterAll } from 'vitest';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  runAllIrParityChecks,
  runAllParserOnlyChecks,
  shutdownJavaDaemon,
} from '../runner.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const CONFORMANCE_TESTS_DIR = join(__dirname, '../../tests');

// Audit finding #10: "do all tiers agree byte-for-byte" was implemented three
// times (ci.yml inline bash/jq, cross-compiler-diff.sh, the TS runner), each
// with its own allowlist handling. The TS runner is now the single source of
// truth and ci.yml delegates to `--ir-parity`.
//
// The two layers have DELIBERATELY different allowlist semantics, and this
// file pins both so a future "simplification" cannot quietly merge them:
//   * Stack-IR / hex parity (--ir-parity) IS scoped by the per-fixture
//     `compilers` allowlist in source.json.
//   * Frontend/parser parity (--parser-only) IGNORES that allowlist — every
//     tier must parse every fixture in every format, no exceptions.
describe('--ir-parity honours the per-fixture compilers allowlist', () => {
  afterAll(async () => {
    await shutdownJavaDaemon();
  });

  it(
    'restricts hex parity to the allowlisted tier on a Go-only fixture',
    async () => {
      const report = await runAllIrParityChecks(CONFORMANCE_TESTS_DIR, { filter: 'babybear' });
      const babybear = report.results.find((r) => r.fixture === 'babybear');

      expect(babybear, 'babybear fixture not found in the IR-parity report').toBeDefined();
      expect(babybear!.status).toBe('ok');
      expect(babybear!.activeCompilers).toEqual(['go']);
      // The other five non-TS tiers must be recorded as allowlist-excluded,
      // not silently absent.
      expect([...babybear!.allowlistExcluded].sort()).toEqual(
        ['java', 'python', 'ruby', 'rust', 'zig'],
      );
      expect(report.allOk).toBe(true);
    },
    600_000,
  );

  it(
    'drives every non-TS tier on a fixture with no allowlist',
    async () => {
      const report = await runAllIrParityChecks(CONFORMANCE_TESTS_DIR, { filter: 'stateful-counter' });
      const fixture = report.results.find((r) => r.fixture === 'stateful-counter');

      expect(fixture, 'stateful-counter fixture not found in the IR-parity report').toBeDefined();
      expect(fixture!.status).toBe('ok');
      expect([...fixture!.activeCompilers].sort()).toEqual(
        ['go', 'java', 'python', 'ruby', 'rust', 'zig'],
      );
      expect(fixture!.allowlistExcluded).toEqual([]);
      // Byte-for-byte: every tier produced the same non-empty hex.
      const hexes = Object.values(fixture!.hexByCompiler);
      expect(hexes).toHaveLength(6);
      expect(new Set(hexes).size).toBe(1);
      expect(hexes[0]!.length).toBeGreaterThan(0);
    },
    600_000,
  );

  it(
    'still parses the Go-only fixture with EVERY tier (parser layer ignores the allowlist)',
    async () => {
      const report = await runAllParserOnlyChecks(CONFORMANCE_TESTS_DIR, { filter: 'babybear' });
      const entries = report.entries.filter((e) => e.fixture === 'babybear');

      expect(entries.length, 'babybear should contribute one entry per declared format').toBeGreaterThan(0);
      for (const entry of entries) {
        const ran = entry.results.map((r) => r.compiler).sort();
        expect(
          ran,
          `parser-only must ignore the "compilers": ["go"] allowlist — ` +
            `format ${entry.format} only ran [${ran.join(',')}]`,
        ).toEqual(['go', 'java', 'python', 'ruby', 'rust', 'ts', 'zig']);
      }
      expect(report.failures).toEqual([]);
      expect(report.skippedFixtures).toEqual([]);
      expect(report.allOk).toBe(true);
    },
    900_000,
  );
});
