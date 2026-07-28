import { describe, it, expect, afterAll } from 'vitest';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  runConformanceTest,
  getSpawnStats,
  resetSpawnStats,
  shutdownJavaDaemon,
} from '../runner.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const CONFORMANCE_TESTS_DIR = join(__dirname, '../../tests');

// Audit finding #17: the runner used to invoke every native compiler TWICE per
// (fixture, format) — once with `--emit-ir`, once with `--hex`. Each spawn
// re-parsed and re-compiled the same source, and with ~64 fixtures × up to 9
// formats × 7 tiers that was the dominant cost of the conformance job.
//
// The tiers whose CLI accepts `--emit-ir-to <path>` now get both artifacts from
// ONE invocation. `babybear` declares `"compilers": ["go"]`, so exactly one
// tier runs and the spawn tally is unambiguous: 1 with single-spawn mode, 2
// with the old double-spawn path.
describe('native compilers are driven with a single spawn per compile', () => {
  afterAll(async () => {
    await shutdownJavaDaemon();
  });

  it(
    'compiles the Go-only babybear fixture with exactly one compiler spawn',
    async () => {
      resetSpawnStats();
      const result = await runConformanceTest(join(CONFORMANCE_TESTS_DIR, 'babybear'));
      const stats = getSpawnStats();

      // Guard against measuring a no-op: the fixture must actually have run.
      expect(
        result.errors,
        `babybear did not compile cleanly, so the spawn tally is meaningless`,
      ).toEqual([]);
      expect(result.goCompiler?.success).toBe(true);
      expect(result.goCompiler?.scriptHex.length ?? 0).toBeGreaterThan(0);
      expect((result.goCompiler?.irJson ?? '').length).toBeGreaterThan(0);

      expect(
        stats.total,
        `babybear is a Go-only fixture, so exactly ONE compiler process should ` +
          `run. Seeing 2 means the runner regressed to the ` +
          `\`--emit-ir\` + \`--hex\` double-spawn path. Tally: ` +
          JSON.stringify(stats.byCommand),
      ).toBe(1);
    },
    180_000,
  );
});
