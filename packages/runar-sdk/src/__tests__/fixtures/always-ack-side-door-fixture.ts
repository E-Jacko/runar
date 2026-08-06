/**
 * Testing-gap remediation P1-4 regression fixture: a `.ts` file under
 * `__tests__/` that is NOT named `*.test.ts`/`*.spec.ts` and uses an
 * always-ack escape hatch. Before P1-4, `always-ack-allowlist.test.ts`'s
 * scan only read `*.test.ts`/`*.spec.ts` files, so a helper module like
 * this one — e.g. a future `src/__tests__/helpers.ts` exporting a
 * `makeProvider()` that quietly disables validation — would be invisible to
 * the gate no matter what it did, and every test file that imported it would
 * go always-ack with nothing in the allowlist ever catching it.
 *
 * This file exists solely to prove the gate now scans every `.ts` file
 * under `__tests__/`, not just test-named ones. It is deliberately never
 * imported by a real test — tests that need an always-ack provider import
 * `newAlwaysAckMockProvider` directly from `../../providers/mock.js`.
 */
import { newAlwaysAckMockProvider } from '../../providers/mock.js';

export function unusedAlwaysAckHelper() {
  return newAlwaysAckMockProvider();
}
