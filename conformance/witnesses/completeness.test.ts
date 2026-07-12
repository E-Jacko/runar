import { it, expect } from 'vitest';
import { readFileSync, readdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const TESTS_DIR = join(__dirname, '..', 'tests');
const REAL_CRYPTO_DIR = join(__dirname, 'real-crypto');

const NON_SPEC_JSON = new Set(['crypto-exempt.json', 'harness-inapplicable.json']);

it('every conformance fixture is witnessed, real-crypto-executed, crypto-exempt, or harness-inapplicable', () => {
  const fixtures = readdirSync(TESTS_DIR, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name);

  // Plain differential witnesses (mock-crypto source-vs-script agreement).
  const witnessed = new Set(
    readdirSync(__dirname)
      .filter((f) => f.endsWith('.json') && !NON_SPEC_JSON.has(f))
      .map((f) => f.replace(/\.json$/, '')),
  );

  // Real-crypto execution specs (real secp256k1 on @bsv/sdk Spend). Every one
  // of these is actually EXECUTED by real-crypto-execution.test.ts, so it
  // counts as covered — no silent caps.
  const realCryptoExecuted = new Set(
    readdirSync(REAL_CRYPTO_DIR)
      .filter((f) => f.endsWith('.json'))
      .map((f) => f.replace(/\.json$/, '')),
  );

  // An exempt/inapplicable entry only counts as COVERAGE if its `coveredBy`
  // claim names a real engine. `coveredBy.kind === "UNCOVERED"` is an honest
  // admission that nothing executes the fixture — coverage-claims.test.ts
  // verifies every OTHER kind's claim is literally true, but "UNCOVERED"
  // fixtures must still surface here as uncovered so the hole cannot hide
  // behind list membership (audit findings #P0-1, #11, #14, #24).
  type LedgerEntry = { fixture: string; coveredBy?: { kind: string } };
  const isCovered = (e: LedgerEntry) => e.coveredBy?.kind !== 'UNCOVERED';

  const cryptoExemptEntries = JSON.parse(readFileSync(join(__dirname, 'crypto-exempt.json'), 'utf-8'))
    .exempt as LedgerEntry[];
  const inapplicableEntries = JSON.parse(
    readFileSync(join(__dirname, 'harness-inapplicable.json'), 'utf-8'),
  ).inapplicable as LedgerEntry[];

  // Used for the "uncovered" computation below: UNCOVERED-kind entries do
  // NOT count as coverage, so their fixture is excluded here on purpose.
  const cryptoExempt = new Set(cryptoExemptEntries.filter(isCovered).map((e) => e.fixture));
  const inapplicable = new Set(inapplicableEntries.filter(isCovered).map((e) => e.fixture));

  // Used for the stray-fixture-name typo guard below: ALL listed entries
  // (including honest UNCOVERED ones) must still name a real fixture.
  const cryptoExemptAll = new Set(cryptoExemptEntries.map((e) => e.fixture));
  const inapplicableAll = new Set(inapplicableEntries.map((e) => e.fixture));

  const uncovered = fixtures.filter(
    (f) =>
      !witnessed.has(f) &&
      !realCryptoExecuted.has(f) &&
      !cryptoExempt.has(f) &&
      !inapplicable.has(f),
  );
  expect(
    uncovered,
    `fixtures with no witness/execution and no exemption (includes fixtures whose exempt/inapplicable entry is honestly marked coveredBy.kind "UNCOVERED" — see conformance/witnesses/*.json for the follow-up issue): ${uncovered.join(', ')}`,
  ).toEqual([]);

  // Guard against typos: an exemption naming a fixture that does not exist.
  const known = new Set(fixtures);
  const strayCrypto = [...cryptoExemptAll].filter((f) => !known.has(f));
  const strayInapplicable = [...inapplicableAll].filter((f) => !known.has(f));
  const strayRealCrypto = [...realCryptoExecuted].filter((f) => !known.has(f));
  expect(strayCrypto, `crypto-exempt lists unknown fixtures: ${strayCrypto.join(', ')}`).toEqual([]);
  expect(
    strayInapplicable,
    `harness-inapplicable lists unknown fixtures: ${strayInapplicable.join(', ')}`,
  ).toEqual([]);
  expect(
    strayRealCrypto,
    `real-crypto specs name unknown fixtures: ${strayRealCrypto.join(', ')}`,
  ).toEqual([]);

  // Honesty guard: a fixture that is executed for real MUST NOT also sit in an
  // exempt list (a stale "routed out" claim). This is what keeps the exempt
  // lists from silently over-claiming coverage.
  const doubleListed = [...realCryptoExecuted].filter(
    (f) => cryptoExemptAll.has(f) || inapplicableAll.has(f),
  );
  expect(
    doubleListed,
    `real-crypto-executed fixtures still listed as exempt (remove them): ${doubleListed.join(', ')}`,
  ).toEqual([]);
});
