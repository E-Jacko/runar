import { it, expect } from 'vitest';
import { readFileSync, readdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const TESTS_DIR = join(__dirname, '..', 'tests');
const REAL_CRYPTO_DIR = join(__dirname, 'real-crypto');

const NON_SPEC_JSON = new Set(['coverage-ledger.json']);

it('every conformance fixture is witnessed, real-crypto-executed, or in the coverage ledger', () => {
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

  // A coverage-ledger entry only counts as COVERAGE if its `coveredBy` claim
  // names a real engine. `coveredBy.kind === "UNCOVERED"` is an honest
  // admission that nothing executes the fixture — coverage-claims.test.ts
  // verifies every OTHER kind's claim is literally true, but "UNCOVERED"
  // fixtures must still surface here as uncovered so the hole cannot hide
  // behind list membership (audit findings #P0-1, #11, #14, #24).
  type LedgerEntry = { fixture: string; cause?: string; coveredBy?: { kind: string } };
  const isCovered = (e: LedgerEntry) => e.coveredBy?.kind !== 'UNCOVERED';

  const ledgerEntries = JSON.parse(readFileSync(join(__dirname, 'coverage-ledger.json'), 'utf-8'))
    .entries as LedgerEntry[];

  // Used for the "uncovered" computation below: UNCOVERED-kind entries do
  // NOT count as coverage, so their fixture is excluded here on purpose.
  const ledgerCovered = new Set(ledgerEntries.filter(isCovered).map((e) => e.fixture));

  // Used for the stray-fixture-name typo guard below: ALL listed entries
  // (including honest UNCOVERED ones) must still name a real fixture.
  const ledgerAll = new Set(ledgerEntries.map((e) => e.fixture));

  const uncovered = fixtures.filter(
    (f) => !witnessed.has(f) && !realCryptoExecuted.has(f) && !ledgerCovered.has(f),
  );
  expect(
    uncovered,
    `fixtures with no witness/execution and no exemption (includes fixtures whose coverage-ledger.json entry is honestly marked coveredBy.kind "UNCOVERED" — see that file for the follow-up issue): ${uncovered.join(', ')}`,
  ).toEqual([]);

  // Guard against typos: an exemption naming a fixture that does not exist.
  const known = new Set(fixtures);
  const strayLedger = [...ledgerAll].filter((f) => !known.has(f));
  const strayRealCrypto = [...realCryptoExecuted].filter((f) => !known.has(f));
  expect(
    strayLedger,
    `coverage-ledger.json lists unknown fixtures: ${strayLedger.join(', ')}`,
  ).toEqual([]);
  expect(
    strayRealCrypto,
    `real-crypto specs name unknown fixtures: ${strayRealCrypto.join(', ')}`,
  ).toEqual([]);

  // Honesty guard: a fixture that is executed for real MUST NOT also sit in the
  // coverage ledger (a stale "routed out" claim). This is what keeps the ledger
  // from silently over-claiming coverage.
  const doubleListed = [...realCryptoExecuted].filter((f) => ledgerAll.has(f));
  expect(
    doubleListed,
    `real-crypto-executed fixtures still listed in coverage-ledger.json (remove them): ${doubleListed.join(', ')}`,
  ).toEqual([]);
});
