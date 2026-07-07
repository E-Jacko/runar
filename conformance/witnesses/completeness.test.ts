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

  const cryptoExempt = new Set(
    (JSON.parse(readFileSync(join(__dirname, 'crypto-exempt.json'), 'utf-8')).exempt as {
      fixture: string;
    }[]).map((e) => e.fixture),
  );

  const inapplicable = new Set(
    (JSON.parse(readFileSync(join(__dirname, 'harness-inapplicable.json'), 'utf-8')).inapplicable as {
      fixture: string;
    }[]).map((e) => e.fixture),
  );

  const uncovered = fixtures.filter(
    (f) =>
      !witnessed.has(f) &&
      !realCryptoExecuted.has(f) &&
      !cryptoExempt.has(f) &&
      !inapplicable.has(f),
  );
  expect(
    uncovered,
    `fixtures with no witness/execution and no exemption: ${uncovered.join(', ')}`,
  ).toEqual([]);

  // Guard against typos: an exemption naming a fixture that does not exist.
  const known = new Set(fixtures);
  const strayCrypto = [...cryptoExempt].filter((f) => !known.has(f));
  const strayInapplicable = [...inapplicable].filter((f) => !known.has(f));
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
    (f) => cryptoExempt.has(f) || inapplicable.has(f),
  );
  expect(
    doubleListed,
    `real-crypto-executed fixtures still listed as exempt (remove them): ${doubleListed.join(', ')}`,
  ).toEqual([]);
});
