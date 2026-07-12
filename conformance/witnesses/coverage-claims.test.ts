/**
 * Ledger honesty gate (audit findings #P0-1, #11, #14, #24).
 *
 * `crypto-exempt.json` and `harness-inapplicable.json` used to carry only a
 * free-text `reason` string. Membership in the list was treated as "covered"
 * by `completeness.test.ts` with NO verification that the claimed coverage
 * (e.g. "Covered by the Go tx-context path") is actually true. Several
 * entries claimed a `conformance/script_execution_test.go` execution path
 * that does not reference the fixture at all.
 *
 * Every entry now carries a structured `coveredBy` field. This test proves
 * each claim by grepping the artifact it points to — it does not trust the
 * free-text `reason`/`cause` fields, which remain for human readability only.
 *
 * `coveredBy.kind` values:
 *   - "go-script-exec"          — the fixture name is literally compiled and
 *                                  executed by conformance/script_execution_test.go
 *                                  (`compileRúnar("<fixture>", ...)`).
 *   - "go-family-exec"          — the fixture's underlying primitive (not the
 *                                  literal fixture contract) is exercised by a
 *                                  real Go test function in script_execution_test.go
 *                                  via an inline reconstruction of the same codegen.
 *   - "integration"             — an on-chain regtest integration test
 *                                  (integration/<tier>/...) deploys/spends the
 *                                  fixture's actual .runar.ts source.
 *   - "interpreter-witness-exec"— the ANF interpreter executes the fixture with
 *                                  realistic tx-context witness bytes injected
 *                                  (TS tier only; not full Bitcoin Script bytes).
 *   - "anf-cross-tier-parity"   — conformance/anf-interpreter/cross-interpreter.test.ts
 *                                  runs the fixture's method through the ANF
 *                                  interpreter across all 7 tiers (TS reference
 *                                  + per-language drivers) and asserts the
 *                                  resulting state/outputs match a pinned
 *                                  golden. Proves cross-tier interpreter
 *                                  correctness; NOT a tx-context accept/reject
 *                                  differential against compiled script bytes.
 *   - "codegen-golden"          — byte-golden only, NOT executed by any engine.
 *                                  An honest opt-out: requires the fixture's own
 *                                  cross-tier expected-script.hex golden to exist,
 *                                  plus (where one exists) the family's dedicated
 *                                  codegen module file.
 *   - "go-only-nocodegen"       — compilers:["go"] proof-system fixture; no TS
 *                                  Stack-IR codegen exists so the TS-based
 *                                  differential/real-crypto harness cannot run it.
 *   - "sdk-corner"              — an acknowledged SDK/harness limitation with no
 *                                  further machine-checkable evidence beyond a
 *                                  non-empty `reason`.
 *   - "UNCOVERED"               — genuinely unexecuted anywhere; carries a
 *                                  mandatory `issue` field. completeness.test.ts
 *                                  does NOT count this fixture as covered, so the
 *                                  top-level completeness gate fails on it by
 *                                  design — the hole stays loud, not hidden.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..', '..');
const TESTS_DIR = join(__dirname, '..', 'tests');
const GO_SCRIPT_EXEC_PATH = join(__dirname, '..', 'script_execution_test.go');
const GO_SCRIPT_EXEC_SRC = readFileSync(GO_SCRIPT_EXEC_PATH, 'utf-8');

interface CoveredBy {
  kind: string;
  [key: string]: unknown;
}
interface LedgerEntry {
  fixture: string;
  coveredBy?: CoveredBy;
  [key: string]: unknown;
}

function loadLedger(file: string, listKey: string): LedgerEntry[] {
  const doc = JSON.parse(readFileSync(join(__dirname, file), 'utf-8'));
  return doc[listKey] as LedgerEntry[];
}

// Per-family dedicated codegen module — only families that genuinely have one
// are listed; a "codegen-golden" entry for a family NOT in this map is still
// valid (e.g. a base builtin with no dedicated module) but only the fixture's
// own golden is checked.
const FAMILY_MODULE: Record<string, string> = {
  ec: 'packages/runar-compiler/src/passes/ec-codegen.ts',
  p256: 'packages/runar-compiler/src/passes/p256-p384-codegen.ts',
  p384: 'packages/runar-compiler/src/passes/p256-p384-codegen.ts',
  rabin: 'packages/runar-compiler/src/passes/rabin-codegen.ts',
  'slh-dsa': 'packages/runar-compiler/src/passes/slh-dsa-codegen.ts',
  wots: 'packages/runar-compiler/src/passes/wots-codegen.ts',
  blake3: 'packages/runar-compiler/src/passes/blake3-codegen.ts',
};

/** Verify one entry's coveredBy claim against the artifact it names. Returns
 * null if the claim is true, or a human-readable failure reason if false. */
function verifyClaim(entry: LedgerEntry): string | null {
  const cb = entry.coveredBy;
  if (!cb || typeof cb.kind !== 'string') {
    return `${entry.fixture}: missing coveredBy.kind`;
  }
  switch (cb.kind) {
    case 'UNCOVERED': {
      if (!cb.issue || typeof cb.issue !== 'string' || cb.issue.trim().length === 0) {
        return `${entry.fixture}: UNCOVERED requires a non-empty "issue" field`;
      }
      return null;
    }
    case 'go-script-exec': {
      const fx = typeof cb.fixture === 'string' ? cb.fixture : entry.fixture;
      const needle = `compileRúnar("${fx}"`;
      if (!GO_SCRIPT_EXEC_SRC.includes(needle)) {
        return `${entry.fixture}: go-script-exec claims "${needle}" in script_execution_test.go — not found`;
      }
      return null;
    }
    case 'go-family-exec': {
      const marker = cb.marker;
      if (typeof marker !== 'string' || marker.length === 0) {
        return `${entry.fixture}: go-family-exec requires a non-empty "marker" field`;
      }
      if (!GO_SCRIPT_EXEC_SRC.includes(`func ${marker}`)) {
        return `${entry.fixture}: go-family-exec claims "func ${marker}" in script_execution_test.go — not found`;
      }
      return null;
    }
    case 'integration': {
      const path = cb.path;
      if (typeof path !== 'string' || path.length === 0) {
        return `${entry.fixture}: integration requires a non-empty "path" field`;
      }
      const full = join(REPO_ROOT, path);
      if (!existsSync(full)) {
        return `${entry.fixture}: integration claims ${path} — file does not exist`;
      }
      const content = readFileSync(full, 'utf-8');
      if (!content.includes(entry.fixture)) {
        return `${entry.fixture}: integration claims ${path} — file does not reference fixture "${entry.fixture}"`;
      }
      return null;
    }
    case 'interpreter-witness-exec': {
      const path = cb.path;
      if (typeof path !== 'string' || path.length === 0) {
        return `${entry.fixture}: interpreter-witness-exec requires a non-empty "path" field`;
      }
      const full = join(REPO_ROOT, path);
      if (!existsSync(full)) {
        return `${entry.fixture}: interpreter-witness-exec claims ${path} — file does not exist`;
      }
      const content = readFileSync(full, 'utf-8');
      if (!content.includes(entry.fixture)) {
        return `${entry.fixture}: interpreter-witness-exec claims ${path} — file does not reference fixture "${entry.fixture}"`;
      }
      return null;
    }
    case 'anf-cross-tier-parity': {
      const inputFile = cb.input;
      if (typeof inputFile !== 'string' || inputFile.length === 0) {
        return `${entry.fixture}: anf-cross-tier-parity requires a non-empty "input" field`;
      }
      const anfDir = join(REPO_ROOT, 'conformance', 'anf-interpreter');
      const inputPath = join(anfDir, 'inputs', inputFile);
      if (!existsSync(inputPath)) {
        return `${entry.fixture}: anf-cross-tier-parity claims conformance/anf-interpreter/inputs/${inputFile} — does not exist`;
      }
      const inputCase = JSON.parse(readFileSync(inputPath, 'utf-8')).case;
      if (inputCase !== entry.fixture) {
        return `${entry.fixture}: anf-cross-tier-parity input ${inputFile} has case="${inputCase}", expected "${entry.fixture}"`;
      }
      const expectedPath = join(anfDir, 'expected', inputFile);
      if (!existsSync(expectedPath)) {
        return `${entry.fixture}: anf-cross-tier-parity claims a pinned golden at conformance/anf-interpreter/expected/${inputFile} — does not exist`;
      }
      return null;
    }
    case 'codegen-golden': {
      const family = cb.family;
      if (typeof family !== 'string' || family.length === 0) {
        return `${entry.fixture}: codegen-golden requires a non-empty "family" field`;
      }
      const goldenPath = join(TESTS_DIR, entry.fixture, 'expected-script.hex');
      if (!existsSync(goldenPath) || readFileSync(goldenPath, 'utf-8').trim().length === 0) {
        return `${entry.fixture}: codegen-golden claims a golden at ${goldenPath} — missing or empty`;
      }
      const modulePath = FAMILY_MODULE[family];
      if (modulePath && !existsSync(join(REPO_ROOT, modulePath))) {
        return `${entry.fixture}: codegen-golden family "${family}" claims module ${modulePath} — does not exist`;
      }
      return null;
    }
    case 'go-only-nocodegen': {
      const srcJsonPath = join(TESTS_DIR, entry.fixture, 'source.json');
      if (!existsSync(srcJsonPath)) {
        return `${entry.fixture}: go-only-nocodegen — ${srcJsonPath} does not exist`;
      }
      const srcCfg = JSON.parse(readFileSync(srcJsonPath, 'utf-8'));
      const compilers = srcCfg.compilers;
      if (!Array.isArray(compilers) || compilers.length !== 1 || compilers[0] !== 'go') {
        return `${entry.fixture}: go-only-nocodegen claims source.json compilers === ["go"], got ${JSON.stringify(compilers)}`;
      }
      return null;
    }
    case 'sdk-corner': {
      if (typeof cb.reason !== 'string' || cb.reason.trim().length === 0) {
        return `${entry.fixture}: sdk-corner requires a non-empty "reason" field`;
      }
      return null;
    }
    default:
      return `${entry.fixture}: unknown coveredBy.kind "${cb.kind}"`;
  }
}

describe('ledger honesty — coveredBy claims must be literally true', () => {
  it('every crypto-exempt.json entry\'s coveredBy claim is verifiably true', () => {
    const entries = loadLedger('crypto-exempt.json', 'exempt');
    const failures = entries.map(verifyClaim).filter((f): f is string => f !== null);
    expect(failures, `false coverage claims:\n${failures.join('\n')}`).toEqual([]);
  });

  it('every harness-inapplicable.json entry\'s coveredBy claim is verifiably true', () => {
    const entries = loadLedger('harness-inapplicable.json', 'inapplicable');
    const failures = entries.map(verifyClaim).filter((f): f is string => f !== null);
    expect(failures, `false coverage claims:\n${failures.join('\n')}`).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// ">=1 accept and >=1 reject" — enforced in code, not just documented.
// ---------------------------------------------------------------------------

interface SpendSpec {
  expect: 'accept' | 'reject';
  [key: string]: unknown;
}
interface Spec {
  fixture?: string;
  acceptOnly?: boolean;
  spends: SpendSpec[];
}

function checkAcceptReject(dir: string, files: string[]): string[] {
  const failures: string[] = [];
  for (const f of files) {
    const spec: Spec = JSON.parse(readFileSync(join(dir, f), 'utf-8'));
    const spends = spec.spends ?? [];
    const accepts = spends.filter((s) => s.expect === 'accept').length;
    const rejects = spends.filter((s) => s.expect === 'reject').length;
    if (accepts === 0) failures.push(`${f}: zero accept spends`);
    if (rejects === 0 && spec.acceptOnly !== true) {
      failures.push(`${f}: zero reject spends and no "acceptOnly": true opt-out`);
    }
    if (rejects > 0 && spec.acceptOnly === true) {
      failures.push(`${f}: has ${rejects} reject spend(s) but "acceptOnly": true is set — stale opt-out`);
    }
  }
  return failures;
}

const NON_SPEC_JSON = new Set(['crypto-exempt.json', 'harness-inapplicable.json']);

describe('ledger honesty — every spend spec has >=1 accept and >=1 reject, or an explicit opt-out', () => {
  it('witnesses/*.json (mock-crypto differential oracle specs)', () => {
    const files = readdirSync(__dirname).filter(
      (f) => f.endsWith('.json') && !NON_SPEC_JSON.has(f),
    );
    const failures = checkAcceptReject(__dirname, files);
    expect(failures, failures.join('\n')).toEqual([]);
  });

  it('witnesses/real-crypto/*.json (real @bsv/sdk Spend specs)', () => {
    const dir = join(__dirname, 'real-crypto');
    const files = readdirSync(dir).filter((f) => f.endsWith('.json'));
    const failures = checkAcceptReject(dir, files);
    expect(failures, failures.join('\n')).toEqual([]);
  });
});
