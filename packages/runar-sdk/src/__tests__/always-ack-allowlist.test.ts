/**
 * Testing-gap remediation plan Phase A2 (reviewer #1, TG-001): machine-checked
 * gate on the always-ack `MockProvider` escape hatches introduced by Phase
 * A1 (`disableBroadcastValidation`, `newAlwaysAckMockProvider`,
 * `{ validateBroadcasts: false }`, `enableBroadcastValidation(false)`).
 *
 * A test file may only use one of those escape hatches if it has a matching
 * entry in `always-ack-allowlist.json`. This keeps the allowlist honest in
 * both directions: it fails on unlisted always-ack usage (someone quietly
 * re-disabling the fund-safety net) AND on stale entries (a file that no
 * longer needs always-ack, or that was deleted) — so the list can only
 * shrink over time, per the plan's success criterion.
 *
 * SCOPE (P1-4): this gate governs `MockProvider` ONLY. A test can still
 * hand-roll an inline `Provider` object whose `broadcast()` acks anything
 * (e.g. `issue-107-broadcaster-injection.test.ts`'s inline broadcaster) —
 * that is real Provider-interface test surface unrelated to `MockProvider`'s
 * C8 validation, and this gate has no visibility into it. Passing this gate
 * means "no unlisted MockProvider always-ack usage", not "every broadcast in
 * this package's test suite is validated".
 */
import { describe, it, expect } from 'vitest';
import { readFileSync, readdirSync, statSync, existsSync } from 'node:fs';
import { join, dirname, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const PACKAGE_ROOT = join(__dirname, '../..');
const SRC_DIR = join(PACKAGE_ROOT, 'src');
const ALLOWLIST_PATH = join(__dirname, 'always-ack-allowlist.json');
/** The escape hatches' own implementation (`disableBroadcastValidation()`
 * literally assigns `this.validateBroadcasts = false`, and
 * `newAlwaysAckMockProvider` is its own declaration site) — not a usage
 * site, and scanning it would make the gate permanently un-satisfiable. */
const MOCK_PROVIDER_PATH = join(SRC_DIR, 'providers', 'mock.ts');

// P1-4: match the bare-identifier assignment form (`x.validateBroadcasts =
// false`), not just the constructor-options object-literal form
// (`{ validateBroadcasts: false }`) the original `:` -only pattern missed.
const ALWAYS_ACK_PATTERN =
  /disableBroadcastValidation|newAlwaysAckMockProvider|validateBroadcasts\s*[:=]\s*false|enableBroadcastValidation\(\s*false\s*\)/;

interface AllowlistEntry {
  file: string;
  reason: string;
  category: 'structure-only' | 'negative-api' | 'fixture-shape' | 'pending-a3';
  /** P0-1: required when the file's contents match `FUND_PATH_PATTERN`
   * (i.e. it calls `.deploy(`/`.call(`/`finalizeCall(` somewhere) — a
   * specific explanation of why the always-ack-using test doesn't actually
   * launder an unverified transaction (e.g. it independently re-verifies
   * script rejection via its own `Spend` replay, or the artifact under test
   * can never be script-valid for ANY call so there is no real spend to
   * protect). Prefer fixing the test over adding this field — see the
   * `$comment` on the JSON file. */
  fundPathJustification?: string;
}

interface Allowlist {
  $comment: string;
  entries: AllowlistEntry[];
}

/** P0-1: a real fund-movement call site — `RunarContract.deploy()`,
 * `.call()`, or `.finalizeCall()`. An allowlisted file whose contents match
 * this needs a `fundPathJustification` (the plan's rule that fund-path
 * deploy/call tests must not be allowlisted, machine-checked). */
const FUND_PATH_PATTERN = /\.deploy\(|\.call\(|finalizeCall\(/;

/**
 * P0-1 ratchet: the allowlist may only shrink. Lower this constant whenever
 * an entry is removed; never raise it to make a new addition pass — if a
 * new file genuinely needs always-ack, that is a sign to reconsider the
 * test, not to spend down the ratchet.
 */
const MAX_ALLOWLIST_ENTRIES = 9;

function readAllowlist(): Allowlist {
  return JSON.parse(readFileSync(ALLOWLIST_PATH, 'utf-8')) as Allowlist;
}

// P1-4: every `.ts` file under `src/`, not just `*.test.ts`/`*.spec.ts` — a
// non-test-named helper (e.g. a future `src/__tests__/helpers.ts` exporting
// `makeProvider()`) that quietly disables validation was previously
// invisible to this scan, and so was every test file that imported it.
function listTsFiles(dir: string): string[] {
  const out: string[] = [];
  for (const name of readdirSync(dir)) {
    const full = join(dir, name);
    const st = statSync(full);
    if (st.isDirectory()) {
      out.push(...listTsFiles(full));
    } else if (/\.ts$/.test(name)) {
      out.push(full);
    }
  }
  return out;
}

/** Files (repo-package-relative, e.g. "src/__tests__/foo.test.ts") that use
 * at least one always-ack escape hatch. Excludes this audit file itself —
 * it names the escape hatches in prose/regex source, not in a call site,
 * and auditing itself would be a meaningless self-referential entry —
 * and `providers/mock.ts`, the escape hatches' own declaration site. */
function filesUsingAlwaysAck(): Set<string> {
  const found = new Set<string>();
  for (const full of listTsFiles(SRC_DIR)) {
    if (full === __filename || full === MOCK_PROVIDER_PATH) continue;
    const contents = readFileSync(full, 'utf-8');
    if (ALWAYS_ACK_PATTERN.test(contents)) {
      found.add(relative(PACKAGE_ROOT, full));
    }
  }
  return found;
}

describe('always-ack MockProvider allowlist (Phase A2)', () => {
  const allowlist = readAllowlist();
  const listedFiles = new Set(allowlist.entries.map((e) => e.file));
  const actualUsage = filesUsingAlwaysAck();

  it(`allowlist count: ${allowlist.entries.length} (ratchet ceiling ${MAX_ALLOWLIST_ENTRIES})`, () => {
    // eslint-disable-next-line no-console
    console.log(`[always-ack-allowlist] ${allowlist.entries.length} file(s) currently allowlisted`);
    // P0-1: the previous version of this assertion (`>= 0`) was a no-op —
    // it could never fail, so the list could grow without bound with no CI
    // signal. The count must be tracked against a committed ceiling that
    // may only be lowered.
    expect(
      allowlist.entries.length,
      `allowlist grew to ${allowlist.entries.length} entries, above the committed ceiling of ` +
      `${MAX_ALLOWLIST_ENTRIES} — lower MAX_ALLOWLIST_ENTRIES only when removing an entry, ` +
      'never raise it to accommodate a new one',
    ).toBeLessThanOrEqual(MAX_ALLOWLIST_ENTRIES);
  });

  it('no duplicate file entries', () => {
    const seen = new Map<string, number>();
    for (const e of allowlist.entries) {
      seen.set(e.file, (seen.get(e.file) ?? 0) + 1);
    }
    const duplicates = [...seen.entries()].filter(([, count]) => count > 1).map(([file]) => file);
    expect(duplicates, `always-ack-allowlist.json has duplicate entries for: ${duplicates.join(', ')}`).toEqual([]);
  });

  it('every fund-path allowlisted file (calls .deploy()/.call()/finalizeCall()) carries a fundPathJustification', () => {
    const missingJustification = allowlist.entries.filter((e) => {
      if (!existsSync(join(PACKAGE_ROOT, e.file))) return false; // caught by the existence check below
      const contents = readFileSync(join(PACKAGE_ROOT, e.file), 'utf-8');
      return FUND_PATH_PATTERN.test(contents) && !e.fundPathJustification?.trim();
    });
    expect(
      missingJustification.map((e) => e.file),
      'these allowlisted files call .deploy()/.call()/finalizeCall() but have no fundPathJustification — ' +
      'the plan requires fund-path deploy/call tests not be allowlisted without one; add a specific ' +
      'fundPathJustification explaining why the always-ack-using test does not launder an unverified tx, ' +
      'or fix the test to run under default validation instead',
    ).toEqual([]);
  });

  it('every allowlist entry has a non-empty reason and a valid category', () => {
    const bad = allowlist.entries.filter(
      (e) =>
        typeof e.file !== 'string' ||
        e.file.trim() === '' ||
        typeof e.reason !== 'string' ||
        e.reason.trim() === '' ||
        !['structure-only', 'negative-api', 'fixture-shape', 'pending-a3'].includes(e.category),
    );
    expect(bad, `malformed allowlist entries: ${JSON.stringify(bad, null, 2)}`).toEqual([]);
  });

  it('every allowlist entry names a file that exists', () => {
    const missing = allowlist.entries.filter((e) => !existsSync(join(PACKAGE_ROOT, e.file)));
    expect(
      missing.map((e) => e.file),
      'always-ack-allowlist.json has entries pointing at files that no longer exist; remove them',
    ).toEqual([]);
  });

  it('no allowlist entry is stale (the file still uses an always-ack escape hatch)', () => {
    const stale = allowlist.entries.filter((e) => existsSync(join(PACKAGE_ROOT, e.file)) && !actualUsage.has(e.file));
    expect(
      stale.map((e) => e.file),
      'always-ack-allowlist.json has entries for files that no longer use ' +
      'disableBroadcastValidation / newAlwaysAckMockProvider / ' +
      'validateBroadcasts: false / enableBroadcastValidation(false) — remove the entry ' +
      '(the allowlist must only shrink, never carry dead entries)',
    ).toEqual([]);
  });

  it('every file using an always-ack escape hatch is on the allowlist', () => {
    const unlisted = [...actualUsage].filter((f) => !listedFiles.has(f)).sort();
    expect(
      unlisted,
      `Unlisted always-ack usage found:\n${unlisted.map((f) => `  - ${f}`).join('\n')}\n` +
      'Add an entry to always-ack-allowlist.json with a file, reason, and category ' +
      '(structure-only | negative-api | fixture-shape | pending-a3), or fix the test ' +
      'to run under default broadcast validation instead.',
    ).toEqual([]);
  });
});
