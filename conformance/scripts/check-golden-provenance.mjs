#!/usr/bin/env node
// -----------------------------------------------------------------------------
// GOLDEN-REGENERATION INTEGRITY GATE  (post-mortem remediation #3, issue #122)
// -----------------------------------------------------------------------------
//
// Problem: conformance goldens/vectors (expected-script.hex, expected-ir.json,
// runtime-vectors/*.json, sdk-output/**/expected-locking.hex, analyzer reports,
// source-map goldens, decompiler baselines) are SELF-PRODUCED by the very
// implementation under test (`pnpm run update-golden`). Nothing stops a PR from
// silently regenerating a golden to match a buggy new compiler output — the
// suite then validates the corrupt bytes against itself and ships green.
//
// This gate detects any change to a golden/vector file in the PR's changed set
// (three-dot diff against the merge-base) and FAILS unless that change carries
// an INDEPENDENT provenance justification. Two ways to satisfy it, per golden:
//
//   (A) Scoped cross-check co-change  — for a fixture golden
//       `conformance/tests/<fixture>/expected-{script.hex,ir.json}`, the same
//       PR also modifies that fixture's independent execution oracle
//       `conformance/witnesses/<fixture>.json`. The differential-execution
//       oracle (witnesses/differential.test.ts) re-runs those spends through a
//       second engine, so the fixture's bytes get an independent check.
//
//   (B) Allowlist entry  — an entry in
//       `conformance/golden-provenance-allowlist.json` pinning the golden's
//       path to a sha256 of its NEW content, with a `verified-against`
//       (official-KAT | second-implementation | differential-oracle |
//       intentional-spec-change), a `reason`, and a `reviewer` sign-off. The
//       sha256 pin is content-addressed, so the entry self-invalidates on any
//       later, different regeneration of the same file.
//
// The gate is intentionally a *provenance* gate, not a correctness proof: it
// cannot itself prove a golden is right, but it forces every golden change to
// surface an independent cross-check or an explicit, reviewable, content-pinned
// sign-off — which is exactly what silent self-regeneration lacks.
//
// Dependency-light by design: Node built-ins + `git` only. No npm install.
//
// Usage:
//   node conformance/scripts/check-golden-provenance.mjs [--base <ref>]
//       Auto-detect the changed set via `git diff --name-only --diff-filter=ACMRT <base>...HEAD`.
//       <base> defaults to $GOLDEN_GATE_BASE, else origin/main.
//   node conformance/scripts/check-golden-provenance.mjs --files a,b,c
//       Use an explicit comma-separated changed set (content read from --root).
//   node conformance/scripts/check-golden-provenance.mjs --files-from list.txt
//       Read the changed set from a newline-delimited file.
//   node conformance/scripts/check-golden-provenance.mjs --print-hashes
//       Print the sha256 of every changed golden (to fill in an allowlist entry).
//   node conformance/scripts/check-golden-provenance.mjs --self-test
//       Run the embedded both-directions verification and exit.
//   Flags: --root <dir> (repo root, default cwd), --json (machine output).
//
// Exit code: 0 = gate satisfied (or no golden changes); 1 = unjustified golden
// change(s); 2 = usage / internal error.
// -----------------------------------------------------------------------------

import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, existsSync, mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname, resolve } from 'node:path';

// --- Golden/vector file classification -------------------------------------
// Each matcher takes a repo-root-relative POSIX path and returns true if the
// file is a self-produced golden/vector guarded by this gate. Keep this list as
// the single source of truth; extend it when a new golden family is added.
const GOLDEN_MATCHERS = [
  // Conformance compiled-output goldens (the core issue-#122 risk surface).
  (p) => /^conformance\/tests\/[^/]+\/expected-script\.hex$/.test(p),
  (p) => /^conformance\/tests\/[^/]+\/expected-ir\.json$/.test(p),
  // Runtime KAT vectors (official known-answer test hashes).
  (p) => /^conformance\/runtime-vectors\/.*\.json$/.test(p),
  // Cross-SDK deployed-locking-script goldens.
  (p) => /^conformance\/sdk-output\/tests\/[^/]+\/expected-.*\.hex$/.test(p),
  // Static-analyzer report goldens.
  (p) => /^conformance\/analyzer\/[^/]+\/expected-analyzer-report\.json$/.test(p),
  // Source-map goldens (per-tier).
  (p) => /^conformance\/source-map\/[^/]+\/[^/]+\/expected-source-map\.json$/.test(p),
  // Decompiler baseline (self-produced coverage/idiom baseline).
  (p) => p === 'packages/decompiler/coverage-baseline.json',
];

const VALID_VERIFIED_AGAINST = new Set([
  'official-KAT',
  'second-implementation',
  'differential-oracle',
  'intentional-spec-change',
]);

const ALLOWLIST_REL = 'conformance/golden-provenance-allowlist.json';

function isGolden(relPath) {
  return GOLDEN_MATCHERS.some((m) => m(relPath));
}

// A fixture golden is `conformance/tests/<fixture>/expected-{script.hex,ir.json}`.
// Its scoped independent oracle is `conformance/witnesses/<fixture>.json`.
function fixtureWitnessFor(relPath) {
  const m = relPath.match(/^conformance\/tests\/([^/]+)\/expected-(?:script\.hex|ir\.json)$/);
  return m ? `conformance/witnesses/${m[1]}.json` : null;
}

function sha256OfFile(absPath) {
  const buf = readFileSync(absPath);
  return createHash('sha256').update(buf).digest('hex');
}

function loadAllowlist(root) {
  const abs = join(root, ALLOWLIST_REL);
  if (!existsSync(abs)) return { entries: [] };
  let parsed;
  try {
    parsed = JSON.parse(readFileSync(abs, 'utf8'));
  } catch (e) {
    throw new Error(`${ALLOWLIST_REL} is not valid JSON: ${e.message}`);
  }
  if (!parsed || !Array.isArray(parsed.entries)) {
    throw new Error(`${ALLOWLIST_REL} must have an "entries" array`);
  }
  return parsed;
}

// Validate a single allowlist entry's shape. Returns an array of problems.
function entryProblems(entry) {
  const problems = [];
  if (typeof entry.path !== 'string' || entry.path.length === 0) problems.push('missing "path"');
  if (typeof entry.sha256 !== 'string' || !/^[0-9a-f]{64}$/.test(entry.sha256 || '')) {
    problems.push('missing/invalid "sha256" (must be 64 hex chars)');
  }
  if (!VALID_VERIFIED_AGAINST.has(entry['verified-against'])) {
    problems.push(`"verified-against" must be one of ${[...VALID_VERIFIED_AGAINST].join(' | ')}`);
  }
  if (typeof entry.reason !== 'string' || entry.reason.trim().length < 8) {
    problems.push('missing "reason" (>= 8 chars explaining the independent cross-check)');
  }
  if (typeof entry.reviewer !== 'string' || entry.reviewer.trim().length === 0) {
    problems.push('missing "reviewer" sign-off marker');
  }
  return problems;
}

/**
 * Core gate logic — pure over its inputs so the self-test can call it directly.
 * @param {{ changedFiles: string[], root: string }} opts
 * @returns {{ goldenChanges: Array, justified: Array, unjustified: Array, badEntries: Array }}
 */
function checkProvenance({ changedFiles, root }) {
  const changedSet = new Set(changedFiles.map((f) => f.trim()).filter(Boolean));
  const allowlist = loadAllowlist(root);

  // Index allowlist entries by path, and pre-collect any malformed entries.
  const byPath = new Map();
  const badEntries = [];
  for (const entry of allowlist.entries) {
    const probs = entryProblems(entry);
    if (probs.length) {
      badEntries.push({ entry, problems: probs });
      continue; // malformed entries never justify anything
    }
    byPath.set(entry.path, entry);
  }

  const goldenChanges = [...changedSet].filter(isGolden).sort();
  const justified = [];
  const unjustified = [];

  for (const g of goldenChanges) {
    // Path (A): scoped cross-check — the fixture's own witness co-changed.
    const witness = fixtureWitnessFor(g);
    if (witness && changedSet.has(witness)) {
      justified.push({ path: g, via: 'cross-check', detail: `co-change of ${witness}` });
      continue;
    }

    // Path (B): allowlist entry pinned to this golden's NEW content hash.
    const entry = byPath.get(g);
    if (entry) {
      const abs = join(root, g);
      if (!existsSync(abs)) {
        // Renamed/removed in working tree but reported changed — treat as
        // unjustified with a clear message rather than crash.
        unjustified.push({ path: g, reason: `allowlisted but file not present at ${g}` });
        continue;
      }
      const actual = sha256OfFile(abs);
      if (actual === entry.sha256) {
        justified.push({
          path: g,
          via: 'allowlist',
          detail: `verified-against=${entry['verified-against']} reviewer=${entry.reviewer}`,
        });
      } else {
        unjustified.push({
          path: g,
          reason:
            `allowlist sha256 mismatch — entry pins ${entry.sha256.slice(0, 12)}… but current ` +
            `content hashes to ${actual.slice(0, 12)}…. The golden changed since it was ` +
            `signed off; update the entry's sha256 + reason for the NEW value.`,
        });
      }
      continue;
    }

    unjustified.push({ path: g, reason: 'no cross-check co-change and no allowlist entry' });
  }

  return { goldenChanges, justified, unjustified, badEntries };
}

// --- Changed-set discovery --------------------------------------------------
function gitChangedFiles(root, base) {
  // Three-dot: diff against the merge-base of <base> and HEAD = the PR's true
  // changed set (matches the repo's review convention). --diff-filter=ACMRT
  // excludes pure Deletions (removing a golden is not a regeneration risk).
  const range = `${base}...HEAD`;
  let out;
  try {
    out = execFileSync(
      'git',
      ['-C', root, 'diff', '--name-only', '--diff-filter=ACMRT', range],
      { encoding: 'utf8' },
    );
  } catch (e) {
    throw new Error(
      `git diff failed for range '${range}': ${e.message.split('\n')[0]}. ` +
        `Ensure the base ref is fetched (checkout with fetch-depth: 0).`,
    );
  }
  return out.split('\n').map((s) => s.trim()).filter(Boolean);
}

// --- Reporting --------------------------------------------------------------
function printHumanReport(res, { asError }) {
  const { goldenChanges, justified, unjustified, badEntries } = res;
  const log = asError ? console.error : console.log;

  if (badEntries.length) {
    log('');
    log('✗ Malformed entries in conformance/golden-provenance-allowlist.json:');
    for (const b of badEntries) {
      log(`    path=${b.entry.path ?? '(none)'} → ${b.problems.join('; ')}`);
    }
  }

  if (goldenChanges.length === 0) {
    console.log('✓ Golden-provenance gate: no golden/vector files changed — nothing to justify.');
    return;
  }

  console.log(`Golden-provenance gate: ${goldenChanges.length} golden/vector file(s) changed.`);
  for (const j of justified) {
    console.log(`  ✓ ${j.path}  [${j.via}: ${j.detail}]`);
  }
  if (unjustified.length === 0) return;

  console.error('');
  console.error(
    `✗ GOLDEN-REGENERATION INTEGRITY GATE FAILED — ${unjustified.length} golden change(s) ` +
      `lack an independent provenance justification:`,
  );
  console.error('');
  for (const u of unjustified) {
    console.error(`  ✗ ${u.path}`);
    console.error(`      ${u.reason}`);
  }
  console.error('');
  console.error('These files are self-produced by the implementation under test. A change to one');
  console.error('must be cross-checked by something OTHER than the compiler that produced it.');
  console.error('Satisfy the gate for EACH file above in ONE of two ways:');
  console.error('');
  console.error('  (A) Cross-check co-change (fixture goldens only):');
  console.error('      also modify that fixture\'s independent execution oracle');
  console.error('      conformance/witnesses/<fixture>.json — the differential oracle');
  console.error('      (witnesses/differential.test.ts) then re-runs its spends through a');
  console.error('      second engine.');
  console.error('');
  console.error('  (B) Allowlist entry (works for any golden):');
  console.error('      add an entry to conformance/golden-provenance-allowlist.json:');
  console.error('        {');
  console.error('          "path": "<the file above>",');
  console.error('          "sha256": "<run: node conformance/scripts/check-golden-provenance.mjs --print-hashes>",');
  console.error('          "verified-against": "official-KAT | second-implementation | differential-oracle | intentional-spec-change",');
  console.error('          "reason": "why the new bytes are correct + which independent oracle confirmed them",');
  console.error('          "reviewer": "gh:your-handle"');
  console.error('        }');
  console.error('');
  console.error('  Full design: conformance/README.md → "Golden-regeneration integrity gate".');
}

// --- CLI --------------------------------------------------------------------
function parseArgs(argv) {
  const args = { root: process.cwd(), base: process.env.GOLDEN_GATE_BASE || 'origin/main' };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--self-test') args.selfTest = true;
    else if (a === '--json') args.json = true;
    else if (a === '--print-hashes') args.printHashes = true;
    else if (a === '--base') args.base = argv[++i];
    else if (a === '--root') args.root = resolve(argv[++i]);
    else if (a === '--files') args.files = argv[++i].split(',');
    else if (a === '--files-from') args.filesFrom = argv[++i];
    else {
      console.error(`Unknown argument: ${a}`);
      process.exit(2);
    }
  }
  return args;
}

function resolveChangedFiles(args) {
  if (args.files) return args.files;
  if (args.filesFrom) {
    return readFileSync(args.filesFrom, 'utf8').split('\n').map((s) => s.trim()).filter(Boolean);
  }
  return gitChangedFiles(args.root, args.base);
}

function runCli(args) {
  const changedFiles = resolveChangedFiles(args);

  if (args.printHashes) {
    const goldens = changedFiles.filter(isGolden).sort();
    if (goldens.length === 0) {
      console.log('No golden/vector files in the changed set.');
      return 0;
    }
    console.log('sha256 of each changed golden (for a golden-provenance-allowlist.json entry):');
    for (const g of goldens) {
      const abs = join(args.root, g);
      const h = existsSync(abs) ? sha256OfFile(abs) : '(file not present)';
      console.log(`  ${h}  ${g}`);
    }
    return 0;
  }

  const res = checkProvenance({ changedFiles, root: args.root });

  if (args.json) {
    console.log(JSON.stringify(res, null, 2));
  } else {
    printHumanReport(res, { asError: res.unjustified.length > 0 });
  }

  if (res.badEntries.length > 0) return 1; // malformed allowlist is a hard fail
  return res.unjustified.length > 0 ? 1 : 0;
}

// --- Self-test (embedded both-directions verification) ----------------------
function selfTest() {
  const results = [];
  const tmp = mkdtempSync(join(tmpdir(), 'golden-gate-selftest-'));
  const write = (rel, content) => {
    const abs = join(tmp, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content);
    return abs;
  };
  const writeAllowlist = (entries) =>
    write(ALLOWLIST_REL, JSON.stringify({ entries }, null, 2));

  const goldenRel = 'conformance/tests/demo/expected-script.hex';
  const goldenBody = '52935387\n';
  const goldenAbs = write(goldenRel, goldenBody);
  const goldenHash = sha256OfFile(goldenAbs);
  const nonGoldenRel = 'packages/runar-compiler/src/passes/05-stack-lower.ts';
  write(nonGoldenRel, 'export const x = 1;\n');
  write('conformance/witnesses/demo.json', '{"fixture":"demo","spends":[]}\n');

  const record = (name, expectFail, actualFail, extra) => {
    const pass = expectFail === actualFail;
    results.push({ name, expected: expectFail ? 'REJECT' : 'PASS', got: actualFail ? 'REJECT' : 'PASS', ok: pass, extra });
    return pass;
  };

  // (a) golden change WITHOUT justification → REJECT
  writeAllowlist([]);
  {
    const r = checkProvenance({ changedFiles: [goldenRel], root: tmp });
    record('a) golden change, no justification', true, r.unjustified.length > 0,
      r.unjustified.map((u) => u.path).join(','));
  }

  // (b1) same golden change WITH a valid, content-pinned allowlist entry → PASS
  writeAllowlist([
    {
      path: goldenRel,
      sha256: goldenHash,
      'verified-against': 'differential-oracle',
      reason: 'demo: bytes re-derived and confirmed by the differential oracle',
      reviewer: 'gh:selftest',
    },
  ]);
  {
    const r = checkProvenance({ changedFiles: [goldenRel], root: tmp });
    record('b1) golden change, valid allowlist entry', false, r.unjustified.length > 0,
      `justified via ${r.justified.map((j) => j.via).join(',')}`);
  }

  // (b1-neg) allowlist entry with a STALE sha256 (wrong value) → REJECT
  writeAllowlist([
    {
      path: goldenRel,
      sha256: 'f'.repeat(64),
      'verified-against': 'differential-oracle',
      reason: 'stale pin — authorizes a different value than the current bytes',
      reviewer: 'gh:selftest',
    },
  ]);
  {
    const r = checkProvenance({ changedFiles: [goldenRel], root: tmp });
    record('b1-neg) golden change, stale allowlist sha256', true, r.unjustified.length > 0,
      r.unjustified.map((u) => u.reason.split(' —')[0]).join(','));
  }

  // (b2) golden change WITH fixture-witness cross-check co-change → PASS
  writeAllowlist([]);
  {
    const r = checkProvenance({
      changedFiles: [goldenRel, 'conformance/witnesses/demo.json'],
      root: tmp,
    });
    record('b2) golden change, witness cross-check co-change', false, r.unjustified.length > 0,
      `justified via ${r.justified.map((j) => j.via).join(',')}`);
  }

  // (c) non-golden change only → NO-OP (PASS, zero goldens detected)
  writeAllowlist([]);
  {
    const r = checkProvenance({ changedFiles: [nonGoldenRel], root: tmp });
    const noGoldens = r.goldenChanges.length === 0;
    record('c) non-golden change only (no-op)', false, r.unjustified.length > 0,
      `goldenChanges=${r.goldenChanges.length}`);
    if (!noGoldens) results[results.length - 1].ok = false;
  }

  rmSync(tmp, { recursive: true, force: true });

  console.log('Golden-provenance gate — self-test (both directions):');
  console.log('');
  let allOk = true;
  for (const r of results) {
    const mark = r.ok ? '✓' : '✗';
    console.log(`  ${mark}  ${r.name}`);
    console.log(`         expected=${r.expected}  got=${r.got}   (${r.extra})`);
    if (!r.ok) allOk = false;
  }
  console.log('');
  console.log(allOk ? '✓ SELF-TEST PASSED (all scenarios behaved as expected)' : '✗ SELF-TEST FAILED');
  return allOk ? 0 : 1;
}

// --- main -------------------------------------------------------------------
function main() {
  const args = parseArgs(process.argv.slice(2));
  try {
    if (args.selfTest) process.exit(selfTest());
    process.exit(runCli(args));
  } catch (e) {
    console.error(`golden-provenance gate: internal error: ${e.message}`);
    process.exit(2);
  }
}

main();
