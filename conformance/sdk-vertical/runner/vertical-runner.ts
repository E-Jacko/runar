// ---------------------------------------------------------------------------
// conformance/sdk-vertical/runner/vertical-runner.ts
// ---------------------------------------------------------------------------
//
// The compiler <-> SDK vertical gate (remediation plan Phase C3 + C4).
//
// For every matrix case, four checks — the first three need no SDK at all,
// which is what makes the fourth meaningful:
//
//   [1] ARTIFACT SELF-CLAIMS   walk the compiled template and confirm every
//                              constructorSlots[].byteOffset is a real 1-byte
//                              OP_0 at an opcode boundary, and that
//                              codeSeparatorIndices == the real
//                              OP_CODESEPARATOR positions.
//   [2] INDEPENDENT SPLICE     re-derive the deployed code part from the
//                              artifact + args using reference/ (which imports
//                              nothing from packages/**), and read the spliced
//                              values back out by disassembly.
//   [3] GOLDEN                 that derivation must equal the checked-in
//                              expected-code-part.hex / expected-vertical.json,
//                              so changing the harness alone cannot move the
//                              target without a reviewable golden diff.
//   [4] SEVEN SDKs             every tier's deployed locking script must carry
//                              the derived code part as its prefix (stateless:
//                              exactly equal), and must agree with the pinned
//                              expected-locking.hex.
//
// Usage:
//   tsx sdk-vertical/runner/vertical-runner.ts [--filter <substr>]
//                                              [--tiers ts,go,...]
//                                              [--no-sdk] [--update-golden]
//                                              [--cases-dir <dir>]
// ---------------------------------------------------------------------------

import { existsSync, readFileSync, readdirSync, writeFileSync } from 'fs';
import { dirname, join, resolve } from 'path';
import { fileURLToPath, pathToFileURL } from 'url';

import { deriveVertical, type RefArtifact } from '../reference/derive.js';
import type { TypedArg } from '../reference/encode.js';
import { buildSdkTools, runSdkTool, type SdkResult } from './sdk-tools.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const VERTICAL_DIR = resolve(join(__dirname, '..'));

interface CaseInput {
  artifact: RefArtifact;
  constructorArgs: TypedArg[];
}

export interface CaseReport {
  name: string;
  failures: string[];
  /** Divergences that reproduced a known-divergences.json entry. */
  known: string[];
  sdkResults: SdkResult[];
}

/** The exact byte a listed divergence must reproduce: `golden` is the byte
 *  the independent derivation says belongs at `byte`, `tier` is the byte the
 *  divergent tier actually produces there. Both are lowercase 2-hex-char. */
interface ExpectedFirstDiff {
  byte: number;
  golden: string;
  tier: string;
}

interface KnownDivergence {
  id: string;
  tier: string;
  cases: string[];
  /** REQUIRED per listed case — see loader validation below (plan P1-3). */
  expectedFirstDiff: Record<string, ExpectedFirstDiff>;
  summary: string;
}

const KNOWN_DIVERGENCES: KnownDivergence[] = (
  JSON.parse(readFileSync(join(VERTICAL_DIR, 'known-divergences.json'), 'utf-8')) as {
    divergences: KnownDivergence[];
  }
).divergences;

// Loader validation: an entry that lists a case with no expectedFirstDiff
// record is exactly the P1-3 over-acceptance bug — it would match ANY
// divergence on that (tier, case) pair, including an unrelated one (a
// truncated script, an empty result that still exits 0). Fail fast at load
// time rather than silently under-checking every run.
for (const d of KNOWN_DIVERGENCES) {
  for (const c of d.cases) {
    if (!d.expectedFirstDiff?.[c]) {
      throw new Error(
        `known-divergences.json: entry '${d.id}' (tier '${d.tier}') lists case '${c}' but has no ` +
          `expectedFirstDiff record for it — every listed case needs one (see README.md).`,
      );
    }
  }
}

/** Entry ids that actually reproduced this run — used to fail stale entries. */
const firedDivergences = new Set<string>();

/** Locate the first differing byte between two hex strings, structurally
 *  (for comparison against `expectedFirstDiff`). `undefined` when the two
 *  are identical for their common length and differ only by trailing length
 *  (truncation/empty-result) — which can never match a recorded byte-level
 *  divergence, by design (plan P1-3: a truncated script must NOT report as
 *  KNOWN just because SOME divergence is tracked for that tier/case). */
function firstDiffStruct(golden: string, actual: string): ExpectedFirstDiff | undefined {
  const n = Math.min(golden.length, actual.length);
  for (let i = 0; i < n; i += 2) {
    const g = golden.slice(i, i + 2);
    const a = actual.slice(i, i + 2);
    if (g !== a) return { byte: i / 2, golden: g, tier: a };
  }
  return undefined;
}

/**
 * A listed (tier, case) pair is KNOWN only when the divergence reproduces the
 * EXACT recorded byte — same offset, same golden byte, same tier byte. Any
 * other divergence on that pair (a different byte, a length-only truncation)
 * is a NEW, unclassified divergence and fails the suite outright.
 */
function knownFor(caseName: string, tier: string, actual: ExpectedFirstDiff | undefined): KnownDivergence | undefined {
  const hit = KNOWN_DIVERGENCES.find((d) => d.tier === tier && d.cases.includes(caseName));
  if (!hit) return undefined;
  const want = hit.expectedFirstDiff[caseName]!;
  if (!actual || actual.byte !== want.byte || actual.golden !== want.golden || actual.tier !== want.tier) {
    return undefined;
  }
  firedDivergences.add(hit.id);
  return hit;
}

function readJson<T>(path: string): T {
  return JSON.parse(readFileSync(path, 'utf-8')) as T;
}

/** Locate the first differing byte, for a diagnosable failure message. */
function firstDiff(a: string, b: string): string {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 2) {
    if (a.slice(i, i + 2) !== b.slice(i, i + 2)) {
      return `first difference at byte ${i / 2}: ${a.slice(i, i + 2)} vs ${b.slice(i, i + 2)}`;
    }
  }
  return `identical for ${n / 2} bytes, then lengths differ (${a.length / 2} vs ${b.length / 2})`;
}

export function runCase(
  caseDir: string,
  opts: { runSdks: boolean; updateGolden: boolean; tiers?: Set<string> },
): CaseReport {
  const name = caseDir.split('/').pop()!;
  const failures: string[] = [];
  const input = readJson<CaseInput>(join(caseDir, 'input.json'));

  // --- [1] + [2] artifact self-claims and independent splice ---------------
  const derived = deriveVertical(input.artifact, input.constructorArgs);
  for (const v of derived.violations) failures.push(`[vertical] ${v.code}: ${v.message}`);

  // --- [3] goldens ---------------------------------------------------------
  const codeGoldenPath = join(caseDir, 'expected-code-part.hex');
  if (!existsSync(codeGoldenPath)) {
    failures.push('[golden] expected-code-part.hex is missing — run the generator');
  } else {
    const golden = readFileSync(codeGoldenPath, 'utf-8').trim().toLowerCase();
    if (golden !== derived.codePartHex) {
      failures.push(
        `[golden] independently-derived code part does not match expected-code-part.hex ` +
          `(${firstDiff(golden, derived.codePartHex)})`,
      );
    }
  }

  const verticalGoldenPath = join(caseDir, 'expected-vertical.json');
  if (!existsSync(verticalGoldenPath)) {
    failures.push('[golden] expected-vertical.json is missing — run the generator');
  } else {
    const g = readJson<Record<string, unknown>>(verticalGoldenPath);
    const actual = {
      codePartByteLength: derived.codePartByteLength,
      slots: derived.slots,
      templateCodeSeparators: derived.templateCodeSeparators,
      deployedCodeSeparators: derived.deployedCodeSeparators,
      codeSepSlotValues: derived.codeSepSlotValues,
    };
    for (const key of Object.keys(actual) as Array<keyof typeof actual>) {
      const want = JSON.stringify(g[key]);
      const got = JSON.stringify(actual[key]);
      if (want !== got) {
        failures.push(`[golden] expected-vertical.json '${key}' mismatch:\n      pinned: ${want}\n      actual: ${got}`);
      }
    }
  }

  // --- [4] seven SDKs ------------------------------------------------------
  const sdkResults: SdkResult[] = [];
  const known: string[] = [];
  if (opts.runSdks) {
    const inputPath = join(caseDir, 'input.json');
    const stateful = (input.artifact.stateFields ?? []).length > 0;
    /** Tiers whose bytes are excluded from agreement checks this case because
     *  known-divergences.json already tracks them. */
    const divergent = new Set<string>();

    for (const tool of ALL_TOOLS) {
      if (opts.tiers && !opts.tiers.has(tool.name)) continue;
      const r = runSdkTool(tool, inputPath);
      sdkResults.push(r);
      if (!r.success) {
        failures.push(`[tier:${r.sdk}] driver failed: ${r.error}`);
        continue;
      }

      // The deployed locking script is codePart [+ inscription] [+ OP_RETURN
      // state]. The vertical pin owns the code part; the state tail is the C2
      // family's surface (conformance/sdk-output/tests/stateful-bytestring-op-n-state).
      if (!r.hex.startsWith(derived.codePartHex)) {
        const actualDiff = firstDiffStruct(derived.codePartHex, r.hex);
        const hit = knownFor(name, r.sdk, actualDiff);
        const detail =
          `[tier:${r.sdk}] deployed locking script does not begin with the independently-derived ` +
          `code part (${firstDiff(derived.codePartHex, r.hex)})`;
        if (hit) {
          divergent.add(r.sdk);
          known.push(`${detail}\n      KNOWN ${hit.id}: ${hit.summary}`);
        } else {
          failures.push(detail);
        }
        continue;
      }

      const tail = r.hex.slice(derived.codePartHex.length);
      if (!stateful && tail.length > 0) {
        failures.push(`[tier:${r.sdk}] stateless contract emitted ${tail.length / 2} trailing bytes after the code part`);
      }
      if (stateful && tail.length > 0 && !tail.startsWith('6a')) {
        failures.push(`[tier:${r.sdk}] state tail does not begin with OP_RETURN (0x6a): ${tail.slice(0, 16)}`);
      }
    }

    const ok = sdkResults.filter((r) => r.success && !divergent.has(r.sdk));
    for (let i = 1; i < ok.length; i++) {
      if (ok[i]!.hex !== ok[0]!.hex) {
        failures.push(`[horizontal] ${ok[0]!.sdk} and ${ok[i]!.sdk} disagree (${firstDiff(ok[0]!.hex, ok[i]!.hex)})`);
      }
    }

    const lockingGoldenPath = join(caseDir, 'expected-locking.hex');
    if (opts.updateGolden) {
      if (ok.length > 0 && failures.length === 0) writeFileSync(lockingGoldenPath, ok[0]!.hex + '\n');
    } else if (!existsSync(lockingGoldenPath)) {
      failures.push('[golden] expected-locking.hex is missing — run with --update-golden');
    } else {
      const golden = readFileSync(lockingGoldenPath, 'utf-8').trim().toLowerCase();
      if (!golden.startsWith(derived.codePartHex)) {
        failures.push(
          `[golden] expected-locking.hex does not begin with the independently-derived code part ` +
            `(${firstDiff(derived.codePartHex, golden)})`,
        );
      }
      for (const r of ok) {
        if (r.hex !== golden) failures.push(`[tier:${r.sdk}] does not match expected-locking.hex (${firstDiff(golden, r.hex)})`);
      }
    }
  }

  return { name, failures, known, sdkResults };
}

const ALL_TOOLS = buildSdkTools();

function main(): void {
  const argv = process.argv.slice(2);
  let filter: string | undefined;
  let runSdks = true;
  let updateGolden = false;
  let tiers: Set<string> | undefined;
  let casesDir = join(VERTICAL_DIR, 'cases');

  for (let i = 0; i < argv.length; i++) {
    switch (argv[i]) {
      case '--filter': filter = argv[++i]; break;
      case '--no-sdk': runSdks = false; break;
      case '--update-golden': updateGolden = true; break;
      case '--tiers': tiers = new Set(argv[++i]!.split(',').map((s) => s.trim())); break;
      case '--cases-dir': casesDir = resolve(argv[++i]!); break;
      default: throw new Error(`unknown argument '${argv[i]}'`);
    }
  }

  if (tiers) {
    const knownTiers = new Set(ALL_TOOLS.map((t) => t.name));
    for (const t of tiers) {
      if (!knownTiers.has(t)) {
        throw new Error(`unrecognized --tiers value '${t}' (known tiers: ${[...knownTiers].sort().join(', ')})`);
      }
    }
  }

  let dirs = readdirSync(casesDir, { withFileTypes: true })
    .filter((d) => d.isDirectory() && existsSync(join(casesDir, d.name, 'input.json')))
    .map((d) => join(casesDir, d.name))
    .sort();
  if (filter) {
    dirs = dirs.filter((d) => d.includes(filter!));
    // A typo'd filter that matches nothing used to silently run zero cases and
    // exit 0 — a green CI run for a gate that checked nothing (plan P2).
    if (dirs.length === 0) {
      throw new Error(`--filter '${filter}' matched no cases under ${casesDir}`);
    }
  }

  const tierLabel = runSdks ? (tiers ? [...tiers].join(',') : `${ALL_TOOLS.length} tiers`) : 'no SDK tiers';
  console.log(`Vertical compiler<->SDK pins: ${dirs.length} cases x (${tierLabel})\n`);

  let failed = 0;
  const tierStatus = new Map<string, { ok: number; fail: number; lastError?: string }>();

  for (const dir of dirs) {
    const rep = runCase(dir, { runSdks, updateGolden, tiers });
    for (const r of rep.sdkResults) {
      const s = tierStatus.get(r.sdk) ?? { ok: 0, fail: 0 };
      if (r.success) s.ok++;
      else {
        s.fail++;
        s.lastError = r.error;
      }
      tierStatus.set(r.sdk, s);
    }
    if (rep.failures.length === 0) {
      console.log(`[+] ${rep.name}${rep.known.length > 0 ? ` (${rep.known.length} known divergence)` : ''}`);
    } else {
      failed++;
      console.log(`[x] ${rep.name}`);
      for (const f of rep.failures) console.log(`    ${f}`);
    }
    for (const k of rep.known) console.log(`    ${k}`);
  }

  // Stale-entry gate: an entry that no longer reproduces means the bug was
  // fixed and the entry must be deleted in the same commit. Only meaningful
  // over a full, unfiltered, all-tier run.
  const fullRun = !filter && !tiers && runSdks;
  if (fullRun) {
    const stale = KNOWN_DIVERGENCES.filter((d) => !firedDivergences.has(d.id));
    if (stale.length > 0) {
      failed++;
      console.log(`\n[x] stale known-divergences.json entries (no longer reproduce — delete them):`);
      for (const d of stale) console.log(`    ${d.id} (${d.tier}): ${d.summary}`);
    }
  }

  if (tierStatus.size > 0) {
    console.log('\nPer-tier driver status:');
    for (const [tier, s] of [...tierStatus].sort()) {
      const line = `  ${tier.padEnd(11)} ok=${s.ok} fail=${s.fail}`;
      console.log(s.fail > 0 ? `${line}\n      last error: ${(s.lastError ?? '').split('\n')[0]}` : line);
    }
  }

  console.log(`\n${dirs.length - failed}/${dirs.length} cases passed.`);
  process.exit(failed > 0 ? 1 : 0);
}

// Run the suite only when invoked as a program. `vertical-pins.test.ts`
// imports `runCase` from here and must not trigger the CLI.
if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) {
  main();
}
