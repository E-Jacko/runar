/**
 * Wire-primitive register gate — reviewer point #4 / TG-004 / P3 / plan Phase C0.
 *
 * `deserialize(serialize(x)) === x` passes for ANY self-consistent framing,
 * including a wrong one. That is exactly how the 2026-08 state-section bug
 * shipped in all seven SDKs at once: #110 taught the SDKs MINIMALDATA and none
 * of the seven compilers, every round-trip stayed green, every cross-SDK
 * comparison stayed green (all seven moved together), and ZERO goldens moved —
 * while contracts carrying a 1-byte 0x01..0x10 ByteString state value became
 * permanently unspendable.
 *
 * So `wire-primitives.json` is a register: for every fund-critical primitive
 * whose BYTES cross a boundary, the ABSOLUTE pin that proves those bytes —
 * a pin against the OTHER implementation of the format, never against the
 * primitive's own inverse. A row is either backed by such a pin or it is an
 * honest, loud `UNCOVERED` with a dated close plan. There is no third state,
 * and a row pointed at a round-trip test to make this gate green would defeat
 * the entire item.
 *
 * Built in the style of `construct-ledger.test.ts` and
 * `witnesses/coverage-claims.test.ts`: claims are MACHINE-CHECKED, never
 * trusted as prose. Free-text `description` / `note` / `residual` are for
 * humans; the paths are the evidence, and they must exist.
 *
 * Six gates, one `it` each so a failure names the specific broken invariant:
 *
 *   1. absolutePins XOR UNCOVERED. A row whose only evidence sits in
 *      `roundTripSmokeTests` FAILS — that is the whole point of the file.
 *   2. every path in absolutePins / roundTripSmokeTests / producedBy /
 *      consumedBy exists on disk.
 *   3. no `absolutePins` path is a known round-trip test (denylist below), and
 *      no path appears in BOTH `absolutePins` and `roundTripSmokeTests` for the
 *      same row — reclassifying a file by listing it twice is not allowed.
 *   4. the REQUIRED_PRIMITIVES set below is hard-coded IN THIS FILE, so a new
 *      fund-critical wire primitive cannot be added without a row.
 *   5. ids are unique; `kind` comes from a closed enum, so a typo cannot invent
 *      an unreviewed evidence class.
 *   6. DENYLIST LIVENESS. Every denylisted path must still exist, and this
 *      denylist must remain a SUPERSET of the one declared in
 *      `construct-ledger.test.ts`. A rename must not silently turn the denylist
 *      into a no-op, and the two gates must not drift into two different
 *      opinions about what counts as evidence — the same failure mode
 *      `scripts/__tests__/wire-format-pr-audit.test.ts` guards for its globs.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');
const REGISTER_FILE = 'wire-primitives.json';
const REGISTER_PATH = join(__dirname, REGISTER_FILE);
const SIBLING_LEDGER_TEST = join(__dirname, 'construct-ledger.test.ts');

interface AbsolutePin {
  kind: string;
  path: string;
  note?: string;
}
interface RegisterRow {
  id?: unknown;
  description?: unknown;
  producedBy?: unknown;
  consumedBy?: unknown;
  absolutePins?: unknown;
  roundTripSmokeTests?: unknown;
  residual?: unknown;
  status?: unknown;
  issue?: unknown;
}

/**
 * Closed enum for `absolutePins[].kind`. A value outside this set is a typo,
 * not a new evidence class. Ordered strongest-first:
 *
 *   spend-execution   — the bytes are EXECUTED on @bsv/sdk's production `Spend`
 *                       (clean-stack, push-only unlocking, minimal-push) or
 *                       broadcast to a node. The grader is consensus.
 *   vertical-pin      — crosses compiler<->SDK: what an SDK DOES with an
 *                       artifact vs what the compiler DECLARED, or vs an
 *                       independent re-derivation of the encoding spec.
 *   cross-tier-golden — frozen bytes two or more INDEPENDENT implementations
 *                       must reproduce.
 *   kat               — expected bytes as literals, derived from the spec /
 *                       consensus rule first. Absolute but tier-local.
 */
const KINDS = new Set(['spend-execution', 'vertical-pin', 'cross-tier-golden', 'kat']);

/**
 * The fund-critical wire-primitive set, hard-coded HERE rather than derived
 * from the register — deriving it from the register would make the gate
 * vacuous (a deleted row would delete its own requirement). Adding an id here
 * is how a new wire primitive is declared; CI stays red until the row exists
 * with real evidence or an honest `UNCOVERED`.
 */
const REQUIRED_PRIMITIVES = [
  // --- the locking script the SDKs write and the compiler reads back --------
  'state-section-framing',
  'constructor-slot-splicing',
  'codeseparator-index',
  // --- the unlocking script the interpreter executes ------------------------
  'unlocking-encodeArg-minimaldata',
  // --- bytes that cross a tier boundary off-chain ---------------------------
  'bip143-preimage-layout',
  'signed-envelope-bytes',
  'canonicalJson',
];

/**
 * Files that ONLY prove an implementation is its own inverse — verified by
 * READING each one, not inferred from the filename.
 *
 * This list is a deliberate SUPERSET of the `ROUND_TRIP_ONLY_PATHS` declared in
 * `construct-ledger.test.ts` (asserted below, so the sibling gate cannot add an
 * entry this one does not know about). The extra entry is the Java analogue of
 * the six per-tier `c9_s1_minimaldata_roundtrip` siblings:
 *
 *   - `MinimalDataRoundTripTest.java` — its own header says "the MINIMALDATA
 *     push-data codec must ROUND-TRIP"; every assertion is
 *     `decode(encode(payload)) === payload` over the C9/S1 value classes, plus
 *     a constructor-slot restore of the same shape. No expected bytes anywhere.
 *     It is the seventh tier of a family whose other six are already denylisted
 *     in construct-ledger.test.ts; its absence there is reported, not patched
 *     from here.
 *
 * A primitive backed ONLY by one of these has no coverage: a round-trip cannot
 * detect a change that moves encode and decode together, which is precisely the
 * shape of the OP_N state-framing bug.
 */
const ROUND_TRIP_ONLY_PATHS = new Set([
  'packages/runar-sdk/src/__tests__/state.test.ts',
  'packages/runar-sdk/src/__tests__/ctor-bytestring-minimaldata-roundtrip.test.ts',
  'packages/runar-go/sdk_c9_s1_minimaldata_roundtrip_test.go',
  'packages/runar-rs/tests/c9_s1_minimaldata_roundtrip.rs',
  'packages/runar-py/tests/test_c9_s1_minimaldata_roundtrip.py',
  'packages/runar-zig/src/sdk_c9_s1_minimaldata_roundtrip_test.zig',
  'packages/runar-rb/spec/sdk/c9_s1_minimaldata_roundtrip_spec.rb',
  'packages/runar-java/src/test/java/runar/lang/sdk/MinimalDataRoundTripTest.java',
]);

function loadRegister(): RegisterRow[] {
  const doc = JSON.parse(readFileSync(REGISTER_PATH, 'utf-8'));
  return doc.primitives as RegisterRow[];
}

/** `absolutePins` entries well-formed enough to have a path checked. */
function pinsOf(row: RegisterRow): AbsolutePin[] {
  return Array.isArray(row.absolutePins) ? (row.absolutePins as AbsolutePin[]) : [];
}

function stringsOf(row: RegisterRow, field: 'producedBy' | 'consumedBy' | 'roundTripSmokeTests'): string[] {
  const v = row[field];
  return Array.isArray(v) ? (v as unknown[]).filter((x): x is string => typeof x === 'string') : [];
}

/**
 * The denylist literally declared in `construct-ledger.test.ts`, read out of
 * its SOURCE. Importing the module would execute its `describe` blocks, and
 * the constant is module-local, so the source is the only honest handle. If
 * the sibling's declaration form changes so this finds nothing, the superset
 * assertion below fails loudly rather than passing vacuously.
 */
function siblingDenylist(): string[] {
  const src = readFileSync(SIBLING_LEDGER_TEST, 'utf-8');
  const block = /const\s+ROUND_TRIP_ONLY_PATHS\s*=\s*new\s+Set\(\[([\s\S]*?)\]\)/.exec(src);
  if (block === null) return [];
  return [...block[1].matchAll(/['"]([^'"]+)['"]/g)].map((m) => m[1]);
}

describe('wire-primitive register — every fund-critical encoding has an ABSOLUTE pin', () => {
  it('every row has at least one absolutePin, or is an honest UNCOVERED — round-trip evidence is never enough', () => {
    const failures: string[] = [];
    for (const row of loadRegister()) {
      const id = String(row.id);
      const pinned = Array.isArray(row.absolutePins) && row.absolutePins.length > 0;
      const uncovered = row.status === 'UNCOVERED';
      const smoke = stringsOf(row, 'roundTripSmokeTests');

      if (pinned && uncovered) {
        failures.push(
          `${id}: has BOTH a non-empty absolutePins and status:"UNCOVERED" — an UNCOVERED row must carry no absolute pin, or drop the status`,
        );
      }
      if (!pinned && !uncovered) {
        failures.push(
          `${id}: has no absolutePins and no status:"UNCOVERED"` +
            (smoke.length > 0
              ? ` — its only evidence is ${smoke.length} round-trip smoke test(s). deserialize(serialize(x)) === x holds for a WRONG framing too; that is how the OP_N state-section bug shipped in seven SDKs. Cite a pin against the other implementation of the format, or mark the row UNCOVERED with a close plan.`
              : ` — an empty cell must be declared, not left blank`),
        );
      }
      if (uncovered && (typeof row.issue !== 'string' || row.issue.trim().length === 0)) {
        failures.push(
          `${id}: status:"UNCOVERED" requires a non-empty "issue" (a tracking ref or a dated close plan)`,
        );
      }
      if (!uncovered && row.issue !== undefined) {
        failures.push(`${id}: has an "issue" but is not UNCOVERED — put the note in absolutePins[].note or "residual"`);
      }
    }
    expect(failures, `rows without an absolute pin:\n${failures.join('\n')}`).toEqual([]);
  });

  it('every declared path exists on disk', () => {
    const failures: string[] = [];
    for (const row of loadRegister()) {
      const id = String(row.id);
      const claims: Array<{ field: string; path: unknown }> = [
        ...pinsOf(row).map((p) => ({ field: 'absolutePins', path: p?.path })),
        ...stringsOf(row, 'roundTripSmokeTests').map((p) => ({ field: 'roundTripSmokeTests', path: p })),
        ...stringsOf(row, 'producedBy').map((p) => ({ field: 'producedBy', path: p })),
        ...stringsOf(row, 'consumedBy').map((p) => ({ field: 'consumedBy', path: p })),
      ];
      for (const { field, path } of claims) {
        if (typeof path !== 'string' || path.trim().length === 0) {
          failures.push(`${id}: ${field} entry with a missing/empty path: ${JSON.stringify(path)}`);
          continue;
        }
        if (path.startsWith('/')) {
          failures.push(`${id}: ${field} path "${path}" must be repo-relative, not absolute`);
          continue;
        }
        if (!existsSync(join(REPO_ROOT, path))) {
          failures.push(
            `${id}: ${field} names ${path} — that path does not exist. Either the evidence was deleted/renamed (fix the register or restore it) or the claim was never true.`,
          );
        }
      }
      // A row must also declare BOTH sides of the boundary; a primitive with no
      // named producer or no named consumer is not a wire primitive.
      for (const field of ['producedBy', 'consumedBy'] as const) {
        if (stringsOf(row, field).length === 0) {
          failures.push(`${id}: "${field}" is missing or empty — name the implementation(s) on that side of the boundary`);
        }
      }
    }
    expect(failures, `dangling or incomplete register claims:\n${failures.join('\n')}`).toEqual([]);
  });

  it('no absolutePin is a known round-trip test', () => {
    const failures: string[] = [];
    for (const row of loadRegister()) {
      for (const pin of pinsOf(row)) {
        if (typeof pin?.path === 'string' && ROUND_TRIP_ONLY_PATHS.has(pin.path)) {
          failures.push(
            `${String(row.id)}: cites ${pin.path} as an ABSOLUTE PIN (kind "${String(pin.kind)}"), but that file only proves the ` +
              `implementation is its own inverse. A round-trip cannot detect a change that moves encode and decode ` +
              `together — the exact shape of the OP_N state-framing bug. Move it to "roundTripSmokeTests" and cite a ` +
              `real pin (spend-execution / vertical-pin / cross-tier-golden / kat), or mark the row UNCOVERED.`,
          );
        }
      }
    }
    expect(failures, `round-trip evidence dressed up as an absolute pin:\n${failures.join('\n')}`).toEqual([]);
  });

  it('no path is claimed as both an absolutePin and a round-trip smoke test', () => {
    const failures: string[] = [];
    for (const row of loadRegister()) {
      const smoke = new Set(stringsOf(row, 'roundTripSmokeTests'));
      for (const pin of pinsOf(row)) {
        if (typeof pin?.path === 'string' && smoke.has(pin.path)) {
          failures.push(
            `${String(row.id)}: ${pin.path} appears in BOTH absolutePins and roundTripSmokeTests. A file is one or the ` +
              `other; listing it twice launders a round-trip into a pin. Split the file, or pick a side.`,
          );
        }
      }
    }
    expect(failures, `evidence claimed on both sides:\n${failures.join('\n')}`).toEqual([]);
  });

  it('every required wire primitive has a row', () => {
    const present = new Set(loadRegister().map((r) => String(r.id)));
    const missing = REQUIRED_PRIMITIVES.filter((id) => !present.has(id));
    expect(
      missing,
      `wire primitive(s) in REQUIRED_PRIMITIVES with no row in ${REGISTER_FILE}:\n${missing.join('\n')}\n` +
        `Add a row with a real absolute pin, or a status:"UNCOVERED" row with a dated close plan.`,
    ).toEqual([]);
  });

  it('ids are unique and absolutePins[].kind comes from the closed enum', () => {
    const failures: string[] = [];
    const seen = new Set<string>();
    for (const row of loadRegister()) {
      if (typeof row.id !== 'string' || row.id.trim().length === 0) {
        failures.push(`row with a missing/empty "id": ${JSON.stringify(row)}`);
        continue;
      }
      const id = row.id;
      if (seen.has(id)) failures.push(`${id}: duplicate wire-primitive id`);
      seen.add(id);

      if (typeof row.description !== 'string' || row.description.trim().length === 0) {
        failures.push(`${id}: missing/empty "description"`);
      }
      if (row.residual !== undefined && (typeof row.residual !== 'string' || row.residual.trim().length === 0)) {
        failures.push(`${id}: "residual" must be a non-empty string when present`);
      }
      for (const pin of pinsOf(row)) {
        if (typeof pin?.kind !== 'string' || !KINDS.has(pin.kind)) {
          failures.push(
            `${id}: absolutePins kind ${JSON.stringify(pin?.kind)} — must be one of ${[...KINDS].join(', ')}`,
          );
        }
      }
    }
    expect(failures, `malformed register rows:\n${failures.join('\n')}`).toEqual([]);
  });

  it('the round-trip denylist is live and stays a superset of construct-ledger.test.ts', () => {
    const failures: string[] = [];

    // Liveness: a denylist that matches nothing is worse than no denylist,
    // because it reads as a guard while guarding nothing.
    for (const path of ROUND_TRIP_ONLY_PATHS) {
      if (!existsSync(join(REPO_ROOT, path))) {
        failures.push(
          `denylisted round-trip test ${path} does not exist — it was deleted or renamed, so the denylist entry is now a ` +
            `no-op. Update the entry to the new path (and check whether the register rows that listed it still hold).`,
        );
      }
    }

    // Superset: the sibling gate's list is the shared vocabulary. If it grows,
    // this gate must know about the new entry too.
    const sibling = siblingDenylist();
    if (sibling.length === 0) {
      failures.push(
        `could not read ROUND_TRIP_ONLY_PATHS out of ${SIBLING_LEDGER_TEST} — its declaration form changed, so the ` +
          `superset check silently stopped working. Re-point the parser (or export the constant and import it).`,
      );
    }
    for (const path of sibling) {
      if (!ROUND_TRIP_ONLY_PATHS.has(path)) {
        failures.push(
          `construct-ledger.test.ts denylists ${path} but this register's ROUND_TRIP_ONLY_PATHS does not. The two gates ` +
            `must not hold two different opinions about what counts as evidence — mirror the entry here.`,
        );
      }
    }

    expect(failures, `denylist liveness / drift:\n${failures.join('\n')}`).toEqual([]);
  });
});
