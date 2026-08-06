#!/usr/bin/env tsx
// -----------------------------------------------------------------------------
// MUST-MOVE-A-GOLDEN GATE for wire-format changes
// (testing-gap plan §0.1 reviewer #3, §2 P9, §3 Phase F1 — finding TG-011)
// -----------------------------------------------------------------------------
//
// Problem this exists for. In 2026-08 a change altered the state-section wire
// framing in ALL SEVEN SDK serializers and moved ZERO pinned bytes. It looked
// safe: the SDK suites were green, cross-SDK conformance was 46/46. It was
// green because the encoder and the decoder were co-changed and every test was a
// round-trip — `deserialize(serialize(x)) === x` holds for *any* self-consistent
// framing, including a wrong one. The result was a contract whose state section
// no longer matched what the compiler emitted.
//
// The rule. A wire-format change that moves no pinned bytes is UNTESTED BY
// DEFINITION, and a tier-local codec test is not "pinned bytes" — it is the
// encoder graded against its own inverse. So:
//
//     changed ∩ WIRE_FORMAT_GLOBS ≠ ∅   ∧   changed ∩ STRONG_PIN_GLOBS = ∅  ⇒  FAIL
//
// The STRONG qualifier is load-bearing, and was added on 2026-08-06 after the
// gate was replayed against the literal changed set of `bd7ec284` — the very
// commit it was built to catch — and exited 0. That commit CO-ADDED
// `packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts`, whose
// name matches the `*minimaldata*` tier-local pin glob; the gate counted it as a
// pin, warned that it was weak, and passed. A round-trip-class test added in the
// same PR as the encoder it exercises is not independent evidence of anything.
// The weak-pin allowance was granted because `conformance/sdk-vertical/**` did
// not exist yet. It does now — 39 cases × 7 tiers of absolute compiler↔SDK pins —
// so every wire-format change has a strong pin available to it.
//
// "Wire format" = anything whose bytes cross a component boundary: the SDK state
// serializers + the shared field-width table, push-data / MINIMALDATA encoding,
// constructor-arg splicing into the locking script, OP_CODESEPARATOR emission +
// the artifact fields that describe it, the sighash scriptCode that consumes
// them, hand-rolled BIP-143 preimage serialization, the OP_RETURN / P2PKH output
// framing emitted by anf-lower AND stack-lower, the SDK ANF interpreters, and
// the transaction assembly that concatenates codePart ‖ OP_RETURN ‖ state.
// "Pin" = a checked-in byte artifact that a framing change is *supposed* to
// move: conformance goldens, cross-SDK locking hex, vertical compiler↔SDK
// fixtures, cross-tier ANF-interpreter expectations, the BIP-143 fixture,
// real-crypto witnesses, and the named framing/MINIMALDATA/codesep test files.
//
// This is deliberately a *process* gate, not a correctness proof. It cannot tell
// a right encoding from a wrong one. It only refuses to let a wire change ship
// with no evidence that anyone looked at the resulting bytes.
//
// What a pin is NOT (2026-08 adversarial audit of this gate — every one of these
// was executed against the CLI and got a clean exit 0):
//   * a brand-new doc whose NAME contains "codesep" — tier-local pins are now
//     matched in two parts, a tier test ROOT and a framing NAME;
//   * an `input.json` under sdk-output/ or sdk-vertical/ — those are inputs, and
//     the pin globs name the `expected-*` files explicitly;
//   * a witness touch that edits only a free-text `note` — content-sensitive
//     pins count only when the evidence (spends / expectedState) actually moved;
//   * "lives under conformance/" — a strong pin means the file's content IS the
//     wire bytes, not that it sits in the conformance directory.
//
// Escape hatch. `conformance/wire-format-exceptions.json` — narrow, per-path,
// content-pinned (sha256 of the reviewed file), expiring, reviewer-signed. Every
// exception used is printed on every run, and one whose content pin no longer
// matches is printed as REJECTED, so an exception can never quietly become the
// norm or silently cover the next change. Malformed / expired entries are a hard
// failure, never a free pass.
//
// NOT implemented: comment/doc-only diff detection. Deciding "this hunk is only
// comments" correctly across TypeScript / Go / Rust / Python / Zig / Ruby / Java
// means handling line comments, block comments, docstrings, and strings that
// contain comment markers, in seven grammars. A half-correct implementation
// fails OPEN (a real byte change misread as a comment ⇒ silent pass), which is
// the one failure mode this gate must not have. Use an exceptions entry for the
// rare comment-only touch of a wire file — it costs one reviewable JSON entry.
//
// Usage:
//   tsx conformance/scripts/wire-format-pr-audit.ts
//       Resolve `git merge-base <base> HEAD` and diff that..HEAD. Base defaults
//       to $WIRE_FORMAT_GATE_BASE, else origin/main. Pass a REF, not a pinned
//       SHA: a stale base SHA sweeps in the goldens other PRs merged in between.
//   tsx conformance/scripts/wire-format-pr-audit.ts --base origin/main
//   tsx conformance/scripts/wire-format-pr-audit.ts --changed-file list.txt
//       Read a newline-delimited changed set (CI can feed it directly).
//   Flags: --root <dir>, --json, --warn-only (report but exit 0).
//
// Exit code: 0 = satisfied (or warn-only); 1 = wire change with no pin; 2 =
// usage / internal error.
// -----------------------------------------------------------------------------

import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { join, resolve } from 'node:path';

// --- Wire-format implementation paths ---------------------------------------
// Grouped by wire family so a failure names the register row that moved. Every
// glob here is liveness-checked by `__tests__/wire-format-pr-audit.test.ts`: a
// glob that matches no file in the repo is a hard test failure, because a gate
// whose globs match nothing reports green forever.

export interface WireFormatRule {
  /** Wire-primitive family (plan §3 C0 register rows). */
  readonly family: string;
  /** One-line description used in the failure report. */
  readonly what: string;
  readonly globs: readonly string[];
}

export const WIRE_FORMAT_RULES: readonly WireFormatRule[] = [
  {
    family: 'sdk-state-serialization',
    what: 'state-section framing written into the deployed locking script (7 SDKs) + the shared field-width table',
    globs: [
      'packages/runar-sdk/src/state.ts',
      'packages/runar-go/sdk_state.go',
      'packages/runar-rs/src/sdk/state.rs',
      'packages/runar-py/runar/sdk/state.py',
      'packages/runar-zig/src/sdk_state.zig',
      'packages/runar-rb/lib/runar/sdk/state.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/StateSerializer.java',
      // STATE_FIELD_WIDTHS: the ONE table that decides every state field's byte
      // width + encoding, read by the compiler (artifact/assembler.ts) AND by
      // the SDK (sdk/state.ts, sdk/slot-layout.ts). Editing it moves deployed
      // bytes on both sides of the boundary at once — the exact class of change
      // that must never ship without a golden moving (gate audit P0-2).
      'packages/runar-ir-schema/src/state-layout.ts',
    ],
  },
  {
    family: 'push-data-encoding',
    what: 'push-data / MINIMALDATA opcode selection (encodeArg, encodePushData) — 7 SDKs + compiler',
    globs: [
      'packages/runar-sdk/src/script-utils.ts',
      'packages/runar-go/sdk_script_utils.go',
      'packages/runar-rs/src/sdk/script_utils.rs',
      'packages/runar-py/runar/sdk/script_utils.py',
      'packages/runar-zig/src/sdk_script_utils.zig',
      'packages/runar-rb/lib/runar/sdk/script_utils.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/ScriptUtils.java',
      'packages/runar-compiler/src/passes/push-encoding.ts',
    ],
  },
  {
    family: 'constructor-slot-splicing',
    what: 'constructor-arg splicing into the locking-script template at constructorSlots offsets (7 SDKs)',
    globs: [
      'packages/runar-sdk/src/slot-layout.ts',
      'packages/runar-sdk/src/contract.ts',
      'packages/runar-go/sdk_contract.go',
      'packages/runar-rs/src/sdk/contract.rs',
      'packages/runar-py/runar/sdk/contract.py',
      'packages/runar-zig/src/sdk_contract.zig',
      'packages/runar-rb/lib/runar/sdk/contract.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/ContractScript.java',
      'packages/runar-java/src/main/java/runar/lang/sdk/RunarContract.java',
    ],
  },
  {
    family: 'codeseparator-emit-and-artifact',
    what: 'OP_CODESEPARATOR emission + the artifact fields (constructorSlots, codeSeparatorIndex/Indices) SDKs read',
    globs: [
      'packages/runar-compiler/src/passes/06-emit.ts',
      'packages/runar-compiler/src/artifact/assembler.ts',
      'packages/runar-compiler/src/ir/artifact.ts',
      'packages/runar-ir-schema/src/artifact.ts',
      // The JSON schema is the machine-checkable peer of artifact.ts: it types
      // constructorSlots / codeSeparatorIndices, the fields every SDK splices
      // and signs on. Changing the shape here without moving a golden means no
      // artifact was ever re-emitted against the new shape (gate audit P2-9).
      'packages/runar-ir-schema/src/schemas/artifact.schema.json',
      'compilers/go/codegen/emit.go',
      'compilers/rust/src/codegen/emit.rs',
      'compilers/python/runar_compiler/codegen/emit.py',
      'compilers/zig/src/codegen/emit.zig',
      'compilers/ruby/lib/runar_compiler/codegen/emit.rb',
      'compilers/java/src/main/java/runar/compiler/passes/Emit.java',
      'packages/runar-go/sdk_types.go',
      'packages/runar-rs/src/sdk/types.rs',
      'packages/runar-py/runar/sdk/types.py',
      'packages/runar-zig/src/sdk_types.zig',
      'packages/runar-rb/lib/runar/sdk/types.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/RunarArtifact.java',
    ],
  },
  {
    family: 'sighash-scriptcode',
    what: 'BIP-143 scriptCode built from the codeSeparator offsets (OP_PUSH_TX preimage, 7 SDKs)',
    globs: [
      'packages/runar-sdk/src/oppushtx.ts',
      'packages/runar-go/sdk_oppushtx.go',
      'packages/runar-rs/src/sdk/oppushtx.rs',
      'packages/runar-py/runar/sdk/oppushtx.py',
      'packages/runar-zig/src/sdk_oppushtx.zig',
      'packages/runar-rb/lib/runar/sdk/oppushtx.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/OpPushTx.java',
    ],
  },
  {
    family: 'bip143-sighash-preimage',
    what: 'hand-rolled BIP-143 signing-preimage serialization (Rust/Python/Ruby/Java; TS+Go delegate to an upstream SDK, Zig builds it inside the globbed sdk_contract.zig)',
    globs: [
      'packages/runar-rs/src/sdk/signer.rs',
      'packages/runar-py/runar/sdk/local_signer.py',
      'packages/runar-rb/lib/runar/sdk/bip143.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/RawTx.java',
    ],
  },
  {
    family: 'state-framing-stack-lower',
    what: 'OP_RETURN / P2PKH output framing + addOutput ordering, emitted by anf-lower AND stack-lower (7 compilers)',
    globs: [
      'packages/runar-compiler/src/passes/05-stack-lower.ts',
      'compilers/go/codegen/stack.go',
      'compilers/rust/src/codegen/stack.rs',
      'compilers/python/runar_compiler/codegen/stack.py',
      'compilers/zig/src/passes/stack_lower.zig',
      'compilers/ruby/lib/runar_compiler/codegen/stack.rb',
      'compilers/java/src/main/java/runar/compiler/passes/StackLower.java',
      // The framing constants are emitted ONE PASS UPSTREAM of stack-lower:
      // `load_const '1976a914'` / `'88ac'` (the P2PKH script the intent
      // builtins pin) live in anf-lower in all seven tiers, and anf-lower also
      // owns addOutputRefs ordering — which hash256(outputs) binds. Globbing
      // only stack-lower left the whole output-framing surface open (P0-1).
      'packages/runar-compiler/src/passes/04-anf-lower.ts',
      'compilers/go/frontend/anf_lower.go',
      'compilers/rust/src/frontend/anf_lower.rs',
      'compilers/python/runar_compiler/frontend/anf_lower.py',
      'compilers/zig/src/passes/anf_lower.zig',
      'compilers/ruby/lib/runar_compiler/frontend/anf_lower.rb',
      'compilers/java/src/main/java/runar/compiler/passes/AnfLower.java',
      // Same byte constants, held as Zig templates: op_return_byte,
      // p2pkh_prefix_with_len, p2pkh_suffix, varint_fd_prefix.
      'compilers/zig/src/passes/helpers/stateful_templates.zig',
    ],
  },
  {
    family: 'sdk-anf-interpreter',
    what: 'off-chain ANF interpreter (7 SDKs): computes the post-state values and the ordered output sequence that hash256(outputs) binds',
    globs: [
      'packages/runar-sdk/src/anf-interpreter.ts',
      'packages/runar-go/anf_interpreter.go',
      'packages/runar-rs/src/sdk/anf_interpreter.rs',
      'packages/runar-py/runar/sdk/anf_interpreter.py',
      'packages/runar-zig/src/sdk_anf_interpreter.zig',
      'packages/runar-rb/lib/runar/sdk/anf_interpreter.rb',
      'packages/runar-java/src/main/java/runar/lang/sdk/AnfInterpreter.java',
    ],
  },
  {
    family: 'sdk-transaction-assembly',
    what: 'continuation-output (codePart ‖ OP_RETURN ‖ state) + multi-contract unlocking-script assembly done OUTSIDE the per-tier contract module',
    globs: [
      // `codePart + "6a" + stateHex`, literally.
      'packages/runar-java/src/main/java/runar/lang/sdk/TransactionBuilder.java',
      // Builds the contract-output list, and therefore the output ORDER that
      // hash256(outputs) commits to.
      'packages/runar-zig/src/sdk_call.zig',
      // Composes the per-input unlocking-script layout for a multi-contract
      // call: stateful prefix ‖ args ‖ change ‖ newAmount ‖ preimage ‖ selector.
      'packages/runar-sdk/src/multi-contract.ts',
    ],
  },
];

// --- Wire anchors (P2-8) -----------------------------------------------------
// Glob liveness proves a PATH still exists. It does NOT prove the encoding logic
// still lives there. Two-step evasion: PR 1 extracts the encoder into a new
// file and leaves a re-export shim (paying the pin cost once); every later PR
// edits the new, unglobbed file freely. Each anchor below pins a byte-level
// token to the file that must still contain it — move the logic and the gate's
// own test goes red until the new file is globbed.

export interface WireFormatAnchor {
  /** A path that is (and must stay) covered by a wire glob. */
  readonly path: string;
  /** Byte-level tokens that must still appear in that file. */
  readonly tokens: readonly string[];
  /** What moving these tokens elsewhere would silently un-gate. */
  readonly why: string;
}

export const WIRE_FORMAT_ANCHORS: readonly WireFormatAnchor[] = [
  ...[
    'packages/runar-compiler/src/passes/04-anf-lower.ts',
    'compilers/go/frontend/anf_lower.go',
    'compilers/rust/src/frontend/anf_lower.rs',
    'compilers/python/runar_compiler/frontend/anf_lower.py',
    'compilers/zig/src/passes/anf_lower.zig',
    'compilers/ruby/lib/runar_compiler/frontend/anf_lower.rb',
    'compilers/java/src/main/java/runar/compiler/passes/AnfLower.java',
  ].map((path) => ({
    path,
    tokens: ['1976a914', '88ac'] as const,
    why: 'P2PKH output framing pinned by the intent builtins',
  })),
  {
    path: 'compilers/zig/src/passes/helpers/stateful_templates.zig',
    tokens: ['p2pkh_prefix_with_len', 'p2pkh_suffix', 'op_return_byte', 'varint_fd_prefix'],
    why: 'Zig holds the same output-framing constants as named templates',
  },
  {
    path: 'packages/runar-ir-schema/src/state-layout.ts',
    tokens: ['STATE_FIELD_WIDTHS'],
    why: 'the single state field-width/encoding table read by both the compiler and the SDK',
  },
  {
    path: 'packages/runar-java/src/main/java/runar/lang/sdk/TransactionBuilder.java',
    tokens: ['"6a"'],
    why: 'the Java continuation output is assembled as codePart + "6a" + stateHex',
  },
];

export const WIRE_FORMAT_GLOBS: readonly string[] = WIRE_FORMAT_RULES.flatMap((r) => r.globs);

// --- Pin paths --------------------------------------------------------------
// A diff to any of these satisfies the rule. Two classes, and the distinction is
// the file's CONTENT, not its directory (gate audit P0-3d — a plain
// `path.startsWith('conformance/')` used to promote any file under conformance/,
// including a brand-new markdown note, to "cross-component byte evidence"):
//
//   * byte-artifact pins — the file's content IS the wire bytes (or a byte-level
//     assertion about them): compiler goldens, cross-SDK locking hex, the
//     compiler↔SDK vertical pins, the cross-tier ANF-interpreter expectations,
//     the BIP-143 fixture, and the real-crypto witnesses.
//   * weak pins — evidence ABOUT bytes rather than the bytes themselves: the
//     named tier-local MINIMALDATA / state-framing / codesep / constructor-slot
//     tests, and the construct ledger. They are reported as moved evidence but
//     they do NOT satisfy the rule on their own: a tier-local codec test is
//     usually the encoder graded against its own inverse (plan P3, reviewer #4),
//     and `bd7ec284` shipped a seven-SDK framing change on exactly one of them.

/** Pins whose bytes ARE the wire format. Every glob is liveness-checked. */
export const BYTE_ARTIFACT_PIN_GLOBS: readonly string[] = [
  // Compiler goldens.
  'conformance/tests/**/expected-*.json',
  'conformance/tests/**/expected-script.hex',
  // Cross-SDK deployed locking scripts. Scoped to the `expected-*` files on
  // purpose (P0-3c): `sdk-output/tests/**` also covered the 48 `input.json`
  // INPUTS — editing an input moves no golden, and `sdk-output/runner/**` /
  // `tools/**` are tooling. A new pin family under sdk-output/ must be added
  // here explicitly: a loud one-line failure, never a silent bypass.
  'conformance/sdk-output/tests/*/expected-*.hex',
  // Vertical compiler↔SDK pins. Same scoping: `cases/*/input.json`,
  // `reference/**`, `runner/**`, `generate.ts` and the contracts are inputs and
  // tooling, not evidence.
  'conformance/sdk-vertical/cases/*/expected-*.hex',
  'conformance/sdk-vertical/cases/*/expected-*.json',
  'conformance/sdk-vertical/artifacts/*.json',
  // Cross-tier ANF-interpreter expectations: post-state values + the ordered
  // output sequence, replayed by all 7 tiers.
  'conformance/anf-interpreter/expected*/*.json',
  // Cross-tier BIP-143 sighash preimage fixture.
  'conformance/sdk-bip143/fixtures.json',
  // Real-crypto execution witnesses (accept/reject + expectedState). CONTENT
  // SENSITIVE — see CONTENT_SENSITIVE_PIN_GLOBS.
  'conformance/witnesses/real-crypto/*.json',
];

/**
 * Byte-artifact pins that carry free text alongside the evidence. A diff that
 * touches only the prose is NOT a moved byte (gate audit P0-3b: editing one
 * `"note"` string in a witness used to launder an entire wire changed set).
 * These count only when `pinDiffIsMaterial` says the evidence itself moved.
 */
export const CONTENT_SENSITIVE_PIN_GLOBS: readonly string[] = [
  'conformance/witnesses/real-crypto/*.json',
];

/** Evidence ABOUT bytes, in a repo-level file rather than a tier's test root. */
export const WEAK_PIN_GLOBS: readonly string[] = [
  // Prose + coverage claims, not bytes.
  'conformance/construct-ledger.json',
];

/**
 * Tier-local pins are matched in TWO parts — a tier test root AND a framing
 * name — because one unanchored recursive `codesep` glob let a brand-new
 * `conformance/codesep-notes.md` (or `docs/state_push_framing.md`, or
 * `README-codesep.md`) satisfy the gate, and satisfy it as a STRONG pin (P0-3a).
 */
export const TIER_LOCAL_PIN_TEST_ROOT_GLOBS: readonly string[] = [
  'packages/*/src/__tests__/**', // TypeScript
  'packages/*/tests/**', // Rust, Python
  'packages/*/spec/**', // Ruby
  'packages/*/src/test/**', // Java
  'packages/runar-go/*_test.go', // Go
  'packages/runar-zig/src/*_test.zig', // Zig
];

/** Matched against the BASENAME of a file already inside a tier test root. */
export const TIER_LOCAL_PIN_NAME_GLOBS: readonly string[] = [
  '*minimaldata*',
  '*MinimalData*',
  '*codesep*',
  '*Codesep*',
  '*state-push-framing*',
  '*state_push_framing*',
  '*StatePushFraming*',
  '*constructor-slots*',
];

/**
 * Pin globs whose target does not exist yet because the phase that creates it
 * has not landed. Declared explicitly so the liveness test can tell "not built
 * yet" apart from "typo'd and therefore dead". Phase C (`sdk-vertical/`) and
 * Phase D0 (`construct-ledger.json`) have both landed, so this is now empty —
 * every pin glob is liveness-checked.
 */
export const PIN_GLOBS_NOT_YET_CREATED: readonly string[] = [];

function isTierLocalPin(path: string): boolean {
  if (!matchesAnyGlob(path, TIER_LOCAL_PIN_TEST_ROOT_GLOBS)) return false;
  const base = path.slice(path.lastIndexOf('/') + 1);
  return matchesAnyGlob(base, TIER_LOCAL_PIN_NAME_GLOBS);
}

export type PinKind = 'byte-artifact' | 'weak';

/** Which pin class a path belongs to, or null if it is not a pin at all. */
export function pinKindOf(path: string): PinKind | null {
  if (matchesAnyGlob(path, BYTE_ARTIFACT_PIN_GLOBS)) return 'byte-artifact';
  if (matchesAnyGlob(path, WEAK_PIN_GLOBS)) return 'weak';
  if (isTierLocalPin(path)) return 'weak';
  return null;
}

/** Pins whose content IS the wire bytes, rather than a claim about them. */
function isStrongPin(path: string): boolean {
  return pinKindOf(path) === 'byte-artifact';
}

// --- Content access ---------------------------------------------------------
// Two questions the gate cannot answer from paths alone:
//   * does an exception still describe the version of the file it was granted
//     for? (content pin, mirroring conformance/golden-provenance-allowlist.json)
//   * did a content-sensitive pin actually move EVIDENCE, or only prose?
// The CLI supplies a git-backed implementation; the gate stays pure over it.

export interface PinContent {
  /** File content at the merge-base, or null when the file was added. */
  before: string | null;
  /** File content now, or null when the file was deleted. */
  after: string | null;
}

export interface ContentAccess {
  /** sha256 of the path's CURRENT content, or null if unreadable/absent. */
  sha256(path: string): string | null;
  /** before/after content of a pin path, or null when it cannot be determined. */
  pinContent(path: string): PinContent | null;
}

/**
 * Keys whose value is prose for a human, never bytes for a machine. A diff that
 * touches only these has moved no evidence.
 */
const FREE_TEXT_KEYS = new Set([
  'note',
  'notes',
  'description',
  'comment',
  'comments',
  '_comment',
  '_doc',
  'documentation',
]);

function stripFreeText(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stripFreeText);
  if (value !== null && typeof value === 'object') {
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(value as Record<string, unknown>)) {
      if (FREE_TEXT_KEYS.has(k)) continue;
      out[k] = stripFreeText(v);
    }
    return out;
  }
  return value;
}

/** A witness is evidence only if it actually replays something. */
function carriesEvidence(parsed: unknown): boolean {
  const spends = (parsed as { spends?: unknown } | null)?.spends;
  return Array.isArray(spends) && spends.length > 0;
}

/**
 * Did this diff to a content-sensitive pin move EVIDENCE?
 *
 * The audit bypass this closes: editing one free-text `"note"` string in
 * `conformance/witnesses/real-crypto/stateful-counter.json` satisfied the gate
 * for an entire seven-SDK wire change. Prose is not a moved byte. Neither is a
 * brand-new witness with an empty `spends` array.
 *
 * Conservative in the safe direction: a deletion, unparseable JSON, or any
 * change outside the free-text keys is material.
 */
export function pinDiffIsMaterial(before: string | null, after: string | null): boolean {
  if (after === null) return true; // deleted evidence is a real change
  let afterJson: unknown;
  try {
    afterJson = JSON.parse(after);
  } catch {
    return true; // never assume unparseable content is cosmetic
  }
  if (!carriesEvidence(afterJson)) return false;
  if (before === null) return true; // genuinely new evidence
  let beforeJson: unknown;
  try {
    beforeJson = JSON.parse(before);
  } catch {
    return true;
  }
  return JSON.stringify(stripFreeText(beforeJson)) !== JSON.stringify(stripFreeText(afterJson));
}

// --- Exceptions -------------------------------------------------------------

export const EXCEPTIONS_REL = 'conformance/wire-format-exceptions.json';

/** An exception may not outlive this many days from the date it was granted. */
export const EXCEPTION_MAX_DAYS = 180;

export interface WireFormatException {
  /** Exact repo-root-relative path this exception covers. Globs are not allowed. */
  path: string;
  /** Why this wire-file change cannot move any pinned bytes. */
  reason: string;
  /** ISO date (YYYY-MM-DD) the exception was granted. */
  date: string;
  /** ISO date (YYYY-MM-DD) it stops applying. Hard failure once passed. */
  expires: string;
  /**
   * sha256 of the covered file's content AS REVIEWED. Content-pinned exactly
   * like conformance/golden-provenance-allowlist.json: the entry authorises ONE
   * reviewed version of the file, and self-invalidates on the next edit — an
   * exception granted for a comment-only touch can never cover a later change.
   */
  sha256: string;
  /** Sign-off marker, e.g. `gh:handle`. */
  reviewer: string;
}

const ISO_DATE = /^\d{4}-\d{2}-\d{2}$/;

function parseIsoDate(s: string): Date | null {
  if (!ISO_DATE.test(s)) return null;
  const d = new Date(`${s}T00:00:00Z`);
  return Number.isNaN(d.getTime()) ? null : d;
}

const DAY_MS = 24 * 60 * 60 * 1000;

/** Validate one exception entry. Returns human-readable problems, empty if fine. */
function exceptionProblems(entry: WireFormatException, index: number, now: Date): string[] {
  const at = `${EXCEPTIONS_REL} entries[${index}]`;
  const problems: string[] = [];
  if (typeof entry?.path !== 'string' || entry.path.trim().length === 0) {
    problems.push(`${at}: missing "path"`);
  } else if (/[*?]/.test(entry.path)) {
    problems.push(`${at}: "path" must be an exact path — globs are not allowed in an exception`);
  }
  if (typeof entry?.reason !== 'string' || entry.reason.trim().length < 20) {
    problems.push(`${at}: missing "reason" (>= 20 chars saying why no pinned bytes can move)`);
  }
  if (typeof entry?.reviewer !== 'string' || entry.reviewer.trim().length === 0) {
    problems.push(`${at}: missing "reviewer" sign-off marker (e.g. "gh:handle")`);
  }
  if (typeof entry?.sha256 !== 'string' || !/^[0-9a-fA-F]{64}$/.test(entry.sha256 ?? '')) {
    problems.push(
      `${at}: missing/invalid "sha256" (64 hex chars) — an exception must pin the exact ` +
        'file content it was granted for, so it cannot silently cover the NEXT change too',
    );
  }
  const granted = typeof entry?.date === 'string' ? parseIsoDate(entry.date) : null;
  if (!granted) problems.push(`${at}: missing/invalid "date" (must be YYYY-MM-DD)`);
  const expires = typeof entry?.expires === 'string' ? parseIsoDate(entry.expires) : null;
  if (!expires) {
    problems.push(
      `${at}: missing/invalid "expires" (must be YYYY-MM-DD) — a wire-format exception is ` +
        'always temporary; an undated waiver is how a hole becomes the norm',
    );
  } else {
    if (expires.getTime() < now.getTime()) {
      problems.push(
        `${at}: EXPIRED on ${entry.expires} — move a pinned byte artifact, or re-review and ` +
          're-date the entry (and re-pin its sha256)',
      );
    }
    if (granted && expires.getTime() - granted.getTime() > EXCEPTION_MAX_DAYS * DAY_MS) {
      problems.push(
        `${at}: "expires" is more than ${EXCEPTION_MAX_DAYS} days after "date" — cap it at ` +
          `${EXCEPTION_MAX_DAYS} days so the waiver comes back for review`,
      );
    }
  }
  return problems;
}

interface ExceptionRejection {
  entry: WireFormatException;
  why: string;
}

/** A validated exception still has to match the file it was granted for. */
function exceptionApplies(
  entry: WireFormatException,
  content: ContentAccess | undefined,
): { applies: true } | { applies: false; why: string } {
  const actual = content?.sha256(entry.path) ?? null;
  if (actual === null) {
    return {
      applies: false,
      why:
        'its sha256 content pin could not be verified (file unreadable, or the gate was run ' +
        'without repository access) — an unverifiable exception never applies',
    };
  }
  if (actual.toLowerCase() !== entry.sha256.toLowerCase()) {
    return {
      applies: false,
      why:
        `sha256 mismatch — the entry pins ${entry.sha256.slice(0, 12)}… but the file now hashes ` +
        `to ${actual.slice(0, 12)}…. The exception was granted for a DIFFERENT version of this ` +
        'file; move a golden, or re-review and re-pin.',
    };
  }
  return { applies: true };
}

/** Read `conformance/wire-format-exceptions.json`. Absent file ⇒ no exceptions. */
export function loadExceptions(root: string): WireFormatException[] {
  const abs = join(root, EXCEPTIONS_REL);
  if (!existsSync(abs)) return [];
  let parsed: unknown;
  try {
    parsed = JSON.parse(readFileSync(abs, 'utf8'));
  } catch (e) {
    throw new Error(`${EXCEPTIONS_REL} is not valid JSON: ${(e as Error).message}`);
  }
  const entries = (parsed as { entries?: unknown })?.entries;
  if (!Array.isArray(entries)) {
    throw new Error(`${EXCEPTIONS_REL} must have an "entries" array`);
  }
  return entries as WireFormatException[];
}

// --- Glob matching ----------------------------------------------------------

/**
 * Translate a path glob to an anchored RegExp.
 *   `**​/`  → zero or more path segments
 *   `**`   → any suffix (including `/`)
 *   `*`    → any run of non-`/` characters
 *   `?`    → one non-`/` character
 * Everything else is matched literally.
 */
export function globToRegExp(glob: string): RegExp {
  let out = '';
  for (let i = 0; i < glob.length; i++) {
    const c = glob[i]!;
    if (c === '*') {
      if (glob[i + 1] === '*') {
        if (glob[i + 2] === '/') {
          out += '(?:[^/]+/)*';
          i += 2;
        } else {
          out += '.*';
          i += 1;
        }
      } else {
        out += '[^/]*';
      }
    } else if (c === '?') {
      out += '[^/]';
    } else {
      out += c.replace(/[.+^${}()|[\]\\]/g, '\\$&');
    }
  }
  return new RegExp(`^${out}$`);
}

const globCache = new Map<string, RegExp>();
function cachedGlob(glob: string): RegExp {
  let re = globCache.get(glob);
  if (!re) {
    re = globToRegExp(glob);
    globCache.set(glob, re);
  }
  return re;
}

export function matchesAnyGlob(path: string, globs: readonly string[]): boolean {
  return globs.some((g) => cachedGlob(g).test(path));
}

/** Which wire family a path belongs to, or null. */
function wireFamilyOf(path: string): WireFormatRule | null {
  for (const rule of WIRE_FORMAT_RULES) {
    if (matchesAnyGlob(path, rule.globs)) return rule;
  }
  return null;
}

// --- The gate ---------------------------------------------------------------

export interface AuditOptions {
  exceptions?: readonly WireFormatException[];
  /** Repository content, for exception content-pins and content-sensitive pins. */
  content?: ContentAccess;
  /** Clock, for exception expiry. Defaults to now. */
  now?: Date;
}

export interface AuditResult {
  /** False ⇒ the PR must not merge as-is. */
  ok: boolean;
  /** Wire-format paths that count against the PR (exceptions already removed). */
  wireHits: string[];
  /** Pin paths that actually count as moved evidence. */
  pinHits: string[];
  /** Pin paths whose diff moved only free text — reported, but not evidence. */
  immaterialPins: string[];
  /** Content-sensitive pins whose diff could not be inspected; counted, but named. */
  unverifiedPins: string[];
  /** Exceptions that actually suppressed a wire hit — always reported. */
  exceptionsUsed: WireFormatException[];
  /** Exceptions that matched a path but did NOT apply (stale content pin, ...). */
  exceptionsRejected: ExceptionRejection[];
  /** True when the only pins are weak (round-trip-class / prose evidence). */
  weakPinOnly: boolean;
  /** Malformed exception entries. Non-empty ⇒ hard failure. */
  problems: string[];
  /** Human-readable report. */
  message: string;
}

/**
 * The gate, pure over its inputs. `changed` is a list of repo-root-relative
 * paths (a PR's three-dot diff against its merge-base).
 */
export function auditChangedPaths(changed: readonly string[], opts: AuditOptions = {}): AuditResult {
  const paths = [...new Set(
    changed.map((p) => p.trim().replace(/^\.\//, '')).filter((p) => p.length > 0),
  )].sort();

  const now = opts.now ?? new Date();
  const content = opts.content;
  const exceptions = opts.exceptions ?? [];
  const validated = exceptions.map((e, i) => ({ entry: e, problems: exceptionProblems(e, i, now) }));
  const problems = validated.flatMap((v) => v.problems);
  // A malformed entry never justifies anything.
  const exceptionByPath = new Map(
    validated.filter((v) => v.problems.length === 0).map((v) => [v.entry.path, v.entry]),
  );

  const allWireHits = paths.filter((p) => wireFamilyOf(p) !== null);
  const exceptionsUsed: WireFormatException[] = [];
  const exceptionsRejected: ExceptionRejection[] = [];
  const wireHits: string[] = [];
  for (const p of allWireHits) {
    const ex = exceptionByPath.get(p);
    if (!ex) {
      wireHits.push(p);
      continue;
    }
    const verdict = exceptionApplies(ex, content);
    if (verdict.applies) {
      exceptionsUsed.push(ex);
    } else {
      exceptionsRejected.push({ entry: ex, why: verdict.why });
      wireHits.push(p);
    }
  }

  const pinHits: string[] = [];
  const immaterialPins: string[] = [];
  const unverifiedPins: string[] = [];
  for (const p of paths) {
    if (pinKindOf(p) === null) continue;
    if (!matchesAnyGlob(p, CONTENT_SENSITIVE_PIN_GLOBS)) {
      pinHits.push(p);
      continue;
    }
    const c = content?.pinContent(p);
    if (!c) {
      // Fail open on the PIN side only — never block a PR because git could not
      // produce a base blob — but name it, so it cannot pass unnoticed.
      unverifiedPins.push(p);
      pinHits.push(p);
    } else if (pinDiffIsMaterial(c.before, c.after)) {
      pinHits.push(p);
    } else {
      immaterialPins.push(p);
    }
  }

  const weakPinOnly = pinHits.length > 0 && !pinHits.some(isStrongPin);

  // Only a STRONG pin satisfies the rule. A weak pin is still recorded and
  // reported (it IS evidence — just not evidence that any cross-component byte
  // was compared), but it cannot close a wire-format change on its own: that is
  // precisely how `bd7ec284` passed this gate when the drill replayed it.
  const ok =
    problems.length === 0 && (wireHits.length === 0 || pinHits.some(isStrongPin));

  return {
    ok,
    wireHits,
    pinHits,
    immaterialPins,
    unverifiedPins,
    exceptionsUsed,
    exceptionsRejected,
    weakPinOnly,
    problems,
    message: renderMessage({
      ok,
      wireHits,
      pinHits,
      immaterialPins,
      unverifiedPins,
      exceptionsUsed,
      exceptionsRejected,
      weakPinOnly,
      problems,
    }),
  };
}

function renderMessage(res: Omit<AuditResult, 'message'>): string {
  const lines: string[] = [];

  if (res.exceptionsUsed.length > 0) {
    lines.push(`Wire-format exceptions applied (${EXCEPTIONS_REL}):`);
    for (const e of res.exceptionsUsed) {
      lines.push(`  ~ ${e.path}`);
      lines.push(`      granted ${e.date}, expires ${e.expires}, reviewer ${e.reviewer}: ${e.reason}`);
    }
    lines.push('');
  }

  if (res.exceptionsRejected.length > 0) {
    lines.push(`Wire-format exceptions NOT applied (${EXCEPTIONS_REL}):`);
    for (const r of res.exceptionsRejected) {
      lines.push(`  ✗ ${r.entry.path}`);
      lines.push(`      ${r.why}`);
    }
    lines.push('');
  }

  if (res.immaterialPins.length > 0) {
    lines.push('Pin(s) that did NOT count — only free text changed:');
    for (const p of res.immaterialPins) lines.push(`    ~ ${p}`);
    lines.push(
      '    A witness whose spends / expectedState did not move is prose, not evidence that ' +
        'any byte moved (gate audit P0-3b).',
    );
    lines.push('');
  }

  if (res.unverifiedPins.length > 0) {
    lines.push('Pin(s) counted but unverified — their before/after content could not be verified:');
    for (const p of res.unverifiedPins) lines.push(`    ? ${p}`);
    lines.push('    Run the gate in a repository with the base ref fetched (fetch-depth: 0).');
    lines.push('');
  }

  if (res.problems.length > 0) {
    lines.push('✗ MUST-MOVE-A-GOLDEN GATE FAILED — malformed exception entries:');
    for (const p of res.problems) lines.push(`    ${p}`);
    lines.push('');
    lines.push('A malformed escape hatch is a gate outage; fix the entries or remove them.');
    return lines.join('\n');
  }

  if (res.wireHits.length === 0) {
    lines.push('✓ Must-move-a-golden gate: no wire-format implementation paths changed.');
    return lines.join('\n');
  }

  if (res.pinHits.length > 0 && !res.weakPinOnly) {
    lines.push(
      `✓ Must-move-a-golden gate: ${res.wireHits.length} wire-format path(s) changed, ` +
        `${res.pinHits.length} pinned byte artifact(s) moved with them.`,
    );
    for (const p of res.pinHits) {
      lines.push(`    pin${isStrongPin(p) ? '' : ' (weak)'}: ${p}`);
    }
    return lines.join('\n');
  }

  lines.push('✗ MUST-MOVE-A-GOLDEN GATE FAILED');
  lines.push('');
  if (res.weakPinOnly) {
    lines.push(
      `${res.wireHits.length} wire-format implementation path(s) changed, and every pin that ` +
        'moved with them is WEAK — evidence ABOUT bytes, never the bytes themselves:',
    );
    lines.push('');
    for (const p of res.pinHits) lines.push(`      ~ ${p}  (WEAK pin)`);
    lines.push('');
    lines.push('A tier-local codec test written in the same PR as the encoder it exercises is');
    lines.push('the encoder graded against its own inverse (round-trip class, plan §2 P3) — it');
    lines.push('holds for ANY self-consistent framing, including a wrong one. This is not a');
    lines.push('hypothetical: bd7ec284 changed state-section framing in seven SDKs, co-added');
    lines.push('exactly one such test, reported "SDK-output conformance 46/46", and shipped a');
    lines.push('state section the compiler no longer agreed with. Replaying that commit through');
    lines.push('this gate used to exit 0 on the strength of that one file.');
    lines.push('');
    lines.push('Move ONE cross-component byte pin as well (all three families exist today):');
    lines.push('        conformance/sdk-vertical/cases/*/expected-*      (compiler↔SDK vertical pin)');
    lines.push('        conformance/sdk-output/tests/*/expected-*.hex    (cross-SDK locking hex)');
    lines.push('        conformance/tests/**/expected-*                  (compiler golden)');
    lines.push('        conformance/anf-interpreter/expected*/*.json     (cross-tier post-state + outputs)');
    lines.push('        conformance/sdk-bip143/fixtures.json             (cross-tier sighash preimage)');
    lines.push('        conformance/witnesses/real-crypto/*.json         (spends + expectedState)');
    lines.push('');
    lines.push('The wire-format path(s) that need it:');
  } else {
    lines.push(
      `${res.wireHits.length} wire-format implementation path(s) changed and NOT ONE pinned byte ` +
        'artifact moved with them:',
    );
  }
  lines.push('');
  const byFamily = new Map<string, string[]>();
  for (const p of res.wireHits) {
    const fam = wireFamilyOf(p)!;
    const key = `${fam.family} — ${fam.what}`;
    byFamily.set(key, [...(byFamily.get(key) ?? []), p]);
  }
  for (const [family, members] of byFamily) {
    lines.push(`  [${family}]`);
    for (const m of members) lines.push(`      ✗ ${m}`);
  }
  lines.push('');
  lines.push('A wire-format change that moves ZERO pinned bytes is untested by definition:');
  lines.push('a co-changed encoder + decoder round-trips cleanly for ANY self-consistent');
  lines.push('framing, including a wrong one. That is exactly how the 2026-08 state-section');
  lines.push('regression shipped green across all seven SDKs.');
  lines.push('');
  lines.push('Do ONE of the following:');
  lines.push('');
  lines.push('  (1) Move a pinned byte artifact in this PR (preferred):');
  lines.push('        conformance/tests/<fixture>/expected-script.hex     (compiler golden)');
  lines.push('        conformance/sdk-output/tests/*/expected-*.hex        (cross-SDK locking hex)');
  lines.push('        conformance/sdk-vertical/cases/*/expected-*          (compiler↔SDK vertical pin)');
  lines.push('        conformance/anf-interpreter/expected*/*.json         (cross-tier post-state + outputs)');
  lines.push('        conformance/sdk-bip143/fixtures.json                 (cross-tier sighash preimage)');
  lines.push('        conformance/witnesses/real-crypto/*.json             (spends + expectedState)');
  lines.push('      An `input.json`, a runner, a generator or a note is NOT a pin, and a');
  lines.push('      tier-local unit test is only a WEAK pin — it never satisfies this gate');
  lines.push('      on its own (see bd7ec284).');
  lines.push('      If no existing fixture exercises the value class you changed, ADD ONE.');
  lines.push('      "No fixture covers it" is the hole, not the excuse.');
  lines.push('');
  lines.push('  (2) Add a cross-component pin for the primitive you touched — a byte');
  lines.push('      comparison against the OTHER implementation of the format, never');
  lines.push('      `deserialize(serialize(x)) === x` (plan §2 P3).');
  lines.push('');
  lines.push(`  (3) If the change genuinely cannot move any bytes, add an entry to`);
  lines.push(`      ${EXCEPTIONS_REL}:`);
  lines.push('        { "path": "<the file above>",');
  lines.push('          "reason": "why no pinned bytes can move",');
  lines.push('          "date": "YYYY-MM-DD",');
  lines.push(`          "expires": "YYYY-MM-DD",   // <= ${EXCEPTION_MAX_DAYS} days after "date"`);
  lines.push('          "sha256": "<sha256 of that file\'s reviewed content>",');
  lines.push('          "reviewer": "gh:your-handle" }');
  lines.push('      Exceptions are per-exact-path, content-pinned (so they cannot cover the NEXT');
  lines.push('      change to the same file), expiring, printed on every run, reviewed in the diff.');
  lines.push('');
  lines.push('  Checklist + full path list: conformance/README.md → "Encoding-change checklist".');

  return lines.join('\n');
}

// --- Changed-set discovery --------------------------------------------------

function git(root: string, args: string[]): string {
  return execFileSync('git', ['-C', root, ...args], {
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
}

/**
 * Resolve the merge-base of `<base>` and HEAD **at run time**.
 *
 * Pass a BRANCH ref (`origin/main`), not a pinned SHA. On a `pull_request` the
 * checkout is `refs/pull/N/merge` — the PR branch already merged with the
 * CURRENT base tip — while `github.event.pull_request.base.sha` is the base tip
 * as of the last sync. Diffing from that stale SHA sweeps in every commit the
 * base advanced by in between, so another PR's regenerated golden lands in this
 * PR's changed set and satisfies the gate for a PR that moved nothing (P1-5).
 */
export function resolveMergeBase(root: string, base: string): string {
  try {
    return git(root, ['merge-base', base, 'HEAD']).trim();
  } catch (e) {
    throw new Error(
      `git merge-base failed for '${base}': ${(e as Error).message.split('\n')[0]}. ` +
        'Ensure the base ref is fetched (checkout with fetch-depth: 0).',
    );
  }
}

function gitChangedFiles(root: string, mergeBase: string): string[] {
  // --diff-filter=ACMRTD keeps Deletions: DELETING a wire-format file is a
  // wire-format change (P2-7 — the old ACMRT filter let a removed serializer
  // contribute no wire hit at all).
  const range = `${mergeBase}..HEAD`;
  let out: string;
  try {
    out = git(root, ['diff', '--name-only', '--diff-filter=ACMRTD', range]);
  } catch (e) {
    throw new Error(
      `git diff failed for range '${range}': ${(e as Error).message.split('\n')[0]}. ` +
        'Ensure the base ref is fetched (checkout with fetch-depth: 0).',
    );
  }
  return out.split('\n').map((s) => s.trim()).filter(Boolean);
}

/**
 * Repository-backed content access: the working tree for "after" (in CI the
 * checkout IS the head commit), the merge-base blob for "before".
 */
function repoContentAccess(root: string, mergeBase: () => string | null): ContentAccess {
  return {
    sha256(path: string): string | null {
      const abs = join(root, path);
      if (!existsSync(abs)) return null;
      try {
        return createHash('sha256').update(readFileSync(abs)).digest('hex');
      } catch {
        return null;
      }
    },
    pinContent(path: string): PinContent | null {
      const base = mergeBase();
      if (!base) return null;
      let before: string | null;
      try {
        before = git(root, ['show', `${base}:${path}`]);
      } catch {
        before = null; // absent at the merge-base ⇒ the file was added
      }
      const abs = join(root, path);
      const after = existsSync(abs) ? readFileSync(abs, 'utf8') : null;
      return { before, after };
    },
  };
}

// --- CLI --------------------------------------------------------------------

interface CliArgs {
  root: string;
  base: string;
  changedFile?: string;
  json?: boolean;
  warnOnly?: boolean;
}

function parseArgs(argv: string[]): CliArgs {
  const args: CliArgs = {
    root: process.cwd(),
    base: process.env.WIRE_FORMAT_GATE_BASE || 'origin/main',
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    // `pnpm run wire-format-audit -- --base X` forwards the bare `--` verbatim.
    if (a === '--') continue;
    else if (a === '--base') args.base = argv[++i]!;
    else if (a === '--root') args.root = resolve(argv[++i]!);
    else if (a === '--changed-file') args.changedFile = argv[++i]!;
    else if (a === '--json') args.json = true;
    else if (a === '--warn-only') args.warnOnly = true;
    else {
      console.error(`Unknown argument: ${a}`);
      process.exit(2);
    }
  }
  return args;
}

/**
 * Run the CLI over an already-parsed argv and return the process exit code.
 * Exported so the gate's own tests can exercise `--changed-file` / `--warn-only`
 * in-process, without a subprocess and without a conditional skip.
 */
export function runCli(argv: string[]): number {
  const args = parseArgs(argv);

  // Resolved once, lazily: `--changed-file` mode is usable in a directory with
  // no base ref at all, and must not crash there — it just cannot content-verify.
  let mergeBase: string | null | undefined;
  const lazyMergeBase = (): string | null => {
    if (mergeBase === undefined) {
      try {
        mergeBase = resolveMergeBase(args.root, args.base);
      } catch {
        mergeBase = null;
      }
    }
    return mergeBase;
  };

  let changed: string[];
  if (args.changedFile) {
    changed = readFileSync(args.changedFile, 'utf8').split('\n');
  } else {
    const base = resolveMergeBase(args.root, args.base);
    mergeBase = base;
    changed = gitChangedFiles(args.root, base);
    if (!args.json) {
      console.log(
        `Wire-format gate: base=${args.base} merge-base=${base.slice(0, 12)} ` +
          `(${changed.length} changed path(s))`,
      );
    }
  }

  const res = auditChangedPaths(changed, {
    exceptions: loadExceptions(args.root),
    content: repoContentAccess(args.root, lazyMergeBase),
  });

  if (args.json) {
    console.log(JSON.stringify(res, null, 2));
  } else if (res.ok) {
    console.log(res.message);
  } else {
    console.error(res.message);
  }

  if (res.ok) return 0;
  if (args.warnOnly) {
    console.error('');
    console.error('(--warn-only: reporting the failure but exiting 0)');
    return 0;
  }
  return 1;
}

const invokedPath = process.argv[1] ? resolve(process.argv[1]) : '';
if (invokedPath && import.meta.url === new URL(`file://${invokedPath}`).href) {
  try {
    process.exit(runCli(process.argv.slice(2)));
  } catch (e) {
    console.error(`wire-format-pr-audit: ${(e as Error).message}`);
    process.exit(2);
  }
}
