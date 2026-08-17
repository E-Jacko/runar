# Rúnar v1 audit — Claude Code — SESSION 2 (2026-08-16)

Audited HEAD: **`52de4384`** (worktree `/Users/siggioskarsson/gitcheckout/runar-claude`).

Session 1 (2026-08-10) audited `a17037d6` and filed CC-001..CC-012; that report is
below this one and is unmodified. `git diff --stat a17037d6 52de4384` touches
**only `runar-verification/**`** (3 Lean-model commits), so every session-1
finding was still on-HEAD unless individually re-verified — which I did.
The remediation branch `fix/v1-audit-remediation` is **not merged into main**.

This session existed to close the five obligations session 1 recorded as NOT done.

| session-1 gap | status now |
|---|---|
| `lake build` / real Lean proof checking | **DONE** |
| `integration:all:run` (Docker was down) | **DONE** |
| `--spend-oracle` never executed | **DONE — and it produced the session's headline** |
| mutation testing (>=200 mutants), any tier | **DONE — TS 621 + Go 246**; Rust and the other 4 tiers still zero |
| 7-tier subprocess fuzzers at scale (`--anf` / `--ir --stateful`) | partial — see "could not verify" |

---

## S0 / S1 across BOTH sessions, ordered by fix cost

All four are live on `52de4384`. The first three share one root cause and one fix.

1. **CC-002 (S0) — cheapest to prove.** Nested declared-results `if` yields a
   **wrongly-spendable** script. Under the deployed default (fold-ON), `param2` =
   0, 1, −1, −2 all give `interp=false, spend=true`. 36-byte contract; one command.
2. **CC-014 (S0) — same root cause, new surface, needs its own fixture.** The
   stateful / `addOutput` manifestation: source accepts, script rejects, funds
   permanently locked. Not covered by #149's recorded reduction.
3. **CC-001 (S0) — the recorded one (issue #149).** Locked funds via a failed
   `OP_VERIFY`. Fix for all three: teach `lowerIf`'s reconcile to compare arm-exit
   **layout** (slot identity order), not just name-set and depth — then ship it in
   all 7 tiers with fixtures for **both** the stateless-`assert` and the
   stateful-`addOutput` shapes, or a partial fix will pass.
4. **CC-007 (S1) — independent, small, self-contained.** `readonly` assignment is
   accepted by all 7 tiers although `spec/semantics.md:247` defines it as an ERROR;
   the emitted 7-byte script has no authorization at all. Fix is a validator rule
   in `02-validate.ts` plus a cross-tier negative fixture.

---

## Headline: CC-013 / CC-014

`--spend-oracle` is the only oracle in the repo that is simultaneously **absolute**
(real `@bsv/sdk` Spend, not tier-vs-tier), **full-tx-context** (real deploy + call,
BIP-143, `OP_CODESEPARATOR`, `checkPreimage`), and **state-VALUE checking** against a
model the compiler never touches. Session 1 never ran it. I did:

| generator | cases | spend inputs | failures |
|---|---|---|---|
| stock | 150 | 442 | 0 |
| stock | 4000 | 11,750 | **0** |
| + sibling local, outer else KEPT (my 1st patch) | 3000 | 8,830 | **0** |
| + sibling local, outer `if` **without else** | 120 | — | **14** |
| same, fresh seeds 111/222/333/444 | 4x200 | — | **16 / 18 / 20 / 10** |

**The shape needs two degrees of freedom at once, and session 1's inference named
only one.** Session 1 wrote that a "subset-rebinding nested arm" would reach #149.
That is measurably *not sufficient*: with the untouched sibling but an outer `else`
still present, 8,830 spend inputs produce zero failures. The second, necessary
condition is that the **outer `if` has no else** — only then does one outer path
rearrange the inherited region while the other leaves it alone, so the two paths
exit at equal DEPTH with different LAYOUT. With an outer else both paths declare
the same result set and `lowerIf`'s reconcile normalises the layout away.

This matters beyond the fuzzer: it tells the fixer that a repair validated on a
shape with a symmetric outer branch will look correct and still be wrong.

### The defect the oracle then finds (CC-014, S0)

`repro/CC-013-nested-sibling-addoutput.runar.ts`:

```ts
let l0: bigint = this.f0;
let l1: PubKey = this.f1;          // live, UNTOUCHED across the inner if
if (p0 > 0n) {                     // outer if — NO else
  if (p0 > 2000n) { l0 = 127n; } else { l0 = 17n; }   // declares results, ROLL+DROPs
}
this.addOutput(1000n, l0, l1);     // positional read of both
```

`interpreterAccepted = true`, `spendAccepted = false`. The engine error is the
rotation signature — `OP_NUM2BIN requires that the size expressed in the top stack
item is large enough to hold the value expressed in the second-from-top stack item`
at PC 605: NUM2BIN received the 33-byte PubKey and the bigint **crossed**.

Source semantics accept the spend and **no valid spend of the UTXO exists** — funds
are permanently locked. Same root cause as CC-001 / issue #149, but #149 is recorded
(`docs/test-skips.md:111`) only as a stateless `assert` shape. The stateful
multi-output surface is undocumented, so a fix validated against the recorded
reduction can leave this live. That is why CC-014 is filed separately from CC-001.

Two independent failure kinds fire per case: `reject-when-accept-intended` (7) and
`interpreter-vs-spend` (7). The second is **model-independent** — ANF interpreter vs
real Spend — so these are not artefacts of my generator patch's expected-state model.

---

## Lean — the obligation session 1 could not attempt

Session 1 verified the axiom count and `sorry` absence **textually** and flagged that
it could not tell whether the proofs actually check. They do.

- `lake build` → **exit 0, 64 jobs, zero errors, zero `declaration uses 'sorry'`
  warnings** (`logs/80-lake-build.log`).
- The brief's "~45 `sorry` / ~100 `axiom` occurrences in the tree" worry resolves
  cleanly: all **36** textual `sorry`/`admit` hits under `RunarVerification/` are
  **prose inside docstrings**, and every one of them is an assertion that the file
  contains none. There are **zero** real sorries.
- `scripts/check-tcb-drift.sh` → exit 0: **axioms = 71**, opaques = 0, opaque stubs =
  0, partial defs = 0, matching `TRUST_MANIFEST.md`. The 87 textual `^axiom` hits
  include 16 docstring false positives; the gate's own counter is the stricter one.

**Verdict: the manifest's headline claim is accurate.** This is a negative finding
and I am recording it as such — H2's "reconcile the manifest against the tree"
resolves in the project's favour.

One real caveat: `lake build` alone only builds the **import cone**. `scripts/lean-verify.sh`
additionally builds every tracked module individually, which closes the
"unreferenced file with a hole" evasion. I ran `lake build` + the TCB gate, not the
full `lean:verify`.

---

## On-chain integration — first real pass in this audit lineage

Docker was down for session 1, so all of its regtest claims were read, not observed.
`integration/run-all.sh --start --stop` against a real regtest node:

**Exit 0, "All integration test suites passed", all 7 tiers:** Go · TypeScript ·
Rust · Python · Ruby · Zig · Java.

Caveat on my own method: the Java `--- Java: PASSED ---` marker is emitted with a
leading ANSI escape, so a `^--- Java` grep misses it and the run looks 6-tier. It
is present (`logs/91:8105`, `BUILD SUCCESSFUL in 3m 31s`). I mention it only
because I briefly mis-read it as a silent skip — it is not one.

This does **not** answer "which fixtures have never been spent on a real node":
the integration suites are hand-written per tier, not a replay of the 71
conformance fixtures. That enumeration remains undone (see below).

---

## Session-1 findings re-verified against HEAD — all still open

| id | sev | at HEAD | evidence |
|---|---|---|---|
| CC-001 | S0 | open | still `describe.skip` @ `nested-declared-results-arm-layout-vm.test.ts:112`; `docs/test-skips.md:111` still records #149 |
| CC-002 | S0 | open, **broader than recorded** | `logs/92`: fold-ON (deployed default) `param2` = 0, 1, −1, −2 → `interp=false, spend=true` (authorization bypass). fold-OFF `param2=5` → `interp=true, spend=false` (locked funds). Both directions live. |
| CC-003 | S3 | open | `arbExecMethodBody` still emits **zero** `kind: 'if'` |
| CC-005 | S3 | open | allowlist now **210** entries, **27** still `unreviewed` |
| CC-007 | S1 | open | go / rust / python all emit `76a97ca9788777` for `Hijack.runar.py` |
| CC-010 | S3 | open | gate over `tests/vectors/*.json` (22 files) → "nothing to justify", exit 0 |
| CC-011 | S3 | open | `--canonical --num 200` → `zig=skip`, "Mismatches: 0", exit 0 — 6-tier parity reported as 7 (`logs/98`) |

---

## H-verdicts — session 2 deltas only

Session 1's H1..H5 verdicts stand except where noted. What follows is what
*changed* because something got executed this time.

### H1 — gates satisfiable without verification: **CONFIRMED, unchanged**
Re-verified at HEAD: the golden-provenance allowlist is now **210** entries (the
brief said 58) of which **27** still declare themselves `unreviewed`, and
`tests/vectors/*.json` (22 files — the ONLY independent oracle for the Go-only
proof-system primitives) is still outside `GOLDEN_MATCHERS`, so the gate exits 0
with "nothing to justify" when they change. Category split at HEAD is
`second-implementation` 144 / `intentional-spec-change` 45 / `differential-oracle`
18 / `official-KAT` 3 — so the brief's "47 of 58 are intentional-spec-change"
framing is stale, but the self-attestation problem is the same shape and larger.

### H2 — oracles weaker than what they check: **CONFIRMED, with one part refuted**
The *Lean* half of H2 resolves in the project's favour and I want that stated
plainly: the proofs **check** (`lake build` exit 0, 64 jobs, zero `sorry`
warnings), the axiom count **is** 71 exactly as `TRUST_MANIFEST.md` claims, and
the tree's 36 `sorry`/`admit` strings are all docstring prose. The brief's
suggested discrepancy does not exist.

What is confirmed is the *boundary* claim, and CC-014 is the demonstration:
`04-anf-lower` / `lowerIf` is outside the verified cone, and a defect there
produces a script whose observable behaviour diverges from the ANF evaluator
(`interpreter-vs-spend`) on a shape the whole apparatus was green on.

### H3 — no signal on single-implementation code: **CONFIRMED, unchanged**
Not re-derived this session beyond CC-010 (above): the vectors that are the only
independent oracle for BabyBear / KoalaBear / Poseidon2 / BN254 / FRI are not
covered by the provenance gate and are not regenerated-and-diffed in CI.

### H4 — generators don't reach the shapes that break: **CONFIRMED — strongest result of the session**
See CC-013 / CC-014. The measurement is not "the fuzzer is small"; it is that the
repo's **best** oracle is green over 11,750 spend inputs on a defect that a
~20-line generator change surfaces on 4/4 fresh seeds. And the shape that was
missing needed **two** simultaneous conditions, only one of which session 1's
reading predicted — so "read the generator and reason about what it can't
express" was necessary but not sufficient; the experiment was required.

Also still true at HEAD, unchanged from session 1: `arbExecMethodBody` emits
**zero** `if` statements, so `--execute` and `--tri-modal` — the only *other*
absolute oracles — have no randomized branch coverage at all.

### H5 — parity encodes a shared misreading: **CONFIRMED, unchanged**
CC-007 (all 7 tiers accept a `readonly` write the spec defines as an ERROR and
emit a 7-byte no-auth script) and CC-002 (all 7 tiers byte-identical on a
wrongly-spendable script) are both re-verified on HEAD. Parity is green on both.

---

## Mutation testing — the obligation session 1 skipped entirely

621 mechanical mutants over `05-stack-lower.ts`, `06-emit.ts` and
`src/optimizer/*`, biased to `lowerIf` (2092-2664) and to PICK/ROLL/depth/slot
arithmetic. Gate: all 71 conformance fixtures, byte-exact fold-OFF hex.

| | n | caught | survived | score |
|---|---|---|---|---|
| raw | 621 | 395 | 226 | 63.6% |
| **corrected** (drop 37 vacuous `constant-fold` mutants) | **578** | **395** | **183** | **68.3%** |
| inside `lowerIf` only | 165 | 100 | **65** | 61% |

**Two flaws in my own harness, both found by self-check, both corrected — stated
because they would each have produced a confidently wrong number:**

1. The first **Go** run reported `246/246 caught, 100.0%`. Every entry's detail
   was `build-fail`: a copy at `$ROOT/.mut-go-wN` is not one of the modules listed
   in `go.work`, so `go build` fails there regardless of the mutation. A 100%
   score arriving directly after the TS tier scored ~36% survival is the tell.
   Rebuilt to mutate `compilers/go` in place, serially, with pristine restore;
   re-validated — details are now `hex-diff`.
2. My TS gate compiles **fold-OFF** (the goldens are fold-OFF), so mutations
   inside `constant-fold.ts` **never execute**. They scored 37/37 survived —
   vacuity, not coverage. Excluded. `dce.ts` (2/2 caught) and `anf-ec.ts` (9/11)
   do run, so the flaw is specific to the folding pass. Anyone repeating this must
   score fold-pass mutants fold-ON against a self-baseline.

Also worth recording: `expected-ir.json` is **ANF** IR (no stack ops), so for
`05-stack-lower` / `06-emit` / `peephole` the fold-OFF hex golden is the *complete*
golden signal — my hex-only gate is faithful there and is not under-counting.

### Escalation — the survivors are not just "golden-blind"

25 branch-merge / frame-offset survivors, re-run against
`branch-result-depth-invariant`, `branch-merged-locals-vm`,
`state-push-framing-vm`, and 300 `--tri-modal` property runs:

> **escalated = 25, caught by a stronger gate = 0, SURVIVED EVERYTHING = 25.**

Equivalence caveat, handled honestly rather than glossed: some survivors **are**
equivalent mutants. I hand-classified a sample and found one —
`05-stack-lower.ts:2660` `if (elseCtx.maxDepth > this.maxDepth)` → `>=` is a
max-update, so assigning on equality is a no-op. Genuinely not a hole. I have not
triaged all 183 for equivalence and do not claim they are all real.

But at least one is provably not equivalent, and it produced CC-016 (below).

### CC-016 — a named, zero-coverage path inside `lowerIf`

`05-stack-lower.ts:2212-2218`:

```ts
if (terminalAssert && thenCtx.stackMap.depth > 1) {
  const excess = thenCtx.stackMap.depth - 1;
  for (let i = 0; i < excess; i++) { thenCtx.emitOp({ op: 'nip' }); thenCtx.stackMap.removeAtDepth(1); }
}
```

Mutating `- 1` → `+ 1` emits two extra `OP_NIP`s and drops two extra slots. That
is not an equivalent mutant by any reading, and **no gate in the repo catches it**.
I instrumented the body in a copied tree and compiled all 71 fixtures:

> the guard is true **0 times**.

No fixture produces a terminal-assert `if` whose then-arm exits at depth > 1. A
stack-cleanup path in the branch-lowering function — the same function carrying
the open #149 defect, in the exact frame-offset class the brief names — has zero
coverage from the corpus and from every execution gate.

### Go tier — completed, and the asymmetry is real but only partly explained

Final Go run (harness fixed, in-place serial): **246 mutants, 246 caught, 0
survived, 100.0%.** Verified genuine, not a repeat of the `build-fail` artefact —
all 246 details are `hex-diff`, spanning `codegen/stack.go` lines 180-5535 and
`codegen/emit.go`, across 14 operator families
(branch-merge 104 / frame-offset 75 / emit 67).

Restricting the TS corpus to Go's operator set and Go's three regions:

| | n | caught | survived | score |
|---|---|---|---|---|
| TS (restricted to Go's ops + regions) | 249 | 141 | 109 | **56.6%** |
| Go | 246 | 246 | 0 | **100.0%** |

**Where the TS survivors are: 55 of the 109 are inside `lowerIf` (2092-2664).**
Go generated 104 mutants inside its own `lowerIf` (1903-2441, a similarly sized
function) and **every one of them died.**

What is verified: both numbers, both corpora, the placement above.

What is **inferred** and I am not asserting as fact: the most likely reading is
that the TS reference tier's `lowerIf` carries materially more *unexercised
decision logic* than the Go tier's — TS yields 165 mutable sites to Go's 104 in a
function of comparable length, and the TS file's own comments describe
backward-compatibility paths for ANF produced before the multi-result node
existed. CC-016 is a *proven* instance of exactly that (a `lowerIf` path with zero
fixture coverage). But I did not instrument branch coverage across the whole
function, so I have not established that this explains all 55.

The corpora are also not equivalent by construction: two different generators over
two different languages. **No "the Go tier is better tested than the TS tier"
conclusion should be drawn from this** — what is supportable is narrower and more
useful: *the TS tier's branch-lowering code has a large block of decision logic
that no fixture and no gate exercises, and the Go tier's does not show the same
signature under a comparable probe.*

Rust mutation was **not attempted**; nor Zig, Ruby, Python or Java.

---

## What I could not verify, and why (session 2)

Session 1's list stands except for the five items this session closed. What is
still not verified, stated without softening:

- **Rust mutation: not attempted.** The brief asked for mutation on "at least Go
  and Rust". I built and ran a TS corpus (621) and a Go corpus (246, partial), and
  did **zero** Rust mutants. Zig, Ruby, Python and Java also have zero mutation
  coverage and I added none. Five of seven tiers remain unmeasured.
- **The Go mutation run is partial and its corpus is weaker than the TS one.**
  It lacks the `cond-negate` and `drop-push-stmt` operators entirely. Any Go score
  I quote is therefore an upper bound on detection difficulty, not a like-for-like
  peer of the TS number, and I have not re-run TS and Go under an identical
  operator set and an identical sampling strategy. **No TS-vs-Go conclusion should
  be drawn from this session.**
- **Equivalent-mutant triage is incomplete.** 183 survivors; I hand-classified a
  handful. I found at least one genuine equivalent (`:2660`) and at least one
  genuine hole (`:2213` → CC-016). The true hole count is somewhere between those
  and I did not determine it. "68.3% mutation score" is a measurement of my corpus
  against that gate, **not** a claim that 183 real defects would ship.
- **`pnpm run lean:verify` was not run in full.** I ran `lake build` (import cone)
  + `check-tcb-drift.sh`. The full gate additionally builds **every tracked module
  individually** — which is precisely the step that would catch a hole parked in a
  file outside the cone — and runs `goldenLoad` / `roundtrip` / `pipelineGolden`.
  I did not execute those three binaries. My "the proofs check" claim covers the
  cone, not every tracked module.
- **`pnpm run test:ci` was never run end to end** this session. I ran
  `conformance:ts` (71/71), the integration matrix, and targeted gates. Stage
  timings and a grep of every skip path actually taken — obligation 1 — were not
  produced.
- **7-tier subprocess fuzzers at scale: still not done.** `--anf` and
  `--ir --stateful` at high volume across all seven tiers were not run; the
  spend-oracle and mutation work consumed the wall-clock. This was also a
  session-1 gap and it remains open.
- **"Which fixtures have never been spent on a real node" is still unanswered.**
  The integration suites passed on all 7 tiers, but they are hand-written per tier,
  not a replay of the 71 conformance fixtures. I did not build the mapping.
- **CC-014's opcode-level mechanism is inferred, not stepped.** The *behaviour* is
  verified (interpreter accepts, real Spend rejects, 4/4 seeds, model-independent
  signal). Attributing it to the same inherited-arm slot rotation as #149 rests on
  the shape and on the `OP_NUM2BIN` crossed-operand signature at PC 605. I did not
  step the two outer paths side by side to prove the slot identities.
- **Whether CC-014 and CC-001 share one fix is assumed.** I recommend one fix for
  both because the shapes and mechanism match. I did not apply a candidate fix and
  confirm it repairs both.
- **Gate perturbations I did not do.** The brief listed fold-ON allowlist
  insert/remove, `script-size-baseline.json`, decompiler fingerprints/templates,
  sdk-envelope and sdk-bip143. Session 1 perturbed golden-provenance, the skip
  linter, `tests/vectors` and TCB drift; **I added none of the remaining ones.**

---

# ============ SESSION 1 REPORT (2026-08-10, HEAD a17037d6) — unmodified ============

# Rúnar v1 audit — Claude Code (prefix `CC`)

**Worktree** `/Users/siggioskarsson/gitcheckout/runar-claude`, detached at **`a17037d6`**.

The prompt names HEAD `e7221a7`. `main` has moved ~20 commits past it and now includes a
P0 ECDSA-forgery fix (`49083e25`), the multi-result branch node (`4b0f688f`), and the EC
complete-formula work. Fixture count is 71, not 66; the golden-provenance allowlist is 210
entries, not 58. **Everything below was measured at `a17037d6`.**

Toolchain: all seven tiers built and their own suites ran (Go, Rust, Zig 0.16.0, Ruby,
Java 17 + Gradle 8.5, Python 3, Node 24 + pnpm 9.15). No tier was unbuildable.
Docker is installed but the daemon is not running, so `integration:all:run` could not be
executed — see "what I could not verify".

---

## Verdicts

| | Hypothesis | Verdict |
|---|---|---|
| **H1** | Gates have satisfiable-without-verification paths | **Confirmed, narrowly.** The gates are real and mostly fail when they should. Two concrete holes: the provenance allowlist accepts entries that declare themselves unreviewed (27 shipped), and `tests/vectors/*.json` — the only independent oracle for the Go-only crypto — is outside the gate entirely. |
| **H2** | Oracles are weaker than what they check | **Confirmed, and the project says so first.** `differential-execution.ts` documents its own verdict-only limitation in a 30-line header and points at `expectedState` as the fix; 24 of 31 real-crypto witnesses carry it. The Lean reconciliation, however, resolves **in the project's favour**: there are zero real `sorry`/`admit` and exactly 71 axioms. |
| **H3** | Differential testing gives zero signal on Go-only code | **Rejected as stated.** The Go-only primitives are verified against *independent third-party reference implementations* (Plonky3, gnark-crypto), executed as compiled Script through go-sdk's interpreter, and a representative subset is broadcast on regtest. Residual gaps are the ungated vector files and 4 pairing vectors. |
| **H4** | Generators don't reach the shapes that break | **Confirmed, and it is the headline.** The only absolute execution oracles generate **no `if` statement at all**. An ~80-line generator patch found a fresh S0 in 39 property runs and diverged on 8/8 seeds. |
| **H5** | Cross-tier parity can encode a shared misreading | **Confirmed twice, with the spec text in-repo.** All 7 tiers emit byte-identical hex for a funds-locking script; all 7 accept a construct `spec/semantics.md:247` defines as an ERROR. |

---

## S0 / S1 findings, ordered by fix cost

### 1. CC-002 — nested `if` also produces a **wrongly-spendable** script (S0) · cheapest to prove, same fix as CC-001

36-byte contract; `param2 = 0`, `1` or `-1` all make the source semantics **reject** and the
compiled script **accept**:

```ts
public run5(param2: bigint): void {
  let br0: bigint = param2;
  const sib0: bigint = param2;
  if (param2 > -8n) {
    if (param2 <= 0n) { br0 = 0n; } else { br0 = 1n; }
  }
  assert(br0 < sib0);
}
```

`runTriModalExecution` → `interpreterAccepted=false, vmAccepted=true, spendAccepted=true`.
All six native tiers emit byte-identical hex (`logs/32-bypass-crosstier.log`). Removing the
*outer* `if` makes all engines agree, which pins the mechanism to the same
inherited-arm rotation as #149.

`docs/test-skips.md:111` records only the other direction ("the else path fails `OP_VERIFY`
and locks funds"). **The open issue's recorded severity understates it: this is an
authorization bypass, not only an availability loss.**

### 2. CC-001 — issue #149, open at HEAD, all 7 tiers agree on the broken bytes (S0)

Un-skipping the checked-in reduction goes red immediately in both fold modes
(`logs/30-unskip-149.log`): `OP_VERIFY` failure at PC 710, funds permanently locked, for
the shape `if (a) { if (b) { x = ..; } else { x = ..; } }`. I compiled the same source on
all seven tiers and diffed: **byte-identical** (`logs/31-issue149-crosstier.log`). Parity is
green on a script that loses funds.

The maintainers' own analysis is accurate and the reasoning for deferring is
honest (both candidate invariants are over-strict at HEAD). My disagreement is only with
shipping it as a release candidate while the reproducer is `describe.skip`'d, so
`pnpm run test:ci` is green.

### 3. CC-007 — `readonly` is not enforced; the compiler emits a 7-byte no-auth script (S1)

`spec/semantics.md:247` states the rule literally:
`<this.p = e, env, sigma> ==> ERROR: cannot assign to readonly property`. No tier implements
it. `02-validate.ts:118` only checks that a stateless contract *has* no mutable property,
never that a readonly one is *written*.

```python
self.owner_hash = hash160(attacker_pk)
assert_(hash160(attacker_pk) == self.owner_hash)
```
compiles — on go, rust, python and java identically — to `76a97ca9788777`:
`OP_DUP OP_HASH160 OP_SWAP OP_HASH160 OP_OVER OP_EQUAL OP_NIP`. That compares
`hash160(pk)` to `hash160(pk)`. It is true for any key; the deployed `owner_hash` is never
referenced. **Anyone can spend.** Reproduced from both the `.runar.ts` and `.runar.py`
surfaces, so "tsc would flag it" does not cover the other eight syntaxes.

Interpreter and VM *agree* on the invented semantics, so every differential oracle in the
repo is green. This is the cleanest instance of H5 in the tree: the spec is written down,
in-repo, and seven independent implementations all read past it.

### 4. CC-008 — four tiers accept a non-literal property initializer that three reject (S2)

`p: bigint = 1n + 2n;` — ts/go/java error; rust/zig/python/ruby compile it and agree
byte-for-byte with each other. No fixture exercises it and there is no cross-tier
*negative* conformance set, so nothing catches the disagreement about what the language is.

---

## H4 — the generator gap, and the experiment that closes it

This is the most actionable result in the audit.

`arbExecMethodBody` (`packages/runar-testing/src/fuzzer/generator.ts:2087`) is the body
generator behind **both** absolute execution oracles (`--execute` and `--tri-modal`). It
emits var-decls, an optional `ForStmt`, ByteString decls, and a terminal assert. It emits
**no `if` statement of any kind.** Branch shapes exist only in `arbGeneratedContract` /
`arbGeneratedStatefulContract`, which drive `--ir` mode — a tier-vs-tier *parity*
comparison, definitionally blind to a defect all seven tiers share.

So every branch-merge miscompilation this project has shipped and fixed — `branch-merged-locals`,
`state-framing`, and open #149 — was outside the reachable space of the only randomized
oracle that could have caught it.

`spend-shapes.ts` does carry `merge-nested-if`, but its `nested` arm rebinds **all k** locals
in both inner arms (`conformance/fuzzer/spend-shapes.ts:773`), so it never leaves a live
inherited sibling for the adopt loop to rotate past — the one ingredient #149 needs.

**Baseline, unpatched, past CI budgets:** `--execute --num 6000` → 71 160 spends, 0
divergences. `--tri-modal` at 8 000 / 50 000 → all agree.

**Patched** (`repro/CC-exec-branch-generator.patch`, ~80 lines: draw a merged local `br0`,
a live sibling `sib0` declared after it, an optional nested declared-results `if` inside the
outer arm, and a non-commutative terminal read):

| seed | property runs to first divergence | direction |
|---|---|---|
| 99 | 39 | vm accepts, source rejects |
| 1 | 9 | vm accepts |
| 2 | 26 | vm accepts |
| 3 | 52 | vm rejects, source accepts |
| 4 | 10 | vm accepts |
| 5 | 14 | vm accepts |
| 6 | 7 | vm accepts |
| 7 | 42 | vm accepts |
| 8 | 20 | vm rejects |

**8/8 seeds, median ~17 runs.** The patch is reverted; the tree is clean.

One sub-result worth its own finding (CC-004): with the *same* nested-branch patch but a
**commutative** terminal clause (`br0 + sib0 !== ...`), 2 000 runs found nothing. Changing
that single clause to `br0 <cmp> sib0` found the bug at run 39. The existing
`arbCarrierClause` / `arbExtraClause` are additive, so a pure pairwise slot swap is
invisible to them. Reaching the shape is necessary but not sufficient — the observation
has to be order-sensitive.

Also measured: `--execute` accept rate is **6 633 / 71 160 = 9.3%**. Roughly ten of every
eleven generated spends are both-engines-reject, i.e. trivially agreeing. Method args are
drawn from `|v| ≤ EXEC_INT_MAG = 8n` (`generator.ts:1625`) and ByteStrings are fixed at 4
bytes, so the boundary integers named in the review (`2^31−1`, `2^31`, `2^32`, `2^64`) are
never drawn.

**Would a generated case now catch the two HEAD-fixed bugs?** For the branch-merged-local
family: yes, with the patch, and no without it. For state-framing: no — that half is an SDK
state-serialization defect and no fuzzer models the deploy→call continuation except
`spend-shapes.ts`, which is TypeScript-only.

---

## H1 — gate perturbation results

Every gate was exercised in both directions where it was feasible to do so.

| Gate | Made to fail? | Result |
|---|---|---|
| golden-provenance, unjustified change | yes | REJECT, correct (`logs/10`) |
| golden-provenance, stale sha | yes | REJECT, correct |
| golden-provenance, `--self-test` | n/a | 7/7 scenarios correct |
| golden-provenance, fabricated allowlist entry | **no** | **PASS** with `reviewer: "unreviewed:generated-by-agent"` and a reason that says no verification was done → **CC-005** |
| golden-provenance, witness content-pin | **no** | PASS on a sha copy alone (by design; only 11 of 71 fixtures have a witness at all) |
| golden-provenance vs `tests/vectors/*.json` | **no** | Not matched at all → **CC-010** |
| skip linter, declared `t.Skip` | yes | ORPHAN detected, exit 1 (`logs/11`) |
| skip linter, runtime early-return / empty describe | **no** | PASS — and 18 such tests exist today → **CC-009** |
| fold-ON allowlist | n/a | `skip: []` — empty, nothing to evade |
| `compareScript` empty-hex (`java: tolerateHexFailure`) | n/a | Correctly treated as a mismatch (`runner.ts:1980`); the leniency is sound |
| canonicalJson 7-tier parity | **no** | Reports "complete, 0 mismatches, exit 0" with `zig=skip` → **CC-011** |
| TCB drift (`check-tcb-drift.sh`) | n/a | axioms = 71, opaques = 0, partial defs = 0; matches the manifest |

The 210-entry allowlist breaks down as 144 `second-implementation`, 45
`intentional-spec-change`, 18 `differential-oracle`, 3 `official-KAT` — i.e. the
`intentional-spec-change` share has *fallen* since the prompt was written (47/58 → 45/210).
That is a real improvement. The remaining weakness is not the category but the sign-off
field: `entryProblems()` requires only a non-empty `reviewer` string and never reads
`review-status`.

---

## H2 — what the oracles actually establish

**Verdict-only agreement.** `differential-execution.ts:20-40` states the limitation itself:
a miscompile that leaves the script acceptable while committing the wrong continuation
state "is invisible to a verdict-only comparison — this oracle reports `agrees: true` while
the state is wrong." The stated fix is the hand-authored `expectedState` pin in
`conformance/witnesses/real-crypto/*.json`. I checked coverage: **24 of 31** files carry at
least one `expectedState`; the 7 that do not are stateless contracts with no state to pin
(`basic-p2pkh`, `ec-unit`, `escrow`, `multi-method`, `multisig`, `p256-primitives`,
`p384-primitives`). That is a genuine, independent, non-derived oracle and it is honestly
scoped.

**Execution coverage.** 41 of 71 fixtures are executed by the plain or real-crypto oracle;
30 are in `coverage-ledger.json` with a machine-checked `coveredBy` claim
(24 `crypto-witness-infeasible`, 3 `stateful-harness-gap`, 2 `go-only`, 1
`interpreter-unsupported`). The ledger is better engineered than the review assumes — the
`cause` vocabulary is a closed set and `coverage-claims.test.ts` proves each claim by
grepping the artifact it names.

**The Lean reconciliation resolves in the project's favour.** The review's "~45 `sorry` /
~100 `axiom` occurrences" are grep artifacts over English prose. Filtering matches that are
inside backticks or comments leaves **one** `sorry` (a string literal in an `IO.println`)
and **zero** real `admit`. Every file I sampled that greps positive
(`Stack/Agrees.lean`, `Stack/Peephole.lean`, `Stack/AgreesStateful.lean`) matches on the
phrase "No `sorry`". `scripts/check-tcb-drift.sh` reports axioms = 71 against the manifest's
71 target. **The manifest's claim is accurate as written.**

I did not build Lean or re-check the proofs, so "the capstone cone is `sorry`-free" is
verified only to the extent that no `sorry` exists anywhere to be in it — which is the
stronger property, and is what I measured.

**The three structural axioms** — plain-English, from `TRUST_MANIFEST.md:38-55`: (1) if the
`crypto_call` residue fallback is false, a compiled crypto builtin's runtime behaviour
differs from what the proof assumed, and only the per-family execution tests
(`compilers/go/codegen/script_correctness_test.go`, the runtime-vector suites) would notice;
(2) if either OP_PUSH_TX preimage-binding shim is false, the injected 760-byte
`checkPreimage` blob does not actually bind the spending transaction, which is BUG-100
re-opened — and because the proof models that blob as an opaque data push, **only execution
covers it**, specifically the regtest integration suite I could not run here.

---

## H3 — what verifies the Go-only primitives

Better than the hypothesis assumes. The chain is:

1. `tests/generate-vectors/` builds vectors from **independent third-party references** —
   `p3-baby-bear` / `p3-koala-bear` / `p3-poseidon2` (Plonky3, the library SP1 is built on)
   and `gnark-crypto` for BN254. Not self-produced.
2. `compilers/go/codegen/script_correctness_test.go` runs those vectors through the
   **compiled Bitcoin Script** on go-sdk's real interpreter (`buildAndExecute` →
   `BuildAndExecuteOps`), not through host arithmetic.
3. `integration/go/{babybear,bn254,poseidon2_kb,fri_colinearity,merkle}_vectors_test.go`
   broadcast a `selectRepresentative` subset (edge cases + wrap-around + identity + p−1 +
   5 random) on a regtest node.

So the answer for each family is **(a) independent reference implementation**, not (b) or
(c). Two residual gaps: those vector files are outside the provenance gate (CC-010), and
`bn254_pairing.json` carries **4 vectors** for the pairing check — the single most
security-critical operation in the Groth16 path. I did not attempt to break the pairing
check; I am flagging the thinness, not claiming a defect.

Note the TS-side vector tests (`tests/babybear-vectors.test.ts` and peers) run through
`TestContract`, i.e. the **interpreter**, and say so in their headers. They validate Rúnar's
interpreter model of `bbFieldAdd`, not the shipped codegen. The codegen coverage is the Go
path above.

---

## H5 — cross-tier parity as shared misreading

Three measurements:

- **CC-001**: seven tiers, byte-identical hex, script locks funds.
- **CC-007**: seven tiers accept a construct `spec/semantics.md:247` defines as an ERROR,
  and both engines agree on the invented semantics.
- **CC-008**: four tiers accept what three reject — parity's *inverse* failure, invisible
  because the fixture set only contains programs every tier accepts.

The structural point: parity is measured only over the accept-set. There is no cross-tier
**negative** conformance suite. I built a 10-program one by hand
(`repro/neg/`, `logs/60`); 8 of 10 agree across all seven tiers, and the 2 that do not are
CC-007 and CC-008. A permanent version of that file is the cheapest high-yield addition to
the suite.

---

## Skips

`lint-no-silent-skips.sh` reports 134 sites / 66 inventory rows, all documented. Classifying
the ones that actually fired in the baseline run:

- **Environmental** (legitimate): the `runSlowTests` cascade — `slh-dsa.test.ts` (9),
  `post-quantum-slh-dual-oracle.test.ts` (4), `post-quantum-bounds.test.ts` (78); the
  regtest-node suites (`multi-contract-call.regtest`, `wallet-client.spec`, 4 total). All
  run in CI.
- **Deliberate scope**: `peephole bounded-exhaustive: swept 26/28 rules; skipped 2
  (checksig-verify-fuse, checkmultisig-verify-fuse)` — the two rules whose preconditions
  need a real signature.
- **Deferred defect — one, and it is an S0**:
  `nested-declared-results-arm-layout-vm.test.ts` (6 skipped) = issue #149 = CC-001/CC-002.
  Documented at `docs/test-skips.md:111` in unusual detail. Documented is not justified: the
  release candidate is green only because this file is skipped.

Outside the inventory entirely: the 18 vacuous tests of CC-009. A latent-but-not-currently-firing
peer exists in `examples.test.ts:93` (a compile failure would return early and pass) — I
verified by instrumentation that it is **not** taken today, so it is not filed.

---

## Determinism

Byte-identical across 5 fresh processes per tier with randomized `PYTHONHASHSEED` and
cleared `RUBYOPT`/`GODEBUG` (3 for Java), on a stateful contract exercising branch merging
(`logs/40-determinism.log`). All six native tiers produced the same sha256 prefix
`be799c167ff1e38b`. **No non-determinism found.**

## SDK wire parity

`--canonical --num 300` (seed 313373): **0 mismatches**, 8m29s. The generator covers the
hostile surface the review names — lone surrogates via an explicit UTF-16 code-unit mode
that bypasses each tier's JSON parser, key ordering, float boundaries, nesting. Caveat:
`zig=skip` in my run because I had not run `zig build canonicalise`; CI does build it, but
the harness's silent degradation is CC-011. I intended a 20 000-case run and killed it —
each case spawns six subprocesses including `cargo run` and `gradle`, so it was not going
to finish; 300 cases is what I actually measured and 300 is what I am claiming.

## Regression corpus

5 entries; `--replay` 5/5 pass. Reverting the state-framing half of the fix
(`git checkout 23ef2d2b~1 -- packages/runar-sdk/src/state.ts`, rebuild) gives:

- `--replay`: **5/5 PASS — does not catch it**
- `conformance:sdk`: 1 FAIL (`stateful-bytestring-op-n-state`)
- `state-push-framing-vm.test.ts`: 9 FAIL
- `runar-sdk` unit tests: 13 FAIL

So the regression is caught — by the fixture and the pinned VM test the fix shipped with,
not by the replayable corpus (CC-012). Tree restored and re-verified green.

## Baseline

| Stage | Result | Time |
|---|---|---|
| `lint:silent-skips` | PASS (134 sites / 66 rows) | 2.3s |
| `typecheck` | PASS (13 tasks) | 6.0s |
| `pnpm run test` | PASS, 0 failures; 108 tests skipped across 5 files | 3m11s |
| `conformance:all` | multi-format 639/639 both fold modes; parser-only 639/639 × 7 tiers; ts 71/71; go/rust/python/zig/ruby/java tier suites pass | 27m12s |
| `conformance:sdk` | PASS all fixtures × 7 tiers (re-run with an explicit `tsx`) | — |

Two log artifacts worth correcting for anyone reading the raw capture: `conformance:all`
exited 1 solely because `npx tsx` was not resolvable at the repo root for the
`conformance:sdk` step (environmental — it passes with `conformance/node_modules/.bin` on
PATH), and `compilers/zig`'s `zig build test` prints `failed command: .../test` to stderr
while actually succeeding (`Build Summary: 3/3 steps succeeded; 741/741 tests passed`). I
initially read both as failures and they are not.

---

## What I could not verify, and why

- **On-chain integration.** `pnpm run integration:all:run` was never run. Docker 29.4.0 is
  installed but the daemon is not running, and starting the user's Docker Desktop was
  outside what I was asked to do. **Everything I say about regtest coverage is read from
  the test sources, not observed.** In particular the two OP_PUSH_TX preimage-binding
  axioms (H2) are covered *only* by execution, so their status at `a17037d6` is unverified
  by me. I also cannot answer "which fixtures have never been spent on a real node" — I can
  only say which have a witness or a real-crypto entry (41 of 71 have an in-process
  execution oracle; the regtest subset is a further restriction I did not enumerate).
- **Mutation testing.** The addendum asked for ≥200 mechanical mutants over
  `05-stack-lower.ts`, `06-emit.ts` and `src/optimizer/*`, plus Go and Rust. **I did not do
  this at all.** The existing 16-mutant curated corpus was not re-run either. The six
  non-TS tiers still have zero mutation coverage and I have added no evidence about it.
- **The Lean proofs themselves.** I did not run `elan`/`lake build`, so I did not confirm
  the proofs *check*. I verified the axiom count, the absence of `sorry`/`admit`, and that
  the drift gate agrees with the manifest — all textual. If `lake build` is red at HEAD I
  would not know.
- **Long `--anf` and `--ir` cross-tier fuzzing.** I ran the TS-in-process oracles at high
  volume (6 000 execute / 50 000 tri-modal) but not the 7-tier subprocess fuzzers at scale;
  each program spawns seven compilers, and I spent that wall-clock on the generator patch
  instead. The `--ir --stateful` path in particular I ran zero fresh cases against.
- **The 20 000-case canonicalJson run** was started and killed. 300 is the number I measured.
- **CC-002's opcode-level mechanism.** The *behaviour* is verified (I ran it, both fold
  modes, six tiers byte-identical). My attribution of it to the same inherited-arm rotation
  as #149 is **inferred** — from the ASM shape (`OP_3 OP_ROLL` present in the then-path and
  absent before the else-path's cleanup, then a post-`OP_ENDIF` `OP_ROT OP_ROT OP_LESSTHAN`)
  and from the fact that deleting the outer `if` makes the divergence vanish. I did not step
  the two paths side by side to prove the slots.
- **CC-008's blast radius.** I verified the four tiers accept and agree byte-for-byte with
  each other; I did not check whether the deployed initial state they encode matches what
  the SDKs expect, so "the artifact is wrong" is not something I am claiming — only that
  four tiers compile a program three tiers define as an error.
- **Whether CC-007 is exploitable in a realistic deployed contract.** I showed the compiler
  emits an unconditional-true script for a contract that reassigns its readonly guard. I did
  **not** find such a pattern in `examples/` or in any shipped contract, and I did not check
  whether a plausible developer would write it. The finding is "the spec rule is
  unenforced and the failure mode is total", not "a shipped contract is drainable".
- **`--spend-oracle`.** I read `spend-shapes.ts` closely enough to identify why its `nested`
  family cannot reach the #149 topology, but I never ran the spend oracle, patched or not.
  The claim that it would catch CC-001 given a subset-rebinding nested arm is **inferred**.

## Tree state

Clean. Every perturbation (generator patch, gate probes, un-skips, `state.ts` revert,
instrumented early-returns) was reverted and re-verified; the patches are kept under
`repro/`. `git status` shows only the untracked `audits/v1-review/` directory.
