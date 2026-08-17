# Rúnar v1 Audit — Grok

| Field | Value |
|---|---|
| Auditor | Grok |
| Finding prefix | `GK` |
| Worktree | `/Users/siggioskarsson/gitcheckout/runar-grok` |
| Reviewed HEAD | `52de438470bb158e6da3bbad00270335be861afc` |
| Prompt HEAD note | `e7221a7` (Palmer merge) is an ancestor of this HEAD |
| Date | 2026-08-16 |
| Source changes | **none** (read + local commands only) |
| Output | `audits/v1-review/grok/` |

## H1 — Gates have satisfiable-without-verification paths

**Verdict: CONFIRMED**

Evidence:

1. **Golden provenance** (`conformance/scripts/check-golden-provenance.mjs:116-170`): accepts `official-KAT | second-implementation | differential-oracle | intentional-spec-change` plus sha256 + reason ≥8 chars + reviewer. No machine check that a written `spec/` document changed. **45/210** entries are `intentional-spec-change`; **0** reason strings cite `spec/` paths (counted this session). **144/210** are `second-implementation` — peer-tier ports of one design, not independent references. **3** are `official-KAT`. **18** `differential-oracle`. (Counts differ from the prompt's 58/47 because the allowlist grew; the *mechanism* is unchanged.)

2. **fold-ON allowlist** (`conformance/fold-on-allowlist.json`): `skip: []` today — good. Contract for additions is prose `reason` + optional `tracking`. Satisfiable without independent Spend.

3. **Compiler allowlist**: 4 fixtures (`babybear`, `babybear-ext4`, `merkle-proof`, `state-covenant`) with `"compilers": ["go"]`. Correctly scopes hex parity; also makes multi-tier differential **vacuous** for those names (H3).

4. **script-size**: `_tolerance_growth_percent: 10`, `_tolerance_shrink_percent: 50` (`conformance/script-size-baseline.json`). Miscompiles that move size within band stay green. Baseline re-stamp is provenance-gated (positive) but still admits intentional-spec-change prose.

5. **sdk-output coverage allowlist**: intentional deploy-hex omissions; method-time fund paths are not what that gate covers.

6. **Skip linter**: `python3 scripts/audit-test-skips.py` → **OK — 134 sites / 66 rows** (executed this session). Documents every skip; does **not** force Gap skips to fail CI. Footer claims zero Gap skips while table row for #149 is Gap (`docs/test-skips.md:111` vs `:118`) — **GK-011**.

7. **update-golden**: still self-produces from TS; provenance is the independence layer — and it is partially self-attesting (GK-003/004).

**What the two RC bugs share with H1:** Palmer-1 moved **zero** goldens (no fixture shape). Palmer-2 co-changed encoder+decoder so round-trips stayed green. Gates that accept re-stamps or empty cells without absolute value pins cannot see that class.

---

## H2 — Oracles are weaker than what they check

**Verdict: CONFIRMED**

### Lean boundary on the fault line

- Capstone property is **observational accept/reject**, not output/state equivalence (`runar-verification/CORRECTNESS.md:100-104`, `TRUST_MANIFEST.md:26-28`).
- Front half (9 parsers, validate, typecheck, **03b**, **04-anf-lower**) is **out of scope**.
- Both Palmer bugs and open **#149** sit in ANF lower / stack-lower join handling — last unverified passes before the proved back half.

**Quiet wrong-state scenario (constructive):**

1. Source: stateful contract; `if` merges ≥2 locals incorrectly (pre-fix) or rotates inherited layout (#149).
2. ANF lowerer emits wrong binding names or stack adopt order.
3. ANF interpreter evaluates the **same** wrong ANF → ACCEPT + wrong post-state.
4. Emitted script matches that ANF → ACCEPT + wrong continuation.
5. Lean `acceptAgrees` holds; tier parity holds; `contract.state` after SDK ANF re-eval agrees with the bug.
6. **What catches it:** independent generator-side `expectedState` (spend-oracle), hand-pinned `expectedState` in real-crypto witnesses, or a human reading on-chain bytes. Accept-only differential does **not**.

### External reference (python-bitcoinlib)

- Pre-Genesis VM (`external-ref.py:20-28`): no OP_LSHIFT/RSHIFT; 10kB script cap; incomplete BSV numeric/push story.
- `differential.sh` **exits 0** if no reference is installed unless `--strict` (`differential.sh:26-31`).
- Allowlisted categorical mismatches only when external fails with exact BTC-only strings (`shift-ops`, large scripts).
- Fixtures run as **locking scripts on empty stack** → almost all fail at first pop with `unsupported`; agreement is coarse.

**Silent incorrect agreement risk:** where both engines refuse the same way, or never reach OP_NUM2BIN / OP_SPLIT / non-minimal OP_IF / post-Genesis numerics, the differential gives **zero** positive signal — not a false green on those ops, a **vacuous** green.

### Three structural axioms (plain English)

| Axiom | If false | What test covers it |
|---|---|---|
| `crypto_call` residue fallback | A non-fragment method body can observationally disagree (script accept ≠ ANF accept) without a proved consume path | Per-fixture empirical goldens + real Spend where present; **not** proved |
| `runOps_checkPreimageBindingRaw_eq` | 760-byte OP_PUSH_TX blob's abort/accept ≠ modelled `checkPreimage` | Real stateful spends / MockProvider validation / script_execution — **not** Lean evaluation of the blob (modelled as opaque data push, `AgreesStateful.lean:63-75`) |
| statefulFull widened peer shim | Prologue+epilogue composition wrong → accept forged state continuation or reject honest | Same: execution only |

### 71 axioms vs ~45 sorry / ~100 axiom

- Drift gate: `TARGET_AXIOMS=71` (`check-tcb-drift.sh:23`).
- `rg` over `*.lean`: **0** `sorry` this session (matches TRUST claim of zero sorry/admit in tree).
- Prompt's ~45 sorry / ~100 axiom is **stale** relative to this tree.
- `CORRECTNESS.md` still says **70** axioms in places — doc drift (**GK-019**), not a second TCB.

---

## H3 — Differential testing gives zero signal on single-implementation code

**Verdict: CONFIRMED (for Go-only families)**

| Primitive / fixture | Verifier | Class |
|---|---|---|
| BabyBear / Ext4 | Plonky3-generated vectors via `tests/generate-vectors` + TestContract (`tests/babybear-vectors.test.ts:1-10`); Go golden | **(a)/(b)** hybrid — upstream field ref, not multi-tier |
| KoalaBear / Poseidon2-KB | In-repo generators + vectors | **(b)** self-produced |
| Merkle SHA-256 | Rust generator building its own trees (`generate_merkle_vectors.rs`) | **(b)** — standard hash, but domain-sep choices are local |
| BN254 / pairing vectors | `tests/vectors/bn254_*.json` | **(b)** unless tied to official suite (not re-verified this session) |
| SP1 FRI | Real Plonky3 postcard fixtures + Go verifier (`sp1fri/verify_test.go:36-50`); on-chain script multi-minute / `-short` skipped | **(a)** fixture + **Environmental** skip on heavy path |
| state-covenant | Combines Go-only BabyBear+Merkle; compilers:["go"] | Golden + Go path only |

Symptomless failure modes still open: Montgomery/reduction edges not in vector tables, Merkle leaf/domain tagging, FRI Fiat-Shamir absorb order (partially pinned by SP1 docs), Groth16 VK / pairing under Environmental time skips.

---

## H4 — Generators don't reach the shapes that break

**Verdict: PARTIALLY CONFIRMED — remapped after 2026-08 remediation**

Post-Palmer remediation (`docs/audit/2026-08-testing-gap-remediation-plan.md`, status executed) added:

- `spend-shapes.ts`: merge-k1/k2/k3+, asymmetric, no-else, nested, loop-carried locals, OP_N ByteString state, negative bigint state, multi-slot ctors.
- `--spend-oracle` with **independent** state model (not ANF re-eval).
- Construct ledger (19 fund-critical rows, all `coveredBy` non-empty).

### Shape checklist (prompt list)

| Shape | Reachable? | Notes |
|---|---|---|
| if/else unequal stack effects, multi-local merge | **Yes** (spend-shapes) | Palmer-1 class |
| early return in nested conditionals, live locals | **No** (inferred) | language supports `return_statement`; fuzzer families don't target it |
| stateful ≥4 fields, partial conditional writes, multi-output | **Partial** | k=4 asymmetric merge; not full addRawOutput×cond matrix |
| loops mutating outer state | **Yes** | loop-carried families |
| addOutput/addRawOutput × cond state | **Partial** | ledger has if-outputs-and-merge-locals; generator emphasis is merge/state wire |
| boundary integers / empty / max bytes | **Partial** | state-bigint-edges fixtures; execute arb limited |
| OP_SPLIT 0/len, NUM2BIN undersize, BIN2NUM non-minimal | **No** (inferred for generators) | may appear only in fixed fixtures |
| DIV/MOD negative/zero, shifts ≥ width | **Partial** | execute may hit some; not construct-biased |
| non-minimal → OP_IF | **No** | |
| **#149 sibling-not-in-results nest** | **No** | GK-027: nested family rebinds all k |

### Would a *generated* case catch the two fixed bugs **now**?

| Bug | execute/tri-modal | spend-oracle | fuzz-regressions replay |
|---|---|---|---|
| Palmer-1 multi-local merge | **No** (stateless / no multi-local state pin) | **Yes** if family drawn (merge-k2+) | **No** dedicated entry (only K=1 empty-pad cousin) |
| Palmer-2 OP_N state framing | **No** | **Yes** (deploy-state-mismatch) | **No** entry |

So H4 is **no longer fully true** for Palmer after remediation, but remains true for **#149** and classic consensus edges.

---

## H5 — Cross-tier parity can encode a shared misreading

**Verdict: CONFIRMED as structural risk; residual open instance is #149**

- Seven compilers are deliberately kept in sync (CLAUDE.md). Palmer-1 was byte-identical wrong on all seven.
- `collectRefs` / `lowerBinding` on TS cover the 19-kind ANF union and throw on unknown kinds — checklist exists; ports mirror it.
- **03b** and **DCE** exist in all 7 tiers; **not** listed in CLAUDE.md pipeline prose (GK-024).
- Constant-fold host integers vs Script: fold-ON cross-tier gate + empty allowlist mitigates; Lean is fold-OFF.
- Peephole/EC rules: shared-port risk (GK-028); mutation gate is 16 curated TS mutants.
- **#149** is the live shared-design fund-lock: reconcile by name-set+depth, not layout — ports share the model.

Parity is necessary. It is not a seventh confirmation of the **spec**; it is seven confirmations of the **TS reading**.

---

## S0 / S1 findings by fix cost (cheapest first)

| ID | Sev | Cost | Title |
|---|---|---|---|
| GK-011 | S3→enables S0 visibility | minutes | Fix Gap footer vs #149 row |
| GK-005 | S3 | small | Construct-ledger UNCOVERED row for #149 |
| GK-006 | S3 | small | Promote Palmer-1/2 into fuzz-regressions |
| GK-027 | S3 | medium | spend-shapes family for inherited-sibling nest |
| GK-001 | **S0** | large (7-tier stack-lower) | Fix #149 arm-layout rotation; un-skip suite |
| GK-002 | **S0** class | process | Never ship accept-only as fund-safety for stateful |
| GK-007/008 | S1 | formal long | Opaque preimage shims + crypto_call residue |
| GK-025 | S1 historical | process | PQ/EC must have real script execution on RC |

Full list: `findings.jsonl` (GK-001…GK-028).

---

## Skips classification (summary)

- **Environmental (majority of 66 rows):** `-short` PQ/WOTS/SLH/Groth16 multi-second-to-minute script runs; `RUNAR_WALLET_ENDPOINT`; optional toolchains; missing-fixture defensive guards; `RUN_SLOW_TESTS` / CI-only slow suites; Rabin pathological tiny-sig guard.
- **Gap (1 live):** Issue **#149** nested declared-results arm layout (`nested-declared-results-arm-layout-vm.test.ts:112`). **Deferred fund-lock defect.**
- **Stale:** none claimed; footer consistency bug only (GK-011).
- **Documented ≠ justified:** Environmental skips mean default `go test -short` never executes SLH/WOTS script paths that previously hid real miscompiles (docs/test-skips.md SLH history).

---

## SDK wire parity (brief)

- `canonicalJson`: TS unit tests cover sort, `-0`, NaN/Inf reject, lone surrogates, nesting (`packages/runar-ir-schema/src/__tests__/canonical-json.test.ts`). Cross-tier: `canonical-json-differential` + envelope fixture 21 vectors / 1 rejection vector.
- Envelope: 5 rejection reasons fixtured; `pubkey-not-allowed` explicitly not cross-tier fixtured (`fixtures.json` note).
- Residual risk: host JSON parse of duplicate keys before canonicalisation; deep hostile inputs — **inferred** gap (GK-026).

---

## Determinism

Not soak-tested this session. Class residual on Go/Python/Ruby/Zig map iteration in stack maps (**GK-021**, confidence **guess**). Cross-tier parity catches stable divergence only.

---

## Regression corpus vs Palmer

- No `fuzz-regressions` entry for multi-local Palmer-1 or OP_N Palmer-2.
- Related: `2026-08-06-branch-k1-empty-pad-guard-bypass` (K=1 empty pad / guard bypass).
- Fixture + unit coverage exists under `conformance/tests/branch-merged-locals`, `merge-locals-*`, `state-push-framing` tests — **not** the same as fuzzer replay.

---

## What I could not verify and why

| Claim | Why |
|---|---|
| Live red of #149 on this machine | Suite is `describe.skip`; I did not un-skip and run vitest (would require compile/test env). Mechanism and skip text treated as **verified** documentation of open defect. |
| Full 7-tier compile of NestedAdopt | No full toolchain run this session. Shared-port conclusion **inferred**. |
| Lean build / `#audit_axioms` | Did not run `lake` / `full-verification.sh`. Axiom count from TRUST + drift script + `rg` for sorry. |
| differential.sh --strict with python-bitcoinlib | Did not execute external differential. Read scripts only. |
| Determinism soak / map iteration bug | Not reproduced — **guess**. |
| Every Go crypto vector vs official KAT byte match | Read generators and headers; did not re-derive Plonky3/SP1 outputs. |
| Host-language integer fold vs Script for all ops | Relied on fold-ON parity design + empty allowlist; no adversarial fold audit. |
| Full frontend rejection matrix | Absence of suite is the finding; did not prove a live permissive-tier accept. |

**Never claimed executed:** vitest suites, `go test`, Lean, differential.sh, fuzzer runs, golden regeneration.

---

## Shared property of the two RC bugs (and #149)

An invariant is **established in one pass** (branch result cardinality / state wire framing / arm stack layout), **assumed by a second** (stack-map naming, SDK encode, outer lowerIf depth), and **violated by a third** (merge of N locals, MINIMALDATA on non-executed bytes, ROLL+DROP of inherited slots). Horizontal parity and ANF self-evaluation **re-encode the violation**. Absolute oracles that pin **values** (not only accept bits) and **layout-sensitive** constructs are the only detectors. Remediation after Palmer closed many cells; **#149** proves the class is not extinct.

---

## Deep pass (2026-08-16 session 2)

### Execution verification of GK-001 / #149

Ran real `@bsv/sdk` Spend via `MockProvider` (audit probe, not product change):

```
npx vitest run audits/v1-review/grok/_probe_nested_adopt.test.ts
→ 2 failed | 4 passed
```

| Path | Expected | Result |
|---|---|---|
| `go(3,1,1)` inner then | p=55 | **accept** fold-ON/OFF |
| `go(3,1,0)` inner else | p=65 | **Spend reject** both fold modes — "top stack element must be truthy… PC:710" |
| `go(3,0,0)` outer skip | p=15 | **accept** |

Confidence on GK-001 upgraded from documentation to **executed**. The defect is a **loud** unspendable on the else path (not the quiet wrong-state face of Palmer), so accept/reject oracles that actually run Spend catch this particular instance — but the suite that would catch it is **`describe.skip`**, and generators still do not produce the shape (GK-027).

### Layer C structural blind spot (new GK-029)

`05-stack-lower.ts` Layer C (`stackMap.depth + postEndifDrops === armDepth`) and the declared-results top-N name check do not compare inherited mid-stack order. `multi-result-branch-node.md` §9 records that a full layout invariant is over-strict (37 failures / TicTacToe regtest). **The safety net designed for the 2026-08 family cannot see the residual open S0.**

### MockProvider getTransaction hole (new GK-030)

`broadcast()` never `transactions.set(fakeTxid, …)`; `finalizeCall` always hits "Failed to fetch transaction after broadcast" on success and continues with an empty shell. **Verified** via probe stderr. Weakens post-broadcast SDK tests; state on success still comes from the ANF-side update path.

### Rust oracle limits (new GK-031, GK-032)

Still open per `docs/audit/upstream-bsv-sdk-bip143-hashprevouts.md` and `mock_broadcast_validation.rs`:

1. **hashPrevouts** current-input-first for `input_index > 0`.
2. **OP_PUSH_TX** byte `0x8d` parsed as disabled OP_2MUL → covenant inputs **UNVALIDATABLE**.

Rust fail-closed mock cannot fully script-validate the primary stateful fund path.

### Mutation measured gap (new GK-033)

`sdkstate-decode-opn-as-length`: `state-push-framing-vm` alone misses decoder-only OP_N reintroduction; only `c28-state-strict` catches. Documented in `mutants.json`, not closed.

### Stale plan table (new GK-034)

§9.1 items **nested loops** and **bigint ≥ 2^63** are **fixed at HEAD** (N22 vitest PASS; magnitude guards in all 7 SDKs). Item **hashPrevouts** remains open. Plan table not updated.

### Nested loop control

```
npx vitest run …/nested-loop-carried-local-vm.test.ts -t "N22: 2x2" → PASS
```

Confirms `flattenNestedLoopBodies` fix is live — do not re-file as open S0.

### Coverage ledger refinement (GK-035)

30 residual fixtures: **24** `crypto-witness-infeasible` (incl. all SLH-DSA variants), 3 stateful-harness-gap, 2 go-only, 1 interpreter-unsupported.

### Revised H1–H5 notes (deep)

- **H1**: + plan staleness (GK-034), mutation partial miss (GK-033), Layer C green while S0 open (GK-029).
- **H2**: + Rust oracle cannot validate OP_PUSH_TX / multi-input (GK-031/032); #149 is loud on Spend so not "quiet", but still CI-green via skip.
- **H4**: + **executed** proof that generator miss is not theoretical.
- **H5**: unchanged; Layer C shared across ports.

### Commands executed this deep pass

- `npx vitest run audits/v1-review/grok/_probe_nested_adopt.test.ts`
- `npx vitest run packages/runar-testing/src/__tests__/nested-loop-carried-local-vm.test.ts -t "N22: 2x2"`
- `npx vitest run packages/runar-testing/src/__tests__/nested-declared-results-arm-layout-vm.test.ts` (6 skipped)
- file reads of lowerIf, mutation, coverage-ledger, upstream hashPrevouts doc
