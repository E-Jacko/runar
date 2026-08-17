# Rúnar v1 audit — Codex

Audit branch: audit/codex/exhaustive-v1

Audited checkout: 52de438470bb158e6da3bbad00270335be861afc

The requested e7221a7b snapshot is an ancestor of this checkout, not its
current tip. The checkout therefore contains later changes and also differs
from the prompt's stated inventory sizes. I did not reset or replace the
checkout. The unrelated deletion of audits/canonical-json-rfc8785-parity.md
was preserved.

## Executive verdict

There is one confirmed S1 compiler defect: a valid nested declared-results
conditional still generates an unspendable branch. The formal and differential
machinery is not an independent semantic oracle at the exact fault line: the
Lean capstone begins after ANF lowering, and its stateful OP_PUSH_TX blob is an
opaque raw byte span. The conformance gates also contain two material S3
weaknesses: intentional golden changes require no objective specification
witness, and the fold-on allowlist has no stale-entry/liveness check.

No S0 was found.

Findings are in findings.jsonl, ordered with the S1 first. The exhaustive
provenance, skip, ANF dispatch, and rejection inventories are in
provenance-matrix.md, skip-matrix.md, conformance-matrix.md, and
rejection-matrix.md.

## H1 — gates have satisfiable-without-verification paths: FAIL

The current allowlist contains 210 entries, not the prompt's 58:

- 45 intentional-spec-change
- 144 second-implementation
- 18 differential-oracle
- 3 official-KAT

Every one of the 210 pinned file hashes recomputed successfully. That proves
content pinning only. The checker explicitly says it is not a correctness proof
at conformance/scripts/check-golden-provenance.mjs:36-39.

The structural weakness is verified in the checker. intentional-spec-change is
accepted at conformance/scripts/check-golden-provenance.mjs:116-121; entry
validation at :156-172 requires only path, hash, category, reason, and reviewer;
the changed-golden path at :235-258 compares only the current hash to the
allowlist hash. No originating commit, spec file, section, spec diff, or
independent oracle is required.

The 45 intentional entries are individual restamps/output touches. Their
originating commits and per-file verdicts are recorded in
provenance-matrix.md. The concrete red flag is
conformance/golden-provenance-allowlist.json:1193-1200: bounded-loop's reason
cites #121 and says the IR now has explicit start/step, while
spec/semantics.md:266-286 still documents count-only, zero-based loops. That is
an output restamp with contradictory live specification, not evidence of a
specification change.

Gate-by-gate result:

| gate | result | evidence |
|---|---|---|
| golden provenance | passes hash/provenance self-tests, but intentional category is self-attesting | conformance/scripts/check-golden-provenance.mjs:116-170; logs/golden-selftest.log:1 |
| fold-on allowlist | currently empty; stale perturbation is accepted by the loader model | conformance/fold-on-allowlist.json:27; conformance/runner/runner.ts:238-297; repro/fold-on-stale-entry.patch |
| per-fixture compiler allowlist | perturbation rejected | conformance/runner/__tests__/allowlist-audit.test.ts:9-37; logs/perturb-compiler-allowlist.log:1 |
| script-size baseline | implementation unions current and baseline fixture names and classifies missing entries | conformance/runner/script-size-check.ts:194-214; invocation blocked by tsx, logs/script-size.log:1 |
| decompiler fingerprints/templates | not run; tsx startup failed | logs/decompiler-fingerprints.log:1; logs/decompiler-templates.log:1 |
| SDK-output coverage | source has stale-entry checks, invocation blocked by tsx | conformance/sdk-output/runner/sdk-runner.ts:311-370; logs/perturb-sdk-coverage.log:1 |
| skip linter | red | scripts/lint-no-silent-skips.sh:32-80; logs/skip-lint.log:1 |

The compiler allowlist has a real source-of-truth test, but its own comment
states that synchronization with conformance/README.md is convention only at
conformance/runner/__tests__/allowlist-audit.test.ts:13-18. This is acceptable
as documentation hygiene only if correctness is independently covered; the
four Go-only fixture exemptions remain definitionally vacuous for cross-tier
parity.

## H2 — oracles are weaker than the property they check: FAIL

The manifest is clear about the formal boundary. The project reports 71 axioms
and zero opaque defaults at runar-verification/TRUST_MANIFEST.md:10-15, and
restricts the capstone trust base at :35-61. The raw grep counts in the tree
also match comments, manifest prose, and trajectory material; they are not
declaration counts. The manifest plus the TCB drift gate is the relevant
authority, not a raw word count.

The proved property is accept/reject agreement, not output equivalence, as
documented at runar-verification/TRUST_MANIFEST.md:26-33. A concrete blind
scenario is already described by the runtime oracle:
packages/runar-testing/src/__tests__/stateful-state-value-oracle.test.ts:6-9
states that Spend can accept a wrong transition because it cannot see the
ANF-level state-value error; the explicit post-state check catches it. Thus an
ANF evaluator and a Script evaluator can agree on acceptance while the stack
top, state bytes, or continuation output is wrong.

The three structural trust boundaries have these consequences and coverage:

1. The crypto_call residue fallback allowed by
   runar-verification/RunarVerification/AxiomAuditCmd.lean:48-53 means a wrong
   crypto residue/codegen interpretation could make authentication or hashing
   accept or reject incorrectly. The named real fixture application is
   runar-verification/tests/OmnibusInstantiation.lean:702-713; it demonstrates
   the fallback is used, not that every crypto implementation is proved.

2. runOps_checkPreimageBindingRaw_eq at
   runar-verification/RunarVerification/Stack/AgreesStateful.lean:116-139
   assumes the parsed deployed 760-byte OP_PUSH_TX blob leaves the preimage
   iff the BIP-143 preimage is correct and aborts otherwise. If false, a
   stateful covenant could accept a transaction whose preimage is not bound, or
   reject every valid continuation. The injected bytes are opaque to the Stack
   evaluator at :71-85. Execution coverage is
   packages/runar-testing/src/__tests__/oppushtx-binding.test.ts:70-120 and
   conformance/script_execution_test.go:847-848.

3. runOps_statefulFullParsedOps_scriptAccepts at
   runar-verification/RunarVerification/Stack/AgreesStateful.lean:648-667
   lifts the same assumption to the full stateful method and output epilogue.
   If false, full-method acceptance can diverge from the deployed script's
   actual preimage binding. The runtime side is exercised by the stateful Spend
   tests, but the Lean theorem itself is still an axiom.

The external differential did not reach python-bitcoinlib:
runar-verification/scripts/differential.sh:1 and
logs/additional-audit.log:9-12 record that python-bitcoinlib was absent and the
Lean side stopped after 2/71 fixtures. Even if installed, a pre-Genesis
python-bitcoinlib VM is not a post-Genesis semantic oracle. It can silently
agree with a wrong tier on 4-byte numeric limits, minimal-encoding rules,
non-minimal OP_IF truthiness, and sighash-flag behavior. Agreement on a
pre-Genesis execution result would not prove the current Script behavior.

## H3 — Go-only primitives receive little or no cross-tier signal: PARTIAL

The allowlist test explicitly makes BabyBear, KoalaBear, Poseidon2, BN254 /
Groth16, Merkle, merkleRootSha256, SP1 FRI, and FiatShamir-KB Go-only at
conformance/runner/__tests__/allowlist-audit.test.ts:24-36. For those fixture
paths, seven-tier parity has one participating implementation.

The named authorities found in the repository are:

| primitive family | authority actually present |
|---|---|
| BabyBear, KoalaBear, Poseidon2 | Plonky3 p3 dependencies in tests/generate-vectors/Cargo.toml:27-31, plus Go vector/codegen tests; no official Bitcoin KAT |
| BN254 / Groth16 | gnark-crypto generator in tests/generate-vectors/bn254/main.go:1-19 and real SP1/Groth16 fixtures; no official Rúnar-independent KAT suite |
| SP1 FRI / FiatShamir-KB | real Plonky3-shaped fixture and pinned configuration in tests/vectors/sp1/fri/minimal-guest/README.md:3-30; this is a concrete fixture authority, not exhaustive transcript proof |
| Merkle / merkleRootSha256 | repository-local generator at tests/generate-vectors/src/generate_merkle_vectors.rs:63-71 and :128-158; no upstream KAT or independent domain-separation source |

The Merkle case is filed as CX-006. The other authorities are named but still
leave field edge cases, Montgomery conversions, transcript binding, VK
handling, and pairing edge cases outside seven-tier differential detection.
The focused Go crypto test command passed 45 tests
(logs/additional-audit.log:16-18), which is evidence of execution, not an
independent semantic specification.

The three official-KAT entries were individually checked:
the BLAKE3 vector identifies the upstream BLAKE3 test_vectors.json source;
the ECDSA vector is RFC 6979-based; the SLH-DSA vector is ACVP-based and has a
Go enforcing xfail plus a self-consistency test. The local consumer coverage
is not seven-way: the repository search finds the KAT consumers in
packages/runar-go/crypto_kat_test.go, packages/runar-py/tests/test_crypto_kat.py,
and packages/runar-rs/tests/crypto_kat.rs. The Go-only policy therefore remains
a release risk even where the authority is real.

## H4 — generators reach many repaired shapes, but not the remaining shape: PARTIAL

The deterministic spend-shape tests passed:
conformance/fuzzer/spend-shapes.ts:482-535 enumerates 32 families, including
k=1/2/3/4 branch merges, asymmetric arms, nested-if, OP_N-range bytes, empty
bytes, negative bigint state, constructor-slot shifts, and loop-carried locals.
The test log records 23 passing tests and the fixed seed 424242 at
logs/spend-shapes-tests.log:1.

The important reachability table is:

| requested shape | generated? | evidence |
|---|---|---|
| unequal if/else stack effects with merged locals | yes, broad family | conformance/fuzzer/spend-shapes.ts:482-491 |
| early return inside nested conditionals with live locals | no generator family found | conformance/fuzzer/spend-shapes.ts:482-535 |
| four or more mutable fields, conditional subset writes, multi-output continuation | partial; k=4 is branch-local shape, not a verified four-field state/output combination | conformance/fuzzer/spend-shapes.ts:487-511 |
| loops mutating outer-scope state | no; loop families carry locals into addOutput | conformance/fuzzer/spend-shapes.ts:523-535 and :575-605 |
| addOutput/addRawOutput interleaved with conditional state writes | no exact family | conformance/fuzzer/spend-shapes.ts:522-535 |
| integer boundaries through 2^31, 2^32, 2^64 and big-number range | partial; zero, negative, 2^31-1 and large values exist | conformance/fuzzer/spend-shapes.ts:499-503 |
| empty/maximal bytes | partial; empty and representative multibyte values exist | conformance/fuzzer/spend-shapes.ts:496-498 |
| OP_SPLIT 0/len, NUM2BIN undersized/huge, BIN2NUM non-minimal | not represented by the spend-shape family list | conformance/fuzzer/spend-shapes.ts:482-535 |
| DIV/MOD negative and zero, shifts at/over width, non-minimal OP_IF | not established by the generated spend corpus | conformance/fuzzer/spend-shapes.ts:482-535 |

For the two fixes at the requested target, a generated branch-merged-local
case now reaches the repaired family. The state-framing bug is different: the
generator's bytes are compiler/Spend shape values, while the exact one-byte
state-section serialization is covered by the pinned SDK-output fixture and
state-push-framing test, not by a fuzz-regression entry. CX-005 records this
missing permanent replay.

The fuzzer README is appropriately honest about the remaining quiet face:
conformance/fuzzer/README.md:132-142 says reintroducing the branch bug produces
loud rejection/disagreement but not necessarily accepted stale state. CX-004
records the separate absence of the Issue #149 nested declared-results layout.

## H5 — cross-tier parity can preserve a shared misreading: PARTIAL / UNVERIFIED

The static ANF dispatch enumeration is complete for the 19-value union. The
individual cells are in conformance-matrix.md. TS covers every value in
packages/runar-compiler/src/passes/05-stack-lower.ts:465-530; Go at
compilers/go/codegen/stack.go:499-555; Rust at
compilers/rust/src/codegen/stack.rs:1217-1303; Python at
compilers/python/runar_compiler/codegen/stack.py:1131-1177; Zig at
compilers/zig/src/passes/stack_lower.zig:941-987; Ruby at
compilers/ruby/lib/runar_compiler/codegen/stack.rb:1384-1425; and Java's
enclosing dispatch at compilers/java/src/main/java/runar/compiler/passes/StackLower.java:1120-1163.
This is dispatch coverage, not a proof of frame arithmetic.

The TypeScript DCE walker explicitly enumerates all kinds and separates
side-effecting verifies, state updates, output nodes, calls, and raw scripts at
packages/runar-compiler/src/optimizer/dce.ts:63-155. Unknown-kind tests exist
in the golden and Python tiers, and Zig's JSON loader rejects unknown kinds at
compilers/zig/src/ir/json.zig:279-287. The focused Python, Ruby, and Zig
fixed-array/unknown-kind tests passed; see logs/additional-audit.log:20-27.

All seven fixed-array implementations have an explicit pass:
TypeScript at packages/runar-compiler/src/passes/03b-expand-fixed-arrays.ts:105,
Go at compilers/go/frontend/expand_fixed_arrays.go:44, Rust at
compilers/rust/src/frontend/expand_fixed_arrays.rs:47, Python at
compilers/python/runar_compiler/frontend/expand_fixed_arrays.py:97, Zig at
compilers/zig/src/passes/expand_fixed_arrays.zig:68, Ruby at
compilers/ruby/lib/runar_compiler/frontend/expand_fixed_arrays.rb:63, and Java
at compilers/java/src/main/java/runar/compiler/passes/ExpandFixedArrays.java:99.

The peephole catalogue has an explicit guard for the non-canonical boolean
case: not-not-elim requires an OP_NUMEQUAL producer at
packages/runar-compiler/src/optimizer/peephole-rules.ts:124-141. Real crypto
fusions are marked skipped in their numeric sweep at :159-188 and rely on
real-crypto tests. The JSON rule catalogue still contains the generic
not-not rule at optimizer/peephole-rules.json:9, so parity against the
implementation's loaded rule set needs the blocked full runner, not just a
source inspection.

The concrete shared-misreading signal is the stale loop section described
under H1. A seven-way restamp can encode the same wrong interpretation of
spec/semantics.md:266-286. Stack-depth, OP_PICK/OP_ROLL offsets, early-return
cleanup, partial state writes, host integer folding, and every peephole
precondition were not fully exercised across all seven tiers in this checkout;
the rejection matrix records those cells as unverifiable rather than guessing.

## SDK wire parity

Curated wire-format and envelope tests passed for the available suites:
86 wire-format tests at logs/wire-audit-tests.log:1, Go envelope tests at
logs/sdk-go-envelope.log:1, Python 21 tests at logs/sdk-py-envelope.log:1,
Ruby 23 examples at logs/sdk-ruby-envelope.log:1, and Rust 9 tests at
logs/sdk-rs-envelope.log:1. The fixture corpus contains hostile non-ASCII,
astral, numeric, and rejection vectors at conformance/sdk-envelope/fixtures.json:112-167
and signing vectors at :230-254.

The randomized canonical-json fuzzer deliberately excludes duplicate keys,
which are handled by fixed vectors; that exclusion is visible in
conformance/fuzzer/canonical-json-differential.ts:198-201. The requested
seven-way hostile randomized run was not completed. Java could not start
Gradle because libnative-platform.dylib could not load on macOS aarch64
(logs/sdk-java-envelope.log:1). A clean result for the available curated
tests does not establish all seven-way reason-string parity.

## Skips

The current docs contain 67 rows and 134 skip sites. The audit script reports
66 live inventory rows because one row has no line-bearing site; the queue and
skip-matrix retain all 67 documented rows. The audit classification is:

- 64 Environmental
- 2 Deliberate scope: the future-arity guard at docs/test-skips.md:61 and
  pathological decompiler set at :91
- 1 Deferred defect: Issue #149 at docs/test-skips.md:111

The source itself contradicts its summary: docs/test-skips.md:111 is a Gap row,
while :118-125 says “None — no gap skips.” CX-001 is the executable defect
behind that row. Every other row has an explicit precondition or scope reason;
the individual verdicts are in skip-matrix.md and queue.md.

The composite skip gate is nevertheless red because active design-document
markers are rejected by scripts/lint-no-silent-skips.sh:32-80. This is CX-003,
not a silent skip finding.

## Determinism

A repeated byte-read smoke test passed for one fixture
(logs/additional-audit.log:29-31). I did not claim process-level compile
determinism: the full cross-tier runner was blocked before compilation by tsx
IPC startup. Hash/map ordering in Go, Python, Ruby, and Zig therefore remains
unverified at the required process/shuffled-environment depth.

## Regression corpus

The permanent corpus contract requires every discovered bug to be human
minimised and replayed at conformance/fuzz-regressions/README.md:19-20.
The current entries include a branch K=1 guard-bypass entry, but no
state-framing/state-push-framing entry. The direct state-push-framing test and
SDK-output fixture are not substitutes for a replayable fuzz entry because
paired encoder/decoder tests can share a mistake. This is CX-005.

## What I could not verify and why

This section is intentionally unsoftened.

1. I did not run the full 7-tier × 9-format conformance matrix, the full
   malformed/truncated frontend fuzz, or the all-tier rejection matrix. The
   direct conformance entry points use tsx, which failed before loading code
   with node:net listen EPERM on a temporary IPC pipe. The exact conservative
   rejection table is in rejection-matrix.md.

2. I did not run every README/docs/formats/examples/RUNAR-SDK-PARITY example.
   The enumeration found 47 markdown files and 563 fenced blocks
   (logs/docs-and-counts.log:1-5); the same tsx startup failure prevented a
   trustworthy compile/run sweep. Many fenced blocks are prose, Lean, or
   generated/reference material, but I did not silently classify them as
   executable.

3. I did not complete the Python-bitcoinlib external differential because the
   dependency is not installed. The command stopped after 2/71 Lean fixtures,
   as recorded in logs/additional-audit.log:9-12.

4. I did not complete Java SDK/conformance execution because Gradle's
   libnative-platform.dylib could not load on macOS aarch64. The Java source
   dispatch and fixed-array implementation were inspected, but Java runtime
   parity is not claimed.

5. I did not run the requested randomized seven-way RFC 8785 canonical-json
   differential or prove identical VerifyEnvelopeReason values across all
   seven SDKs. Curated Go, Python, Ruby, Rust, and wire-format tests passed;
   Java was blocked and the randomized runner was blocked by tsx.

6. I did not use parity as evidence that the 45 intentional goldens are
   semantically right. Their individual hash/origin records are in
   provenance-matrix.md; the missing objective spec witness is filed as
   CX-002.

7. The full Lean gate did complete successfully: 137 jobs, 71 axioms, zero
   opaques/stubs/partial definitions, all 71 goldens WF and round-trip clean,
   and 44/71 pipeline goldens byte-exact. Sixteen crypto byte anchors were
   reported inert or stale by the gate. This confirms manifest/TCB accounting;
   it does not discharge the opaque rawBytes axioms. The opaque boundary and
   the three structural axioms are source-verified in
   runar-verification/RunarVerification/Stack/AgreesStateful.lean:71-85,
   :134, and :660-667.
