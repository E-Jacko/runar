# SELF-CRITIQUE

**Weakest finding: GK-021 (determinism / map iteration).** I did not run a
soak, did not grep every emit path for unordered map iteration, and filed a
host-language pattern as S2 with confidence `guess`. It is a real class in
multi-language compilers, but in this repo cross-tier hex parity already fails
hard on stable divergence; flaky single-tier order is unproven. Treat GK-021 as
a reminder, not a defect report.

**Pattern-match risk.** I know CompCert-style “front half unverified / back half
proved,” and I know “parity is not correctness.” That template fits Rúnar, and
the Palmer commit message / fuzzer README already say it. The danger is
re-deriving the template without tracing *this* `lowerIf`. I did read the #149
suite header and the post-Palmer `results`-declaration path in
`05-stack-lower.ts` / `04-anf-lower.ts`, but I did not step a NestedAdopt
compile through stack maps by hand or un-skip the vitest. GK-001’s mechanism is
author-documented in-tree; my contribution is connecting it to H1–H5 and the
generator blind spot (GK-027), not independently rediscovering the ROLL.

**Files I skimmed and should not own opinions on:** full bodies of
`Stack/Agrees*.lean` beyond axiom/shim grep; per-tier stack_lower ports beyond
confirming Palmer touched all seven; `sp1_fri.go` / BN254 pairing codegen;
Ruby/Java/Zig SDK state serializers line-by-line; `peephole-rules` JSON content;
`metamorphic-fuzz.ts` transform set; decompiler fingerprint gates. Crypto
findings on FRI/Groth16 are provenance-class, not “I found a bad fold.”

**Probes likely to dud:** P13–P15 if the surface names (`slice`, `num2bin`)
don’t match exports; P25 if NULLFAIL is already pinned hard; P35 as “write three
formats” without a harness; P47 if EC infinity is already fixture-locked; P46 if
non-default loop step is invalid Rúnar. **Highest EV probes:** P01, P02, P27,
P34, P45, P50. **P04** may correctly hard-fail at compile (outputs+multi-merge
guard) — that is still a useful pin of the diagnostic, not a dud if expected.

**What I ran:** `python3 scripts/audit-test-skips.py` (OK); local file reads;
`python3` counts on allowlists/witnesses/construct ledger; `rg`-equivalent greps
via shell; `git show` on `23ef2d2b`. **What I did not run:** vitest, go test,
lake, differential.sh, any fuzzer mode, any compiler CLI. Claims about live
redness of #149 are from checked-in `describe.skip` documentation, not a fresh
failure log on this machine.

**Calibration:** trust GK-001/003/005/011/027 and H1–H2 structure highly; treat
Go-only crypto severity as process risk not a named bad constant; discount
GK-021 and any “tiers will disagree” probe prediction — shared design more often
agrees on wrong.

---

## Deep-pass addendum

**Stronger than before:** GK-001 is no longer doc-only — NestedAdopt was executed under
MockProvider+Spend; inner-else rejects on both fold modes. Nested-loop "open" from the
remediation plan was a false positive for this HEAD (N22 PASS).

**Still weak:** GK-021 determinism. Did not re-derive EC formula status item-by-item after
the ec-formulas merge (GK-034 notes uncertainty). Did not re-run full mutation harness
(cited measured gap from mutants.json prose). Interpreter-only NestedAdopt probe via
TestContract returned 0n — API misuse likely; did not treat as oracle agreement evidence.

**New risk of overfit:** MockProvider getTransaction miss (GK-030) is real but may be
intentional (state from ANF path); severity S2 not S0. Rust oracle limits are environment
upstream issues, not Rúnar miscompiles — still release risk for Rust-tier confidence.
