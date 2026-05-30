import RunarVerification.Pipeline
import RunarVerification.ANF.EntryModel

/-!
# ANF IR — Typed-entry discharge bridge (WS0a Task 8, piece 2c — the PAYOFF)

This is the §11.5 payoff: a **from-witness** corollary of the dispatch-level
omnibus `compileSafe_observational_correct_arith_consume`
(`Pipeline.lean`) that discharges ALL of its entry-side premises by
construction, via the type-directed entry model of `ANF.EntryModel`.

The omnibus quantifies the initial ANF state, the initial stack, and the
tagged stack-map FREELY, then demands FIVE entry-side facts about them:

* `hAgrees`     — `agreesTagged tsm initialAnf initialStack`
* `hUntag`      — `untagSm tsm = (params.reverse).map (·.name)`
* `hTypedEntry` — `EntryBigintTyped Γ initialAnf`
* `hTsmTyped`   — `entryTsmArithTyped Γ tsm`
* `hCoh`        — `tsmCoherent initialAnf tsm`

Those are exactly the "§11.5 typed-entry assumption": properties of an
*arbitrary* runtime entry that the omnibus has to be GIVEN.  This file
instantiates the entry concretely as the type-directed
`mkEntryState` / `mkStackEntry` / `mkTsm` triple over a free raw
`witness`, and feeds the `EntryModel` by-construction lemmas
(`agreesTagged_mkEntry`, `untagSm_mkTsm`,
`mkEntryState_entryBigintTyped_noProps`, `entryTsmArithTyped_mkEntry`,
`tsmCoherent_mkEntry`) directly into the omnibus.

**The point (verify in the report):** the resulting theorem
`arith_consume_from_witness` carries ONLY program-side hypotheses
(`hWF` / `hMem` / `hPublic` / `hSafe` / `hSinglePublic` / `hName` /
`hChain`) plus the structural `hnd` (distinct param names) and
`hAllBigint` (every param declared `.bigint`) and a *free* `witness`.
There is NO `agreesTagged`, NO `EntryBigintTyped`, NO
`entryTsmArithTyped`, NO `tsmCoherent`, and NO `hUntag` premise — every
one is discharged by the type-directed construction.  That is the §11.5
typed-entry assumption eliminated for stateless arith.

This is a NEW leaf file that nothing else imports yet.  `EntryModel`
does NOT import `Pipeline`, and `Pipeline` does NOT import `EntryModel`,
so importing both here is cycle-free; this file does NOT touch the
omnibus or the entry-model lemmas.
-/

namespace RunarVerification.ANF.EntryDischarge

-- `compileSafe` lives directly in `Pipeline`; the omnibus theorem +
-- `successAgrees` / `runParsedBytes` live in `Pipeline.Soundness`.
open RunarVerification.Pipeline (compileSafe)
open RunarVerification.Pipeline.Soundness
  (successAgrees runParsedBytes compileSafe_observational_correct_arith_consume)
-- Sub-namespaces brought into scope by short name (`WF.ANF`, `Agrees.…`,
-- `Lower.…`, `Eval.…`).
open RunarVerification.ANF (ANFProgram ANFMethod ANFParam ANFType)
open RunarVerification.ANF.Eval (Value State)
open RunarVerification.ANF.TypeCheck (TypeEnv.ofParamsProps)
open RunarVerification.ANF.EntryModel
  (mkEntryState mkStackEntry mkTsm
   agreesTagged_mkEntry untagSm_mkTsm
   mkEntryState_entryBigintTyped_noProps
   entryTsmArithTyped_mkEntry tsmCoherent_mkEntry)
open RunarVerification.ANF
open RunarVerification.Stack

/-- **WS0a Task 8 piece 2c — the PAYOFF.**

`compileSafe_observational_correct_arith_consume` holds **from a raw
witness**, with every entry-side premise discharged by construction.

Given the program-side hypotheses (well-formed program `hWF`, the method
is a public member `hMem`/`hPublic`, the deployed bytes `hSafe`, the
single-public-method filter `hSinglePublic`, the non-constructor name
`hName`, and the emittable-arith chain predicate `hChain`), plus the two
structural facts that the method's parameters have distinct names (`hnd`)
and are all declared `.bigint` (`hAllBigint`), the deployed `compileSafe`
bytes are observationally correct on the **type-directed entry** built
from ANY raw `witness`: running the parsed Script agrees (on its success
bit) with evaluating the ANF body.

The five §11.5 entry premises are supplied entirely by the `EntryModel`
by-construction lemmas — none is a hypothesis here:

* `agreesTagged`     ⟸ `agreesTagged_mkEntry`
* `hUntag`           ⟸ `untagSm_mkTsm`
* `EntryBigintTyped` ⟸ `mkEntryState_entryBigintTyped_noProps`
  (at `Γ := ofParamsProps [] anfM.params`)
* `entryTsmArithTyped` ⟸ `entryTsmArithTyped_mkEntry`
* `tsmCoherent`      ⟸ `tsmCoherent_mkEntry`

Stateless / no-property case (`propsVals := []`), which is exactly the
scope the `EntryModel` no-props corollaries cover. -/
theorem arith_consume_from_witness
    (p : ANFProgram) (hWF : WF.ANF p) (anfM : ANFMethod) (bytes : ByteArray)
    (hMem : anfM ∈ p.methods) (hPublic : anfM.isPublic = true)
    (hSafe : compileSafe p = .ok bytes)
    (hSinglePublic : p.methods.filter (·.isPublic) = [anfM])
    (hName : anfM.name ≠ "constructor")
    (hChain :
      Agrees.emittableArithChainReadyNoDblNeg
        (Lower.computeLastUses anfM.body)
        anfM.body
        (List.reverse (anfM.params.map (·.name)))
        0 false)
    (witness : List Value)
    (hnd : (anfM.params.map ANFParam.name).Nodup)
    (hAllBigint : ∀ pr ∈ anfM.params, pr.type = ANFType.bigint) :
    successAgrees
      (RunarVerification.ANF.Eval.evalBindingsP p.methods
        (mkEntryState anfM.params [] witness) anfM.body)
      (runParsedBytes bytes (mkStackEntry anfM.params [] witness)) :=
  compileSafe_observational_correct_arith_consume
    p hWF anfM bytes hMem hPublic hSafe
    (mkEntryState anfM.params [] witness)
    (mkStackEntry anfM.params [] witness)
    (mkTsm anfM.params)
    (agreesTagged_mkEntry anfM.params [] witness hnd)
    (TypeEnv.ofParamsProps [] anfM.params)
    hSinglePublic hName hChain
    (untagSm_mkTsm anfM.params)
    (mkEntryState_entryBigintTyped_noProps anfM.params [] witness hnd)
    (entryTsmArithTyped_mkEntry [] anfM.params hnd hAllBigint)
    (tsmCoherent_mkEntry [] anfM.params [] witness hnd)

/-! ## WS0a Task 8-A — the arith discharge is harness-instantiable

`arith_consume_from_witness` carries ONLY program-side / structural
hypotheses, and every one is a **decidable** structural fact about the
triple `(p, anfM, bytes)`.  This section bundles them into a single
`Bool`-valued `arithFamilyReady p anfM bytes`, so a harness can decide —
by `native_decide`/`decide` — whether a concrete fixture's deployed bytes
are arith-discharge-eligible, and then fire `arith_family_verified` for an
arbitrary runtime `witness` with no further proof obligation.

Two facts cannot enter the `Bool` bundle, for the same root reason:
`ANFMethod` carries no `DecidableEq` instance (its `ANFValue` embeds a
`ByteArray` via `rawScript`, and Lean derives no `DecidableEq` for that
mutual block).  Those are `anfM ∈ p.methods` and the single-public filter
`p.methods.filter (·.isPublic) = [anfM]`.

* **membership is recovered, not assumed:** `anfM ∈ p.methods` is *derived*
  inside `arith_family_verified` from the single-public filter (`anfM` is in
  its own singleton image of `List.filter`, and `filter ⊆ id`), so it is not
  a separate hypothesis.
* **the single-public filter stays one separate `Prop` hypothesis** of
  `arith_family_verified` (`hSinglePublic`).  Per the task's documented
  fallback, this still achieves "all the genuinely Bool-decidable structural
  facts bundled + harness-checkable"; the residue is exactly the one fact
  that is undecidable for lack of `DecidableEq ANFMethod`.  Concrete fixtures
  discharge it by `rfl` (see `smoke_filter`).

The `compileSafe p = .ok bytes` fact, by contrast, **does** enter the
bundle: `Except CompileError ByteArray` has no generic `DecidableEq`
instance, but `compileSafeProducesBool` matches `compileSafe p` and
compares the `ok` payload through `DecidableEq ByteArray` (`decide (b' =
bytes)`), which `compileSafe_of_producesBool` bridges back to the `Prop`
equality.
-/

/-- **Bool encoder for `compileSafe p = .ok bytes`.**

`Except CompileError ByteArray` carries no generic `DecidableEq`, so we
hand-roll the decision: run `compileSafe p`, and on `.ok b'` compare the
payload to `bytes` through `DecidableEq ByteArray`.  `.error` is `false`. -/
def compileSafeProducesBool (p : ANFProgram) (bytes : ByteArray) : Bool :=
  match compileSafe p with
  | .ok b' => decide (b' = bytes)
  | .error _ => false

/-- Bridge: `compileSafeProducesBool p bytes = true → compileSafe p = .ok bytes`. -/
theorem compileSafe_of_producesBool
    (p : ANFProgram) (bytes : ByteArray)
    (h : compileSafeProducesBool p bytes = true) : compileSafe p = .ok bytes := by
  unfold compileSafeProducesBool at h
  cases hc : compileSafe p with
  | error e => rw [hc] at h; simp at h
  | ok b' =>
      rw [hc] at h
      simp only at h
      exact congrArg Except.ok (of_decide_eq_true h)

/-- **Bool→Prop bridge for the all-`.bigint` param hypothesis.**

`ANFType` derives `DecidableEq` but NOT `LawfulBEq`, so `beq_iff_eq` is
unavailable on `==`; we phrase the `Bool` as `List.all` over a
`decide`-based predicate and bridge each element with `of_decide_eq_true`. -/
theorem hAllBigint_of_bool
    (anfM : ANFMethod)
    (h : anfM.params.all (fun pr => decide (pr.type = ANFType.bigint)) = true) :
    ∀ pr ∈ anfM.params, pr.type = ANFType.bigint := by
  intro pr hpr
  exact of_decide_eq_true ((List.all_eq_true.mp h) pr hpr)

/-- **The bundled, harness-decidable arith-readiness predicate.**

A genuinely `Bool`-valued conjunction of every arith-discharge structural
fact that is decidable without `DecidableEq ANFMethod`:

* `WF.programIsWF p`                       — the `Bool` whose `= true` is `WF.ANF p`;
* `compileSafeProducesBool p bytes`        — `compileSafe p = .ok bytes` (see above);
* `anfM.isPublic`                          — already a `Bool` field;
* `decide (anfM.name ≠ "constructor")`     — `String` has `DecidableEq`;
* `emittableArithChainReadyNoDblNegBool …` — the `Bool` mirror of the omnibus chain;
* `decide ((params.map name).Nodup)`       — `List.Nodup` over `String` is decidable;
* `params.all (fun pr => decide (pr.type = .bigint))` — every param declared `.bigint`.

The single-public filter and `anfM ∈ p.methods` are intentionally absent —
see the section note. -/
def arithFamilyReady (p : ANFProgram) (anfM : ANFMethod) (bytes : ByteArray) : Bool :=
  WF.programIsWF p
    && compileSafeProducesBool p bytes
    && anfM.isPublic
    && decide (anfM.name ≠ "constructor")
    && Agrees.emittableArithChainReadyNoDblNegBool
        (Lower.computeLastUses anfM.body) anfM.body
        (List.reverse (anfM.params.map (·.name))) 0 false
    && decide ((anfM.params.map ANFParam.name).Nodup)
    && anfM.params.all (fun pr => decide (pr.type = ANFType.bigint))

/-- **WS0a Task 8-A — the arith discharge, harness-instantiable.**

If `arithFamilyReady p anfM bytes = true` (one `native_decide`-able check
on the concrete fixture) and the single-public filter holds, then the
deployed `compileSafe` bytes are observationally correct on the
type-directed entry built from ANY raw `witness` — running the parsed
Script agrees (on its success bit) with evaluating the ANF body.

The proof destructures the `Bool` conjunction into its individual facts
(`Bool.and_eq_true`), bridges each `Bool`/`decide` conjunct to its `Prop`
form, *derives* `anfM ∈ p.methods` from `hSinglePublic`, and applies
`arith_consume_from_witness`. -/
theorem arith_family_verified
    (p : ANFProgram) (anfM : ANFMethod) (bytes : ByteArray)
    (hReady : arithFamilyReady p anfM bytes = true)
    (hSinglePublic : p.methods.filter (·.isPublic) = [anfM])
    (witness : List Value) :
    successAgrees
      (RunarVerification.ANF.Eval.evalBindingsP p.methods
        (mkEntryState anfM.params [] witness) anfM.body)
      (runParsedBytes bytes (mkStackEntry anfM.params [] witness)) := by
  unfold arithFamilyReady at hReady
  simp only [Bool.and_eq_true] at hReady
  obtain ⟨⟨⟨⟨⟨⟨hWFb, hSafeb⟩, hPub⟩, hNameb⟩, hChainb⟩, hndb⟩, hBigb⟩ := hReady
  have hWF : WF.ANF p := hWFb
  have hSafe : compileSafe p = .ok bytes := compileSafe_of_producesBool p bytes hSafeb
  have hName : anfM.name ≠ "constructor" := of_decide_eq_true hNameb
  have hChain :
      Agrees.emittableArithChainReadyNoDblNeg
        (Lower.computeLastUses anfM.body) anfM.body
        (List.reverse (anfM.params.map (·.name))) 0 false :=
    (Agrees.emittableArithChainReadyNoDblNegBool_iff _ _ _ _ _).mp hChainb
  have hnd : (anfM.params.map ANFParam.name).Nodup := of_decide_eq_true hndb
  have hAllBigint : ∀ pr ∈ anfM.params, pr.type = ANFType.bigint :=
    hAllBigint_of_bool anfM hBigb
  -- membership is recovered from the single-public filter (not assumed).
  have hMem : anfM ∈ p.methods := by
    have hmem : anfM ∈ p.methods.filter (·.isPublic) := by
      rw [hSinglePublic]; exact List.mem_singleton_self anfM
    exact (List.mem_filter.mp hmem).1
  exact arith_consume_from_witness p hWF anfM bytes hMem hPub hSafe hSinglePublic
    hName hChain witness hnd hAllBigint

/-! ## Non-vacuity smoke

A concrete tiny stateless arith contract `Add3Sub`
(`add3sub(p2 p1 p0) = -((p0 + p1) - p2)`): three `.bigint` params and an
add / sub / unary-negate chain (no consecutive negates, so the
`noDblNeg` chain classifier admits it).  We show `arithFamilyReady` is
satisfied on it by `native_decide` against its own deployed bytes, then
fire `arith_family_verified` for a free `witness` — confirming the bundle
is genuinely satisfiable (NOT vacuously closed). -/

private def smokeArithProg : ANFProgram :=
  { contractName := "Add3Sub"
    properties := []
    methods :=
      [ { name := "add3sub"
          params := [ANFParam.mk "p2" .bigint, ANFParam.mk "p1" .bigint,
                     ANFParam.mk "p0" .bigint]
          body :=
            [⟨"t0", .binOp "+" "p0" "p1" none, none⟩,
             ⟨"t1", .binOp "-" "t0" "p2" none, none⟩,
             ⟨"t2", .unaryOp "-" "t1" none, none⟩]
          isPublic := true } ] }

private def smokeArithMethod : ANFMethod :=
  { name := "add3sub"
    params := [ANFParam.mk "p2" .bigint, ANFParam.mk "p1" .bigint,
               ANFParam.mk "p0" .bigint]
    body :=
      [⟨"t0", .binOp "+" "p0" "p1" none, none⟩,
       ⟨"t1", .binOp "-" "t0" "p2" none, none⟩,
       ⟨"t2", .unaryOp "-" "t1" none, none⟩]
    isPublic := true }

/-- The deployed bytes of the smoke program (`compileSafe` succeeds; the
`.error` arm is unreachable and never taken). -/
private def smokeArithBytes : ByteArray :=
  match compileSafe smokeArithProg with
  | .ok b => b
  | .error _ => ByteArray.empty

/-- **Smoke — the bundle is satisfiable.**  `arithFamilyReady` holds on the
concrete `Add3Sub` program against its own deployed bytes, decided by the
kernel-reflected `native_decide` (the `compileSafe` byte-equality conjunct
forces the full pipeline to run). -/
theorem smoke_arithFamilyReady :
    arithFamilyReady smokeArithProg smokeArithMethod smokeArithBytes = true := by
  native_decide

/-- The smoke program's single public method is `[smokeArithMethod]`.
Proved by `rfl` (no `DecidableEq ANFMethod`, so `decide` is unavailable). -/
private theorem smoke_filter :
    smokeArithProg.methods.filter (·.isPublic) = [smokeArithMethod] := by
  unfold smokeArithProg smokeArithMethod
  rfl

/-- **Smoke — `arith_family_verified` fires for the concrete program.**
The bundled discharge holds on `Add3Sub` for an arbitrary runtime
`witness`, so the bundle is non-vacuous. -/
theorem smoke_arith_family_verified (witness : List Value) :
    successAgrees
      (RunarVerification.ANF.Eval.evalBindingsP smokeArithProg.methods
        (mkEntryState smokeArithMethod.params [] witness) smokeArithMethod.body)
      (runParsedBytes smokeArithBytes (mkStackEntry smokeArithMethod.params [] witness)) :=
  arith_family_verified smokeArithProg smokeArithMethod smokeArithBytes
    smoke_arithFamilyReady smoke_filter witness

end RunarVerification.ANF.EntryDischarge
