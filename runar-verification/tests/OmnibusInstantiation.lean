import RunarVerification

/-!
# Per-fixture OMNIBUS INSTANTIATION harness

`tests/PipelineConformance.lean` *classifies* conformance fixtures into
per-family `VERIFIED-modulo-*` tiers but never APPLIES the headline
omnibus theorem.  This module closes that gap: for a representative set
of fixtures — one per discharged family, plus a transcription of the
REAL `conformance/tests/basic-p2pkh` golden — it states and proves a
fully-applied instance of

  `Pipeline.compileSafe_observational_correct_modulo_codegen_axioms`

with **every premise discharged**:

* decidable premises (`hWF`, `hSafe`, `hNoLoop`, the classifier
  antecedents) by `native_decide` / `decide`;
* keyed premises whose Bool classifier is FALSE for the fixture
  *vacuously*, via the uniform `vacuous (by native_decide)` idiom;
* the fixture's OWN family's keyed premise with concrete witnesses
  (mirroring the corresponding consume-theorem smoke).

## Fixtures and families

| fixture                | family branch exercised             | source              |
|------------------------|-------------------------------------|---------------------|
| `omniArith`  (Add3Sub) | arith consume (wave 39)             | synthetic (add3sub) |
| `omniCounter` (inc)    | update_prop consume (wave 64)       | synthetic (counter) |
| `omniHashLock`         | crypto_call hash-then-assert (W1)   | synthetic hash-lock |
| `omniStateful`         | stateful consume (gated prologue)   | synthetic stateful  |
| `omniSf`               | statefulFull consume (widened)      | synthetic (SF)      |
| `omniDispatch` (MX)    | mixed dispatch consume, selector 0  | synthetic 2-method  |
| `omniMxHL`   (MX)      | mixed dispatch consume, selector 1  | synthetic 2-method  |
| `omniP2pkh`            | crypto_call fallback sub-omnibus    | REAL `basic-p2pkh`  |

`omniP2pkh*` is a faithful Lean transcription of
`conformance/tests/basic-p2pkh/expected-ir.json`; `main` re-loads the
JSON golden at runtime and checks the transcription compiles to
byte-identical Script (see `checkP2pkhTranscription`).

## Premise-shape findings — RESOLVED (2026-06-12 omnibus repair)

The first harness wiring (PR #77) surfaced two WRONG-SHAPED omnibus
premises; both are now fixed in `Pipeline.lean` and the two
previously-uninstantiable fragments are instantiated below:

1. **`statefulFull` (fixed by re-keying `hValueTruthy`).**  The widened
   stateful body ends in `addOutput` (`bodyEndsInAssert = false`), which
   made the keyed truthiness premise go LIVE although the statefulFull
   consume theorem never consumes it and the harness cannot discharge it
   mechanically: the run is gated on the OPAQUE `authBackend.checkSig`
   verdict (on a rejected witness the deployed bytes ABORT at
   `OP_CHECKSIGVERIFY` — they never complete with a falsy top; on an
   accepted witness the top is the NONEMPTY serialized output).
   `hValueTruthy` is now keyed off `statefulFullDischargedB p anfM =
   false`, exempting exactly the discharged path; see
   `omnibus_instantiation_statefulFull`.

2. **The mixed-dispatch HASH-LOCK arm (fixed by single-public-gating
   the alignment bundle).**  `hUntag` pinned `tsm` to the selected
   method's reversed params, so `hAgrees` forced the first param slot to
   the stack TOP — the `.vBigint` selector for a dispatch entry — while
   the keyed `hDispatchMixedFrag` bundle forced the same name to
   `.vBytes`: jointly unsatisfiable.  The METHOD-local entry-peel
   premises (`hHashAssertFrag` etc.) had the same flaw (their classifier
   fires on the hash-lock method, but their consequent pins a
   non-selector-headed stack).  `hUntag` and the five peel premises are
   now gated on `(p.methods.filter (·.isPublic)).length < 2`; dispatch
   instantiations pass `tsm := []` (whose `agreesTagged` carries only
   props/outputs equality); see
   `omnibus_instantiation_dispatchMixed_hashLock` (selector 1).

Run with `lake exe omnibusInstantiation`.
-/

open RunarVerification
open RunarVerification.ANF
open RunarVerification.ANF.Eval (Value State)
open RunarVerification.Stack
open RunarVerification.Stack.Eval (StackState)
open RunarVerification.Script
open RunarVerification.Pipeline
open RunarVerification.Pipeline.Soundness

namespace OmnibusInstantiation

/-! ## Uniform discharge helpers -/

/-- Vacuous discharge for a keyed premise whose Bool classifier is FALSE
for the fixture: `classifier = false` (decided by `native_decide`)
refutes the antecedent `classifier = true`. -/
theorem vacuous {b : Bool} {P : Prop} (hb : b = false) : b = true → P :=
  fun ht => absurd ht (by simp [hb])

/-- Vacuous discharge for the keyed truthiness premise on
assert-terminated bodies (`bodyEndsInAssert = true` refutes the
antecedent `… = false`) — and, post 2026-06-12 re-keying, for the whole
truthiness premise on the statefulFull discharged path
(`statefulFullDischargedB = true` refutes the antecedent `… = false`). -/
theorem vacuousAssert {b : Bool} {P : Prop} (hb : b = true) : b = false → P :=
  fun hf => absurd hf (by simp [hb])

/-- Vacuous discharge for a `Prop`-keyed premise whose antecedent is
refuted by `native_decide` — used for the single-public-gated alignment
and entry-peel premises on MULTI-public (dispatch) fixtures. -/
theorem vacuousOf {P Q : Prop} (hp : ¬P) : P → Q :=
  fun h => absurd h hp

/-- Vacuous discharge for the keyed arith typed-entry premise, through
the decidable mirror `emittableArithChainReadyNoDblNegBool`. -/
theorem vacuousArith {lastUses : List (String × Nat)} {body : List ANFBinding}
    {sm : Lower.StackMap} {ci : Nat} {pn : Bool} {Name P : Prop}
    (hb : Agrees.emittableArithChainReadyNoDblNegBool lastUses body sm ci pn = false) :
    (Name ∧ Agrees.emittableArithChainReadyNoDblNeg lastUses body sm ci pn) → P :=
  fun hc =>
    absurd ((Agrees.emittableArithChainReadyNoDblNegBool_iff lastUses body sm ci pn).mpr hc.2)
      (by simp [hb])

/-- `EntryBigintTyped` is vacuous over the EMPTY typing context (no name
is declared `.bigint`). -/
theorem entryBigintTyped_empty (st : State) :
    WellTyped.EntryBigintTyped Typed.TypeEnv.empty st :=
  fun _n hn => absurd hn (by simp [Typed.TypeEnv.lookup, Typed.TypeEnv.empty])

/-! ## Fixture A — arith family (`Add3Sub`, the wave-19/21 smoke shape)

`add3sub(p2, p1, p0) { t0 := p0 + p1; t1 := t0 - p2; t2 := -t1 }` —
single-public, value-terminated, emittable consume-arith chain.  Entry
states come from the type-directed `EntryModel` constructors (entry
predicates hold BY CONSTRUCTION); the concrete witness `p0=1, p1=2,
p2=0` makes the final value `-3` (truthy), dischargeable by
`native_decide` on the concrete run. -/

def omniArithParams : List ANFParam :=
  [ANFParam.mk "p2" .bigint, ANFParam.mk "p1" .bigint, ANFParam.mk "p0" .bigint]

def omniArithMethod : ANFMethod :=
  { name := "add3sub"
    params := omniArithParams
    body :=
      [⟨"t0", .binOp "+" "p0" "p1" none, none⟩,
       ⟨"t1", .binOp "-" "t0" "p2" none, none⟩,
       ⟨"t2", .unaryOp "-" "t1" none, none⟩]
    isPublic := true }

def omniArithProg : ANFProgram :=
  { contractName := "Add3Sub", properties := [], methods := [omniArithMethod] }

def omniArithBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniArithProg))

def omniArithWitness : List Value := [.vBigint 0, .vBigint 2, .vBigint 1]

def omniArithAnf : State := EntryModel.mkEntryState omniArithParams [] omniArithWitness
def omniArithStk : StackState := EntryModel.mkStackEntry omniArithParams [] omniArithWitness

/-- **Omnibus instantiation — arith family.** -/
theorem omnibus_instantiation_arith :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniArithProg.methods omniArithAnf
        omniArithMethod.body)
      (runParsedBytes omniArithBytes omniArithStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniArithProg
    (by native_decide)                                                   -- hWF
    omniArithMethod omniArithBytes
    (by unfold omniArithProg; simp)                                      -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniArithAnf omniArithStk
    (EntryModel.mkTsm omniArithParams)
    (EntryModel.agreesTagged_mkEntry _ _ _ (by decide))                  -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    (TypeCheck.TypeEnv.ofParamsProps [] omniArithParams)                 -- Γ
    (fun _ => EntryModel.untagSm_mkTsm omniArithParams)                  -- hUntag (single-public)
    (EntryModel.mkEntryState_entryBigintTyped_noProps _ _ _ (by decide)) -- hTypedEntry
    (fun _ => EntryModel.entryTsmArithTyped_mkEntry [] omniArithParams
      (by decide) (fun pr hpr => by
        simp only [omniArithParams, List.mem_cons, List.not_mem_nil, or_false] at hpr
        rcases hpr with h | h | h <;> subst h <;> rfl))                  -- hTsmTyped (LIVE)
    (by intro bn cond thn els src h; simp [omniArithMethod] at h)        -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))   -- hValueTruthy (LIVE)
    (EntryModel.tsmCoherent_mkEntry [] omniArithParams [] omniArithWitness
      (by decide))                                                       -- hCoh

/-! ## Fixture B — update_prop family (`Counter.inc`, the wave-63 smoke shape)

The canonical single-public `count + 1 ; update_prop count` increment. -/

def omniCounterMethod : ANFMethod :=
  { name := "inc"
    params := [ANFParam.mk "count" .bigint]
    body := Agrees.updatePropConsumeBody "count" "+" 1
    isPublic := true }

def omniCounterProg : ANFProgram :=
  { contractName := "Counter"
    properties := [ANFProperty.mk "count" .bigint false none]
    methods := [omniCounterMethod] }

def omniCounterEnv : Typed.TypeEnv := Typed.TypeEnv.empty.extend "count" .bigint
def omniCounterAnf : State := { props := [("count", .vBigint 5)] }
def omniCounterStk : StackState :=
  { stack := [.vBigint 5], props := [("count", .vBigint 5)] }
def omniCounterBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniCounterProg))
def omniCounterTsm : Agrees.TaggedStackMap := [("count", Agrees.SlotKind.prop)]

theorem omniCounter_entryBigintTyped :
    WellTyped.EntryBigintTyped omniCounterEnv omniCounterAnf := by
  intro nm hnm
  by_cases h : nm = "count"
  · subst h; exact ⟨.vBigint 5, rfl, ⟨5, rfl⟩⟩
  · exfalso
    have hc : ("count" == nm) = false := by
      rw [beq_eq_false_iff_ne]; exact fun hh => h hh.symm
    simp only [omniCounterEnv, Typed.TypeEnv.lookup, Typed.TypeEnv.extend,
      Typed.TypeEnv.empty, List.find?_cons, hc, List.find?_nil,
      Option.map_none, reduceCtorEq] at hnm

theorem omniCounter_agreesTagged :
    Agrees.agreesTagged omniCounterTsm omniCounterAnf omniCounterStk :=
  ⟨⟨rfl, trivial⟩, rfl, rfl⟩

theorem omniCounter_coh : Agrees.tsmCoherent omniCounterAnf omniCounterTsm := by
  intro s hs
  simp only [omniCounterTsm, List.mem_singleton] at hs
  subst hs; rfl

theorem omniCounter_wt : Agrees.entryTsmArithTyped omniCounterEnv omniCounterTsm := by
  intro s hs
  simp only [omniCounterTsm, List.mem_singleton] at hs
  subst hs
  show omniCounterEnv.lookup "count" = some .bigint
  decide

/-- The fixture's OWN keyed premise: the classifier-pinned body equality
recovers `prop = "count"`, after which the tsm equality is `rfl`. -/
theorem omniCounter_updatePropFrag :
    Agrees.updatePropConsumeShapeBool omniCounterMethod.body = true →
      ∀ (prop op : String) (c : Int),
        omniCounterMethod.body = Agrees.updatePropConsumeBody prop op c →
        omniCounterTsm = [(prop, Agrees.SlotKind.prop)] ∧
        Agrees.entryTsmArithTyped omniCounterEnv omniCounterTsm := by
  intro _ prop op c hEq
  simp only [omniCounterMethod, Agrees.updatePropConsumeBody, List.cons.injEq,
    ANFBinding.mk.injEq, and_true, true_and] at hEq
  have hprop : prop = "count" := by
    obtain ⟨h1, _⟩ := hEq
    simp_all
  subst hprop
  exact ⟨rfl, omniCounter_wt⟩

/-- **Omnibus instantiation — update_prop family.** -/
theorem omnibus_instantiation_updateProp :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniCounterProg.methods omniCounterAnf
        omniCounterMethod.body)
      (runParsedBytes omniCounterBytes omniCounterStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniCounterProg
    (by native_decide)                                                   -- hWF
    omniCounterMethod omniCounterBytes
    (by unfold omniCounterProg; simp)                                    -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniCounterAnf omniCounterStk
    omniCounterTsm
    omniCounter_agreesTagged                                             -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    omniCounterEnv                                                       -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    omniCounter_entryBigintTyped                                         -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [omniCounterMethod, Agrees.updatePropConsumeBody] at h)     -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    omniCounter_updatePropFrag                                           -- hUpdatePropFrag (LIVE)
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))   -- hValueTruthy (LIVE)
    omniCounter_coh                                                      -- hCoh

/-! ## Fixture C — crypto_call hash-then-assert family (production hash-lock)

`unlock(expected, x) { d := sha256(x); ok := (d === expected); assert ok }`
(`AgreesHashCall.hashAssertSmokeMethod`).  Assert-terminated, so the
truthiness premise is vacuous; the acceptance bits agree SYMBOLICALLY
(the digest comparison verdict is backend-opaque on both sides). -/

def omniHashLockProg : ANFProgram :=
  { contractName := "HL", properties := [],
    methods := [AgreesHashCall.hashAssertSmokeMethod] }

def omniHashLockArgB : ByteArray := ByteArray.mk #[1, 2, 3]
def omniHashLockExpB : ByteArray := ByteArray.mk #[4, 5]

def omniHashLockAnf : State :=
  { params := [("expected", .vBytes omniHashLockExpB), ("x", .vBytes omniHashLockArgB)] }

def omniHashLockStk : StackState :=
  { stack := [.vBytes omniHashLockArgB, .vBytes omniHashLockExpB] }

def omniHashLockBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniHashLockProg))

def omniHashLockTsm : Agrees.TaggedStackMap :=
  [("x", Agrees.SlotKind.param), ("expected", Agrees.SlotKind.param)]

theorem omniHashLock_coh :
    Agrees.tsmCoherent omniHashLockAnf omniHashLockTsm := by
  intro s hs
  simp only [omniHashLockTsm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h <;> subst h <;> rfl

/-- **Omnibus instantiation — crypto_call hash-then-assert family.** -/
theorem omnibus_instantiation_hashLock :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniHashLockProg.methods omniHashLockAnf
        AgreesHashCall.hashAssertSmokeMethod.body)
      (runParsedBytes omniHashLockBytes omniHashLockStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniHashLockProg
    (by native_decide)                                                   -- hWF
    AgreesHashCall.hashAssertSmokeMethod omniHashLockBytes
    (by unfold omniHashLockProg; simp)                                   -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniHashLockAnf omniHashLockStk
    omniHashLockTsm
    ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩                                      -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesHashCall.hashAssertSmokeMethod,
          AgreesHashCall.hashAssertBody] at h)                           -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ _ => ⟨"d", "ok", "a0", "x", "expected", "sha256",
      .byteString, .byteString, none, none, none,
      omniHashLockArgB, omniHashLockExpB, [],
      rfl, rfl, Or.inl rfl, by decide, rfl, rfl, rfl, by decide⟩)        -- hHashAssertFrag (LIVE)
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ => vacuousAssert (by native_decide))                          -- hValueTruthy
    omniHashLock_coh                                                     -- hCoh

/-! ## Fixture D — stateful family (gated prologue, `AgreesStateful.smokeMethod`)

`verify(pre) { _opPushTxSig …; _cp0 := check_preimage pre; assert _cp0 }`
on the sample BIP-143 context; the spend witness signature comes from the
existence axiom via `Classical.choose` (exactly as the consume-theorem
smoke).  Assert-terminated ⇒ truthiness vacuous.  See module docstring,
honest note 1, for why the WIDENED `statefulFull` fragment is NOT
instantiable through the omnibus. -/

def omniStatefulProg : ANFProgram :=
  { contractName := "ST", properties := [],
    methods := [AgreesStateful.smokeMethod] }

def omniStatefulPreimage : ByteArray :=
  Stack.TxContext.buildPreimage Stack.TxContext.sampleCtx

def omniStatefulAnf : State := { params := [("pre", .vBytes omniStatefulPreimage)] }

-- BUG-100: no spender-witness signature; the deployed stack carries only the
-- preimage. The binding is enforced by the on-chain OP_PUSH_TX blob.
def omniStatefulStk : StackState :=
  { stack := [.vBytes omniStatefulPreimage] }

def omniStatefulBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniStatefulProg))

def omniStatefulTsm : Agrees.TaggedStackMap := [("pre", Agrees.SlotKind.param)]

theorem omniStateful_coh :
    Agrees.tsmCoherent omniStatefulAnf omniStatefulTsm := by
  intro s hs
  simp only [omniStatefulTsm, List.mem_singleton] at hs
  subst hs; rfl

/-- **Omnibus instantiation — stateful family (gated prologue).** -/
theorem omnibus_instantiation_stateful :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniStatefulProg.methods omniStatefulAnf
        AgreesStateful.smokeMethod.body)
      (runParsedBytes omniStatefulBytes omniStatefulStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniStatefulProg
    (by native_decide)                                                   -- hWF
    AgreesStateful.smokeMethod omniStatefulBytes
    (by unfold omniStatefulProg; simp)                                   -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniStatefulAnf omniStatefulStk
    omniStatefulTsm
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩                                           -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesStateful.smokeMethod,
          Stack.StatefulBridge.gatedStatefulPrologueBody,
          Stack.AgreesD2.statefulPrologueBody] at h)                     -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ _ => ⟨"pre", .byteString, Stack.TxContext.sampleCtx,
      omniStatefulPreimage, [],
      rfl, rfl, by decide,
      Stack.ValidTxContext.sampleCtx_valid, rfl, rfl, rfl⟩)              -- hStatefulFrag (LIVE)
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ => vacuousAssert (by native_decide))                          -- hValueTruthy
    omniStateful_coh                                                     -- hCoh

/-! ## Fixture D' — WIDENED stateful family (prologue + state-output epilogue)

`verify(sats, stateVal, pre)` with the composed
`check_preimage ; assert ; add_output` body on the sample BIP-143
context (`AgreesStateful.smokeFullMethod`; witnesses mirror
`smoke_statefulFull_consume_fires`).  The body ends in `addOutput`
(`bodyEndsInAssert = false`), but the re-keyed `hValueTruthy` premise is
EXEMPT on the discharged statefulFull path (`statefulFullDischargedB =
true` refutes its antecedent): the deployed bytes either ABORT at
`OP_CHECKSIGVERIFY` (rejected witness) or complete with the NONEMPTY
serialized output on top — no truthiness obligation reaches the
harness.  Previously NOT instantiable (module docstring, finding 1). -/

def omniSfProg : ANFProgram :=
  { contractName := "SF",
    properties := AgreesStateful.smokeFullProps,
    methods := [AgreesStateful.smokeFullMethod] }

def omniSfPreimage : ByteArray :=
  Stack.TxContext.buildPreimage Stack.TxContext.sampleCtx

def omniSfAnf : State :=
  { params := [("sats", .vBigint 1000), ("stateVal", .vBigint 7),
               ("pre", .vBytes omniSfPreimage)] }

def omniSfCp : ByteArray := ByteArray.mk #[0xAA, 0xBB, 0xCC]

-- BUG-100: no spender-witness signature; the deployed stack carries the
-- preimage, state value, satoshis, and code part (no witness).
def omniSfStk : StackState :=
  { stack := [.vBytes omniSfPreimage, .vBigint 7, .vBigint 1000,
              .vBytes omniSfCp] }

def omniSfBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniSfProg))

def omniSfTsm : Agrees.TaggedStackMap :=
  [("pre", Agrees.SlotKind.param), ("stateVal", Agrees.SlotKind.param),
   ("sats", Agrees.SlotKind.param)]

theorem omniSf_coh : Agrees.tsmCoherent omniSfAnf omniSfTsm := by
  intro s hs
  simp only [omniSfTsm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h <;> subst h <;> rfl

/-- **Omnibus instantiation — WIDENED stateful family (statefulFull).** -/
theorem omnibus_instantiation_statefulFull :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniSfProg.methods omniSfAnf
        AgreesStateful.smokeFullMethod.body)
      (runParsedBytes omniSfBytes omniSfStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniSfProg
    (by native_decide)                                                   -- hWF
    AgreesStateful.smokeFullMethod omniSfBytes
    (by unfold omniSfProg; simp)                                         -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniSfAnf omniSfStk
    omniSfTsm
    ⟨⟨rfl, rfl, rfl, trivial⟩, rfl, rfl⟩                                 -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesStateful.smokeFullMethod, AgreesStateful.statefulFullBody,
          Stack.StatefulBridge.gatedStatefulPrologueBody,
          Stack.AgreesD2.statefulPrologueBody,
          Stack.AgreesD2.statefulEpilogueBody] at h)                     -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ _ => ⟨"pre", "sats", "stateVal", "count", .bigint, .bigint,
      .byteString, Stack.TxContext.sampleCtx, omniSfPreimage, omniSfCp,
      7, 1000, [],
      rfl, rfl, rfl, by native_decide,
      Stack.ValidTxContext.sampleCtx_valid, rfl, rfl, rfl, rfl, rfl⟩)     -- hStatefulFullFrag (LIVE)
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (vacuousAssert (by native_decide))                                   -- hValueTruthy (EXEMPT path)
    omniSf_coh                                                           -- hCoh

/-! ## Fixture E — mixed dispatch family (`MX`, selector 0 / passthrough arm)

Two public methods: passthrough `ma(x) { t0 := x }` and the hash-lock
`unlock(expected, h)`.  Instantiated on selector 0.  Post the 2026-06-12
premise-shape repair `hUntag` is single-public-gated (vacuous here), so
the witness value for `x` is no longer forced to coincide with the
selector; the fixture keeps `x = 0` and its original `tsm` for
continuity (the gated `hUntag` is still satisfiable as supplied).  The
previously-uninstantiable selector-1 hash-lock arm is Fixture E' below. -/

def omniMxMa : ANFMethod :=
  { name := "ma", params := [ANFParam.mk "x" .bigint],
    body := [ANFBinding.mk "t0" (.loadParam "x") none], isPublic := true }

def omniMxUnlock : ANFMethod :=
  { name := "unlock"
    params := [ANFParam.mk "expected" .byteString, ANFParam.mk "h" .byteString]
    body := AgreesHashCall.hashAssertBody "d" "ok" "a0" "h" "expected" "sha256"
      none none none
    isPublic := true }

def omniMxProg : ANFProgram :=
  { contractName := "MX", properties := [], methods := [omniMxMa, omniMxUnlock] }

def omniMxAnf : State := { params := [("x", .vBigint 0)] }
def omniMxStk : StackState := { stack := [.vBigint 0, .vBigint 7] }
def omniMxBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniMxProg))
def omniMxTsm : Agrees.TaggedStackMap := [("x", Agrees.SlotKind.param)]

theorem omniMxEnv_entryBigintTyped :
    WellTyped.EntryBigintTyped (Typed.TypeEnv.empty.extend "x" .bigint) omniMxAnf := by
  intro nm hnm
  by_cases h : nm = "x"
  · subst h; exact ⟨.vBigint 0, rfl, ⟨0, rfl⟩⟩
  · exfalso
    have hc : ("x" == nm) = false := by
      rw [beq_eq_false_iff_ne]; exact fun hh => h hh.symm
    simp only [Typed.TypeEnv.lookup, Typed.TypeEnv.extend, Typed.TypeEnv.empty,
      List.find?_cons, hc, List.find?_nil, Option.map_none, reduceCtorEq] at hnm

theorem omniMx_coh : Agrees.tsmCoherent omniMxAnf omniMxTsm := by
  intro s hs
  simp only [omniMxTsm, List.mem_singleton] at hs
  subst hs; rfl

theorem omniMx_wt :
    Agrees.entryTsmArithTyped (Typed.TypeEnv.empty.extend "x" .bigint) omniMxTsm := by
  intro s hs
  simp only [omniMxTsm, List.mem_singleton] at hs
  subst hs
  show (Typed.TypeEnv.empty.extend "x" .bigint).lookup "x" = some .bigint
  decide

theorem omniMx_filter :
    omniMxProg.methods.filter (·.isPublic) = [omniMxMa, omniMxUnlock] := rfl

/-- **Omnibus instantiation — mixed dispatch family (selector 0).** -/
theorem omnibus_instantiation_dispatchMixed :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniMxProg.methods omniMxAnf
        omniMxMa.body)
      (runParsedBytes omniMxBytes omniMxStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniMxProg
    (by native_decide)                                                   -- hWF
    omniMxMa omniMxBytes
    (by unfold omniMxProg; simp)                                         -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniMxAnf omniMxStk
    omniMxTsm
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩                                           -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    (Typed.TypeEnv.empty.extend "x" .bigint)                             -- Γ
    (fun _ => rfl)                                                       -- hUntag (gate false; still satisfiable)
    omniMxEnv_entryBigintTyped                                           -- hTypedEntry
    (fun _ => omniMx_wt)                                                 -- hTsmTyped
    (by intro bn cond thn els src h; simp [omniMxMa] at h)               -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuousOf (by native_decide))                                       -- hHashCallFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hHashAssertFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hHashChainFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hStatefulFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hStatefulFullFrag (multi-public)
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (fun _ => ⟨0, [.vBigint 7],
      (by rw [omniMx_filter]; rfl),                                      -- selector index
      rfl,                                                               -- witness-headed stack
      (fun _ => ⟨"x", "t0", .bigint, none, .vBigint 0, rfl, rfl, rfl⟩),  -- passthrough arm
      (vacuous (by native_decide))⟩)                                     -- hash-lock arm (vacuous)
    (fun _ _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))   -- hValueTruthy (LIVE)
    omniMx_coh                                                           -- hCoh

/-! ## Fixture E' — mixed dispatch family (`MX`, selector 1 / HASH-LOCK arm)

The previously-unsatisfiable arm (module docstring, finding 2): selector
`1` selects `unlock(expected, h)`, whose keyed dispatch bundle pins the
witness stack to `selector :: vBytes h :: vBytes expected`.  With
`hUntag` and the method-local entry-peel premises single-public-gated,
the harness passes `tsm := []` (its `agreesTagged` carries only
props/outputs equality) and discharges the gated premises vacuously —
including `hHashAssertFrag`, whose method-local classifier DOES fire on
`unlock` but whose consequent pins a non-selector-headed stack. -/

def omniMxArgB : ByteArray := ByteArray.mk #[1, 2, 3]
def omniMxExpB : ByteArray := ByteArray.mk #[4, 5]

def omniMxHLAnf : State :=
  { params := [("expected", .vBytes omniMxExpB), ("h", .vBytes omniMxArgB)] }

def omniMxHLStk : StackState :=
  { stack := [.vBigint 1, .vBytes omniMxArgB, .vBytes omniMxExpB] }

/-- **Omnibus instantiation — mixed dispatch family (selector 1, hash-lock).** -/
theorem omnibus_instantiation_dispatchMixed_hashLock :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniMxProg.methods omniMxHLAnf
        omniMxUnlock.body)
      (runParsedBytes omniMxBytes omniMxHLStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniMxProg
    (by native_decide)                                                   -- hWF
    omniMxUnlock omniMxBytes
    (by unfold omniMxProg; simp)                                         -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniMxHLAnf omniMxHLStk
    []                                                                   -- tsm (free for dispatch)
    ⟨trivial, rfl, rfl⟩                                                  -- hAgrees (empty tsm)
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (vacuousOf (by native_decide))                                       -- hUntag (multi-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [omniMxUnlock, AgreesHashCall.hashAssertBody] at h)         -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuousOf (by native_decide))                                       -- hHashCallFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hHashAssertFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hHashChainFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hStatefulFrag (multi-public)
    (vacuousOf (by native_decide))                                       -- hStatefulFullFrag (multi-public)
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (fun _ => ⟨1, [.vBytes omniMxArgB, .vBytes omniMxExpB],
      (by rw [omniMx_filter]; rfl),                                      -- selector index
      rfl,                                                               -- witness-headed stack
      (vacuous (by native_decide)),                                      -- passthrough arm (vacuous)
      (fun _ => ⟨"d", "ok", "a0", "h", "expected", "sha256", .byteString,
        .byteString, none, none, none, omniMxArgB, omniMxExpB, [],
        rfl, rfl, Or.inl rfl, by decide, rfl, rfl, rfl,
        by decide⟩)⟩)                                                    -- hash-lock arm (LIVE)
    (fun _ => vacuousAssert (by native_decide))                          -- hValueTruthy
    (by intro s hs; simp at hs)                                          -- hCoh (empty tsm)

/-! ## Fixture F — REAL conformance fixture `basic-p2pkh` (crypto_call fallback)

Faithful Lean transcription of
`conformance/tests/basic-p2pkh/expected-ir.json` (constructor + public
`unlock(sig, pubKey)` with `hash160`-equality and `checkSig` asserts).
Every keyed classifier is FALSE for this body, so every keyed premise is
discharged VACUOUSLY and the conclusion flows through the `crypto_call`
sub-omnibus axiom — this is exactly the
`VERIFIED-modulo-crypto-call-codegen-axioms` tier of
`tests/PipelineConformance.lean`, now realized as an actual theorem
application per fixture.  `main` re-loads the JSON golden and checks the
transcription compiles to byte-identical Script. -/

def omniP2pkhConstructor : ANFMethod :=
  { name := "constructor"
    params := [ANFParam.mk "pubKeyHash" .addr]
    body :=
      [⟨"t0", .loadProp "pubKeyHash", none⟩,
       ⟨"t1", .call "super" ["t0"], none⟩,
       ⟨"t2", .loadProp "pubKeyHash", none⟩,
       ⟨"t3", .updateProp "pubKeyHash" "t2", none⟩]
    isPublic := false }

def omniP2pkhUnlock : ANFMethod :=
  { name := "unlock"
    params := [ANFParam.mk "sig" .sig, ANFParam.mk "pubKey" .pubKey]
    body :=
      [⟨"t0", .loadParam "pubKey", none⟩,
       ⟨"t1", .call "hash160" ["t0"], none⟩,
       ⟨"t2", .loadProp "pubKeyHash", none⟩,
       ⟨"t3", .binOp "===" "t1" "t2" (some "bytes"), none⟩,
       ⟨"t4", .assert "t3", none⟩,
       ⟨"t5", .loadParam "sig", none⟩,
       ⟨"t6", .loadParam "pubKey", none⟩,
       ⟨"t7", .call "checkSig" ["t5", "t6"], none⟩,
       ⟨"t8", .assert "t7", none⟩]
    isPublic := true }

def omniP2pkhProg : ANFProgram :=
  { contractName := "P2PKH"
    properties := [ANFProperty.mk "pubKeyHash" .addr true none]
    methods := [omniP2pkhConstructor, omniP2pkhUnlock] }

def omniP2pkhSigB : ByteArray := ByteArray.mk #[0x30, 0x01]
def omniP2pkhPkB : ByteArray := ByteArray.mk #[0x02, 0x03]
def omniP2pkhPhB : ByteArray := ByteArray.mk #[0x09]

def omniP2pkhAnf : State :=
  { params := [("sig", .vBytes omniP2pkhSigB), ("pubKey", .vBytes omniP2pkhPkB)]
    props := [("pubKeyHash", .vBytes omniP2pkhPhB)] }

def omniP2pkhStk : StackState :=
  { stack := [.vBytes omniP2pkhPkB, .vBytes omniP2pkhSigB]
    props := [("pubKeyHash", .vBytes omniP2pkhPhB)] }

def omniP2pkhBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniP2pkhProg))

def omniP2pkhTsm : Agrees.TaggedStackMap :=
  [("pubKey", Agrees.SlotKind.param), ("sig", Agrees.SlotKind.param)]

theorem omniP2pkh_coh : Agrees.tsmCoherent omniP2pkhAnf omniP2pkhTsm := by
  intro s hs
  simp only [omniP2pkhTsm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h <;> subst h <;> rfl

/-- **Omnibus instantiation — the REAL `basic-p2pkh` conformance golden.** -/
theorem omnibus_instantiation_p2pkh :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniP2pkhProg.methods omniP2pkhAnf
        omniP2pkhUnlock.body)
      (runParsedBytes omniP2pkhBytes omniP2pkhStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniP2pkhProg
    (by native_decide)                                                   -- hWF
    omniP2pkhUnlock omniP2pkhBytes
    (by unfold omniP2pkhProg; simp)                                      -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniP2pkhAnf omniP2pkhStk
    omniP2pkhTsm
    ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩                                      -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h; simp [omniP2pkhUnlock] at h)        -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ => vacuous (by native_decide))                                -- hMathByteCatFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ => vacuousAssert (by native_decide))                          -- hValueTruthy
    omniP2pkh_coh                                                        -- hCoh

/-! ## Fixture H — math_byte-WIDENED 2-arg `cat` family (`AgreesCat.smokeMethod`)

`f(a, b) { d := cat(a, b) }` on concrete two-bytes entry (`a ↦ #[01,02]`,
`b ↦ #[03]`, the deployed stack carrying them as `b` over `a`).  Value-
terminated (the concatenation lands on top), so the truthiness premise is
LIVE; the concatenated result `#[01,02,03]` is nonempty ⇒ truthy by
`truthy_of_scriptAccepts` on the concrete run.  This is the only LIVE
instantiation that drives the new `hMathByteCatFrag` consume arm of the
omnibus dispatch end-to-end. -/

def omniCatProg : ANFProgram :=
  { contractName := "C", properties := [],
    methods := [AgreesCat.smokeMethod] }

def omniCatAB : ByteArray := ByteArray.mk #[1, 2]
def omniCatBB : ByteArray := ByteArray.mk #[3]

def omniCatAnf : State :=
  { params := [("b", .vBytes omniCatBB), ("a", .vBytes omniCatAB)] }

def omniCatStk : StackState :=
  { stack := [.vBytes omniCatBB, .vBytes omniCatAB] }

def omniCatBytes : ByteArray :=
  Emit.emitFast (peepholeProgram (Lower.lower omniCatProg))

def omniCatTsm : Agrees.TaggedStackMap :=
  [("b", Agrees.SlotKind.param), ("a", Agrees.SlotKind.param)]

theorem omniCat_coh : Agrees.tsmCoherent omniCatAnf omniCatTsm := by
  intro s hs
  simp only [omniCatTsm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h <;> subst h <;> rfl

/-- **Omnibus instantiation — math_byte-WIDENED 2-arg `cat` family.** -/
theorem omnibus_instantiation_cat :
    Stack.Eval.acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP omniCatProg.methods omniCatAnf
        AgreesCat.smokeMethod.body)
      (runParsedBytes omniCatBytes omniCatStk) :=
  compileSafe_observational_correct_modulo_codegen_axioms
    omniCatProg
    (by native_decide)                                                   -- hWF
    AgreesCat.smokeMethod omniCatBytes
    (by unfold omniCatProg; simp)                                        -- hMem
    rfl                                                                  -- hPublic
    (EntryDischarge.compileSafe_of_producesBool _ _ (by native_decide))  -- hSafe
    omniCatAnf omniCatStk
    omniCatTsm
    ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩                                      -- hAgrees
    (by native_decide)                                                   -- hNoLoop
    Typed.TypeEnv.empty                                                  -- Γ
    (fun _ => rfl)                                                       -- hUntag (single-public)
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesCat.smokeMethod] at h)                               -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (fun _ _ => ⟨"d", "a", "b", none, omniCatAB, omniCatBB, [],
      rfl, rfl, by decide, rfl, rfl, rfl⟩)                              -- hMathByteCatFrag (LIVE)
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashCallFrag
    (fun _ => vacuous (by native_decide))                                -- hHashAssertFrag
    (fun _ => vacuous (by native_decide))                                -- hHashChainFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFrag
    (fun _ => vacuous (by native_decide))                                -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))   -- hValueTruthy (LIVE)
    omniCat_coh                                                          -- hCoh

/-! ## Trust-footprint evidence (build-time, human-readable) -/

#print axioms omnibus_instantiation_arith
#print axioms omnibus_instantiation_p2pkh
#print axioms omnibus_instantiation_statefulFull
#print axioms omnibus_instantiation_dispatchMixed_hashLock
#print axioms omnibus_instantiation_cat

/-! ## Trust-boundary GATE (PROVE-001, build-enforced)

`#audit_axioms` (`RunarVerification/AxiomAuditCmd.lean`) **fails the build** if
any of these fully-applied omnibus instantiations depends on `sorryAx` or on an
axiom outside the documented v1 trust base; it logs each one's `native_decide`
exposure. Unlike the `#print axioms` lines above (diagnostic only), these are
enforced — a regression or an undisclosed new axiom turns the build red. Covers
all nine discharged-fragment instantiations. -/

#audit_axioms omnibus_instantiation_arith
#audit_axioms omnibus_instantiation_updateProp
#audit_axioms omnibus_instantiation_hashLock
#audit_axioms omnibus_instantiation_stateful
#audit_axioms omnibus_instantiation_statefulFull
#audit_axioms omnibus_instantiation_dispatchMixed
#audit_axioms omnibus_instantiation_dispatchMixed_hashLock
#audit_axioms omnibus_instantiation_p2pkh
#audit_axioms omnibus_instantiation_cat

end OmnibusInstantiation

/-! ## Runtime harness -/

open OmnibusInstantiation in
/-- Check the `omniP2pkhProg` transcription against the on-disk golden:
the loaded `expected-ir.json` must compile (`compileSafe`) to bytes
IDENTICAL to the transcription's. -/
def checkP2pkhTranscription : IO Bool := do
  let path : System.FilePath :=
    ".." / "conformance" / "tests" / "basic-p2pkh" / "expected-ir.json"
  let src ← IO.FS.readFile path
  match RunarVerification.ANF.ANFProgram.fromString src with
  | .error e =>
      IO.eprintln s!"  basic-p2pkh: golden failed to parse: {e}"
      return false
  | .ok loaded =>
      if loaded.contractName ≠ omniP2pkhProg.contractName then
        IO.eprintln "  basic-p2pkh: contract name mismatch"
        return false
      match RunarVerification.Pipeline.compileSafe loaded,
            RunarVerification.Pipeline.compileSafe omniP2pkhProg with
      | .ok lb, .ok tb =>
          if lb = tb then
            IO.println s!"  basic-p2pkh: transcription compiles byte-identical ({lb.size} bytes)"
            return true
          else
            IO.eprintln "  basic-p2pkh: transcription bytes DIVERGE from golden"
            return false
      | _, _ =>
          IO.eprintln "  basic-p2pkh: compileSafe failed"
          return false

def main : IO UInt32 := do
  IO.println "OmnibusInstantiation: per-fixture omnibus theorem applications"
  IO.println ""
  IO.println "  fixture        family branch                       source"
  IO.println "  -------        -------------                       ------"
  IO.println "  omniArith      arith consume                       synthetic (add3sub)"
  IO.println "  omniCounter    update_prop consume                 synthetic (counter inc)"
  IO.println "  omniHashLock   crypto_call hash-then-assert        synthetic (hash-lock)"
  IO.println "  omniStateful   stateful consume (gated prologue)   synthetic (stateful)"
  IO.println "  omniSf         statefulFull consume (widened)      synthetic (SF)"
  IO.println "  omniDispatch   mixed dispatch consume (selector 0) synthetic (MX)"
  IO.println "  omniMxHL       mixed dispatch consume (selector 1) synthetic (MX hash-lock)"
  IO.println "  omniP2pkh      crypto_call fallback sub-omnibus    REAL basic-p2pkh golden"
  IO.println "  omniCat        math_byte 2-arg cat consume         synthetic (cat(a,b))"
  IO.println ""
  IO.println "Each row is a zero-sorry theorem `omnibus_instantiation_*` applying"
  IO.println "`compileSafe_observational_correct_modulo_codegen_axioms` with all"
  IO.println "premises discharged (vacuous keyed premises via native_decide on the"
  IO.println "per-family Bool classifiers)."
  IO.println ""
  IO.println "Transcription fidelity check:"
  let ok ← checkP2pkhTranscription
  if ok then
    IO.println ""
    IO.println "OmnibusInstantiation: OK"
    return 0
  else
    return 1
