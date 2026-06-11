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
| `omniDispatch` (MX)    | mixed dispatch consume, selector 0  | synthetic 2-method  |
| `omniP2pkh`            | crypto_call fallback sub-omnibus    | REAL `basic-p2pkh`  |

`omniP2pkh*` is a faithful Lean transcription of
`conformance/tests/basic-p2pkh/expected-ir.json`; `main` re-loads the
JSON golden at runtime and checks the transcription compiles to
byte-identical Script (see `checkP2pkhTranscription`).

## Honest notes (premise-shape findings)

1. **`statefulFull` cannot be instantiated through the omnibus.**  The
   widened stateful body (`statefulFullBody`) ends in `addOutput`, so
   `bodyEndsInAssert = false` and the keyed `hValueTruthy` premise goes
   LIVE — yet the statefulFull branch never consumes it (its consume
   theorem needs no truthiness), and it is NOT derivable from the keyed
   `hStatefulFullFrag` entry bundle: the spend-witness verdict
   (`checkPreimage`) is backend-opaque, and on a falsifying context the
   bytes run completes with a falsy top, making `hValueTruthy` FALSE.
   The stateful family is therefore instantiated here on the
   prologue-only fragment (assert-terminated ⇒ `hValueTruthy` vacuous).
   Suggested premise-shape fix (not taken here, to keep the omnibus
   signature stable): key `hValueTruthy` off the `statefulFull`
   classifier as well.

2. **The mixed-dispatch HASH-LOCK arm cannot be instantiated through
   the omnibus.**  `hUntag` pins `tsm` to the selected method's
   reversed params, and `hAgrees`+`hCoh` then force the SELECTED
   method's first param slot to resolve to the stack TOP — which for a
   dispatch entry is the `.vBigint` selector, while the hash-lock arm's
   keyed bundle (`hDispatchMixedFrag`) simultaneously forces the same
   name to resolve to the `.vBytes` argument.  `.vBigint _ = .vBytes _`
   is unsatisfiable, so only selector arms whose param value can
   coincide with the selector are instantiable (here: the passthrough
   arm at selector 0 with witness value 0).  The consume-theorem smokes
   are unaffected (they carry no `tsm`); the conflict is between the
   omnibus's GLOBAL alignment bundle and the selector-headed dispatch
   stack layout.

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
antecedent `… = false`). -/
theorem vacuousAssert {b : Bool} {P : Prop} (hb : b = true) : b = false → P :=
  fun hf => absurd hf (by simp [hb])

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
    (EntryModel.untagSm_mkTsm omniArithParams)                           -- hUntag
    (EntryModel.mkEntryState_entryBigintTyped_noProps _ _ _ (by decide)) -- hTypedEntry
    (fun _ => EntryModel.entryTsmArithTyped_mkEntry [] omniArithParams
      (by decide) (fun pr hpr => by
        simp only [omniArithParams, List.mem_cons, List.not_mem_nil, or_false] at hpr
        rcases hpr with h | h | h <;> subst h <;> rfl))                  -- hTsmTyped (LIVE)
    (by intro bn cond thn els src h; simp [omniArithMethod] at h)        -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (vacuous (by native_decide))                                         -- hHashAssertFrag
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (vacuous (by native_decide))                                         -- hStatefulFrag
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))     -- hValueTruthy (LIVE)
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
    rfl                                                                  -- hUntag
    omniCounter_entryBigintTyped                                         -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [omniCounterMethod, Agrees.updatePropConsumeBody] at h)     -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    omniCounter_updatePropFrag                                           -- hUpdatePropFrag (LIVE)
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (vacuous (by native_decide))                                         -- hHashAssertFrag
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (vacuous (by native_decide))                                         -- hStatefulFrag
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (fun _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))     -- hValueTruthy (LIVE)
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
    rfl                                                                  -- hUntag
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesHashCall.hashAssertSmokeMethod,
          AgreesHashCall.hashAssertBody] at h)                           -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (fun _ => ⟨"d", "ok", "a0", "x", "expected", "sha256",
      .byteString, .byteString, none, none, none,
      omniHashLockArgB, omniHashLockExpB, [],
      rfl, rfl, Or.inl rfl, by decide, rfl, rfl, rfl, by decide⟩)        -- hHashAssertFrag (LIVE)
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (vacuous (by native_decide))                                         -- hStatefulFrag
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (vacuousAssert (by native_decide))                                   -- hValueTruthy
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

noncomputable def omniStatefulSig : ByteArray :=
  Classical.choose
    (Stack.StatefulBridge.exists_checkSig_witness_under_validTxContext
      Stack.TxContext.sampleCtx Stack.ValidTxContext.sampleCtx_valid)

theorem omniStatefulSig_spec :
    RunarVerification.ANF.Eval.Crypto.authBackend.checkSig omniStatefulSig
        AgreesStateful.stG
      = RunarVerification.ANF.Eval.Crypto.checkPreimage omniStatefulPreimage :=
  Classical.choose_spec
    (Stack.StatefulBridge.exists_checkSig_witness_under_validTxContext
      Stack.TxContext.sampleCtx Stack.ValidTxContext.sampleCtx_valid)

noncomputable def omniStatefulStk : StackState :=
  { stack := [.vBytes omniStatefulPreimage, .vBytes omniStatefulSig] }

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
    rfl                                                                  -- hUntag
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h
        simp [AgreesStateful.smokeMethod,
          Stack.StatefulBridge.gatedStatefulPrologueBody,
          Stack.AgreesD2.statefulPrologueBody] at h)                     -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (vacuous (by native_decide))                                         -- hHashAssertFrag
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (fun _ => ⟨"pre", .byteString, Stack.TxContext.sampleCtx, omniStatefulSig,
      omniStatefulPreimage, [],
      rfl, rfl, by decide, by decide,
      Stack.ValidTxContext.sampleCtx_valid, rfl, rfl, rfl,
      omniStatefulSig_spec⟩)                                             -- hStatefulFrag (LIVE)
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (vacuousAssert (by native_decide))                                   -- hValueTruthy
    omniStateful_coh                                                     -- hCoh

/-! ## Fixture E — mixed dispatch family (`MX`, selector 0 / passthrough arm)

Two public methods: passthrough `ma(x) { t0 := x }` and the hash-lock
`unlock(expected, h)`.  Instantiated on selector 0.  The witness value
for `x` is `0` — the one value that lets the omnibus's global alignment
bundle (`hUntag`+`hAgrees`+`hCoh`, which pin `x`'s slot to the stack TOP
= the selector) coexist with the keyed dispatch bundle (see module
docstring, honest note 2). -/

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
    rfl                                                                  -- hUntag
    omniMxEnv_entryBigintTyped                                           -- hTypedEntry
    (fun _ => omniMx_wt)                                                 -- hTsmTyped
    (by intro bn cond thn els src h; simp [omniMxMa] at h)               -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (vacuous (by native_decide))                                         -- hHashAssertFrag
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (vacuous (by native_decide))                                         -- hStatefulFrag
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (fun _ => ⟨0, [.vBigint 7],
      (by rw [omniMx_filter]; rfl),                                      -- selector index
      rfl,                                                               -- witness-headed stack
      (fun _ => ⟨"x", "t0", .bigint, none, .vBigint 0, rfl, rfl, rfl⟩),  -- passthrough arm
      (vacuous (by native_decide))⟩)                                     -- hash-lock arm (vacuous)
    (fun _ => Stack.Eval.truthy_of_scriptAccepts (by native_decide))     -- hValueTruthy (LIVE)
    omniMx_coh                                                           -- hCoh

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
    rfl                                                                  -- hUntag
    (entryBigintTyped_empty _)                                           -- hTypedEntry
    (vacuousArith (by native_decide))                                    -- hTsmTyped
    (by intro bn cond thn els src h; simp [omniP2pkhUnlock] at h)        -- hIfValTyped
    (vacuous (by native_decide))                                         -- hMathByteFrag
    (vacuous (by native_decide))                                         -- hUpdatePropFrag
    (vacuous (by native_decide))                                         -- hMethodCallFrag
    (vacuous (by native_decide))                                         -- hHashCallFrag
    (vacuous (by native_decide))                                         -- hHashAssertFrag
    (vacuous (by native_decide))                                         -- hHashChainFrag
    (vacuous (by native_decide))                                         -- hStatefulFrag
    (vacuous (by native_decide))                                         -- hStatefulFullFrag
    (vacuous (by native_decide))                                         -- hDispatchFrag
    (vacuous (by native_decide))                                         -- hDispatchMixedFrag
    (vacuousAssert (by native_decide))                                   -- hValueTruthy
    omniP2pkh_coh                                                        -- hCoh

/-! ## Trust-footprint evidence (build-time) -/

#print axioms omnibus_instantiation_arith
#print axioms omnibus_instantiation_p2pkh

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
  IO.println "  omniDispatch   mixed dispatch consume (selector 0) synthetic (MX)"
  IO.println "  omniP2pkh      crypto_call fallback sub-omnibus    REAL basic-p2pkh golden"
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
