import RunarVerification.ANF.Syntax
import RunarVerification.ANF.Eval
import RunarVerification.ANF.Typed
import RunarVerification.ANF.TypeCheck
import RunarVerification.Stack.Agrees

/-!
# ANF IR — Type-fidelity for the emittable-arith fragment (Wave 34)

This module closes the `.vBool`-operand divergence that wave 33 flagged as
the real blocker for retiring the arith sub-omnibus axiom
(`compileSafe_observational_correct_modulo_arith_codegen`).

## The wave-33 finding (restated)

For an `emittableArithChainReady` body, the arith sub-omnibus's conclusion
`successAgrees (evalBindings initialAnf body) (runParsedBytes bytes initialStack)`
is FALSE on a `.vBool`-operand input, because:

* ANF `evalBinOp "+"` has no `.vBool` arm → `.error` → `isNone`
  (`ANF/Eval.lean:191`);
* the Script VM coerces `asInt? (.vBool b) = some (if b then 1 else 0)`
  (`Stack/Eval.lean`), so `OP_ADD` succeeds → `isSome`.

Nothing structural excludes `.vBool`: `emittableArithChainReady` is
depth/last-use only, `agreesTagged` only equates the two sides' *values*,
and `WF.ANF` is purely structural (SSA / scope / name-uniqueness, no
types).  The real Runar type-checker (`03-typecheck.ts:904-922`) rejects
`bool + int` — both operands of an arith op must be `isBigintFamily` — but
`WF.ANF` does not model that.

## What this module adds (ADD-ONLY)

* `Value.IsBigint` — the runtime-value side of "is a bigint".
* `Value.isBigint_iff_not_vBool_not_others` — bridges `IsBigint` to the
  exact `hNonBool` / head-bigint shapes the wave-30 failure step and the
  wave-32 success step consume.
* `EntryBigintTyped Γ anfSt` — the **typed-entry** hypothesis: every name
  the typing context `Γ` declares `.bigint` resolves, in the runtime ANF
  state `anfSt`, to a `.vBigint` value.  This is the framework bridge
  between a declared param/temp type and its runtime value tag.  It is the
  analogue of wave-25's `agreesTagged` premise: a fact about method entry
  that the omnibus must be GIVEN, not derived (see the design note below).
* `arithOperandBigint Γ ref` — the structural arith-rule predicate: a
  single operand `ref` is declared `.bigint` in `Γ` (mirrors the
  type-checker's `isBigintFamily(leftType/rightType)` arith check).
* the soundness lemmas (Deliverable B): typed-entry + structural-typed
  operand ⇒ the operand's runtime value is `.vBigint`, hence non-`.vBool`.

## Design note (Q-c) — typed-entry is a NEW premise, not derivable

`agreesTagged` pins the SAME `ANF.Eval.Value` on the ANF and stack sides;
it carries no type tag distinct from the value itself.  `WF.ANF` is
structural.  A purely structural well-typed predicate on the body can
state "operand `l` is a param declared `bigint`" (`arithOperandBigint`),
but it CANNOT constrain the *runtime* value `anfSt.resolveRef l` to be
`.vBigint`: the omnibus quantifies `initialAnf` freely, so a param's
runtime value is unconstrained by any structural/`agreesTagged`/`WF` fact.
The declared-type ⇒ runtime-value-tag link is exactly `EntryBigintTyped`,
which must be supplied as a hypothesis.  Prior-arith-temp operands ARE
derivable (their producing op returns a bigint — the wave-32 success
lockstep already establishes this), so the new premise is only needed for
the *entry* operands (params / props), matching `taggedAllBigint`'s role
as an input to the success capstone.
-/

namespace RunarVerification.ANF
namespace WellTyped

open RunarVerification.ANF.Eval (Value State)

/-! ## Runtime-value bigint-ness -/

/-- A runtime value is a bigint. -/
def Value.IsBigint (v : Value) : Prop := ∃ i : Int, v = .vBigint i

/-- A bigint value is not a bool. -/
theorem Value.IsBigint.not_vBool {v : Value} (h : Value.IsBigint v) :
    ∀ b : Bool, v ≠ .vBool b := by
  obtain ⟨i, hi⟩ := h
  intro b hEq
  rw [hi] at hEq
  exact absurd hEq (by simp)

/-- A bigint value is `.vBigint` of some explicit `Int`. -/
theorem Value.IsBigint.exists_int {v : Value} (h : Value.IsBigint v) :
    ∃ i : Int, v = .vBigint i := h

/-- Decision-shape: a value is either `IsBigint` or it is `.vBool`/other.
The wave-30 failure step needs `hNonBool` on a value already known
non-bigint; this lemma says a value KNOWN bigint discharges `hNonBool`
unconditionally (it is never a bool). -/
theorem nonBool_of_isBigint {v : Value} (h : Value.IsBigint v) :
    ∀ b : Bool, v ≠ .vBool b :=
  h.not_vBool

/-! ## Typed-entry hypothesis (the framework bridge)

`EntryBigintTyped Γ anfSt` says: every name `Γ` declares at `.bigint`
resolves to a `.vBigint` runtime value in `anfSt`.  This is the
declared-type ⇒ runtime-value-tag bridge that `agreesTagged` and `WF`
cannot supply.  In a real method dispatch the VM decodes a `bigint`
parameter as a `.vBigint` Value, which is exactly this property at entry.
-/

/-- Typing context type: reuse the existing `Typed.TypeEnv`. -/
abbrev TypeEnv := RunarVerification.ANF.Typed.TypeEnv

/-- The typed-entry hypothesis.  Every `.bigint`-typed name in `Γ`
resolves to a `.vBigint` value in `anfSt`. -/
def EntryBigintTyped (Γ : TypeEnv) (anfSt : State) : Prop :=
  ∀ n : String, Γ.lookup n = some .bigint →
    ∃ v : Value, anfSt.resolveRef n = some v ∧ Value.IsBigint v

/-! ## Structural arith-rule predicate (Deliverable A — minimal)

`arithOperandBigint Γ ref` is the structural side of the type-checker's
arith rule: the operand `ref` is declared `.bigint` in `Γ`.  An emittable
binOp operand-pair is well-typed when BOTH operands satisfy this; the
emittable unaryOp operand when its single operand does.  This is the
MINIMAL fragment of the full type system needed to exclude `.vBool`
operands — it mirrors `checkBinaryExpr`'s `isBigintFamily(leftType)` /
`isBigintFamily(rightType)` checks for the arith ops (03-typecheck.ts:907,914).
-/

/-- The operand `ref` is declared `.bigint` in `Γ` (structural arith rule). -/
def arithOperandBigint (Γ : TypeEnv) (ref : String) : Prop :=
  Γ.lookup ref = some .bigint

/-- A binOp value is arith-well-typed: emittable op, both operands declared
`.bigint`.  (`rt` is irrelevant — the emittable arith ops are numeric.) -/
def binOpArithWellTyped (Γ : TypeEnv) (op l r : String) : Prop :=
  (op = "+" ∨ op = "-" ∨ op = "*") ∧
    arithOperandBigint Γ l ∧ arithOperandBigint Γ r

/-- A unaryOp value is arith-well-typed: emittable NEGATE, operand declared
`.bigint`. -/
def unaryOpArithWellTyped (Γ : TypeEnv) (operand : String) : Prop :=
  arithOperandBigint Γ operand

/-! ## Soundness (Deliverable B)

From the typed-entry hypothesis + a structurally arith-well-typed operand,
the operand's runtime value is `.vBigint` — discharging both the wave-30
failure step's `hNonBool` and the wave-32 success step's head-bigint
precondition for entry operands. -/

/-- **B.0 — operand soundness.** A `.bigint`-declared operand resolves to a
`.vBigint` runtime value under the typed-entry hypothesis. -/
theorem operand_isBigint_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String)
    (hEntry : EntryBigintTyped Γ anfSt)
    (hTyped : arithOperandBigint Γ ref) :
    ∃ v : Value, anfSt.resolveRef ref = some v ∧ Value.IsBigint v :=
  hEntry ref hTyped

/-- **B.1 — operand resolves to an explicit `.vBigint i`.** The success
step (`agrees_success_step_binOp`) consumes `lookupAnfByKind = some
(.vBigint a)`; via the head-correspondence `resolveRef = lookupAnfByKind`
this lemma supplies the explicit `i`. -/
theorem operand_resolveRef_vBigint_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String)
    (hEntry : EntryBigintTyped Γ anfSt)
    (hTyped : arithOperandBigint Γ ref) :
    ∃ i : Int, anfSt.resolveRef ref = some (.vBigint i) := by
  obtain ⟨v, hRes, hBig⟩ := operand_isBigint_of_typedEntry Γ anfSt ref hEntry hTyped
  obtain ⟨i, hi⟩ := hBig
  exact ⟨i, by rw [hRes, hi]⟩

/-- **B.2 — `hNonBool` discharge (failure step).** Under typed-entry, a
`.bigint`-declared operand's runtime value (read via `lookupAnfByKind`
through the head correspondence) is never a `.vBool` — exactly the
`hNonBool` premise of `successAgrees_arith_consume_first_binOp_fail` /
`_first_unary_fail`. -/
theorem lookupAnfByKind_nonBool_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String) (k : RunarVerification.Stack.Agrees.SlotKind)
    (hEntry : EntryBigintTyped Γ anfSt)
    (hTyped : arithOperandBigint Γ ref)
    (hHeadCorr : anfSt.resolveRef ref
      = RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (ref, k)) :
    ∀ (b : Bool) (v : Value),
      RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (ref, k) = some v → v ≠ .vBool b := by
  obtain ⟨v0, hRes, hBig⟩ := operand_isBigint_of_typedEntry Γ anfSt ref hEntry hTyped
  have hLk : RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (ref, k) = some v0 := by
    rw [← hHeadCorr]; exact hRes
  intro b v hLkv
  rw [hLk] at hLkv
  have hvEq : v = v0 := (Option.some.inj hLkv).symm
  rw [hvEq]
  exact hBig.not_vBool b

/-- **B.3 — head-bigint discharge (success step).** Under typed-entry, a
`.bigint`-declared operand's runtime value (via `lookupAnfByKind` through
the head correspondence) is an explicit `.vBigint i` — exactly the
`hBigintL` / `hBigintR` / `hBigint` premises of `agrees_success_step_binOp`
/ `agrees_success_step_unary`. -/
theorem lookupAnfByKind_vBigint_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String) (k : RunarVerification.Stack.Agrees.SlotKind)
    (hEntry : EntryBigintTyped Γ anfSt)
    (hTyped : arithOperandBigint Γ ref)
    (hHeadCorr : anfSt.resolveRef ref
      = RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (ref, k)) :
    ∃ i : Int,
      RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (ref, k) = some (.vBigint i) := by
  obtain ⟨i, hRes⟩ := operand_resolveRef_vBigint_of_typedEntry Γ anfSt ref hEntry hTyped
  exact ⟨i, by rw [← hHeadCorr]; exact hRes⟩

/-- **B.4 — both binOp operands at once (success step convenience).** -/
theorem binOp_operands_vBigint_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (op l r : String)
    (k_l k_r : RunarVerification.Stack.Agrees.SlotKind)
    (hEntry : EntryBigintTyped Γ anfSt)
    (hTyped : binOpArithWellTyped Γ op l r)
    (hHeadCorrL : anfSt.resolveRef l
      = RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (l, k_l))
    (hHeadCorrR : anfSt.resolveRef r
      = RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (r, k_r)) :
    (∃ a : Int,
        RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (l, k_l) = some (.vBigint a)) ∧
    (∃ b : Int,
        RunarVerification.Stack.Agrees.lookupAnfByKind anfSt (r, k_r) = some (.vBigint b)) := by
  obtain ⟨_hEmit, hTL, hTR⟩ := hTyped
  exact ⟨lookupAnfByKind_vBigint_of_typedEntry Γ anfSt l k_l hEntry hTL hHeadCorrL,
         lookupAnfByKind_vBigint_of_typedEntry Γ anfSt r k_r hEntry hTR hHeadCorrR⟩

/-! ## Deliverable C — connecting the invariant to the wave-33 walk

The two soundness lemmas above produce EXACTLY the premise shapes the
existing wave-30 / wave-32 per-binding steps consume:

* `lookupAnfByKind_nonBool_of_typedEntry` ⇒ the `hNonBool` of
  `Stack.Agrees.successAgrees_arith_consume_first_binOp_fail` and
  `_first_unary_fail`;
* `lookupAnfByKind_vBigint_of_typedEntry` ⇒ the `hBigint` of
  `Stack.Agrees.agrees_success_step_binOp` / `agrees_success_step_unary`.

So with `EntryBigintTyped` + a structural arith-well-typed body the wave-33
walk's per-binding obligations are total: every entry operand the body
reads as an arith operand is provably `.vBigint`, so the `.vBool` divergent
case is unreachable.  The walk itself (`successAgrees_arith_consume_…`) is
a forward reference into `Stack.AgreesA3`, so its assembly belongs in that
module; this file lands the type-fidelity substrate it composes with.
The wiring is exercised end-to-end by the two smoke tests below.
-/

/-! ## MANDATORY smoke tests

A concrete WELL-TYPED program where the predicate holds and the
bigint-operand soundness FIRES, and a concrete ILL-TYPED (bool-operand)
program where the predicate FAILS (confirming it excludes the divergent
case). -/

/-- Smoke (well-typed) — typing context for `t0 = p0 + p1` with both params
declared `.bigint`. -/
def smokeWTEnv : TypeEnv :=
  (Typed.TypeEnv.empty.extend "p0" .bigint).extend "p1" .bigint

/-- Smoke (well-typed) — runtime ANF state with `p0 = 3`, `p1 = 4` (both
`.vBigint`).  This is a valid typed entry for `smokeWTEnv`. -/
def smokeWTAnf : State :=
  { params := [("p0", .vBigint 3), ("p1", .vBigint 4)] }

/-- The body's binOp operands are arith-well-typed in `smokeWTEnv`. -/
theorem smoke_wt_binOpArithWellTyped :
    binOpArithWellTyped smokeWTEnv "+" "p0" "p1" := by
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · show smokeWTEnv.lookup "p0" = some .bigint; decide
  · show smokeWTEnv.lookup "p1" = some .bigint; decide

/-- The typed-entry hypothesis holds for `smokeWTAnf` under `smokeWTEnv`:
every `.bigint`-declared name (`p0`, `p1`) resolves to a `.vBigint`. -/
theorem smoke_wt_entryBigintTyped :
    EntryBigintTyped smokeWTEnv smokeWTAnf := by
  intro n hn
  -- `smokeWTEnv.lookup n = some .bigint` forces `n ∈ {"p0", "p1"}`.
  by_cases h0 : n = "p0"
  · subst h0; exact ⟨.vBigint 3, rfl, ⟨3, rfl⟩⟩
  · by_cases h1 : n = "p1"
    · subst h1; exact ⟨.vBigint 4, rfl, ⟨4, rfl⟩⟩
    · -- Any other name does not resolve to `.bigint` in `smokeWTEnv`.
      exfalso
      have hp1 : ("p1" == n) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => h1 h.symm
      have hp0 : ("p0" == n) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => h0 h.symm
      simp only [smokeWTEnv, Typed.TypeEnv.lookup, Typed.TypeEnv.extend, Typed.TypeEnv.empty,
        List.find?_cons, hp1, hp0, List.find?_nil, Option.map_none, reduceCtorEq] at hn

/-- **Smoke (well-typed) — the soundness FIRES.**  Under the typed entry,
both operands `p0`, `p1` resolve (via `lookupAnfByKind` through the param
head-correspondence) to explicit `.vBigint` values, and neither is a
`.vBool`.  The `.param` head-correspondence holds because `smokeWTAnf` has
no bindings, so `resolveRef = lookupParam = lookupAnfByKind (·, .param)`. -/
theorem smoke_wt_soundness_fires :
    (∃ a : Int,
        RunarVerification.Stack.Agrees.lookupAnfByKind smokeWTAnf ("p0", .param)
          = some (.vBigint a)) ∧
    (∃ b : Int,
        RunarVerification.Stack.Agrees.lookupAnfByKind smokeWTAnf ("p1", .param)
          = some (.vBigint b)) ∧
    (∀ (b : Bool) (v : Value),
        RunarVerification.Stack.Agrees.lookupAnfByKind smokeWTAnf ("p0", .param) = some v →
          v ≠ .vBool b) := by
  have hCorrL : smokeWTAnf.resolveRef "p0"
      = RunarVerification.Stack.Agrees.lookupAnfByKind smokeWTAnf ("p0", .param) := by
    show smokeWTAnf.resolveRef "p0" = smokeWTAnf.lookupParam "p0"; rfl
  have hCorrR : smokeWTAnf.resolveRef "p1"
      = RunarVerification.Stack.Agrees.lookupAnfByKind smokeWTAnf ("p1", .param) := by
    show smokeWTAnf.resolveRef "p1" = smokeWTAnf.lookupParam "p1"; rfl
  obtain ⟨hL, hR⟩ := binOp_operands_vBigint_of_typedEntry smokeWTEnv smokeWTAnf "+" "p0" "p1"
    .param .param smoke_wt_entryBigintTyped smoke_wt_binOpArithWellTyped hCorrL hCorrR
  refine ⟨hL, hR, ?_⟩
  exact lookupAnfByKind_nonBool_of_typedEntry smokeWTEnv smokeWTAnf "p0" .param
    smoke_wt_entryBigintTyped smoke_wt_binOpArithWellTyped.2.1 hCorrL

/-- Smoke (ill-typed) — typing context for `t0 = p0 + p1` where `p1` is
declared `.bool` (the divergent case: a `bool + int` the real type-checker
REJECTS at `03-typecheck.ts:914`). -/
def smokeITEnv : TypeEnv :=
  (Typed.TypeEnv.empty.extend "p0" .bigint).extend "p1" .bool

/-- **Smoke (ill-typed) — the predicate FAILS.**  The right operand `p1` is
NOT declared `.bigint`, so `binOpArithWellTyped` cannot hold — the
structural arith-rule predicate EXCLUDES this `bool`-operand program.  This
is the divergent case wave 33 found: had we admitted it, a `.vBool` `p1`
would make ANF fail / Script succeed. -/
theorem smoke_it_predicate_fails :
    ¬ binOpArithWellTyped smokeITEnv "+" "p0" "p1" := by
  rintro ⟨_hEmit, _hL, hR⟩
  -- `hR : arithOperandBigint smokeITEnv "p1"`, i.e. lookup = some .bigint;
  -- but `p1` is declared `.bool`, so the two `some`s disagree.
  unfold arithOperandBigint at hR
  have hP1 : smokeITEnv.lookup "p1" = some .bool := rfl
  rw [hP1] at hR
  exact absurd hR (by decide)

/-! ## Deliverable A (Wave 44) — cond-bool typing (entry route)

The `if_val` arith fragment (`ifValArithBody`) is a method body of EXACTLY
one `.ifVal cond thn els` binding.  There are no prior bindings, so the
condition ref `cond` is an **entry value** (a `.bool`-typed param or prop),
NOT a body-produced comparison-result temp.  Its bool-ness therefore CANNOT
be derived from the body — it is an entry fact, the bool analogue of
`EntryBigintTyped`.  This is route **(i)**: a new entry premise.

`CondBoolTyped Γ anfSt cond` says: the cond ref is declared `.bool` in `Γ`
AND every `.bool`-declared name resolves to a `.vBool` runtime value in
`anfSt`.  The soundness lemma extracts the explicit witness bool for the
cond, exactly the `∃ b, resolveRef cond = some (.vBool b)` the `if_val` walk
consumes (`hCond` of `successAgrees_ifVal_arith_unconditional`).

This mirrors `EntryBigintTyped`'s shape: a declared-type ⇒ runtime-value-tag
bridge that `agreesTagged` / `WF` cannot supply (the omnibus quantifies
`initialAnf` freely; nothing structural pins the cond's runtime tag), so it
is supplied as a hypothesis (input-side, never restating the conclusion). -/

/-- A runtime value is a bool. -/
def Value.IsBool (v : Value) : Prop := ∃ b : Bool, v = .vBool b

/-- The cond-bool entry hypothesis.  The cond ref `cond` is declared `.bool`
in `Γ`, and every `.bool`-declared name in `Γ` resolves to a `.vBool` value
in `anfSt`.  The first conjunct is the structural typing rule (the cond is a
bool); the second is the declared-type ⇒ runtime-tag bridge for bools. -/
def CondBoolTyped (Γ : TypeEnv) (anfSt : State) (cond : String) : Prop :=
  Γ.lookup cond = some .bool ∧
    (∀ n : String, Γ.lookup n = some .bool →
      ∃ b : Bool, anfSt.resolveRef n = some (.vBool b))

/-- **A.0 — cond soundness.**  Under `CondBoolTyped`, the cond ref resolves
to an explicit `.vBool b` runtime value.  This is exactly the `hCond`
premise (`resolveRef cond = some (.vBool b)`) of the wave-41 `if_val`
walk. -/
theorem condBool_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (cond : String)
    (hCond : CondBoolTyped Γ anfSt cond) :
    ∃ b : Bool, anfSt.resolveRef cond = some (.vBool b) :=
  hCond.2 cond hCond.1

/-! ## Deliverable A (Wave 44) — MANDATORY smoke

A concrete WELL-TYPED entry where the cond `c` is declared `.bool` and
resolves to `.vBool true`, so `condBool_of_typedEntry` FIRES; and a concrete
entry where `c` is declared `.bigint` (not a bool), so `CondBoolTyped`
FAILS — confirming the predicate is real (it pins the cond to a bool). -/

/-- Smoke (cond-bool) — typing context: `c` is `.bool`, `p0`/`p1` `.bigint`. -/
def smokeCondEnv : TypeEnv :=
  ((Typed.TypeEnv.empty.extend "c" .bool).extend "p0" .bigint).extend "p1" .bigint

/-- Smoke (cond-bool) — runtime state: `c = true`, `p0 = 3`, `p1 = 4`. -/
def smokeCondAnf : State :=
  { params := [("c", .vBool true), ("p0", .vBigint 3), ("p1", .vBigint 4)] }

/-- `CondBoolTyped` holds for `smokeCondAnf` under `smokeCondEnv`: `c` is the
only `.bool`-declared name, and it resolves to `.vBool true`. -/
theorem smoke_condBoolTyped :
    CondBoolTyped smokeCondEnv smokeCondAnf "c" := by
  refine ⟨rfl, ?_⟩
  intro n hn
  by_cases hc : n = "c"
  · subst hc; exact ⟨true, rfl⟩
  · -- Any other name is `.bigint` (or absent), never `.bool`.
    exfalso
    by_cases h0 : n = "p0"
    · subst h0
      have hp0 : smokeCondEnv.lookup "p0" = some .bigint := rfl
      rw [hp0] at hn; exact absurd hn (by decide)
    · by_cases h1 : n = "p1"
      · subst h1
        have hp1 : smokeCondEnv.lookup "p1" = some .bigint := rfl
        rw [hp1] at hn; exact absurd hn (by decide)
      · have hp1 : ("p1" == n) = false := by rw [beq_eq_false_iff_ne]; exact fun h => h1 h.symm
        have hp0 : ("p0" == n) = false := by rw [beq_eq_false_iff_ne]; exact fun h => h0 h.symm
        have hcc : ("c" == n) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hc h.symm
        simp only [smokeCondEnv, Typed.TypeEnv.lookup, Typed.TypeEnv.extend,
          Typed.TypeEnv.empty, List.find?_cons, hp1, hp0, hcc, List.find?_nil,
          Option.map_none, reduceCtorEq] at hn

/-- **Smoke (cond-bool) — the soundness FIRES.**  The cond `c` resolves to an
explicit `.vBool b` (here `true`). -/
theorem smoke_condBool_fires :
    ∃ b : Bool, smokeCondAnf.resolveRef "c" = some (.vBool b) :=
  condBool_of_typedEntry smokeCondEnv smokeCondAnf "c" smoke_condBoolTyped

/-- Smoke (cond-not-bool) — `c` declared `.bigint` (not a bool). -/
def smokeCondITEnv : TypeEnv :=
  (Typed.TypeEnv.empty.extend "c" .bigint).extend "p0" .bigint

/-- **Smoke (cond-not-bool) — the predicate FAILS.**  `c` is not declared
`.bool`, so the structural conjunct of `CondBoolTyped` cannot hold — the
predicate genuinely pins the cond to a bool. -/
theorem smoke_condBool_predicate_fails :
    ¬ CondBoolTyped smokeCondITEnv smokeCondAnf "c" := by
  rintro ⟨hLk, _hRes⟩
  have hC : smokeCondITEnv.lookup "c" = some .bigint := rfl
  rw [hC] at hLk
  exact absurd hLk (by decide)

/-! ## Deliverable (Wave 46) — bytes typing for the `math_byte_call` family

The `math_byte_call` retirement family is method bodies built from builtin
`.call func args` bindings whose operand/return types are MIXED — unlike the
all-`.bigint` arith fragment.  The single-arg slice of this family is already
structurally landed in `Stack/AgreesA4.lean` (`structuralCallValue` over
`abs`/`len`/`bin2num`/`toByteString`/`pack`); its ANF-side success lemma
(`evalValue_structuralCallValue_ok`) consumes a per-call `argShapeOk`
hypothesis of shape `∃ b, resolveRef arg = some (.vBytes b)` for the
bytes-input builtins (`len : bytes → bigint`, `bin2num : bytes → bigint`,
`toByteString`, …).

That `argShapeOk` premise is, for the `.byteString`-input builtins, exactly
the bytes analogue of what `EntryBigintTyped` already supplies for arith
operands.  This deliverable lands the type-fidelity bridge that DISCHARGES it
from a single declared-type ⇒ runtime-tag hypothesis — `EntryBytesTyped` —
generalising `EntryBigintTyped` from the all-bigint surface to the
bytes-typed entries the mixed `math_byte_call` family needs.  No new axioms;
this is the foundational lemma whose soundness output (`∃ b, resolveRef arg =
some (.vBytes b)`) is byte-shape-identical to the `argShapeOk` field A4's
walk already consumes, so the next wave can drop the ad-hoc premise.
-/

/-- A runtime value is a byte string. -/
def Value.IsBytes (v : Value) : Prop := ∃ b : ByteArray, v = .vBytes b

/-- A bytes value is not a bool. -/
theorem Value.IsBytes.not_vBool {v : Value} (h : Value.IsBytes v) :
    ∀ b : Bool, v ≠ .vBool b := by
  obtain ⟨ba, hba⟩ := h
  intro b hEq
  rw [hba] at hEq
  exact absurd hEq (by simp)

/-- A bytes value is not a bigint. -/
theorem Value.IsBytes.not_vBigint {v : Value} (h : Value.IsBytes v) :
    ∀ i : Int, v ≠ .vBigint i := by
  obtain ⟨ba, hba⟩ := h
  intro i hEq
  rw [hba] at hEq
  exact absurd hEq (by simp)

/-- The typed-entry hypothesis for byte strings.  Every `.byteString`-declared
name in `Γ` resolves to a `.vBytes` runtime value in `anfSt`.  This is the
bytes analogue of `EntryBigintTyped`: the declared-type ⇒ runtime-value-tag
bridge for the `byteString` slot. -/
def EntryBytesTyped (Γ : TypeEnv) (anfSt : State) : Prop :=
  ∀ n : String, Γ.lookup n = some .byteString →
    ∃ v : Value, anfSt.resolveRef n = some v ∧ Value.IsBytes v

/-- The operand `ref` is declared `.byteString` in `Γ` (structural rule for
the bytes-input builtins: `len`, `bin2num`, `toByteString`, `cat`'s operands,
…).  Sibling of `arithOperandBigint`. -/
def byteOperandBytes (Γ : TypeEnv) (ref : String) : Prop :=
  Γ.lookup ref = some .byteString

/-- **Bytes operand soundness.**  A `.byteString`-declared operand resolves to
a `.vBytes` runtime value under the bytes typed-entry hypothesis.  Sibling of
`operand_isBigint_of_typedEntry`. -/
theorem arg_isBytes_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String)
    (hEntry : EntryBytesTyped Γ anfSt)
    (hTyped : byteOperandBytes Γ ref) :
    ∃ v : Value, anfSt.resolveRef ref = some v ∧ Value.IsBytes v :=
  hEntry ref hTyped

/-- **Bytes operand resolves to an explicit `.vBytes b`.**  This is exactly the
`argShapeOk` field A4's `evalValue_structuralCallValue_ok` consumes for the
bytes-input builtins (`∃ b, resolveRef arg = some (.vBytes b)`).  Sibling of
`operand_resolveRef_vBigint_of_typedEntry`. -/
theorem arg_resolveRef_vBytes_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String)
    (hEntry : EntryBytesTyped Γ anfSt)
    (hTyped : byteOperandBytes Γ ref) :
    ∃ b : ByteArray, anfSt.resolveRef ref = some (.vBytes b) := by
  obtain ⟨v, hRes, hBytes⟩ := arg_isBytes_of_typedEntry Γ anfSt ref hEntry hTyped
  obtain ⟨b, hb⟩ := hBytes
  exact ⟨b, by rw [hRes, hb]⟩

/-- **Bytes `hNonBool` discharge.**  Under the bytes typed-entry, a
`.byteString`-declared operand's runtime value is never a `.vBool`.  Mirrors
`lookupAnfByKind_nonBool_of_typedEntry` for the bytes slot — needed so a
mixed bytes/bool body's failure-step `hNonBool` is also discharged from the
entry hypothesis. -/
theorem arg_nonBool_of_typedEntry
    (Γ : TypeEnv) (anfSt : State) (ref : String)
    (hEntry : EntryBytesTyped Γ anfSt)
    (hTyped : byteOperandBytes Γ ref) :
    ∀ (b : Bool) (v : Value),
      anfSt.resolveRef ref = some v → v ≠ .vBool b := by
  obtain ⟨v0, hRes, hBytes⟩ := arg_isBytes_of_typedEntry Γ anfSt ref hEntry hTyped
  intro b v hResv
  rw [hRes] at hResv
  have hvEq : v = v0 := (Option.some.inj hResv).symm
  rw [hvEq]
  exact hBytes.not_vBool b

/-! ## Deliverable (Wave 46) — MANDATORY smoke

A concrete WELL-TYPED entry where `s0` is declared `.byteString` and resolves
to a `.vBytes`, so `arg_resolveRef_vBytes_of_typedEntry` FIRES (this is the
`argShapeOk` premise for `len(s0)` / `bin2num(s0)`); and a concrete entry
where `s0` is declared `.bigint` (not bytes), so `EntryBytesTyped` cannot
supply the bytes resolution — confirming the predicate genuinely pins the
operand to `.vBytes` and is not vacuously true. -/

/-- Smoke (bytes well-typed) — `s0` declared `.byteString`, `p0` `.bigint`. -/
def smokeBytesEnv : TypeEnv :=
  (Typed.TypeEnv.empty.extend "s0" .byteString).extend "p0" .bigint

/-- Smoke (bytes well-typed) — runtime state: `s0 = #[0x01, 0x02]`, `p0 = 7`. -/
def smokeBytesAnf : State :=
  { params := [("s0", .vBytes (ByteArray.mk #[0x01, 0x02])), ("p0", .vBigint 7)] }

/-- The bytes typed-entry hypothesis holds for `smokeBytesAnf` under
`smokeBytesEnv`: the only `.byteString`-declared name (`s0`) resolves to a
`.vBytes`. -/
theorem smoke_bytes_entryBytesTyped :
    EntryBytesTyped smokeBytesEnv smokeBytesAnf := by
  intro n hn
  by_cases hs : n = "s0"
  · subst hs; exact ⟨.vBytes (ByteArray.mk #[0x01, 0x02]), rfl, ⟨_, rfl⟩⟩
  · exfalso
    by_cases h0 : n = "p0"
    · subst h0
      have hp0 : smokeBytesEnv.lookup "p0" = some .bigint := rfl
      rw [hp0] at hn; exact absurd hn (by decide)
    · have hp0 : ("p0" == n) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => h0 h.symm
      have hss : ("s0" == n) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hs h.symm
      simp only [smokeBytesEnv, Typed.TypeEnv.lookup, Typed.TypeEnv.extend,
        Typed.TypeEnv.empty, List.find?_cons, hp0, hss, List.find?_nil,
        Option.map_none, reduceCtorEq] at hn

/-- `s0` is declared `.byteString` in `smokeBytesEnv`. -/
theorem smoke_bytes_operandBytes :
    byteOperandBytes smokeBytesEnv "s0" := by
  show smokeBytesEnv.lookup "s0" = some .byteString; decide

/-- **Smoke (bytes well-typed) — the soundness FIRES.**  The bytes operand `s0`
resolves to an explicit `.vBytes b` — exactly the `argShapeOk` shape A4's
single-arg walk consumes for `len`/`bin2num`. -/
theorem smoke_bytes_soundness_fires :
    ∃ b : ByteArray, smokeBytesAnf.resolveRef "s0" = some (.vBytes b) :=
  arg_resolveRef_vBytes_of_typedEntry smokeBytesEnv smokeBytesAnf "s0"
    smoke_bytes_entryBytesTyped smoke_bytes_operandBytes

/-- Smoke (bytes ill-typed) — `s0` declared `.bigint` (not bytes). -/
def smokeBytesITEnv : TypeEnv :=
  (Typed.TypeEnv.empty.extend "s0" .bigint).extend "p0" .bigint

/-- **Smoke (bytes ill-typed) — the structural predicate FAILS.**  `s0` is not
declared `.byteString`, so `byteOperandBytes` cannot hold — the predicate
genuinely pins the operand to `.byteString` (had we admitted a `.bigint` `s0`,
a `.vBigint` runtime value would make a `len(s0)` body diverge between the
bytes-consuming Script op and the ANF evaluator). -/
theorem smoke_bytes_predicate_fails :
    ¬ byteOperandBytes smokeBytesITEnv "s0" := by
  intro h
  unfold byteOperandBytes at h
  have hS0 : smokeBytesITEnv.lookup "s0" = some .bigint := rfl
  rw [hS0] at h
  exact absurd h (by decide)

/-! ## Bool reflections of the atomic operand predicates (WS0a Task 1)

Decidable `Bool`-valued checkers for the four atomic predicates, plus their
`_iff` equivalence lemmas.  These enable `native_decide` in downstream
harness code without any `sorry` or new `axiom`.

Implementation note: `ANFType` derives `BEq` but not `LawfulBEq`, so
`(a == b) = true ↔ a = b` does not hold via `beq_iff_eq` here.  We use
`decide` instead so each checker is definitionally the `Prop`-as-`Bool`,
and `simp` closes the `_iff` goals directly. -/

def arithOperandBigintBool (Γ : TypeEnv) (ref : String) : Bool :=
  decide (Γ.lookup ref = some .bigint)

def byteOperandBytesBool (Γ : TypeEnv) (ref : String) : Bool :=
  decide (Γ.lookup ref = some .byteString)

def binOpArithWellTypedBool (Γ : TypeEnv) (op l r : String) : Bool :=
  (op == "+" || op == "-" || op == "*") &&
    arithOperandBigintBool Γ l && arithOperandBigintBool Γ r

def unaryOpArithWellTypedBool (Γ : TypeEnv) (operand : String) : Bool :=
  arithOperandBigintBool Γ operand

theorem arithOperandBigintBool_iff (Γ : TypeEnv) (ref : String) :
    arithOperandBigintBool Γ ref = true ↔ arithOperandBigint Γ ref := by
  simp [arithOperandBigintBool, arithOperandBigint]

theorem byteOperandBytesBool_iff (Γ : TypeEnv) (ref : String) :
    byteOperandBytesBool Γ ref = true ↔ byteOperandBytes Γ ref := by
  simp [byteOperandBytesBool, byteOperandBytes]

theorem binOpArithWellTypedBool_iff (Γ : TypeEnv) (op l r : String) :
    binOpArithWellTypedBool Γ op l r = true ↔ binOpArithWellTyped Γ op l r := by
  simp [binOpArithWellTypedBool, binOpArithWellTyped, arithOperandBigintBool,
    arithOperandBigint, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨(h | h) | h, hL⟩, hR⟩
    · exact ⟨Or.inl h, hL, hR⟩
    · exact ⟨Or.inr (Or.inl h), hL, hR⟩
    · exact ⟨Or.inr (Or.inr h), hL, hR⟩
  · rintro ⟨h | h | h, hL, hR⟩
    · exact ⟨⟨Or.inl (Or.inl h), hL⟩, hR⟩
    · exact ⟨⟨Or.inl (Or.inr h), hL⟩, hR⟩
    · exact ⟨⟨Or.inr h, hL⟩, hR⟩

theorem unaryOpArithWellTypedBool_iff (Γ : TypeEnv) (operand : String) :
    unaryOpArithWellTypedBool Γ operand = true ↔ unaryOpArithWellTyped Γ operand := by
  simp [unaryOpArithWellTypedBool, unaryOpArithWellTyped, arithOperandBigintBool_iff]

private def Γ_t1_smoke : TypeEnv :=
  (((Typed.TypeEnv.empty.extend "a" .bigint).extend "b" .bigint).extend "f" .bool)

example : arithOperandBigintBool Γ_t1_smoke "a" = true := by native_decide
example : arithOperandBigintBool Γ_t1_smoke "f" = false := by native_decide
example : binOpArithWellTypedBool Γ_t1_smoke "+" "a" "b" = true := by native_decide
example : binOpArithWellTypedBool Γ_t1_smoke "+" "a" "f" = false := by native_decide

/-! ## Bool reflections of the ENTRY typing predicates (WS0a Task 2)

Decidable `Bool`-valued checkers for the three ENTRY-shaped predicates
(`EntryBigintTyped`, `EntryBytesTyped`, `CondBoolTyped`), plus their `_iff`
equivalence lemmas.  Unlike the atomic operand predicates (Task 1), these
quantify over names via `Γ.lookup n`, so a sound checker must range over the
binding names and test each name's CANONICAL type (`Γ.lookup b.1`), NOT the
entry's own stored type (`b.2`).  Under shadowing those differ — e.g.
`Γ = [("a",.bool),("a",.bigint)]` has `lookup "a" = .bool`, so
`EntryBigintTyped` does NOT constrain `"a"`, but a `b.2`-based checker would
(via the second entry), breaking the reverse `_iff` direction.  Testing
`Γ.lookup b.1` ranges over exactly the names where `lookup = some ty` can
hold (a name absent from `bindings` has `lookup = none`, making the predicate
vacuous), so it is equivalent to the `∀`-quantified `Prop`.

No `sorry`, no new `axiom`. -/

/-- **Lookup-membership bridge.**  If `Γ.lookup n = some ty`, then the entry
that `find?` returned is a member of `Γ.bindings` whose name is `n` (and whose
stored type is `ty`).  This is the witness used to instantiate the `List.all`
in the forward `_iff` direction; the looked-up name is exactly a binding
name.  (Not a new axiom — a small reusable structural lemma.) -/
theorem lookup_mem_name (Γ : TypeEnv) (n : String) (ty : ANFType)
    (h : Γ.lookup n = some ty) :
    ∃ e : String × ANFType, e ∈ Γ.bindings ∧ e.1 = n ∧ e.2 = ty := by
  unfold Typed.TypeEnv.lookup at h
  cases hf : Γ.bindings.find? (·.fst == n) with
  | none => rw [hf] at h; simp at h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem : e ∈ Γ.bindings := List.mem_of_find?_eq_some hf
    have hp : ((·.fst == n) e : Bool) = true :=
      @List.find?_some _ (·.fst == n) e Γ.bindings hf
    have hname : e.1 = n := eq_of_beq hp
    exact ⟨e, hmem, hname, h⟩

/-- Bool reflection of `EntryBigintTyped`.  Ranges over binding names; for each
name whose CANONICAL type is `.bigint`, requires `resolveRef` to be a
`.vBigint`. -/
def entryBigintTypedBool (Γ : TypeEnv) (anfSt : State) : Bool :=
  Γ.bindings.all (fun b =>
    !decide (Γ.lookup b.1 = some ANFType.bigint) ||
      (match anfSt.resolveRef b.1 with | some (.vBigint _) => true | _ => false))

theorem entryBigintTypedBool_iff (Γ : TypeEnv) (anfSt : State) :
    entryBigintTypedBool Γ anfSt = true ↔ EntryBigintTyped Γ anfSt := by
  unfold entryBigintTypedBool EntryBigintTyped
  rw [List.all_eq_true]
  constructor
  · -- Bool ⇒ Prop: a `.bigint`-looked-up name is a binding name; apply `all`.
    intro hAll n hn
    obtain ⟨e, hmem, hename, _⟩ := lookup_mem_name Γ n .bigint hn
    have hb := hAll e hmem
    have hlook : Γ.lookup e.1 = some ANFType.bigint := by rw [hename]; exact hn
    simp only [hlook, decide_true, Bool.not_true, Bool.false_or] at hb
    rw [hename] at hb
    split at hb
    · next i heq => exact ⟨.vBigint i, heq, ⟨i, rfl⟩⟩
    · exact absurd hb (by simp)
  · -- Prop ⇒ Bool: per binding, case on whether its canonical type is `.bigint`.
    intro hProp b _hb
    by_cases hlook : Γ.lookup b.1 = some ANFType.bigint
    · obtain ⟨v, hres, hbig⟩ := hProp b.1 hlook
      obtain ⟨i, hi⟩ := hbig
      simp only [hlook, decide_true, Bool.not_true, Bool.false_or]
      rw [hres, hi]
    · simp only [hlook, decide_false, Bool.not_false, Bool.true_or]

/-- Bool reflection of `EntryBytesTyped`. -/
def entryBytesTypedBool (Γ : TypeEnv) (anfSt : State) : Bool :=
  Γ.bindings.all (fun b =>
    !decide (Γ.lookup b.1 = some ANFType.byteString) ||
      (match anfSt.resolveRef b.1 with | some (.vBytes _) => true | _ => false))

theorem entryBytesTypedBool_iff (Γ : TypeEnv) (anfSt : State) :
    entryBytesTypedBool Γ anfSt = true ↔ EntryBytesTyped Γ anfSt := by
  unfold entryBytesTypedBool EntryBytesTyped
  rw [List.all_eq_true]
  constructor
  · intro hAll n hn
    obtain ⟨e, hmem, hename, _⟩ := lookup_mem_name Γ n .byteString hn
    have hb := hAll e hmem
    have hlook : Γ.lookup e.1 = some ANFType.byteString := by rw [hename]; exact hn
    simp only [hlook, decide_true, Bool.not_true, Bool.false_or] at hb
    rw [hename] at hb
    split at hb
    · next ba heq => exact ⟨.vBytes ba, heq, ⟨ba, rfl⟩⟩
    · exact absurd hb (by simp)
  · intro hProp b _hb
    by_cases hlook : Γ.lookup b.1 = some ANFType.byteString
    · obtain ⟨v, hres, hbytes⟩ := hProp b.1 hlook
      obtain ⟨ba, hba⟩ := hbytes
      simp only [hlook, decide_true, Bool.not_true, Bool.false_or]
      rw [hres, hba]
    · simp only [hlook, decide_false, Bool.not_false, Bool.true_or]

/-- Bool reflection of `CondBoolTyped`.  Leading conjunct: the cond ref is
declared `.bool`.  Second conjunct: every `.bool`-canonical-typed binding name
resolves to a `.vBool`. -/
def condBoolTypedBool (Γ : TypeEnv) (anfSt : State) (cond : String) : Bool :=
  decide (Γ.lookup cond = some ANFType.bool) &&
    Γ.bindings.all (fun b =>
      !decide (Γ.lookup b.1 = some ANFType.bool) ||
        (match anfSt.resolveRef b.1 with | some (.vBool _) => true | _ => false))

theorem condBoolTypedBool_iff (Γ : TypeEnv) (anfSt : State) (cond : String) :
    condBoolTypedBool Γ anfSt cond = true ↔ CondBoolTyped Γ anfSt cond := by
  unfold condBoolTypedBool CondBoolTyped
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  apply and_congr_right
  intro _
  constructor
  · intro hAll n hn
    obtain ⟨e, hmem, hename, _⟩ := lookup_mem_name Γ n .bool hn
    have hb := hAll e hmem
    have hlook : Γ.lookup e.1 = some ANFType.bool := by rw [hename]; exact hn
    simp only [hlook, decide_true, Bool.not_true, Bool.false_or] at hb
    rw [hename] at hb
    split at hb
    · next bb heq => exact ⟨bb, heq⟩
    · exact absurd hb (by simp)
  · intro hProp b _hb
    by_cases hlook : Γ.lookup b.1 = some ANFType.bool
    · obtain ⟨bb, hres⟩ := hProp b.1 hlook
      simp only [hlook, decide_true, Bool.not_true, Bool.false_or]
      rw [hres]
    · simp only [hlook, decide_false, Bool.not_false, Bool.true_or]

/-! ## WS0a Task 2 — MANDATORY smoke tests

A concrete entry (`a ↦ vBigint 3`, `f ↦ vBool true`) typed by `Γ` (a:bigint,
f:bool): the bigint-entry checker holds (the only `.bigint` name `a` resolves
to a `.vBigint`), and the cond-bool checker holds at cond `"f"` (declared
`.bool`, resolves to `.vBool`). -/

private def Γ_t2_smoke : TypeEnv :=
  ((Typed.TypeEnv.empty.extend "a" .bigint).extend "f" .bool)

private def st_t2_smoke : State :=
  { params := [("a", .vBigint 3), ("f", .vBool true)] }

example : entryBigintTypedBool Γ_t2_smoke st_t2_smoke = true := by native_decide
example : condBoolTypedBool Γ_t2_smoke st_t2_smoke "f" = true := by native_decide

/-! ## WS0a Task 6 — Type preservation through `evalBindings` (arith fragment)

This section proves **type preservation** through the big-step evaluator for
the ARITH-relevant value fragment only:

* `loadConst (.int / .bool / .bytes)`, `loadParam`, `loadProp`,
  `loadConst (.refAlias)`,
* `binOp` with an arithmetic op (`+ - * / %`),
* `unaryOp` with an arith op (`-`, `~`).

Preservation for the crypto / output / `ifVal` / `loop` / `methodCall`
constructors is intentionally DEFERRED to later WS1 work — this slice is what
unblocks the keystone (Task 7) and the WS1 arith retirement.

The statement is the standard one: if a binding's value type-checks to `τ`
under `Γ` (`TypeCheck.typeOfValue`), and the runtime state is well-typed w.r.t.
`Γ` (`StateWellTyped`), then `evalValue` succeeds with a value of kind `τ`, and
the post-binding state stays well-typed w.r.t. the extended environment
`Γ.extend name τ`.

No new `axiom`, no `sorry`: the proofs are by direct case analysis on the
fragment's `ANFValue` constructors, reusing `Eval.evalBinOp` / `Eval.evalValue`
reductions and the two `State.addBinding` lookup helpers below. -/

open RunarVerification.ANF.Eval (EvalError EvalResult)
open RunarVerification.ANF.TypeCheck (typeOfValue isArithOp)

/-! ### `ValueHasKind` — the runtime-value side of a type

Dispatches to the three concrete runtime kinds the arith fragment produces
(`IsBigint` / `IsBool` / `IsBytes`); every other `ANFType` (the crypto /
preimage / point kinds the arith fragment never produces) maps to `True`.
This keeps the invariant minimal while remaining sound: the fragment only ever
*reads* refs of those other types (transported verbatim through
`StateWellTyped`) and only ever *produces* bigint / bool / bytes values. -/
def ValueHasKind (v : Value) (ty : ANFType) : Prop :=
  match ty with
  | .bigint     => Value.IsBigint v
  | .bool       => Value.IsBool v
  | .byteString => Value.IsBytes v
  | _           => True

@[simp] theorem ValueHasKind_bigint (v : Value) :
    ValueHasKind v .bigint = Value.IsBigint v := rfl
@[simp] theorem ValueHasKind_bool (v : Value) :
    ValueHasKind v .bool = Value.IsBool v := rfl
@[simp] theorem ValueHasKind_byteString (v : Value) :
    ValueHasKind v .byteString = Value.IsBytes v := rfl

/-! ### `StateWellTyped` — the runtime state respects the typing context

Every name `Γ` declares at `ty` resolves, in the runtime ANF state, to a value
of kind `ty`.  This is the multi-type generalisation of `EntryBigintTyped`
(which is exactly its `.bigint`-only specialisation). -/
def StateWellTyped (Γ : TypeEnv) (anfSt : State) : Prop :=
  ∀ name ty, Γ.lookup name = some ty →
    ∃ v, anfSt.resolveRef name = some v ∧ ValueHasKind v ty

/-! ### State-extension lemmas (the binding leg)

Two small structural facts about `State.resolveRef` after `State.addBinding`.
Not axioms — direct `simp`/`rfl` proofs over `List.find?`. -/

/-- After binding `name ↦ v`, resolving `name` yields exactly `v`. -/
theorem resolveRef_addBinding_self (s : State) (name : String) (v : Value) :
    (s.addBinding name v).resolveRef name = some v := by
  unfold State.resolveRef State.addBinding State.lookupBinding
  simp only [List.find?_cons, beq_self_eq_true, Option.map_some]
  rfl

/-- After binding `name ↦ v`, resolving any other name `m ≠ name` is
unchanged. -/
theorem resolveRef_addBinding_ne (s : State) (name m : String) (v : Value)
    (h : name ≠ m) :
    (s.addBinding name v).resolveRef m = s.resolveRef m := by
  unfold State.resolveRef State.addBinding State.lookupBinding
  have hbeq : ((name, v).fst == m) = false := beq_false_of_ne h
  simp only [List.find?_cons, hbeq]
  rfl

/-- **State-extension preservation.**  If the current state is well-typed under
`Γ` and the freshly produced value `v` has kind `τ`, then after binding
`name ↦ v` the state is well-typed under `Γ.extend name τ`.  The new name carries
the new kind; every other name inherits `StateWellTyped Γ`. -/
theorem stateWellTyped_addBinding
    (Γ : TypeEnv) (anfSt : State) (name : String) (v : Value) (τ : ANFType)
    (hSt : StateWellTyped Γ anfSt) (hVK : ValueHasKind v τ) :
    StateWellTyped (Γ.extend name τ) (anfSt.addBinding name v) := by
  intro m ty hLk
  by_cases hm : name = m
  · -- new name: lookup gives τ, resolve gives v.
    subst hm
    rw [Typed.TypeEnv.lookup_extend_self] at hLk
    have hty : ty = τ := (Option.some.inj hLk).symm
    subst hty
    exact ⟨v, resolveRef_addBinding_self anfSt name v, hVK⟩
  · -- other name: inherit from `hSt`.
    rw [Typed.TypeEnv.lookup_extend_other Γ name m τ hm] at hLk
    obtain ⟨v', hres, hvk⟩ := hSt m ty hLk
    exact ⟨v', by rw [resolveRef_addBinding_ne anfSt name m v hm]; exact hres, hvk⟩

/-! ### The arith fragment selector -/

/-- `arithFragmentValue b = true` exactly for the scoped value constructors:
the three scalar literals (`int` / `bool` / `bytes`), `refAlias`, `loadParam`,
`loadProp`, an arithmetic `binOp` (`+ - * / %`), and the arith negate `unaryOp`
(`-`).  `thisRef` is OUT of scope (it produces `.addr`, deferred).

**`~` deliberately excluded** (see the `unaryOp` divergence note on
`evalArithBinding_preserves`): `typeOfValue` types `unaryOp "~" : bigint →
bigint` (matching `03-typecheck.ts`'s bitwise-NOT-over-bigint rule), but the
ANF evaluator's `Eval.evalUnaryOp "~"` is the *byte*-inversion path
(`invertBytesValue`), which ERRORS on a `.vBigint` operand.  A `~`-on-bigint
binding therefore type-checks but does NOT evaluate to a value — so a
"`evalValue` succeeds with kind `τ`" preservation claim would be FALSE for it.
Excluding `~` keeps this lemma sound and non-vacuous; the `~` row is a genuine
evaluator/type-checker divergence flagged for WS1 (it does not affect the
arith chain the keystone consumes, which is `+ - * / %` plus negate). -/
def arithFragmentValue : ANFValue → Bool
  | .loadConst (.int _)      => true
  | .loadConst (.bool _)     => true
  | .loadConst (.bytes _)    => true
  | .loadConst (.refAlias _) => true
  | .loadConst .thisRef      => false
  | .loadParam _             => true
  | .loadProp _              => true
  | .binOp op _ _ _          => isArithOp op
  | .unaryOp op _ _          => op == "-"
  | _                        => false

/-- **Evaluation-safety side condition.**  For the partial arith ops `/` and
`%`, `evalBinOp` errors on a zero divisor; every other fragment value evaluates
unconditionally.  This guard pins exactly the divisor-nonzero precondition so
the preservation claim stays both TOTAL and honest (never vacuous): for
`+ - *`, negate, and the literals/refs it is `True`. -/
def arithBindingEvalSafe (v : ANFValue) (s : State) : Prop :=
  match v with
  | .binOp "/" _ r _ => ∀ b : Int, s.resolveRef r = some (.vBigint b) → b ≠ 0
  | .binOp "%" _ r _ => ∀ b : Int, s.resolveRef r = some (.vBigint b) → b ≠ 0
  | _                => True

/-- **Read-correspondence side condition (entry slots).**  `evalValue` reads a
`loadParam pn` via `lookupParam` and a `loadProp pn` via `lookupProp`, whereas
both `typeOfValue` and `StateWellTyped` index those names through `Γ.lookup` /
`resolveRef`.  Since `resolveRef = lookupBinding <|> lookupParam <|> lookupProp`,
the two agree exactly when no binding (or, for `loadParam`, no binding *and* no
property) shadows the name.  This guard pins that agreement for the two entry
constructors; for `refAlias` / `binOp` / `unaryOp` / literals (which already
read through `resolveRef`) it is `True`.  Mirrors the head-correspondence
hypothesis the wave-32 / wave-33 success steps already consume (see
`smoke_wt_soundness_fires`). -/
def arithBindingReadCorr (v : ANFValue) (s : State) : Prop :=
  match v with
  | .loadParam pn => s.lookupParam pn = s.resolveRef pn
  | .loadProp pn  => s.lookupProp pn = s.resolveRef pn
  | _             => True

/-! ### `evalValue` reduction helpers (binOp / unaryOp)

Given the operands' resolved `.vBigint` values and the corresponding
`evalBinOp` / `evalUnaryOp` *result* equation, these reduce the full
`evalValue` of the binding to `Except.ok (res, anfSt)` (the state is
unchanged).  Factored out so the five arith binOps and the negate unaryOp share
one reduction line.  Pure `simp`/`rfl` — no axioms. -/

private theorem binOp_evalValue_of_binOpEq (anfSt : State) (op l r : String)
    (a c : Int) (rt : Option String) (res : Value)
    (hRa : anfSt.resolveRef l = some (.vBigint a))
    (hRc : anfSt.resolveRef r = some (.vBigint c))
    (hb : Eval.evalBinOp op (.vBigint a) (.vBigint c) rt = Except.ok res) :
    Eval.evalValue anfSt (.binOp op l r rt) = Except.ok (res, anfSt) := by
  rw [show Eval.evalValue anfSt (.binOp op l r rt)
        = (Eval.evalBinOp op (.vBigint a) (.vBigint c) rt) >>= (fun res => pure (res, anfSt)) by
      simp only [Eval.evalValue, Eval.lookupRef, hRa, hRc]; rfl]
  rw [hb]; rfl

private theorem unaryOp_evalValue_of_eq (anfSt : State) (op o : String)
    (a : Int) (rt : Option String) (res : Value)
    (hRa : anfSt.resolveRef o = some (.vBigint a))
    (hu : Eval.evalUnaryOp op (.vBigint a) rt = Except.ok res) :
    Eval.evalValue anfSt (.unaryOp op o rt) = Except.ok (res, anfSt) := by
  rw [show Eval.evalValue anfSt (.unaryOp op o rt)
        = (Eval.evalUnaryOp op (.vBigint a) rt) >>= (fun res => pure (res, anfSt)) by
      simp only [Eval.evalValue, Eval.lookupRef, hRa]; rfl]
  rw [hu]; rfl

/-! ### Per-binding preservation (the key lemma) -/

/-- **Per-binding type preservation.**  For a binding whose value is in the
arith fragment, type-checks to `τ` under `Γ`, with a well-typed state, the
divisor-nonzero side condition (`hSafe`) and the entry-read correspondence
(`hCorr`): `evalValue` succeeds with a value of kind `τ`, and the post-binding
state is well-typed under `Γ.extend b.name τ`. -/
theorem evalArithBinding_preserves
    (retEnv : List (String × ANFType)) (Γ : TypeEnv) (anfSt : State)
    (b : ANFBinding) (τ : ANFType)
    (hFrag : arithFragmentValue b.value = true)
    (hTy : typeOfValue retEnv Γ b.value = some τ)
    (hSt : StateWellTyped Γ anfSt)
    (hSafe : arithBindingEvalSafe b.value anfSt)
    (hCorr : arithBindingReadCorr b.value anfSt) :
    ∃ v, Eval.evalValue anfSt b.value = Except.ok (v, anfSt) ∧ ValueHasKind v τ ∧
      StateWellTyped (Γ.extend b.name τ) (anfSt.addBinding b.name v) := by
  -- `evalValue` returns `(value, state)` with the state unchanged on every
  -- fragment constructor, so the binding leg uses `addBinding b.name (value)`.
  obtain ⟨name, value, sl⟩ := b
  simp only [ANFBinding.value, ANFBinding.name] at *
  cases value with
  | loadConst c =>
    cases c with
    | int i =>
      simp only [typeOfValue] at hTy
      have hτ : τ = .bigint := (Option.some.inj hTy).symm
      subst hτ
      exact ⟨.vBigint i, by simp only [Eval.evalValue], ⟨i, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint i) .bigint hSt ⟨i, rfl⟩⟩
    | bool bb =>
      simp only [typeOfValue] at hTy
      have hτ : τ = .bool := (Option.some.inj hTy).symm
      subst hτ
      exact ⟨.vBool bb, by simp only [Eval.evalValue], ⟨bb, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBool bb) .bool hSt ⟨bb, rfl⟩⟩
    | bytes by_ =>
      simp only [typeOfValue] at hTy
      have hτ : τ = .byteString := (Option.some.inj hTy).symm
      subst hτ
      exact ⟨.vBytes by_, by simp only [Eval.evalValue], ⟨by_, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBytes by_) .byteString hSt ⟨by_, rfl⟩⟩
    | refAlias n =>
      -- `typeOfValue (.loadConst (.refAlias n)) = Γ.lookup n`; eval reads via
      -- `lookupRef = resolveRef`, so `hSt` connects directly.
      simp only [typeOfValue] at hTy
      obtain ⟨v, hres, hvk⟩ := hSt n τ hTy
      refine ⟨v, ?_, hvk, stateWellTyped_addBinding Γ anfSt name v τ hSt hvk⟩
      simp only [Eval.evalValue, Eval.lookupRef, hres]; rfl
    | thisRef =>
      simp only [arithFragmentValue, Bool.false_eq_true] at hFrag   -- out of fragment
  | loadParam pn =>
    -- `typeOfValue (.loadParam pn) = Γ.lookup pn`; eval reads via `lookupParam`,
    -- which `hCorr` equates to `resolveRef pn`, so `hSt` connects.
    simp only [typeOfValue] at hTy
    obtain ⟨v, hres, hvk⟩ := hSt pn τ hTy
    refine ⟨v, ?_, hvk, stateWellTyped_addBinding Γ anfSt name v τ hSt hvk⟩
    simp only [arithBindingReadCorr] at hCorr
    have hLp : anfSt.lookupParam pn = some v := by rw [hCorr]; exact hres
    simp only [Eval.evalValue, hLp]
  | loadProp pn =>
    simp only [typeOfValue] at hTy
    obtain ⟨v, hres, hvk⟩ := hSt pn τ hTy
    refine ⟨v, ?_, hvk, stateWellTyped_addBinding Γ anfSt name v τ hSt hvk⟩
    simp only [arithBindingReadCorr] at hCorr
    have hLp : anfSt.lookupProp pn = some v := by rw [hCorr]; exact hres
    simp only [Eval.evalValue, hLp]
  | binOp op l r rt =>
    -- `typeOfValue` forces both operands `.bigint`; `hSt` ⇒ both resolve to a
    -- `.vBigint`; `evalBinOp` on two `.vBigint` produces a `.vBigint` for the
    -- arith ops (`/`,`%` need the nonzero divisor supplied by `hSafe`).
    simp only [arithFragmentValue] at hFrag   -- hFrag : isArithOp op = true
    simp only [typeOfValue] at hTy
    -- `hTy` shape: `match Γ.lookup l, Γ.lookup r with | some .bigint, some .bigint => …`.
    have hLR : Γ.lookup l = some .bigint ∧ Γ.lookup r = some .bigint := by
      revert hTy
      cases hl : Γ.lookup l with
      | none => intro h; simp only [reduceCtorEq] at h
      | some tl =>
        cases tl <;> intro hTy <;>
          first
          | (cases hr : Γ.lookup r with
             | none => rw [hr] at hTy; simp only [reduceCtorEq] at hTy
             | some tr => cases tr <;> simp_all)
          | simp_all
    obtain ⟨hLb, hRb⟩ := hLR
    obtain ⟨a, hRa⟩ := operand_resolveRef_vBigint_of_typedEntry Γ anfSt l
      (fun _ hh => hSt _ _ hh) hLb
    obtain ⟨c, hRc⟩ := operand_resolveRef_vBigint_of_typedEntry Γ anfSt r
      (fun _ hh => hSt _ _ hh) hRb
    -- `typeOfValue` returns `.bigint` for an arith op on two bigints.
    have hτ : τ = .bigint := by
      rw [hLb, hRb] at hTy; rw [hFrag] at hTy; exact (Option.some.inj hTy).symm
    subst hτ
    -- The five arith ops, splitting `/` `%` on the nonzero-divisor guard.
    -- (`rcases` directly on the left-associated `isArithOp` disjunction — no
    -- `tauto`, which is unavailable in this project.)
    unfold isArithOp at hFrag
    simp only [Bool.or_eq_true, beq_iff_eq] at hFrag
    rcases hFrag with (((h|h)|h)|h)|h <;> subst h
    · -- "+"
      exact ⟨.vBigint (a + c),
        binOp_evalValue_of_binOpEq anfSt "+" l r a c rt _ hRa hRc (by simp only [Eval.evalBinOp]; rfl),
        ⟨a + c, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint (a + c)) .bigint hSt ⟨_, rfl⟩⟩
    · -- "-"
      exact ⟨.vBigint (a - c),
        binOp_evalValue_of_binOpEq anfSt "-" l r a c rt _ hRa hRc (by simp only [Eval.evalBinOp]; rfl),
        ⟨a - c, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint (a - c)) .bigint hSt ⟨_, rfl⟩⟩
    · -- "*"
      exact ⟨.vBigint (a * c),
        binOp_evalValue_of_binOpEq anfSt "*" l r a c rt _ hRa hRc (by simp only [Eval.evalBinOp]; rfl),
        ⟨a * c, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint (a * c)) .bigint hSt ⟨_, rfl⟩⟩
    · -- "/": nonzero divisor from `hSafe`.
      have hc0 : c ≠ 0 := by simp only [arithBindingEvalSafe] at hSafe; exact hSafe c hRc
      have hb : Eval.evalBinOp "/" (.vBigint a) (.vBigint c) rt = Except.ok (.vBigint (a / c)) := by
        simp only [Eval.evalBinOp]; rw [if_neg (by simpa using hc0)]; rfl
      exact ⟨.vBigint (a / c),
        binOp_evalValue_of_binOpEq anfSt "/" l r a c rt _ hRa hRc hb,
        ⟨a / c, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint (a / c)) .bigint hSt ⟨_, rfl⟩⟩
    · -- "%": nonzero divisor from `hSafe`.
      have hc0 : c ≠ 0 := by simp only [arithBindingEvalSafe] at hSafe; exact hSafe c hRc
      have hb : Eval.evalBinOp "%" (.vBigint a) (.vBigint c) rt = Except.ok (.vBigint (a % c)) := by
        simp only [Eval.evalBinOp]; rw [if_neg (by simpa using hc0)]; rfl
      exact ⟨.vBigint (a % c),
        binOp_evalValue_of_binOpEq anfSt "%" l r a c rt _ hRa hRc hb,
        ⟨a % c, rfl⟩,
        stateWellTyped_addBinding Γ anfSt name (.vBigint (a % c)) .bigint hSt ⟨_, rfl⟩⟩
  | unaryOp op operand rt =>
    -- `arithFragmentValue` admits only `op = "-"` here.  `typeOfValue` forces
    -- the operand `.bigint`; negate produces a `.vBigint` on a `.vBigint`.
    simp only [arithFragmentValue, beq_iff_eq] at hFrag
    subst hFrag
    simp only [typeOfValue] at hTy
    have hOb : Γ.lookup operand = some .bigint := by
      revert hTy
      cases hl : Γ.lookup operand with
      | none => intro h; simp only [reduceCtorEq] at h
      | some tl => cases tl <;> intro hTy <;> simp_all
    obtain ⟨a, hRa⟩ := operand_resolveRef_vBigint_of_typedEntry Γ anfSt operand
      (fun _ hh => hSt _ _ hh) hOb
    have hτ : τ = .bigint := by
      rw [hOb] at hTy; exact (Option.some.inj hTy).symm
    subst hτ
    exact ⟨.vBigint (-a),
      unaryOp_evalValue_of_eq anfSt "-" operand a rt _ hRa (by simp only [Eval.evalUnaryOp]; rfl),
      ⟨-a, rfl⟩,
      stateWellTyped_addBinding Γ anfSt name (.vBigint (-a)) .bigint hSt ⟨_, rfl⟩⟩
  | _ =>
    -- All remaining constructors are out of the arith fragment:
    -- `arithFragmentValue` is `false`, contradicting `hFrag`.
    simp only [arithFragmentValue, Bool.false_eq_true] at hFrag

/-! ### Body-level preservation (induction over the binding list)

The per-binding lemma above carries two per-state side conditions
(`arithBindingEvalSafe` for `/`,`%` and `arithBindingReadCorr` for `loadParam`,
`loadProp`).  Those depend on the *running* state, which changes as bindings
accumulate, so they cannot be hoisted to the initial state for a uniform
binding-list sweep.  The body-level lemma therefore ranges over the
**guard-free arith fragment** — the scoped values for which BOTH side
conditions are unconditionally `True`:

* the three scalar literals (`int` / `bool` / `bytes`),
* `refAlias` (reads through `resolveRef`, so no read-correspondence needed),
* `binOp` with `+`, `-`, `*` (total — no zero-divisor obligation),
* `unaryOp` with `-` (negate).

`/`, `%`, `loadParam`, `loadProp` are excluded here (they remain covered by the
per-binding lemma when their side conditions are supplied).  This guard-free
fragment is exactly the arith chain the keystone (Task 7) and the WS1 arith
retirement consume: a sequence of `+ - *`-binOps / negate over operand refs. -/

/-- The guard-free arith fragment: literals, `refAlias`, `binOp (+,-,*)`,
`unaryOp (-)`.  Excludes `/`, `%`, `loadParam`, `loadProp` (whose per-binding
preservation carries a running-state side condition). -/
def arithFragmentValueGuardFree : ANFValue → Bool
  | .loadConst (.int _)      => true
  | .loadConst (.bool _)     => true
  | .loadConst (.bytes _)    => true
  | .loadConst (.refAlias _) => true
  | .binOp op _ _ _          => op == "+" || op == "-" || op == "*"
  | .unaryOp op _ _          => op == "-"
  | _                        => false

/-- The guard-free fragment is a sub-fragment of the full arith fragment. -/
theorem arithFragmentValue_of_guardFree {v : ANFValue}
    (h : arithFragmentValueGuardFree v = true) : arithFragmentValue v = true := by
  cases v with
  | loadConst c => cases c <;> simp_all [arithFragmentValueGuardFree, arithFragmentValue]
  | binOp op l r rt =>
      simp only [arithFragmentValueGuardFree, Bool.or_eq_true, beq_iff_eq] at h
      simp only [arithFragmentValue, isArithOp, Bool.or_eq_true, beq_iff_eq]
      rcases h with (h|h)|h <;> subst h <;> simp
  | unaryOp op o rt => simpa [arithFragmentValueGuardFree, arithFragmentValue] using h
  | _ => simp_all [arithFragmentValueGuardFree]

/-- The guard-free fragment never triggers the divisor-nonzero obligation. -/
theorem evalSafe_of_guardFree {v : ANFValue} (s : State)
    (h : arithFragmentValueGuardFree v = true) : arithBindingEvalSafe v s := by
  cases v with
  | loadConst c => cases c <;> trivial
  | binOp op l r rt =>
      -- `op ∈ {+,-,*}`, so the `arithBindingEvalSafe` match takes the `_` arm.
      simp only [arithFragmentValueGuardFree, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (h|h)|h <;> subst h <;> trivial
  | _ => trivial

/-- The guard-free fragment never triggers the entry-read-correspondence
obligation (it has no `loadParam` / `loadProp`). -/
theorem readCorr_of_guardFree {v : ANFValue} (s : State)
    (h : arithFragmentValueGuardFree v = true) : arithBindingReadCorr v s := by
  cases v with
  | loadConst c => cases c <;> trivial
  | _ => trivial

/-- **`checkBody` head reduction (guard-free).**  For a guard-free head (never
`ifVal` / `loop`), `checkBody` of a `cons` reduces to the `typeOfValue` branch:
type the head, then continue with the extended environment.  Discharges the
`v ≠ ifVal` / `v ≠ loop` side goals the `checkBody` match raises. -/
private theorem checkBody_cons_guardFree
    (retEnv : List (String × ANFType)) (Γ : TypeEnv)
    (name : String) (v : ANFValue) (sl : Option SourceLoc) (rest : List ANFBinding)
    (hgf : arithFragmentValueGuardFree v = true) :
    TypeCheck.checkBody retEnv Γ (.mk name v sl :: rest)
      = (match typeOfValue retEnv Γ v with
         | some τ => TypeCheck.checkBody retEnv (Γ.extend name τ) rest
         | none => none) := by
  cases v with
  | loadConst c =>
      cases c <;>
        first
        | (rw [TypeCheck.checkBody] <;> first | rfl | (intro _ _ _ h; cases h))
        | simp [arithFragmentValueGuardFree] at hgf
  | binOp op l r rt => rw [TypeCheck.checkBody] <;> first | rfl | (intro _ _ _ h; cases h)
  | unaryOp op o rt => rw [TypeCheck.checkBody] <;> first | rfl | (intro _ _ _ h; cases h)
  | _ => simp [arithFragmentValueGuardFree] at hgf

/-- **Body-level type preservation (strong form).**  For a binding list whose
values are all in the guard-free arith fragment and which type-checks under `Γ`
(`checkBody` succeeds with final environment `Γ'`), starting from a well-typed
state: `evalBindings` succeeds with a final state well-typed under `Γ'`.  Proven
by induction on the binding list, each step discharged by
`evalArithBinding_preserves` (its side conditions supplied by the guard-free
lemmas). -/
theorem evalArithBindings_preserves_strong
    (retEnv : List (String × ANFType)) :
    ∀ (body : List ANFBinding) (Γ Γ' : TypeEnv) (anfSt : State),
      body.all (arithFragmentValueGuardFree ·.value) = true →
      TypeCheck.checkBody retEnv Γ body = some Γ' →
      StateWellTyped Γ anfSt →
      ∃ anfSt', Eval.evalBindings anfSt body = Except.ok anfSt' ∧ StateWellTyped Γ' anfSt'
  | [], Γ, Γ', anfSt, _, hChk, hSt => by
      -- empty body: `checkBody … [] = some Γ`, so `Γ' = Γ`; `evalBindings … [] = ok anfSt`.
      simp only [TypeCheck.checkBody, Option.some.injEq] at hChk
      subst hChk
      exact ⟨anfSt, by simp only [Eval.evalBindings], hSt⟩
  | .mk name v sl :: rest, Γ, Γ', anfSt, hAll, hChk, hSt => by
      -- Head is guard-free; peel the `body.all`.
      rw [List.all_cons, Bool.and_eq_true] at hAll
      obtain ⟨hHeadFrag, hRestFrag⟩ := hAll
      simp only [ANFBinding.value] at hHeadFrag
      -- `checkBody` on a guard-free head goes through the `typeOfValue` branch.
      rw [checkBody_cons_guardFree retEnv Γ name v sl rest hHeadFrag] at hChk
      -- Extract `typeOfValue … v = some τ` and the type-checked tail.
      obtain ⟨τ, hTyV, hChkRest⟩ :
          ∃ τ, typeOfValue retEnv Γ v = some τ ∧
            TypeCheck.checkBody retEnv (Γ.extend name τ) rest = some Γ' := by
        revert hChk
        cases hT : typeOfValue retEnv Γ v with
        | none => intro hChk; simp only [hT] at hChk; exact absurd hChk (by simp)
        | some τ => intro hChk; simp only [hT] at hChk; exact ⟨τ, rfl, hChk⟩
      -- Apply the per-binding lemma (side conditions from the guard-free lemmas).
      obtain ⟨vval, hEvV, _hvk, hStExt⟩ :=
        evalArithBinding_preserves retEnv Γ anfSt (.mk name v sl) τ
          (by simp only [ANFBinding.value]; exact arithFragmentValue_of_guardFree hHeadFrag)
          (by simp only [ANFBinding.value]; exact hTyV)
          hSt
          (by simp only [ANFBinding.value]; exact evalSafe_of_guardFree anfSt hHeadFrag)
          (by simp only [ANFBinding.value]; exact readCorr_of_guardFree anfSt hHeadFrag)
      simp only [ANFBinding.value, ANFBinding.name] at hEvV hStExt
      -- Step the evaluator past the head, then recurse on `rest`.
      have hStep : Eval.evalBindings anfSt (.mk name v sl :: rest)
          = Eval.evalBindings (anfSt.addBinding name vval) rest := by
        simp only [Eval.evalBindings, hEvV]; rfl
      rw [hStep]
      exact evalArithBindings_preserves_strong retEnv rest (Γ.extend name τ) Γ'
        (anfSt.addBinding name vval) hRestFrag hChkRest hStExt

/-- **Body-level preservation (`isSome` form).**  The corollary the keystone
consumes: a guard-free arith body that type-checks runs to completion (no
evaluation error) from any well-typed state. -/
theorem evalArithBindings_preserves
    (retEnv : List (String × ANFType)) (Γ Γ' : TypeEnv) (anfSt : State)
    (body : List ANFBinding)
    (hAllFrag : body.all (arithFragmentValueGuardFree ·.value) = true)
    (hBodyTy : TypeCheck.checkBody retEnv Γ body = some Γ')
    (hSt0 : StateWellTyped Γ anfSt) :
    (Eval.evalBindings anfSt body).toOption.isSome = true := by
  obtain ⟨anfSt', hEv, _⟩ :=
    evalArithBindings_preserves_strong retEnv body Γ Γ' anfSt hAllFrag hBodyTy hSt0
  rw [hEv]; rfl

/-! ### MANDATORY smoke test

A concrete 2-binding arith body `t1 = a + b ; t2 = t1 * a` over an entry where
`a`, `b` are `.bigint` params.  We exhibit a well-typed entry state, show the
body type-checks and is guard-free, and fire `evalArithBindings_preserves` —
demonstrating the body runs to completion (and, via the strong form, lands in a
well-typed final state binding `t1 = 7`, `t2 = 21`). -/

/-- Smoke env: `a : bigint`, `b : bigint`. -/
private def Γ_t6_smoke : TypeEnv :=
  (Typed.TypeEnv.empty.extend "a" .bigint).extend "b" .bigint

/-- Smoke entry state: `a = 3`, `b = 4`. -/
private def st_t6_smoke : State :=
  { params := [("a", .vBigint 3), ("b", .vBigint 4)] }

/-- Smoke body: `t1 = a + b ; t2 = t1 * a`. -/
private def body_t6_smoke : List ANFBinding :=
  [ .mk "t1" (.binOp "+" "a" "b" none) none,
    .mk "t2" (.binOp "*" "t1" "a" none) none ]

/-- The smoke body is entirely in the guard-free arith fragment. -/
theorem smoke_t6_guardFree :
    body_t6_smoke.all (arithFragmentValueGuardFree ·.value) = true := by native_decide

/-- The smoke entry is well-typed under `Γ_t6_smoke`. -/
theorem smoke_t6_stateWellTyped : StateWellTyped Γ_t6_smoke st_t6_smoke := by
  intro nm ty hLk
  by_cases ha : nm = "a"
  · subst ha
    have : ty = .bigint := by
      have : Γ_t6_smoke.lookup "a" = some .bigint := rfl
      rw [this] at hLk; exact (Option.some.inj hLk).symm
    subst this; exact ⟨.vBigint 3, rfl, ⟨3, rfl⟩⟩
  · by_cases hb : nm = "b"
    · subst hb
      have : ty = .bigint := by
        have : Γ_t6_smoke.lookup "b" = some .bigint := rfl
        rw [this] at hLk; exact (Option.some.inj hLk).symm
      subst this; exact ⟨.vBigint 4, rfl, ⟨4, rfl⟩⟩
    · exfalso
      have hbb : ("b" == nm) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hb h.symm
      have haa : ("a" == nm) = false := by rw [beq_eq_false_iff_ne]; exact fun h => ha h.symm
      simp only [Γ_t6_smoke, Typed.TypeEnv.lookup, Typed.TypeEnv.extend, Typed.TypeEnv.empty,
        List.find?_cons, hbb, haa, List.find?_nil, Option.map_none, reduceCtorEq] at hLk

/-- **Smoke — `evalArithBindings_preserves` FIRES.**  The 2-binding arith body
type-checks (witnessed by `checkBody … = some _`) and runs to completion from the
well-typed entry. -/
theorem smoke_t6_body_runs :
    (Eval.evalBindings st_t6_smoke body_t6_smoke).toOption.isSome = true := by
  -- `checkBody` succeeds (decidable `isSome`); extract its final env, then feed
  -- the discharge through the body lemma.
  obtain ⟨Γ', hChk⟩ : ∃ Γ', TypeCheck.checkBody [] Γ_t6_smoke body_t6_smoke = some Γ' :=
    Option.isSome_iff_exists.mp (by native_decide)
  exact evalArithBindings_preserves [] Γ_t6_smoke Γ' st_t6_smoke body_t6_smoke
    smoke_t6_guardFree hChk smoke_t6_stateWellTyped

/-- Smoke — the strong form lands in a well-typed final state (sanity: the body
evaluates without error and the final env types every bound temp). -/
theorem smoke_t6_final_wellTyped :
    ∃ Γ' anfSt', TypeCheck.checkBody [] Γ_t6_smoke body_t6_smoke = some Γ' ∧
      Eval.evalBindings st_t6_smoke body_t6_smoke = Except.ok anfSt' ∧
      StateWellTyped Γ' anfSt' := by
  obtain ⟨Γ', hChk⟩ : ∃ Γ', TypeCheck.checkBody [] Γ_t6_smoke body_t6_smoke = some Γ' :=
    Option.isSome_iff_exists.mp (by native_decide)
  obtain ⟨anfSt', hEv, hStW⟩ :=
    evalArithBindings_preserves_strong [] body_t6_smoke Γ_t6_smoke Γ' st_t6_smoke
      smoke_t6_guardFree hChk smoke_t6_stateWellTyped
  exact ⟨Γ', anfSt', hChk, hEv, hStW⟩

end WellTyped
end RunarVerification.ANF
