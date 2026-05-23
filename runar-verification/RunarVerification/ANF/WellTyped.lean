import RunarVerification.ANF.Syntax
import RunarVerification.ANF.Eval
import RunarVerification.ANF.Typed
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

end WellTyped
end RunarVerification.ANF
