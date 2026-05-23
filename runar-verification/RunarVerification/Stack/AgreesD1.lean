import RunarVerification.Stack.Eval

/-!
# `AgreesD1` — runtime selection substrate for the multi-method dispatch family

This module is the first dedicated substrate file for the Phase-D **D1
multi-method Merkle dispatch** retirement (axiom
`merkle_dispatch_selection_correct` / sub-omnibus
`compileSafe_observational_correct_modulo_dispatch_codegen` in
`Pipeline.lean`). It is intentionally standalone: it imports only
`RunarVerification.Stack.Eval` and is NOT wired into any existing
file's import graph. Integration is the orchestrator's job.

## What the compiler does (the lowering map this file targets)

For a program with `n ≥ 2` public methods, `Script/Emit.lean`
(`emitDispatch` / `emitDispatchChain`, lines 351-360) emits, for each
public method body `body_i`:

```
[OP_DUP push(0) OP_NUMEQUAL OP_IF OP_DROP <body0> OP_ELSE]
[OP_DUP push(1) OP_NUMEQUAL OP_IF OP_DROP <body1> OP_ELSE]
…
[push(n-1) OP_NUMEQUALVERIFY <body_{n-1}>]
[OP_ENDIF * (n-1)]
```

`Script/Parse.lean` (`parseScriptFrame`, lines 459-474) matches the
`OP_IF` / `OP_ELSE` / `OP_ENDIF` brackets and reconstructs each
non-last branch as a nested `.ifOp thn (some els)` op (see
`Stack/Eval.lean#runOps`, lines 813-830, for the runtime IF
semantics). So `runParsedBytes` of an `n = 2` dispatch chain runs the
flat op-list:

```
[.dup, .push (.bigint 0), .opcode "OP_NUMEQUAL",
 .ifOp (.opcode "OP_DROP" :: body0)
       (some (.push (.bigint 1) :: .opcode "OP_NUMEQUALVERIFY" :: body1))]
```

## What this file proves

The runtime *selection step* of the `n = 2` dispatch head. With the
caller's method-index witness `i = 0` on top of stack
(`stack = vBigint 0 :: rest`), the head opcodes
`OP_DUP push(0) OP_NUMEQUAL OP_IF OP_DROP` consume the witness and the
duplicated copy, and `runOps` of the whole parsed op-list collapses to
`runOps body0 { stack := rest }`. That is exactly the
`merkle_dispatch_selection_correct` conclusion shape for the `i = 0`
branch — the post-dispatch stack is `rest`.

This is the substrate the D1 axiom currently stands in for: the
selection rewrite itself, proven from the `runOps` / `stepNonIf`
definitions. The single-public consume theorems then handle
`runOps body0` unchanged (they are body-level, witness-agnostic), so
the capstone `compileSafe_multi_public_observational_correct` (which
already takes `hDispatchToOps` as a hypothesis) can consume this
directly.
-/

namespace RunarVerification
namespace Stack
namespace AgreesD1

open RunarVerification.ANF.Eval (Value)
open RunarVerification.Stack.Eval

/-- The runtime shape of the parsed `n = 2` dispatch head body that the
recursive-descent parser reconstructs for two public methods. The
caller supplies the two branch bodies `body0` / `body1`; this is the
*entire* op-list `runParsedBytes` runs (head + nested IF). -/
def dispatch2Ops (body0 body1 : List StackOp) : List StackOp :=
  [ .dup,
    .push (.bigint 0),
    .opcode "OP_NUMEQUAL",
    .ifOp (.opcode "OP_DROP" :: body0)
      (some (.push (.bigint 1) :: .opcode "OP_NUMEQUALVERIFY" :: body1)) ]

/-- `OP_DUP` is not an `.ifOp` (discharges `runOps_cons_nonIf_eq`). -/
private theorem dup_not_if :
    ∀ thn els, (StackOp.dup) ≠ .ifOp thn els := by
  intro _ _ h; exact StackOp.noConfusion h

/-- `OP_DROP` (as a named opcode) is not an `.ifOp`. -/
private theorem dropOp_not_if :
    ∀ thn els, (StackOp.opcode "OP_DROP") ≠ .ifOp thn els := by
  intro _ _ h; exact StackOp.noConfusion h

/-! ## Branch-0 selection

The core selection lemma. With method-index witness `0` on top of
stack, the dispatch head selects branch 0 and discards both the
witness and its duplicate, leaving the body to run on `rest`. -/

set_option maxHeartbeats 800000 in
/-- **D1 branch-0 selection (substrate).**

When the unlocking caller pushed dispatch index `0`
(`initial.stack = vBigint 0 :: rest`), running the parsed 2-method
dispatch op-list equals running `body0` on the post-dispatch stack
`{ initial with stack := rest }`.

This is the `i = 0` instance of the `merkle_dispatch_selection_correct`
conclusion, proven directly from the `runOps` / `stepNonIf` / `applyDup`
/ `liftIntBin` definitions. The `OP_NUMEQUAL` of `0 = 0` reduces to
`vBool true`, the reconstructed `.ifOp` takes its `thn` branch, and
`OP_DROP` removes the witness copy the leading `OP_DUP` created. -/
theorem dispatch2_select_branch0
    (body0 body1 : List StackOp)
    (initial : StackState)
    (rest : List Value)
    (hWitness : initial.stack = Value.vBigint (Int.ofNat 0) :: rest) :
    runOps (dispatch2Ops body0 body1) initial
      = runOps body0 { initial with stack := rest } := by
  -- The intermediate states, written inline (no `set` — this project
  -- has no Mathlib). Each opcode step is discharged as a closed `rfl`-
  -- backed equation, then rewritten into the goal.
  unfold dispatch2Ops
  -- OP_DUP: duplicate the witness `0`.
  rw [runOps_cons_nonIf_eq StackOp.dup _ initial dup_not_if]
  have hDup : stepNonIf StackOp.dup initial
      = .ok { initial with stack :=
          (Value.vBigint (Int.ofNat 0) :: Value.vBigint (Int.ofNat 0) :: rest) } := by
    rw [stepNonIf_dup]; unfold applyDup
    rw [hWitness]; simp only [StackState.push, hWitness]
  rw [hDup]
  simp only []
  -- push 0.
  rw [runOps_cons_nonIf_eq (.push (.bigint 0)) _ _
    (by intro _ _ h; exact StackOp.noConfusion h)]
  have hPush : stepNonIf (.push (.bigint 0))
      { initial with stack :=
          (Value.vBigint (Int.ofNat 0) :: Value.vBigint (Int.ofNat 0) :: rest) }
      = .ok { initial with stack :=
          (Value.vBigint (Int.ofNat 0)
            :: Value.vBigint (Int.ofNat 0)
            :: Value.vBigint (Int.ofNat 0) :: rest) } := by
    rw [stepNonIf_push_bigint]; rfl
  rw [hPush]
  simp only []
  -- OP_NUMEQUAL: pop two `0`s → vBool (0 = 0) = true.
  rw [runOps_cons_nonIf_eq (.opcode "OP_NUMEQUAL") _ _
    (by intro _ _ h; exact StackOp.noConfusion h)]
  have hNumEq : stepNonIf (.opcode "OP_NUMEQUAL")
      { initial with stack :=
          (Value.vBigint (Int.ofNat 0)
            :: Value.vBigint (Int.ofNat 0)
            :: Value.vBigint (Int.ofNat 0) :: rest) }
      = .ok { initial with stack :=
          (Value.vBool true :: Value.vBigint (Int.ofNat 0) :: rest) } := by
    rw [stepNonIf_opcode]; rfl
  rw [hNumEq]
  simp only []
  -- The reconstructed `.ifOp`: pop `vBool true`, take the thn branch.
  have hIf :
      runOps
        [.ifOp (.opcode "OP_DROP" :: body0)
          (some (.push (.bigint 1) :: .opcode "OP_NUMEQUALVERIFY" :: body1))]
        { initial with stack :=
            (Value.vBool true :: Value.vBigint (Int.ofNat 0) :: rest) }
      = runOps (.opcode "OP_DROP" :: body0)
          { initial with stack := (Value.vBigint (Int.ofNat 0) :: rest) } := by
    -- Expose the outer `.ifOp` step (one layer), pop the `vBool true`
    -- condition, take the thn branch. The true-branch runs `thn` then
    -- the empty trailing `rest`; the `runOps []` is identity, collapsed
    -- by case-splitting on the thn run.
    rw [runOps]
    unfold StackState.pop?
    simp only [asBool?]
    cases hT : runOps (.opcode "OP_DROP" :: body0)
        { initial with stack := (Value.vBigint (Int.ofNat 0) :: rest) } with
    | error e => rfl
    | ok s'' => simp only [runOps_nil]
  rw [hIf]
  -- OP_DROP removes the witness copy → { initial with stack := rest }.
  rw [runOps_cons_nonIf_eq (.opcode "OP_DROP") _ _ dropOp_not_if]
  have hDrop : stepNonIf (.opcode "OP_DROP")
      { initial with stack := (Value.vBigint (Int.ofNat 0) :: rest) }
      = .ok { initial with stack := rest } := by
    rw [stepNonIf_opcode]; unfold runOpcode applyDrop; rfl
  rw [hDrop]

/-! ## Smoke

Concrete instantiation. The branch-0 selection fires on a real
2-method dispatch op-list: witness `0`, `body0 = [OP_1ADD]`,
`body1 = [OP_2MUL]`, post-witness stack `[7]`. Running the parsed
dispatch leaves `[8]` (= `runOps [OP_1ADD]` on `[7]`). Proven by the
general lemma plus single-step evaluation of `OP_1ADD` — no axiom. -/

/-- Single-step evaluation of `OP_1ADD` on `[7]` yields `[8]`. -/
private theorem run_1add_on_7 :
    runOps [.opcode "OP_1ADD"]
        ({ stack := [Value.vBigint 7] } : StackState)
      = .ok ({ stack := [Value.vBigint 8] } : StackState) := by
  rw [runOps_cons_nonIf_eq (.opcode "OP_1ADD") _ _
    (by intro _ _ h; exact StackOp.noConfusion h)]
  have hStep : stepNonIf (.opcode "OP_1ADD")
      ({ stack := [Value.vBigint 7] } : StackState)
      = .ok ({ stack := [Value.vBigint 8] } : StackState) := by
    rw [stepNonIf_opcode]; rfl
  rw [hStep]
  simp only [runOps_nil]

/-- Concrete branch-0 selection: the parsed 2-method dispatch with
witness `0` on `[0, 7]` reduces to `[8]` (branch 0 = `OP_1ADD`).
Confirms `dispatch2_select_branch0` is not vacuous. -/
theorem dispatch2_select_branch0_smoke :
    runOps
        (dispatch2Ops [.opcode "OP_1ADD"] [.opcode "OP_2MUL"])
        ({ stack := [Value.vBigint (Int.ofNat 0), Value.vBigint 7] } : StackState)
      = .ok ({ stack := [Value.vBigint 8] } : StackState) := by
  rw [dispatch2_select_branch0 [.opcode "OP_1ADD"] [.opcode "OP_2MUL"]
    ({ stack := [Value.vBigint (Int.ofNat 0), Value.vBigint 7] } : StackState)
    [Value.vBigint 7] rfl]
  exact run_1add_on_7

end AgreesD1
end Stack
end RunarVerification
