import RunarVerification.Stack.Eval
import RunarVerification.Stack.Sim

/-!
# Stack IR — consensus acceptance bit (truthy top-of-stack)

Bitcoin consensus does NOT accept a script merely because it completes
without a VM error: the script must ALSO leave a truthy value on top of
the stack. The Rúnar compiler's terminal-assert elision (`lowerMethod`
drops a public method's trailing `OP_VERIFY`, leaving the asserted bool
as the script's implicit return value) is designed around exactly that
consensus rule.

The development's original observational surface compared mere
COMPLETION bits (`(runParsedBytes …).toOption.isSome`), which disagrees
with consensus on any assert-terminated public method evaluated on a
non-satisfying entry: the ANF evaluator's `assert` errors while the
deployed bytes complete with `false` on top (pinned by the `termCx_*`
theorems in `Pipeline.lean`).

This module defines the consensus-faithful acceptance bit
`scriptAccepts` and proves the **keystone elision lemma**
`runOps_append_verify_isSome_iff_scriptAccepts`: appending one
`OP_VERIFY` to an op list completes exactly when the bare op list is
*accepted*. The truthiness predicate `topTruthy` mirrors EXACTLY the
`OP_VERIFY` arm of `runOpcode` (`asBool?`-based) so the lemma is
definitional on each case.
-/

namespace RunarVerification.Stack
namespace Eval

open RunarVerification.ANF.Eval (Value EvalError EvalResult)

/-- Truthiness of the top of a stack, mirroring EXACTLY the `OP_VERIFY`
arm of `runOpcode`: an empty stack is falsy (consensus treats a script
that leaves nothing on the stack as invalid), and a top value with no
boolean interpretation (`asBool? = none` — e.g. `vOpaque`) is falsy
here because `OP_VERIFY` rejects it with a type error. -/
def topTruthy : List Value → Bool
  | [] => false
  | v :: _ =>
      match asBool? v with
      | some b => b
      | none   => false

@[simp] theorem topTruthy_nil : topTruthy [] = false := rfl

theorem topTruthy_cons (v : Value) (rest : List Value) :
    topTruthy (v :: rest)
      = match asBool? v with
        | some b => b
        | none   => false := rfl

/-- **The consensus-faithful script acceptance bit.** Bitcoin consensus
accepts a script run iff it completes WITHOUT a VM error AND leaves a
truthy value on top of the stack. The completion-only bit
(`.toOption.isSome`) is NOT the consensus bit: a public method whose
terminal `assert`'s `OP_VERIFY` was elided by `lowerMethod` completes
with the (possibly falsy) bool on top. -/
def scriptAccepts : EvalResult StackState → Bool
  | .error _ => false
  | .ok s    => topTruthy s.stack

@[simp] theorem scriptAccepts_error (e : EvalError) :
    scriptAccepts (.error e) = false := rfl

@[simp] theorem scriptAccepts_ok (s : StackState) :
    scriptAccepts (.ok s) = topTruthy s.stack := rfl

/-- Acceptance implies completion (the new bit strictly refines the old). -/
theorem isSome_of_scriptAccepts {r : EvalResult StackState}
    (h : scriptAccepts r = true) : r.toOption.isSome = true := by
  cases r with
  | error e => simp [scriptAccepts] at h
  | ok s => rfl

/-- On a run that is known to land a truthy top whenever it completes,
the acceptance bit coincides with the completion bit. This is the glue
that lifts the existing completion-based `successAgrees` walks to the
acceptance surface for value-terminated method fragments. -/
theorem scriptAccepts_eq_isSome_of_truthy
    (r : EvalResult StackState)
    (hTruthy : ∀ s, r = .ok s → topTruthy s.stack = true) :
    scriptAccepts r = r.toOption.isSome := by
  cases r with
  | error _ => rfl
  | ok s =>
      show topTruthy s.stack = true
      exact hTruthy s rfl

/-- Converse glue for smokes: a `native_decide`d acceptance fact yields
the per-completion truthiness hypothesis. -/
theorem truthy_of_scriptAccepts
    {r : EvalResult StackState} (h : scriptAccepts r = true) :
    ∀ s, r = .ok s → topTruthy s.stack = true := by
  intro s hr
  subst hr
  exact h

/-- **The consensus-faithful agreement notion** between an ANF evaluation
result and a deployed-bytes run: the ANF side COMPLETES exactly when the
bytes side is ACCEPTED (completes with a truthy top). This replaces the
old completion-vs-completion `successAgrees` as the observational
surface of every headline pipeline theorem: the ANF evaluator's `assert`
errors on a failed condition, while the deployed bytes of an
assert-terminated public method (terminal `OP_VERIFY` elided by
`lowerMethod`) complete with the falsy bool on top — the two bits agree
only under the acceptance reading, which is what Bitcoin consensus
actually checks. -/
def acceptAgrees {α : Type} (a : EvalResult α) (r : EvalResult StackState) : Prop :=
  a.toOption.isSome ↔ scriptAccepts r = true

/-- Lift a completion-bit agreement to the acceptance surface, given
that the bytes run lands a truthy top whenever it completes. This is the
mechanical adapter for VALUE-terminated method fragments: their lowered
ops leave the body's final value on top, so acceptance = completion
exactly under the (explicit, input-side) truthiness fact. -/
theorem acceptAgrees_of_completion_of_truthy {α : Type}
    {a : EvalResult α} {r : EvalResult StackState}
    (h : a.toOption.isSome ↔ r.toOption.isSome)
    (hTruthy : ∀ s, r = .ok s → topTruthy s.stack = true) :
    acceptAgrees a r := by
  unfold acceptAgrees
  rw [scriptAccepts_eq_isSome_of_truthy r hTruthy]
  exact h

/-- Smoke-side constructor: both bits concretely true. -/
theorem acceptAgrees_of_bits_true {α : Type}
    {a : EvalResult α} {r : EvalResult StackState}
    (hA : a.toOption.isSome = true) (hR : scriptAccepts r = true) :
    acceptAgrees a r :=
  iff_of_true (by simpa using hA) hR

/-- Smoke-side constructor: both bits concretely false (the termCx-class
agreement: ANF assert errors, bytes complete falsy — REJECTED). -/
theorem acceptAgrees_of_bits_false {α : Type}
    {a : EvalResult α} {r : EvalResult StackState}
    (hA : a.toOption.isSome = false) (hR : scriptAccepts r = false) :
    acceptAgrees a r :=
  iff_of_false (by simp [hA]) (by simp [hR])

/-- `OP_VERIFY` as a single-op run: the concrete reduction. -/
private theorem runOps_single_verify (s : StackState) :
    runOps [.opcode "OP_VERIFY"] s
      = (match s.stack with
         | [] => Except.error (.unsupported "OP_VERIFY: empty stack")
         | v :: rest =>
             match asBool? v with
             | some true  => Except.ok { s with stack := rest }
             | some false => Except.error .assertFailed
             | none       => Except.error (.typeError "OP_VERIFY: non-bool")) := by
  rw [Sim.runOps_cons_nonIf_eq (.opcode "OP_VERIFY") [] s (by intro _ _ h; cases h)]
  have hStep : stepNonIf (.opcode "OP_VERIFY") s = runOpcode "OP_VERIFY" s := rfl
  rw [hStep]
  have hV : runOpcode "OP_VERIFY" s
      = (match s.pop? with
         | none => Except.error (.unsupported "OP_VERIFY: empty stack")
         | some (v, s') =>
             match asBool? v with
             | some true  => Except.ok s'
             | some false => Except.error .assertFailed
             | none       => Except.error (.typeError "OP_VERIFY: non-bool")) := rfl
  rw [hV]
  cases hstk : s.stack with
  | nil =>
      have : s.pop? = none := by unfold StackState.pop?; rw [hstk]
      rw [this]
  | cons v rest =>
      have : s.pop? = some (v, { s with stack := rest }) := by
        unfold StackState.pop?; rw [hstk]
      rw [this]
      cases hb : asBool? v with
      | none => simp only [hb]
      | some b => cases b <;> simp only [hb] <;> exact runOps_nil _

/-- **Keystone elision lemma.** Appending a single `OP_VERIFY` to an op
list COMPLETES exactly when the bare op list is ACCEPTED (completes with
a truthy top). This is the formal content of the compiler's
terminal-assert elision: a public method's trailing `OP_VERIFY` may be
dropped because consensus itself performs the final truthiness check.
The truthiness notion is the VM's own `asBool?`, so each case is
definitional. -/
theorem runOps_append_verify_isSome_iff_scriptAccepts
    (ops : List StackOp) (s : StackState) :
    (runOps (ops ++ [.opcode "OP_VERIFY"]) s).toOption.isSome = true
      ↔ scriptAccepts (runOps ops s) = true := by
  rw [runOps_append]
  cases h : runOps ops s with
  | error e => simp [Except.toOption]
  | ok s' =>
      show (runOps [.opcode "OP_VERIFY"] s').toOption.isSome = true
        ↔ scriptAccepts (.ok s') = true
      rw [runOps_single_verify s']
      cases hstk : s'.stack with
      | nil => simp [scriptAccepts, topTruthy, hstk, Except.toOption]
      | cons v rest =>
          cases hb : asBool? v with
          | none =>
              simp [scriptAccepts, topTruthy, hstk, hb, Except.toOption]
          | some b =>
              cases b <;>
                simp [scriptAccepts, topTruthy, hstk, hb, Except.toOption]

end Eval
end Stack
end RunarVerification
