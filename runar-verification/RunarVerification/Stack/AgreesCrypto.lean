import RunarVerification.ANF.Syntax
import RunarVerification.ANF.Eval
import RunarVerification.Stack.Syntax
import RunarVerification.Stack.Eval
import RunarVerification.Stack.Lower
import RunarVerification.Stack.HashOps

/-! # `Stack/AgreesCrypto.lean` — crypto_call retirement-path PoC substrate

**Path 2 Tier 1 — investigation wave (crypto_call sub-omnibus).**  This file is
*standalone-compilable* (`lake env lean RunarVerification/Stack/AgreesCrypto.lean`)
and **not** import-wired into `RunarVerification.lean`.  It carries the honest
substrate for the question "can a single-crypto-call fragment be peeled off the
universal `crypto_call` fallback via the `update_prop` operational-M3 template?".

## The verdict, made formal here

The `update_prop` retirement template
(`Pipeline.compileSafe_observational_correct_updateProp_consume`) composes four
legs into a body-level `successAgrees` between the ANF interpreter
(`ANF.Eval.evalBindings`) and the deployed Script bytes (`runOps` of the lowered
ops).  The M2 leg is the *agreement* leg: it requires the ANF eval and the Stack
run to share their success bit.  For arith / update_prop that holds because both
sides compute through the SAME concrete arithmetic.

For a single crypto call (`sha256` / `hash160` / `ripemd160` / `hash256`) the two
sides DIVERGE at the source:

* **Stack side computes.**  `runOpcode "OP_SHA256"` is
  `liftBytesUnary s (fun b => .vBytes (Crypto.sha256 b))` — it invokes the shared
  backend `Crypto.hashBackend.sha256` and SUCCEEDS on any bytes-topped stack.
  This is fully proven, codegen-to-spec, in `Stack.HashOps.runOps_sha256Ops_eq`
  (re-exposed here as `sha256_step_transport`).

* **ANF side refuses.**  `ANF.Eval.callBuiltin? "sha256" args = .ok none`
  (no `"sha256"` arm — see `Eval.lean:1512` `callBuiltin?`), so
  `evalValue (.call "sha256" args)` returns `.error (.unsupported …)` BEFORE the
  backend is ever reached (`Eval.lean:1752-1756`).  The ANF interpreter
  deliberately leaves crypto primitives unevaluated (docstring `Eval.lean:1724`:
  "Cryptographic primitives still return `.error .unsupported`").

Therefore both sides *reference* `Crypto.hashBackend`, but only the Stack side
*calls* it.  The shared-backend "transparent agreement" that makes `update_prop`'s
arith step agree does NOT hold for crypto: the ANF success bit is `false`, the
Stack success bit is `true`, and `successAgrees` requires `false ↔ true`, which is
`False`.  `crypto_call_M2_disagreement` below proves exactly this.

## What this means for retirement

* `crypto_call` CANNOT be retired wholesale — it is the residual universal
  fallback (hypothesis `True`), the catch-all for every body that no decidable
  family classifier (arith / if_val / math_byte / update_prop / loop /
  method_call / dispatch / stateful) claims.
* A single-crypto-call fragment CANNOT be peeled off via the `update_prop`
  template **as the model stands**, because the M2 agreement leg is false.  The
  blocker is NOT a missing Stack-side lemma (those exist: `HashOps`); it is the
  ANF interpreter's deliberate `.unsupported` short-circuit for crypto builtins.
* The unblock is a Phase-B model change *reported, not made* here: wire the
  crypto hashes into `callBuiltin?` (route `"sha256"` → `Crypto.sha256`, etc.) so
  BOTH sides hit `Crypto.hashBackend`.  ONLY THEN does the M2 step agree and the
  single-opcode crypto fragment become retirable on the `update_prop` template,
  reusing `HashOps.runOps_sha256Ops_eq` for M3/M4 unchanged.

No `sorry`/`admit`, no new axioms (the pre-existing `Crypto.hashBackend` TCB axiom
is USED, not introduced).  Every lemma ships an in-file smoke. -/

namespace RunarVerification.Stack.AgreesCrypto

open RunarVerification.ANF.Eval (Value State EvalResult evalValue callBuiltin?)
open RunarVerification.Stack
open RunarVerification.Stack.Eval
open RunarVerification.ANF.Eval.Crypto

/-! ## Part 1 — the Stack-side single-opcode step transport (M3/M4 substrate EXISTS)

The Stack VM already has full codegen-to-spec for the single-opcode crypto
hashes.  We re-expose `Stack.HashOps.runOps_sha256Ops_eq` (and the `hash160`
peer) under the local "step transport" name to make the point that the
*operational* legs the `update_prop` template needs are already proven for
crypto.  `OP_SHA256` / `OP_HASH160` are both in `Parse.isAllowedOpcodeName`
(`Script/Parse.lean:669`), so the M4 round-trip allowlist obligation is also
discharged for these ops. -/

/-- **M3/M4 substrate (sha256).**  Running the single allowlisted op `OP_SHA256`
on a bytes-topped stack pushes `Crypto.sha256 bytes` — the shared backend.  This
is the crypto analogue of `update_prop`'s `updateProp_M3_runEq`: a single-opcode
operational step against the same backend the spec uses. -/
theorem sha256_step_transport
    (s : StackState) (bytes : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes bytes :: rest)
    (hLen : bytes.size ≤ 520) :
    runOps [.opcode "OP_SHA256"] s
      = .ok ({ s with stack := .vBytes (sha256 bytes) :: rest }) :=
  HashOps.runOps_sha256Ops_eq s bytes rest hStk hLen

/-- **M3/M4 substrate (hash160).**  Same for `OP_HASH160` → `Crypto.hash160`
(`= ripemd160 ∘ sha256`). -/
theorem hash160_step_transport
    (s : StackState) (bytes : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes bytes :: rest)
    (hLen : bytes.size ≤ 520) :
    runOps [.opcode "OP_HASH160"] s
      = .ok ({ s with stack := .vBytes (hash160 bytes) :: rest }) :=
  HashOps.runOps_hash160Ops_eq s bytes rest hStk hLen

/-! ## Part 2 — the M2 obstruction: the ANF interpreter refuses crypto

`callBuiltin? "sha256" args = .ok none` for ALL args (there is no `"sha256"` arm
in `callBuiltin?`), so the `.call "sha256"` arm of `evalValue` takes the
`none` branch and returns `.error`.  These two lemmas pin the asymmetry that
breaks the M2 agreement leg. -/

/-- `callBuiltin?` has no `sha256` arm: it returns `.ok none` for every
argument list.  (The catch-all `| _ => return none` at `Eval.lean:1659`.) -/
theorem callBuiltin_sha256_none (args : List Value) :
    callBuiltin? "sha256" args = .ok none := by
  cases args with
  | nil => rfl
  | cons a rest => rfl

/-- Consequently `evalValue` on a `.call "sha256"` binding ALWAYS errors,
regardless of the argument bytes present in the state.  The crypto primitive is
NEVER evaluated on the ANF side. -/
theorem evalValue_call_sha256_errors
    (s : State) (x : String) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes)) :
    (evalValue s (.call "sha256" [x])).toOption = none := by
  show (evalValue s (RunarVerification.ANF.ANFValue.call "sha256" [x])).toOption = none
  unfold evalValue
  -- `args.mapM (lookupRef s)` succeeds (x resolves to bytes), then
  -- `callBuiltin? "sha256" _ = .ok none` forces the `.error .unsupported` arm.
  simp only [List.mapM_cons, List.mapM_nil, RunarVerification.ANF.Eval.lookupRef, hx,
    bind, Except.bind, pure, Except.pure]
  rw [callBuiltin_sha256_none]
  rfl

/-! ## Part 3 — the headline: M2 agreement FAILS for the single-sha256 step

`successAgrees a b := a.toOption.isSome ↔ b.toOption.isSome`
(`Pipeline.lean:307`).  Take the ANF side to be `evalValue (.call "sha256" [x])`
(success bit `false`, by Part 2) and the Stack side to be
`runOps [OP_SHA256]` on the matching bytes-topped stack (success bit `true`, by
Part 1).  The agreement `false ↔ true` is `False`.  This is the formal statement
that a single-crypto-call fragment is NOT retirable via the `update_prop`
operational-M3 template AS THE MODEL STANDS — the obstruction is the ANF
interpreter's `.unsupported` short-circuit, not any missing Stack lemma. -/

/-- **The crypto_call M2 disagreement.**  For a state `s` resolving `x` to
`bytes`, and the matching stack `sStk` with `bytes` on top, the ANF eval of
`.call "sha256" [x]` and the Stack run of `[OP_SHA256]` do NOT share their
success bit — the `successAgrees`-style biconditional is `False`. -/
theorem crypto_call_M2_disagreement
    (s : State) (x : String) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes))
    (sStk : StackState) (rest : List Value)
    (hStk : sStk.stack = .vBytes bytes :: rest)
    (hLen : bytes.size ≤ 520) :
    ¬ ((evalValue s (.call "sha256" [x])).toOption.isSome
        ↔ (runOps [.opcode "OP_SHA256"] sStk).toOption.isSome) := by
  -- ANF side: success bit false.
  have hAnf : (evalValue s (.call "sha256" [x])).toOption.isSome = false := by
    rw [evalValue_call_sha256_errors s x bytes hx]; rfl
  -- Stack side: success bit true.
  have hStack : (runOps [.opcode "OP_SHA256"] sStk).toOption.isSome = true := by
    rw [sha256_step_transport sStk bytes rest hStk hLen]; rfl
  intro hIff
  rw [hAnf, hStack] at hIff
  exact (Bool.false_ne_true) (hIff.mpr rfl)

/-! ## Part 4 — MANDATORY in-file smokes (anti-vacuous, concrete) -/

/-- Concrete state: a single binding `x ↦ vBytes #[0x01,0x02,0x03]`. -/
private def smokeState : State :=
  { (default : State) with bindings := [("x", .vBytes (ByteArray.mk #[1, 2, 3]))] }

/-- Concrete stack with the same bytes on top. -/
private def smokeStk : StackState :=
  { (default : StackState) with stack := [.vBytes (ByteArray.mk #[1, 2, 3])] }

/-- SMOKE (Part 2).  The ANF eval of `.call "sha256" ["x"]` on the concrete
state really errors (`toOption.isSome = false`). -/
theorem smoke_anf_sha256_errors :
    (evalValue smokeState (.call "sha256" ["x"])).toOption.isSome = false := by
  native_decide

/-- SMOKE (Part 1).  The Stack run of `[OP_SHA256]` on the concrete stack really
succeeds (`toOption.isSome = true`).  This fires the shared `Crypto.hashBackend`
through `OP_SHA256`; it is anti-vacuous (the run does not error). -/
theorem smoke_stack_sha256_succeeds :
    (runOps [.opcode "OP_SHA256"] smokeStk).toOption.isSome = true := by
  have h :
      runOps [.opcode "OP_SHA256"] smokeStk
        = .ok ({ smokeStk with
                  stack := .vBytes (sha256 (ByteArray.mk #[1, 2, 3])) :: [] }) :=
    sha256_step_transport smokeStk (ByteArray.mk #[1, 2, 3]) [] rfl (by decide)
  rw [h]; rfl

/-- SMOKE (Part 3 — the headline).  The disagreement lemma FIRES on the concrete
state/stack pair: the ANF (false) / Stack (true) success bits are not equivalent.
This is the anti-fraud witness that the single-crypto-call M2 leg genuinely
fails — not a vacuous statement. -/
theorem smoke_crypto_call_M2_disagreement :
    ¬ ((evalValue smokeState (.call "sha256" ["x"])).toOption.isSome
        ↔ (runOps [.opcode "OP_SHA256"] smokeStk).toOption.isSome) :=
  crypto_call_M2_disagreement smokeState "x" (ByteArray.mk #[1, 2, 3]) rfl
    smokeStk [] rfl (by decide)

/-- SMOKE (anti-vacuity, explicit).  The two success bits are concretely
`false` and `true` — both witnesses are exhibited, so neither side of the
disagreement is degenerate. -/
theorem smoke_M2_bits_concrete :
    (evalValue smokeState (.call "sha256" ["x"])).toOption.isSome = false
    ∧ (runOps [.opcode "OP_SHA256"] smokeStk).toOption.isSome = true :=
  ⟨smoke_anf_sha256_errors, smoke_stack_sha256_succeeds⟩

end RunarVerification.Stack.AgreesCrypto
