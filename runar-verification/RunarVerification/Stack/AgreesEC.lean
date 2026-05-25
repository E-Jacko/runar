import RunarVerification.ANF.Eval
import RunarVerification.Stack.Eval
import RunarVerification.Stack.Ec
import RunarVerification.Crypto.Secp256k1
import RunarVerification.Pipeline

/-! # `Stack/AgreesEC.lean` — single-EC-op codegen-to-spec PoC substrate

**EC sizing PoC (peer of wave-68's `AgreesCrypto.lean`).**  This file is a
STANDALONE sizing proof-of-concept for the secp256k1 EC codegen-to-spec tier
(`Crypto/Spec.lean §7`, the 10 `emitEc*_runOps_eq` axioms).  It is NOT wired
into `RunarVerification.lean`; it is built directly via `lake env lean` to
demonstrate that the SIMPLEST EC op (`ecModReduce`) is dischargeable off the
multi-op operational-M3 template (`runOps_cons_nonIf_eq` chaining), exactly the
way the SHA single-opcode transport was discharged in wave 68 — but for an
8-op fragment rather than a 1-op fragment, and against a FULLY EVALUABLE spec
(no opaque crypto backend).

## What this PoC establishes (and what it deliberately does not)

* `emitEcModReduce` lowers to the 8-op fragment
  `[OP_2DUP, OP_MOD, rot, drop, over, OP_ADD, swap, OP_MOD]`.  Every op is a
  `stepNonIf` arm the Stack VM evaluates concretely.  We prove
  `runOps Stack.Ec.emitEcModReduce stkSt = .ok {... ecModReduce value m ...}`
  by 8 sequential `runOps_cons_nonIf_eq` reductions — the EC analogue of
  `HashOps.runOps_sha256Ops_eq`, scaled to a multi-op fragment.

* **HONEST PRECONDITION (`m ≠ 0`).**  The Stack op `OP_MOD` returns
  `.error .divByZero` when the modulus is `0`, but the spec
  `Crypto.Secp256k1.ecModReduce` returns `0` in that case.  So the
  codegen-to-spec equality holds **only under `m ≠ 0`**.  The `Crypto/Spec.lean`
  axiom `emitEcModReduce_runOps_eq` as currently stated carries NO such
  hypothesis — meaning it is FALSE at `m = 0` and cannot be discharged
  verbatim.  Discharging it for real requires either (a) adding `m ≠ 0`
  (or a curve-`n`/curve-`p` typing invariant guaranteeing it) to the axiom,
  or (b) a divByZero-tolerant `successAgrees` formulation.  This PoC proves
  the TRUE statement (with `m ≠ 0`) and the M2 agreement peer.

* This is a SIZING PoC for ONE op-class (the "tiny / all-evaluable-opcodes"
  class).  It does NOT touch the medium ops (reverse32 ~300-op loops:
  `ecPointX/Y`, `ecMakePoint`, `ecNegate`, `ecEncodeCompressed`, `ecOnCurve`)
  nor the hard ops (`ecAdd`, `ecMul`, `ecMulGen` — Jacobian group law,
  50k+ ops, M4-walled).  See the SIZING REPORT in the task deliverable.

## Constraints honoured

No `sorry`/`admit`.  No new axioms (the spec defs in `Crypto/Secp256k1` and the
Stack VM in `Stack/Eval` are USED, not introduced).  No `...`.  The headline
transport is proved by honest step-chaining (no `simp`/`native_decide` fakes);
`native_decide` appears ONLY in a concrete smoke (the spec is computable, so the
smoke is legitimate, unlike the SHA backend which would panic). -/

-- The per-step `simp only [match_Except_ok_runOps]` reductions trip the
-- unused-simp-arg linter (Lean's iota reducer sometimes fires the match
-- reduction first), but the lemma IS the intended driver and keeping it
-- documents the step. Silence the cosmetic linter only.
set_option linter.unusedSimpArgs false

namespace RunarVerification.Stack.AgreesEC

open RunarVerification.ANF.Eval (Value State EvalResult EvalError evalValue callBuiltin?)
open RunarVerification.Stack
open RunarVerification.Stack.Eval
open RunarVerification.Pipeline.Soundness (successAgrees)

/-! ## Part 1 — the Stack-side multi-op M3 step transport (`ecModReduce`)

`Stack.Ec.emitEcModReduce` is the 8-op fragment

```text
[ .opcode "OP_2DUP", .opcode "OP_MOD", .rot, .drop,
  .over, .opcode "OP_ADD", .swap, .opcode "OP_MOD" ]
```

Run on `stack = vBigint m :: vBigint value :: rest` (TOS = `m`), it computes
`((value % m) + m) % m` = `Crypto.Secp256k1.ecModReduce value m` (the `m ≠ 0`
branch).  This is the EC peer of `HashOps.runOps_sha256Ops_eq` — a
codegen-to-spec operational step, but over 8 ops instead of 1, and against a
concrete (non-axiom) spec. -/

/-- **M3 substrate (ecModReduce).**  Running the lowered `emitEcModReduce`
fragment on `[m, value] ++ rest` (m on TOS) pushes
`Crypto.Secp256k1.ecModReduce value m`, provided `m ≠ 0` (the divByZero guard).

Proof: 8 honest `runOps_cons_nonIf_eq` step reductions.  No `simp` closing the
arithmetic — the result coordinate is exactly the spec def unfolded. -/
theorem ecModReduce_step_transport
    (s : StackState) (value m : Int) (rest : List Value)
    (hStk : s.stack = .vBigint m :: .vBigint value :: rest)
    (hM : m ≠ 0) :
    runOps Stack.Ec.emitEcModReduce s
      = .ok { s with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce value m)
                        :: rest } := by
  -- Destructure `s` and substitute its stack shape so every `stepNonIf`
  -- reduces by `rfl` (the non-stack fields `alt/out/props/pre` ride along
  -- unchanged through every step). `emitEcModReduce` is a literal 8-op list.
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  -- Generic non-`.ifOp` proofs.
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niRot : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niOver : ∀ t e, StackOp.over ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  -- Field record carried through every step (only `.stack` changes).
  -- Step 1: OP_2DUP.
  show runOps
      ([ StackOp.opcode "OP_2DUP", StackOp.opcode "OP_MOD", StackOp.rot,
         StackOp.drop, StackOp.over, StackOp.opcode "OP_ADD", StackOp.swap,
         StackOp.opcode "OP_MOD" ])
      { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_2DUP"), stepNonIf_opcode]
  rw [show runOpcode "OP_2DUP"
        { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint value :: .vBigint m
                        :: .vBigint value :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 2: OP_MOD  → value % m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_MOD"), stepNonIf_opcode]
  rw [show runOpcode "OP_MOD"
        { stack := .vBigint m :: .vBigint value :: .vBigint m :: .vBigint value :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m) :: .vBigint m :: .vBigint value :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      show (if m == 0 then (Except.error EvalError.divByZero : EvalResult StackState)
            else .ok (StackState.push
                  { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
                    outputs := out, props := props, preimage := pre }
                  (.vBigint (value % m)))) = _
      rw [if_neg (by simpa using hM)]; rfl]
  simp only [match_Except_ok_runOps]
  -- Step 3: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot]
  rw [show stepNonIf StackOp.rot
        { stack := .vBigint (value % m) :: .vBigint m :: .vBigint value :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint value :: .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: drop.
  rw [runOps_cons_nonIf_eq _ _ _ niDrop]
  rw [show stepNonIf StackOp.drop
        { stack := .vBigint value :: .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 5: over.
  rw [runOps_cons_nonIf_eq _ _ _ niOver]
  rw [show stepNonIf StackOp.over
        { stack := .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_ADD  → (value % m) + m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_ADD"), stepNonIf_opcode]
  rw [show runOpcode "OP_ADD"
        { stack := .vBigint m :: .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m + m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 7: swap.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap]
  rw [show stepNonIf StackOp.swap
        { stack := .vBigint (value % m + m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint (value % m + m) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 8: OP_MOD  → ((value % m) + m) % m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_MOD"), stepNonIf_opcode]
  rw [show runOpcode "OP_MOD"
        { stack := .vBigint m :: .vBigint (value % m + m) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint ((value % m + m) % m) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      show (if m == 0 then (Except.error EvalError.divByZero : EvalResult StackState)
            else .ok (StackState.push
                  { stack := rest, altstack := alt,
                    outputs := out, props := props, preimage := pre }
                  (.vBigint ((value % m + m) % m)))) = _
      rw [if_neg (by simpa using hM)]; rfl]
  simp only [match_Except_ok_runOps, runOps_nil]
  -- Final: the pushed coordinate equals the spec def at `m ≠ 0`.
  have hSpec :
      RunarVerification.Crypto.Secp256k1.ecModReduce value m = (value % m + m) % m := by
    unfold RunarVerification.Crypto.Secp256k1.ecModReduce
    rw [if_neg hM]
  rw [hSpec]

/-! ## Part 2 — the M2 success-bit agreement (peer of wave-68)

`successAgrees a b := a.toOption.isSome ↔ b.toOption.isSome`.  The Stack side of
the `ecModReduce` fragment succeeds (Part 1).  An ANF side that COMPUTES
`ecModReduce` (the standalone `Crypto.ecModReduce` def already exists in
`ANF/Eval.lean`, line 417, but is NOT yet wired into `callBuiltin?` — see the
SIZING REPORT) would have success bit `true`, giving the M2 agreement.

Until the `callBuiltin?` arm lands, we state the agreement against the
Stack-side success directly: the deployed `emitEcModReduce` fragment SUCCEEDS on
a well-typed nonzero-modulus stack.  This is the leaf a gated dispatch wave would
hand to the consume theorem once the ANF arm is wired. -/

/-- The deployed `emitEcModReduce` fragment SUCCEEDS (success bit `true`) on a
two-int stack with nonzero modulus.  This is the Stack-side half of the M2 leg;
the ANF half is the (not-yet-wired) `callBuiltin? "ecModReduce"` arm. -/
theorem ecModReduce_stack_succeeds
    (s : StackState) (value m : Int) (rest : List Value)
    (hStk : s.stack = .vBigint m :: .vBigint value :: rest)
    (hM : m ≠ 0) :
    (runOps Stack.Ec.emitEcModReduce s).toOption.isSome = true := by
  rw [ecModReduce_step_transport s value m rest hStk hM]; rfl

/-! ## Part 3 — MANDATORY in-file smokes (anti-vacuous, concrete)

Unlike the SHA PoC, the EC spec is fully EVALUABLE, so the smokes may fire by
`native_decide` on the concrete coordinate (the spec is a closed-form `Int`
function — no opaque backend to panic the kernel evaluator). -/

/-- Concrete stack `[7, 23]` (m = 7 on TOS, value = 23 below). -/
private def smokeStk : StackState :=
  { (default : StackState) with stack := [.vBigint 7, .vBigint 23] }

/-- SMOKE (Part 1, structural).  The transport FIRES on the concrete stack:
running `emitEcModReduce` on `[7, 23]` yields `[23 mod 7 = 2]`.  This is the
anti-vacuity witness that the 8-op fragment really evaluates to the spec value. -/
theorem smoke_ecModReduce_transport :
    runOps Stack.Ec.emitEcModReduce smokeStk
      = .ok { smokeStk with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce 23 7) :: [] } :=
  ecModReduce_step_transport smokeStk 23 7 [] rfl (by decide)

/-- SMOKE (anti-vacuity, the headline).  The deployed result coordinate is
concretely `2` — the spec value `ecModReduce 23 7 = 2` matches by computation.
`native_decide` is LEGITIMATE here: the EC spec is a closed-form computable
`Int` function (contrast the SHA backend, which is a non-executable TCB axiom). -/
theorem smoke_ecModReduce_value_concrete :
    RunarVerification.Crypto.Secp256k1.ecModReduce 23 7 = 2 := by native_decide

/-- SMOKE (Part 2).  The Stack-side M2 success bit fires on the concrete pair. -/
theorem smoke_ecModReduce_succeeds :
    (runOps Stack.Ec.emitEcModReduce smokeStk).toOption.isSome = true :=
  ecModReduce_stack_succeeds smokeStk 23 7 [] rfl (by decide)

/-! ## Part 4 — the wired `callBuiltin?` EC arms (deliverable 2)

Wave 71 left the `callBuiltin? "ecModReduce"` arm UNWIRED (see Part 2's note).
This wave wires the eight in-scope EC ops into `ANF.Eval.callBuiltin?`, each
routing through the concrete `Crypto.Secp256k1.*` backend defs already exposed
in `ANF/Eval.lean` (`Crypto.ecAdd` … `Crypto.ecPointY`).  `ecMul` / `ecMulGen`
stay UNWIRED (scoped out — kept as named codegen-discharge axioms).

The arm lemmas below pin each arm's reduction by `rfl` (the peer of
`AgreesCrypto.callBuiltin_sha256_arm`).  Together with the Part-1 Stack-side
transport they close the M2 leg for `ecModReduce`: the ANF side now COMPUTES
`Crypto.ecModReduce value m` instead of returning `.ok none` → `crypto_call`.
No new axiom: the backend defs are concrete. -/

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecModReduce` arm now fires on a two-int argument list, returning the
backend reduction.  Pins the ANF half of the `ecModReduce` M2 agreement. -/
theorem callBuiltin_ecModReduce_arm (a m : Int) :
    callBuiltin? "ecModReduce" [.vBigint a, .vBigint m]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecModReduce a m))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecAdd` arm fires on two byte-valued points. -/
theorem callBuiltin_ecAdd_arm (p q : ByteArray) :
    callBuiltin? "ecAdd" [.vBytes p, .vBytes q]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecAdd p q))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecNegate` arm fires on one byte-valued point. -/
theorem callBuiltin_ecNegate_arm (p : ByteArray) :
    callBuiltin? "ecNegate" [.vBytes p]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecNegate p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecOnCurve` arm fires on one byte-valued point, returning a Bool. -/
theorem callBuiltin_ecOnCurve_arm (p : ByteArray) :
    callBuiltin? "ecOnCurve" [.vBytes p]
      = .ok (some (.vBool (RunarVerification.ANF.Eval.Crypto.ecOnCurve p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecEncodeCompressed` arm fires on one byte-valued point. -/
theorem callBuiltin_ecEncodeCompressed_arm (p : ByteArray) :
    callBuiltin? "ecEncodeCompressed" [.vBytes p]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecEncodeCompressed p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecMakePoint` arm fires on two ints. -/
theorem callBuiltin_ecMakePoint_arm (x y : Int) :
    callBuiltin? "ecMakePoint" [.vBigint x, .vBigint y]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecMakePoint x y))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecPointX` arm fires on one byte-valued point, returning an Int. -/
theorem callBuiltin_ecPointX_arm (p : ByteArray) :
    callBuiltin? "ecPointX" [.vBytes p]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecPointX p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecPointY` arm fires on one byte-valued point, returning an Int. -/
theorem callBuiltin_ecPointY_arm (p : ByteArray) :
    callBuiltin? "ecPointY" [.vBytes p]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecPointY p))) := rfl

/-- SMOKE (deliverable 2, ANF arm anti-vacuity).  The wired `ecModReduce` arm,
applied to the same concrete pair `(23, 7)`, computes the spec value `2` — the
ANF half now AGREES with the Stack-side transport (`smoke_ecModReduce_value_concrete`).
`native_decide` is legitimate: the EC spec is a closed-form computable `Int`. -/
theorem smoke_callBuiltin_ecModReduce_arm :
    (match callBuiltin? "ecModReduce" [.vBigint 23, .vBigint 7] with
     | .ok (some (.vBigint n)) => n == 2
     | _ => false) = true := by native_decide

/-- SMOKE (deliverable 2).  A NOT-wired op (`ecMul`, scoped out) still returns
`.ok none` — confirming the scope boundary: only the eight in-scope arms route
through the backend; `ecMul` / `ecMulGen` keep falling through to `crypto_call`. -/
theorem smoke_callBuiltin_ecMul_unwired :
    callBuiltin? "ecMul" [.vBytes (ByteArray.mk #[0x00]), .vBigint 1] = .ok none := rfl

/-! ## Part 5 — the `reverse32` loop transport (deliverable 3)

`Stack.Ec.emitReverse32Step` is the 7-op fragment

```text
[ .push (.bigint 1), .opcode "OP_SPLIT", .rot, .rot, .swap, .opcode "OP_CAT", .swap ]
```

Run on `stack = vBytes value :: vBytes acc :: rest` (value on TOS, with
`1 ≤ value.size`), it peels the FIRST byte off `value` and PREPENDS it to `acc`,
leaving `stack = vBytes (value.extract 1 value.size) :: vBytes (value.extract 0 1 ++ acc) :: rest`.
The loop `emitReverse32Loop n` iterates this `n` times; over a full-size value it
reverses the byte order into the accumulator (verified empirically: a length-3
value `[10,20,30]` with acc `[99]` becomes `[30,20,10,99]`).

**BLOCK (the OP_0 wrapper).** `emitReverse32Ops = [.opcode "OP_0", .swap] ++ loop ++ [.drop]`
initializes the accumulator with `OP_0`. The Lean Stack VM models `OP_0` as
`.vBigint 0` (`Stack.Eval.runOpcode "OP_0" = s.push (.vBigint 0)`), NOT an empty
byte-vector. The very first loop step's `OP_CAT` then rejects the `vBigint 0`
accumulator (`liftBytesBin` requires both operands `asBytes?`), so
`runOps Stack.Ec.emitReverse32Ops s = .error (.typeError "binary bytes op …")`
for EVERY input — the wrapper transport is FALSE as stated in the current VM.
The obstacle is a VM model-fidelity gap (real Script `OP_0` pushes the empty
byte-vector, which `OP_CAT` treats as empty bytes), reconcilable only by either
(a) the codegen emitting `.push (.bytes ByteArray.empty)` instead of `.opcode "OP_0"`
(byte-identical on the wire — all three emit `[0x00]` — but distinct in the VM),
or (b) a VM change making `OP_0` push a bytes-coercible empty value. Both are out
of scope this wave (codegen / VM dispatch edits are forbidden without a BLOCK).
The loop body lemma below is therefore proved over the SEMANTICALLY-CORRECT
bytes-accumulator form; it is the reusable substrate the medium-EC-op discharge
waves consume once the OP_0 init is reconciled. No new axiom. -/

/-- **reverse32 single-step transport.**  One `emitReverse32Step` on
`[value, acc] ++ rest` (value on TOS, `1 ≤ value.size`) peels the head byte of
`value` onto the front of `acc`. -/
theorem reverse32_step_transport
    (s : StackState) (value acc : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes value :: .vBytes acc :: rest)
    (hSize : 1 ≤ value.size) :
    runOps Stack.Ec.emitReverse32Step s
      = .ok { s with
              stack := .vBytes (value.extract 1 value.size)
                        :: .vBytes (value.extract 0 1 ++ acc) :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niRot : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  have stepNonIf_rot : ∀ (st : StackState), stepNonIf .rot st = applyRot st := by
    intro st; rfl
  -- emitReverse32Step is the literal 7-op list.
  show runOps
      ([ StackOp.push (.bigint 1), StackOp.opcode "OP_SPLIT", StackOp.rot,
         StackOp.rot, StackOp.swap, StackOp.opcode "OP_CAT", StackOp.swap ])
      { stack := .vBytes value :: .vBytes acc :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  -- Step 1: push 1.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 1)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 1.  Guard discharged by hSize.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 1 :: .vBytes value :: .vBytes acc :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: .vBytes acc :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte, Int.toNat_one]
      rw [if_neg (by omega : ¬ (1 : Nat) > value.size)] ]
  simp only [match_Except_ok_runOps]
  -- Step 3: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := .vBytes (value.extract 1 value.size) :: .vBytes (value.extract 0 1)
                    :: .vBytes acc :: rest, altstack := alt, outputs := out,
          props := props, preimage := pre }
        = .ok { stack := .vBytes acc :: .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := .vBytes acc :: .vBytes (value.extract 1 value.size)
                    :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1) :: .vBytes acc
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 5: swap.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1) :: .vBytes acc
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes acc :: .vBytes (value.extract 0 1)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_CAT → extract 0 1 ++ acc.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes acc :: .vBytes (value.extract 0 1)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1 ++ acc)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 7: swap → final layout.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1 ++ acc)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1 ++ acc) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

/-! ### The loop spec and transport (by induction on the iteration count)

`reverseTail`/`reverseAcc` recursively model the value-residue and accumulator
that `emitReverse32Loop n` leaves on the stack: each iteration peels the head
byte (`extract 0 1`) onto the front of the accumulator and recurses on the tail
(`extract 1 size`).  `reverse32_loop_transport` then proves the loop's `runOps`
matches these specs, threaded by `n` honest applications of the step lemma.

These are closed-form `ByteArray` functions (no axiom).  For a full-size value
the residue is empty and the accumulator is the byte-reversed value prefixed onto
the original `acc` — the byte-reversal the medium EC ops need (witnessed by the
concrete smoke below). -/

/-- The value-residue after `n` reverse-loop iterations. -/
def reverseTail : Nat → ByteArray → ByteArray
  | 0,     v => v
  | k + 1, v => reverseTail k (v.extract 1 v.size)

/-- The accumulator after `n` reverse-loop iterations: each step prepends the
current head byte (`extract 0 1`) to the front of the running accumulator. -/
def reverseAcc : Nat → ByteArray → ByteArray → ByteArray
  | 0,     _, acc => acc
  | k + 1, v, acc => reverseAcc k (v.extract 1 v.size) (v.extract 0 1 ++ acc)

/-- **reverse32 loop transport.**  Running `emitReverse32Loop n` on
`[value, acc] ++ rest` (value on TOS, `n ≤ value.size`) leaves
`[reverseTail n value, reverseAcc n value acc] ++ rest`.  Proved by induction on
`n` via `reverse32_step_transport`.  The `n ≤ value.size` precondition keeps every
intermediate `OP_SPLIT` index in range. -/
theorem reverse32_loop_transport
    (n : Nat) :
    ∀ (s : StackState) (value acc : ByteArray) (rest : List Value),
      s.stack = .vBytes value :: .vBytes acc :: rest →
      n ≤ value.size →
      runOps (Stack.Ec.emitReverse32Loop n) s
        = .ok { s with
                stack := .vBytes (reverseTail n value)
                          :: .vBytes (reverseAcc n value acc) :: rest } := by
  induction n with
  | zero =>
      intro s value acc rest hStk _
      show runOps [] s = _
      rw [runOps_nil]
      obtain ⟨stk, alt, out, props, pre⟩ := s
      simp only at hStk
      subst hStk
      rfl
  | succ k ih =>
      intro s value acc rest hStk hLe
      -- emitReverse32Loop (k+1) = emitReverse32Step ++ emitReverse32Loop k
      have hUnfold : Stack.Ec.emitReverse32Loop (k + 1)
          = Stack.Ec.emitReverse32Step ++ Stack.Ec.emitReverse32Loop k := rfl
      rw [hUnfold, runOps_append]
      -- One step peels the head byte.
      rw [reverse32_step_transport s value acc rest hStk (by omega)]
      simp only [match_Except_ok_runOps]
      -- Recurse on the tail.  `(value.extract 1 value.size).size = value.size - 1 ≥ k`.
      have hTailSize : (value.extract 1 value.size).size = value.size - 1 := by
        rw [ByteArray.size_extract]
        omega
      rw [ih { s with stack := .vBytes (value.extract 1 value.size)
                        :: .vBytes (value.extract 0 1 ++ acc) :: rest }
            (value.extract 1 value.size) (value.extract 0 1 ++ acc) rest rfl
            (by rw [hTailSize]; omega)]
      rfl

/-! ### MANDATORY smokes for the loop transport (deliverable 3) -/

/-- Concrete value `[10,20,30]` (TOS), accumulator `[99]`. -/
private def smokeRevStk : StackState :=
  { (default : StackState) with
    stack := [.vBytes (ByteArray.mk #[10, 20, 30]), .vBytes (ByteArray.mk #[99])] }

/-- SMOKE (step, anti-vacuity).  One step on `[[10,20,30],[99]]` peels `10`:
result `[[20,30], [10,99]]`. -/
theorem smoke_reverse32_step :
    runOps Stack.Ec.emitReverse32Step smokeRevStk
      = .ok { smokeRevStk with
              stack := [.vBytes ((ByteArray.mk #[10, 20, 30]).extract 1 3),
                        .vBytes ((ByteArray.mk #[10, 20, 30]).extract 0 1
                                  ++ ByteArray.mk #[99])] } :=
  reverse32_step_transport smokeRevStk (ByteArray.mk #[10, 20, 30]) (ByteArray.mk #[99]) []
    rfl (by decide)

/-- SMOKE (loop, the headline).  Running the 3-iteration loop on `[[10,20,30],[99]]`
reverses the value into the accumulator: the result accumulator byte-list is
`[30, 20, 10, 99]` and the residue is empty.  `native_decide` is legitimate —
`reverseTail` / `reverseAcc` are closed-form computable `ByteArray` functions. -/
theorem smoke_reverse32_loop_value_concrete :
    (reverseAcc 3 (ByteArray.mk #[10, 20, 30]) (ByteArray.mk #[99])).toList
        = [30, 20, 10, 99]
      ∧ (reverseTail 3 (ByteArray.mk #[10, 20, 30])).toList = [] := by
  native_decide

/-- SMOKE (loop transport fires).  The loop `runOps` on the concrete stack
succeeds and lands the reversed accumulator — the step lemma really composes. -/
theorem smoke_reverse32_loop_succeeds :
    (runOps (Stack.Ec.emitReverse32Loop 3) smokeRevStk).toOption.isSome = true := by
  rw [reverse32_loop_transport 3 smokeRevStk (ByteArray.mk #[10, 20, 30])
        (ByteArray.mk #[99]) [] rfl (by decide)]
  rfl

/-- BLOCK WITNESS (deliverable 3 honest block).  The production `emitReverse32Ops`
wrapper (which initializes the accumulator with `.opcode "OP_0"` → `vBigint 0`)
ERRORS under the current Stack VM: the first loop step's `OP_CAT` rejects the
non-bytes accumulator.  This is the precise sub-goal that blocks lifting the loop
transport to `emitReverse32Ops` (and thus to `ecPointX/Y`, `ecMakePoint`,
`ecNegate`, `ecOnCurve`, `ecAdd`). -/
theorem smoke_reverse32_ops_blocked_on_OP_0 :
    (runOps Stack.Ec.emitReverse32Ops smokeRevStk).toOption.isSome = false := by
  native_decide

end RunarVerification.Stack.AgreesEC
