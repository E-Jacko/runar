import RunarVerification.Script.LoopParse
import RunarVerification.Stack.AgreesLoopParsed
import RunarVerification.Stack.AgreesLoopParametric

/-!
# Acceptance-surface bridge — closing the loop parse round-trip back to `m.ops`

PR #95 (`Script.LoopParse`) landed the GENERAL parse round-trip for the
loop instruction set, but its headline
`compileSafe_single_public_runOps_eq_loop` /
`emitFast_single_public_runOps_eq_loop` land at the PARSER'S NORMALIZED
view `loopNormalizeOps m.ops`, NOT at the original `m.ops`. The
normaliser rewrites three SEMANTIC-only loop classes:

* `.pickStruct d ↦ .pick d` — `runOps`-INequal out of bounds (different
  error strings) but `scriptAccepts`-EQUAL (both reject).
* `.placeholder i n ↦ .push (.bigint 0)` — `runOps`-equal (`OP_0`).
* `.pushCodesepIndex ↦ .push (.bigint 0)` — `runOps`-equal (`OP_0`).
* `.push v ↦ .push (normalizePushVal v)` — `normalizePushVal` changes
  REPRESENTATION for non-canonical pushes (e.g. `.bigint 17 ↦ .bytes
  [0x11]`), which is NOT `runOps`-equal and NOT `scriptAccepts`-equal in
  general (different runtime value on top of the stack). The upstream
  pipeline omnibus likewise leaves its conclusion at `normalizeOps m.ops`
  and does NOT close this push gap — the honest bridge is therefore
  restricted to CANONICAL pushes (`normalizePushVal v = v`), which is
  EXACTLY the shape every loop fixture emits (small-int `.bigint` in
  `[-1, 0..16]`).

This module proves, per loop op class, that `loopNormalizeStackOp op` is
`scriptAccepts`-cons-equivalent to `op` (reusing the Tier 4c per-op facts
`scriptAccepts_pickStruct_pick_cons` and the `runOps`-level
`runOps_placeholder_cons_eq` / `runOps_pushCodesepIndex_cons_eq`), threads
them through the list via `scriptAccepts_runOps_prefix_cong`, and composes
with #95's `runOps`-equality headline to land the acceptance-surface
round-trip back on `m.ops`:

```
scriptAccepts (runParsedBytes (compileSafe p) s) = scriptAccepts (runOps m.ops s)
```

Add-only. Touches NOTHING in the omnibus / dispatch cascade /
`OmnibusLoop.lean` / `tests/OmnibusInstantiation.lean`.
-/

namespace RunarVerification.Stack.LoopAccept

open RunarVerification.Stack (StackOp PushVal)
open RunarVerification.Stack.Eval (StackState runOps scriptAccepts)
open RunarVerification.Script.Parse
  (loopNormalizeStackOp loopNormalizeOps RunarEmittableLoop AreLoopEmittable
   normalizePushVal isPushLikeLoopOp
   loopNormalizeStackOp_eq_self_of_RunarEmittable
   runOps_placeholder_cons_eq runOps_pushCodesepIndex_cons_eq)
open RunarVerification.Stack.LoopBridge
  (scriptAccepts_pickStruct_pick_cons scriptAccepts_runOps_prefix_cong)

/-! ## (a) Per-op `scriptAccepts`-cons head equivalence

For each `RunarEmittableLoop op`, replacing the head `op` of a cons by
its loop-normalised form `loopNormalizeStackOp op` preserves
`scriptAccepts`. The `.push` case is the ONLY one carrying a side
condition — `normalizePushVal v = v` (canonical push) — because a
non-canonical normalisation lands a genuinely different runtime value. -/

/-- `runOps`-level: `.placeholder i n` cons-agrees with `.push (.bigint 0)`,
lifted to `scriptAccepts` (general over `i`). The Tier 4c
`scriptAccepts_placeholder_push_cons` only covered `i = 0`; this lifts the
general `runOps_placeholder_cons_eq` (any `i`). -/
theorem scriptAccepts_placeholder_push_cons_gen (i : Nat) (n : String)
    (rest : List StackOp) (s : StackState) :
    scriptAccepts (runOps (.placeholder i n :: rest) s)
      = scriptAccepts (runOps (.push (.bigint 0) :: rest) s) := by
  rw [runOps_placeholder_cons_eq i n rest s]

/-- `runOps`-level: `.pushCodesepIndex` cons-agrees with `.push (.bigint 0)`,
lifted to `scriptAccepts`. -/
theorem scriptAccepts_pushCodesepIndex_push_cons (rest : List StackOp) (s : StackState) :
    scriptAccepts (runOps (.pushCodesepIndex :: rest) s)
      = scriptAccepts (runOps (.push (.bigint 0) :: rest) s) := by
  rw [runOps_pushCodesepIndex_cons_eq rest s]

/-- The push-canonicality side condition for the `.push` op class. For a
non-push op it is vacuously satisfied. -/
def loopPushCanonical : StackOp → Prop
  | .push v => normalizePushVal v = v
  | _       => True

/-- **Per-op head equivalence.** For any `RunarEmittableLoop op` whose
push (if it is one) is canonical, the loop-normalised head is
`scriptAccepts`-cons-equivalent to the original. -/
theorem scriptAccepts_loopNormalizeStackOp_cons
    (op : StackOp) (hOp : RunarEmittableLoop op)
    (hCanon : loopPushCanonical op)
    (rest : List StackOp) (s : StackState) :
    scriptAccepts (runOps (loopNormalizeStackOp op :: rest) s)
      = scriptAccepts (runOps (op :: rest) s) := by
  cases hOp with
  | flat op h =>
      rw [loopNormalizeStackOp_eq_self_of_RunarEmittable op h]
  | push v h =>
      -- `loopNormalizeStackOp (.push v) = .push (normalizePushVal v)`;
      -- canonical push ⇒ `normalizePushVal v = v` ⇒ heads identical.
      have hv : normalizePushVal v = v := hCanon
      show scriptAccepts (runOps (.push (normalizePushVal v) :: rest) s)
        = scriptAccepts (runOps (.push v :: rest) s)
      rw [hv]
  | pickStruct d hd =>
      show scriptAccepts (runOps (.pick d :: rest) s)
        = scriptAccepts (runOps (.pickStruct d :: rest) s)
      rw [scriptAccepts_pickStruct_pick_cons d rest s]
  | placeholder i n =>
      show scriptAccepts (runOps (.push (.bigint 0) :: rest) s)
        = scriptAccepts (runOps (.placeholder i n :: rest) s)
      rw [scriptAccepts_placeholder_push_cons_gen i n rest s]
  | pushCodesepIndex =>
      show scriptAccepts (runOps (.push (.bigint 0) :: rest) s)
        = scriptAccepts (runOps (.pushCodesepIndex :: rest) s)
      rw [scriptAccepts_pushCodesepIndex_push_cons rest s]
  | loopOpcode name h =>
      -- `loopNormalizeStackOp (.opcode name) = .opcode name` (identity arm).
      rfl

/-! ## (b) List-level canonicality predicate -/

/-- Every op in the list satisfies `loopPushCanonical` (every push is
canonical). For the loop fixture this is `decide`able on the explicit
literal (all pushes are small-int `.bigint`). -/
def AllLoopPushCanonical : List StackOp → Prop
  | [] => True
  | op :: rest => loopPushCanonical op ∧ AllLoopPushCanonical rest

/-! ## (c) The list-level `scriptAccepts` normalisation-preservation -/

/-- **The acceptance-surface loop-normalisation identity.** For an
`AreLoopEmittable` op list whose pushes are all canonical, running the
loop-normalised list is `scriptAccepts`-equivalent to running the
original — closing the SEMANTIC-only loop swaps (`pickStruct`/`placeholder`/
`pushCodesepIndex`) on the acceptance surface. By structural induction on
the list, threading each head equivalence through the (already-normalised)
tail via `scriptAccepts_runOps_prefix_cong`. -/
theorem scriptAccepts_runOps_loopNormalizeOps_eq :
    ∀ (ops : List StackOp), AreLoopEmittable ops → AllLoopPushCanonical ops →
      ∀ (s : StackState),
        scriptAccepts (runOps (loopNormalizeOps ops) s)
          = scriptAccepts (runOps ops s) := by
  intro ops hOps
  induction ops with
  | nil => intro _ s; rfl
  | cons op rest ih =>
      intro hCanon s
      cases hOps with
      | cons _ _ hOp hRest _ =>
          obtain ⟨hCanonHead, hCanonRest⟩ := hCanon
          -- `loopNormalizeOps (op :: rest) = loopNormalizeStackOp op :: loopNormalizeOps rest`.
          show scriptAccepts (runOps (loopNormalizeStackOp op :: loopNormalizeOps rest) s)
            = scriptAccepts (runOps (op :: rest) s)
          -- Step 1: thread the IH (tail normalisation) under the normalised head,
          -- via prefix congruence on the single-element prefix `[loopNormalizeStackOp op]`.
          have hTailCong : ∀ s',
              scriptAccepts (runOps (loopNormalizeOps rest) s')
                = scriptAccepts (runOps rest s') :=
            fun s' => ih hRest hCanonRest s'
          have hStep1 :
              scriptAccepts (runOps (loopNormalizeStackOp op :: loopNormalizeOps rest) s)
                = scriptAccepts (runOps (loopNormalizeStackOp op :: rest) s) := by
            have := scriptAccepts_runOps_prefix_cong
              [loopNormalizeStackOp op] (loopNormalizeOps rest) rest hTailCong s
            simpa using this
          rw [hStep1]
          -- Step 2: the per-op head equivalence.
          exact scriptAccepts_loopNormalizeStackOp_cons op hOp hCanonHead rest s

/-! ## (d) Composition with #95 → acceptance round-trip on `m.ops`

`Pipeline.Soundness.emitFast_single_public_runOps_eq_loop` (and its
`compileSafe` peer) give the `runOps`-equality round-trip to
`loopNormalizeOps m.ops`; rewriting through the acceptance-surface
normalisation identity closes the bridge back to the original `m.ops`. -/

open RunarVerification.ANF (ANFProgram)
open RunarVerification.Stack (StackMethod StackProgram)
open RunarVerification.Stack
open RunarVerification.Script
open RunarVerification.Pipeline (compileSafe peepholeProgram)
open RunarVerification.Pipeline.Soundness (runParsedBytes)

/-- **HEADLINE (`emitFast` peer): acceptance-surface loop round-trip on
`m.ops`.** For a single-public-method program whose body is
`AreLoopEmittable` with canonical pushes, the deployed bytes are ACCEPTED
from `initialStack` exactly when running the ORIGINAL body `m.ops` is
accepted. -/
theorem scriptAccepts_emitFast_single_public_runOps_eq_loop
    (p : StackProgram) (m : StackMethod) (initialStack : StackState)
    (hPublic : Emit.publicMethodsOf p = [m])
    (hOps : AreLoopEmittable m.ops)
    (hCanon : AllLoopPushCanonical m.ops) :
    scriptAccepts (runParsedBytes (Emit.emitFast p) initialStack)
      = scriptAccepts (runOps m.ops initialStack) := by
  rw [Pipeline.Soundness.emitFast_single_public_runOps_eq_loop
        p m initialStack hPublic hOps]
  exact scriptAccepts_runOps_loopNormalizeOps_eq m.ops hOps hCanon initialStack

/-- **HEADLINE (`compileSafe` peer): acceptance-surface loop round-trip on
`m.ops`.** The deployed bytes of a single-public-method loop program are
ACCEPTED from `initialStack` exactly when the ORIGINAL body `m.ops` is
accepted. -/
theorem scriptAccepts_compileSafe_single_public_runOps_eq_loop
    (p : ANFProgram) (bytes : ByteArray)
    (m : StackMethod) (initialStack : StackState)
    (hSafe : compileSafe p = .ok bytes)
    (hPublic : Emit.publicMethodsOf (peepholeProgram (Lower.lower p)) = [m])
    (hOps : AreLoopEmittable m.ops)
    (hCanon : AllLoopPushCanonical m.ops) :
    scriptAccepts (runParsedBytes bytes initialStack)
      = scriptAccepts (runOps m.ops initialStack) := by
  rw [Pipeline.Soundness.compileSafe_single_public_runOps_eq_loop
        p bytes m initialStack hSafe hPublic hOps]
  exact scriptAccepts_runOps_loopNormalizeOps_eq m.ops hOps hCanon initialStack

/-! ## (e) Anti-vacuity smoke: the count=3 fixture chain

`AgreesLoopParametric` proved `AreLoopEmittable loopOkPeepChain` and
`loopNormalizeOps loopOkPeepChain = loopOkParsedOps`. Here we confirm the
GENERAL acceptance-surface normalisation identity, instantiated on the
fixture chain, reproduces exactly the Tier 4c
`scriptAccepts_parsedOps_eq_peepChain` (the hand-threaded three-swap
acceptance equivalence between the parsed ops and the peephole chain) —
i.e. the general bridge SUBSUMES the fixed-fixture acceptance equivalence. -/

/-- The fixture chain's pushes are all canonical (small-int `.bigint`). -/
theorem allLoopPushCanonical_loopOkPeepChain :
    AllLoopPushCanonical LoopBridge.loopOkPeepChain := by
  rw [LoopBridge.loopOkPeepChain_explicit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (show normalizePushVal _ = _; decide)
    | trivial

/-- **ANTI-VACUITY.** The general acceptance-surface normalisation
identity, on the count=3 fixture chain, equals the Tier 4c
`scriptAccepts_parsedOps_eq_peepChain` (with the orientation flipped: Tier
4c states `parsedOps ≡ peepChain`; the general identity rewrites
`loopNormalizeOps peepChain = parsedOps`, so the two agree on every
state). -/
theorem scriptAccepts_loopNormalizeOps_loopOkPeepChain_eq (s : StackState) :
    scriptAccepts (runOps LoopBridge.loopOkParsedOps s)
      = scriptAccepts (runOps LoopBridge.loopOkPeepChain s) := by
  have hGen := scriptAccepts_runOps_loopNormalizeOps_eq
    LoopBridge.loopOkPeepChain
    LoopBridge.areLoopEmittable_loopOkPeepChain
    allLoopPushCanonical_loopOkPeepChain s
  rw [LoopBridge.loopNormalizeOps_loopOkPeepChain_eq] at hGen
  exact hGen

end RunarVerification.Stack.LoopAccept
