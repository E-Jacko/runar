import RunarVerification.Script.LoopParse
import RunarVerification.Stack.AgreesLoopParsed

/-!
# Anti-vacuity smoke: the GENERAL loop round-trip subsumes the count=3 pin

`Script.LoopParse` builds the count-AGNOSTIC parse round-trip for the
loop instruction set (`AreLoopEmittable` ⇒ `parseScript (emitOps ops) =
.ok (loopNormalizeOps ops)`). This file proves that the general
machinery, instantiated on the canonical fixture's peephole chain
`LoopBridge.loopOkPeepChain` (the count=3 loop), reproduces EXACTLY the
explicit `LoopBridge.loopOkParsedOps` that Tier 4c obtained by
`native_decide` on the FIXED bytes (`loopOk_parse_pin`).

Concretely:

1. `loopNormalizeOps loopOkPeepChain = loopOkParsedOps` — the general
   loop-normaliser reproduces the hand-written parsed op list.
2. `AreLoopEmittable loopOkPeepChain` — the fixture chain is in the
   general predicate.
3. The two combine so that
   `parseScript (Emit.emitOps loopOkPeepChain) = .ok loopOkParsedOps`
   follows from the GENERAL `parseScript_emit_round_trip_loop` — i.e.
   the general theorem subsumes the fixed `native_decide` pin (modulo
   the byte-source: the pin parses `compileSafe loopOkProg`, here we
   parse `Emit.emitOps loopOkPeepChain` directly; the bridge
   `Stack.AgreesLoopBridge.loopOkM_peepholed_ops_eq` ties the two
   together at the op-list level).

This is the evidence the general machinery is CORRECT: nothing in
`Script.LoopParse` is vacuous, and the parametric foundation
reproduces the fixed-input certificate on the fixture.
-/

namespace RunarVerification.Stack.LoopBridge

open RunarVerification.Script.Parse (loopNormalizeOps AreLoopEmittable
  parseScript_emit_round_trip_loop)

/-- (1) The general loop-normaliser, applied to the fixture's peephole
chain, reproduces the hand-written `loopOkParsedOps`. Proven by
unfolding `loopOkPeepChain` to its explicit literal form (the
`native_decide`-checked `loopOkPeepChain_explicit`) and `decide`-ing
the resulting closed computation. -/
theorem loopNormalizeOps_loopOkPeepChain_eq :
    loopNormalizeOps loopOkPeepChain = loopOkParsedOps := by
  rw [loopOkPeepChain_explicit]
  rfl

/-- (2) The fixture's peephole chain is `AreLoopEmittable`. The chain is
flat (no IF), its pushes are all canonical small-int `.bigint`, it has
two `.pickStruct` (depths 2, 3 — both in `[1..16]`), one `.placeholder`
in the epilogue, the rest short-form / allowlisted opcodes. The
per-cons tail obligations (push-like ops not followed by `OP_PICK` /
`OP_ROLL`) hold because no push/placeholder is immediately followed by
a pick/roll in this chain. Established by `decide` on the explicit
literal. -/
theorem areLoopEmittable_loopOkPeepChain :
    AreLoopEmittable loopOkPeepChain := by
  rw [loopOkPeepChain_explicit]
  -- Build the 21-op chain by repeated `.cons`, separating the head op
  -- proof from the push-like tail obligation. `op_tac` proves each head
  -- op; the tail obligation is `decide`d on the closed remaining bytes.
  refine .cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_
    (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_
    (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_
    (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_ (.cons _ _ ?_
    (.cons _ _ ?_ .nil ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  -- 21 head-op goals followed by 21 tail-obligation goals, interleaved
  -- by `refine`. Each head is one of: small-bigint push, pickStruct
  -- (depth ∈ [1..16]), roll (flat), short-form (flat), loop-opcode,
  -- placeholder. Each tail is a `decide`able `restNotPickOrRoll`.
  all_goals first
    | exact .push _ (RunarVerification.Script.Parse.normalizedPush_bigint_small _ (by decide))
    | exact .pickStruct _ (by decide)
    | exact .placeholder _ _
    | exact .loopOpcode _ (by decide)
    | exact .flat _ (by decide)
    | (intro _; exact ⟨by decide, by decide⟩)
    | (intro h; exact absurd h (by decide))

/-- (3) ANTI-VACUITY: the GENERAL round-trip, on the fixture chain,
reproduces the explicit `loopOkParsedOps` that Tier 4c got by
`native_decide` on the fixed bytes. -/
theorem parseScript_emitOps_loopOkPeepChain_eq :
    RunarVerification.Script.Parse.parseScript
        (RunarVerification.Script.Emit.emitOps loopOkPeepChain)
      = .ok loopOkParsedOps := by
  rw [parseScript_emit_round_trip_loop loopOkPeepChain areLoopEmittable_loopOkPeepChain]
  rw [loopNormalizeOps_loopOkPeepChain_eq]

end RunarVerification.Stack.LoopBridge
