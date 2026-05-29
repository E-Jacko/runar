import RunarVerification.Pipeline
import RunarVerification.ANF.EntryModel

/-!
# ANF IR — Typed-entry discharge bridge (WS0a Task 8, piece 2c — the PAYOFF)

This is the §11.5 payoff: a **from-witness** corollary of the dispatch-level
omnibus `compileSafe_observational_correct_arith_consume`
(`Pipeline.lean`) that discharges ALL of its entry-side premises by
construction, via the type-directed entry model of `ANF.EntryModel`.

The omnibus quantifies the initial ANF state, the initial stack, and the
tagged stack-map FREELY, then demands FIVE entry-side facts about them:

* `hAgrees`     — `agreesTagged tsm initialAnf initialStack`
* `hUntag`      — `untagSm tsm = (params.reverse).map (·.name)`
* `hTypedEntry` — `EntryBigintTyped Γ initialAnf`
* `hTsmTyped`   — `entryTsmArithTyped Γ tsm`
* `hCoh`        — `tsmCoherent initialAnf tsm`

Those are exactly the "§11.5 typed-entry assumption": properties of an
*arbitrary* runtime entry that the omnibus has to be GIVEN.  This file
instantiates the entry concretely as the type-directed
`mkEntryState` / `mkStackEntry` / `mkTsm` triple over a free raw
`witness`, and feeds the `EntryModel` by-construction lemmas
(`agreesTagged_mkEntry`, `untagSm_mkTsm`,
`mkEntryState_entryBigintTyped_noProps`, `entryTsmArithTyped_mkEntry`,
`tsmCoherent_mkEntry`) directly into the omnibus.

**The point (verify in the report):** the resulting theorem
`arith_consume_from_witness` carries ONLY program-side hypotheses
(`hWF` / `hMem` / `hPublic` / `hSafe` / `hSinglePublic` / `hName` /
`hChain`) plus the structural `hnd` (distinct param names) and
`hAllBigint` (every param declared `.bigint`) and a *free* `witness`.
There is NO `agreesTagged`, NO `EntryBigintTyped`, NO
`entryTsmArithTyped`, NO `tsmCoherent`, and NO `hUntag` premise — every
one is discharged by the type-directed construction.  That is the §11.5
typed-entry assumption eliminated for stateless arith.

This is a NEW leaf file that nothing else imports yet.  `EntryModel`
does NOT import `Pipeline`, and `Pipeline` does NOT import `EntryModel`,
so importing both here is cycle-free; this file does NOT touch the
omnibus or the entry-model lemmas.
-/

namespace RunarVerification.ANF.EntryDischarge

-- `compileSafe` lives directly in `Pipeline`; the omnibus theorem +
-- `successAgrees` / `runParsedBytes` live in `Pipeline.Soundness`.
open RunarVerification.Pipeline (compileSafe)
open RunarVerification.Pipeline.Soundness
  (successAgrees runParsedBytes compileSafe_observational_correct_arith_consume)
-- Sub-namespaces brought into scope by short name (`WF.ANF`, `Agrees.…`,
-- `Lower.…`, `Eval.…`).
open RunarVerification.ANF (ANFProgram ANFMethod ANFParam ANFType)
open RunarVerification.ANF.Eval (Value State)
open RunarVerification.ANF.TypeCheck (TypeEnv.ofParamsProps)
open RunarVerification.ANF.EntryModel
  (mkEntryState mkStackEntry mkTsm
   agreesTagged_mkEntry untagSm_mkTsm
   mkEntryState_entryBigintTyped_noProps
   entryTsmArithTyped_mkEntry tsmCoherent_mkEntry)
open RunarVerification.ANF
open RunarVerification.Stack

/-- **WS0a Task 8 piece 2c — the PAYOFF.**

`compileSafe_observational_correct_arith_consume` holds **from a raw
witness**, with every entry-side premise discharged by construction.

Given the program-side hypotheses (well-formed program `hWF`, the method
is a public member `hMem`/`hPublic`, the deployed bytes `hSafe`, the
single-public-method filter `hSinglePublic`, the non-constructor name
`hName`, and the emittable-arith chain predicate `hChain`), plus the two
structural facts that the method's parameters have distinct names (`hnd`)
and are all declared `.bigint` (`hAllBigint`), the deployed `compileSafe`
bytes are observationally correct on the **type-directed entry** built
from ANY raw `witness`: running the parsed Script agrees (on its success
bit) with evaluating the ANF body.

The five §11.5 entry premises are supplied entirely by the `EntryModel`
by-construction lemmas — none is a hypothesis here:

* `agreesTagged`     ⟸ `agreesTagged_mkEntry`
* `hUntag`           ⟸ `untagSm_mkTsm`
* `EntryBigintTyped` ⟸ `mkEntryState_entryBigintTyped_noProps`
  (at `Γ := ofParamsProps [] anfM.params`)
* `entryTsmArithTyped` ⟸ `entryTsmArithTyped_mkEntry`
* `tsmCoherent`      ⟸ `tsmCoherent_mkEntry`

Stateless / no-property case (`propsVals := []`), which is exactly the
scope the `EntryModel` no-props corollaries cover. -/
theorem arith_consume_from_witness
    (p : ANFProgram) (hWF : WF.ANF p) (anfM : ANFMethod) (bytes : ByteArray)
    (hMem : anfM ∈ p.methods) (hPublic : anfM.isPublic = true)
    (hSafe : compileSafe p = .ok bytes)
    (hSinglePublic : p.methods.filter (·.isPublic) = [anfM])
    (hName : anfM.name ≠ "constructor")
    (hChain :
      Agrees.emittableArithChainReadyNoDblNeg
        (Lower.computeLastUses anfM.body)
        anfM.body
        (List.reverse (anfM.params.map (·.name)))
        0 false)
    (witness : List Value)
    (hnd : (anfM.params.map ANFParam.name).Nodup)
    (hAllBigint : ∀ pr ∈ anfM.params, pr.type = ANFType.bigint) :
    successAgrees
      (RunarVerification.ANF.Eval.evalBindingsP p.methods
        (mkEntryState anfM.params [] witness) anfM.body)
      (runParsedBytes bytes (mkStackEntry anfM.params [] witness)) :=
  compileSafe_observational_correct_arith_consume
    p hWF anfM bytes hMem hPublic hSafe
    (mkEntryState anfM.params [] witness)
    (mkStackEntry anfM.params [] witness)
    (mkTsm anfM.params)
    (agreesTagged_mkEntry anfM.params [] witness hnd)
    (TypeEnv.ofParamsProps [] anfM.params)
    hSinglePublic hName hChain
    (untagSm_mkTsm anfM.params)
    (mkEntryState_entryBigintTyped_noProps anfM.params [] witness hnd)
    (entryTsmArithTyped_mkEntry [] anfM.params hnd hAllBigint)
    (tsmCoherent_mkEntry [] anfM.params [] witness hnd)

end RunarVerification.ANF.EntryDischarge
