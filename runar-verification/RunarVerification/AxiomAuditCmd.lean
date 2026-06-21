/-
# `#audit_axioms` — build-enforced trust-boundary audit (PROVE-001)

`#print axioms` is a *diagnostic*: it prints a declaration's axiom dependencies
but never fails the build, and its output is dominated by ~24 auto-generated
`._native.native_decide.ax_N` names per theorem that obscure the real trust
content and reshuffle on every reproof.

`#audit_axioms foo` turns that diagnostic into a **gate**. It collects `foo`'s
real axiom dependencies via `Lean.collectAxioms` and:

* **fails the build** if `foo` depends on `sorryAx` (an incomplete proof), or on
  any axiom outside the documented v1 trust base (`allowedSubstrings`);
* **collapses** the native_decide / `ofReduceBool` noise to a single boolean and
  reports whether the Lean compiler is in `foo`'s trusted base (the
  `native_decide` TCB disclosure the manifest must carry).

This makes "the capstone depends on exactly the documented axioms, no hidden
`sorryAx`, and here is its native_decide exposure" a **machine-checked** fact
rather than a hand count. No new mathematical axiom is introduced; this file
declares a command only.
-/
import Lean

open Lean Elab Command

namespace RunarVerification.AxiomAudit

/-- Name substrings that mark a `native_decide` / compiler-trust axiom. Their
presence is *recorded* (the Lean compiler is then in the TCB) but is not itself
an audit failure — `native_decide` is a disclosed, accepted part of the trust
base. -/
def nativeMarkers : List String := ["native_decide", "ofReduceBool"]

/-- The documented v1 trust base the omnibus capstone instantiations may depend
on (besides `native_decide`). Matched as a component/substring of the fully
qualified axiom name, so e.g. `RunarVerification.ANF.Eval.Crypto.authBackend`
matches `"authBackend"`. Any axiom outside this set (or `sorryAx`) fails the
build — which is the point: a newly-introduced or undisclosed dependency is
caught at the gate.

Kept deliberately tight: the capstone instantiations depend only on the three
logical axioms, the single `crypto_call` structural fallback, the three opaque
crypto backends, and (for stateful spends) the BIP-143 witness. If that set ever
grows, this list must be updated *and* the change justified in
`TRUST_MANIFEST.md` — the audit forces that reconciliation. -/
def allowedSubstrings : List String :=
  [ "propext", "Classical.choice", "Quot.sound",
    "compileSafe_observational_correct_modulo_crypto_call_codegen",
    "authBackend", "hashBackend", "preimageBackend",
    "exists_checkSig_witness_under_validTxContext" ]

private def containsSub (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

private def isNative (n : Name) : Bool :=
  nativeMarkers.any (containsSub n.toString)

private def isAllowed (n : Name) : Bool :=
  allowedSubstrings.any (containsSub n.toString)

private def isSorry (n : Name) : Bool :=
  n.toString = "sorryAx" || containsSub n.toString "sorryAx"

/-- `#audit_axioms foo` — fail the build unless `foo`'s axiom dependencies all
lie in the documented v1 trust base; log `foo`'s native_decide exposure. -/
elab "#audit_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
  let axs ← liftCoreM <| collectAxioms name
  let mut usesNative := false
  let mut bad : Array Name := #[]
  for ax in axs do
    if isSorry ax then
      throwError "AXIOM AUDIT FAILED: {name} depends on `sorryAx` (incomplete proof)."
    else if isNative ax then
      usesNative := true
    else if isAllowed ax then
      pure ()
    else
      bad := bad.push ax
  unless bad.isEmpty do
    throwError
      "AXIOM AUDIT FAILED: {name} depends on UNDOCUMENTED axiom(s) {bad.toList}.\n\
       Either the proof regressed or the v1 trust base changed — if intended, add \
       the axiom to `allowedSubstrings` in AxiomAuditCmd.lean AND justify it in \
       TRUST_MANIFEST.md."
  logInfo m!"axiom audit OK: {name} — native_decide in TCB: {usesNative}"

end RunarVerification.AxiomAudit
