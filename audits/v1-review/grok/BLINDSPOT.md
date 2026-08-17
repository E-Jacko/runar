# BLINDSPOT

What this verification apparatus cannot see is not a missing test file; it is a
**property of programs**. Invisible programs are those for which (1) the source
and the ANF binding model agree on a story about stack *depth* and *names* that
is false about stack *layout* or *value provenance*, and (2) every absolute
oracle either reuses that same ANF story or only checks whether the script
finishes with a truthy top. On such programs, seven compilers can emit identical
hex, the ANF interpreter can accept, Lean can prove accept/reject agreement for
any fragment that still classifies, the external pre-Genesis reference can
vacuously agree on empty-stack failure, and the deploy-time locking-script
gate can match across seven SDKs — while the locking script is still
unspendable on one branch, or spendable into a wrong continuation. Palmer-1’s
quiet face and open issue #149 are the same animal: join points where an
invariant is established in lowering, assumed in reconcile, and never named in
the construct ledger as “layout, not depth.”

A second invisible family is **single-implementation absolute semantics**:
Go-only field/FRI/Merkle codegen, and any large PQ script path that CI runs only
under non-`-short` jobs. Parity is empty by policy; goldens and self-produced
vectors can co-evolve; formal verification axiomatizes or defers the primitive.
The apparatus then proves “we all agree with ourselves,” which is necessary
plumbing and zero evidence about the prime field edge or the transcript absorb
order that was never in the vector table.

A related invisibility sits *inside* the safety net: Layer C and the declared-results
top-N check (`05-stack-lower.ts`) prove depth and result-slot names, not the order of
inherited mid-stack slots. NestedAdopt fails Spend on the else path while those
invariants hold and while the only regression suite for it is `describe.skip`.
We executed that path: 2 failed / 4 passed under real Spend (see EXECUTION-LOG.md).

**The single change that most reduces escape rate before v1:** make
**layout-sensitive nested branch joins with live non-result siblings** (the #149
shape) a hard, default-CI absolute gate — un-skipped real Spend + independent
expectedState + construct-ledger `UNCOVERED` until green + a spend-shapes family
that can *generate* it — and treat any future join/layout bug the same way:
depth-and-name agreement is not acceptance. Everything else (provenance
hygiene, Go-only KAT labels, axiom doc drift) is secondary to the fact that the
next RC fund-lock will look like another “both arms leave equal depth” pass
while the middle of the stack was rotated.
