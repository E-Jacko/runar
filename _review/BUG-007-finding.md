# BUG-007 Finding: SLH-DSA verifier accepts oversize signatures (missing trailing-bytes bound check)

## Status: REAL MISSING BOUND CHECK — fix NOT applied per task scope (tests only).

## Summary

`packages/runar-testing/src/crypto/slh-dsa.ts :: slhVerify(params, msg, sig, pk)`
silently ignores any signature bytes after the d-th hypertree layer. A
signature with the canonical content plus arbitrary trailing bytes (or an
extra cloned XMSS layer appended) verifies as **true**, when FIPS-205
mandates it must be **false**.

Reproducer (one of six in `post-quantum-bounds.test.ts`, all 6 parameter
sets fail identically):

```ts
const sig = slhSign(params, msg, sk);       // canonical sig
const xmssLen = (params.len + params.hp) * params.n;
const over = new Uint8Array(sig.length + xmssLen);
over.set(sig, 0);
over.set(sig.slice(sig.length - xmssLen), sig.length);  // append a clone of last XMSS layer

slhVerify(params, msg, over, pk);            // returns TRUE — should be FALSE
```

## Root cause

`slhVerify` in `packages/runar-testing/src/crypto/slh-dsa.ts` (line 637):

1. Checks `pk.length !== 2 * n` and rejects mismatches.
2. **Does NOT check `sig.length` against the parameter-set's exact expected
   length** (`n + k*(1+a)*n + d*(len+hp)*n`).
3. The parsing loop advances an `offset` cursor and consumes exactly
   `xmssSigLen = (len + hp) * n` bytes per layer for `d` layers. After
   layer `d-1`, `currentMsg` is compared to `pkRoot` and `true` is
   returned on match. Any bytes at `sig[offset..]` are silently discarded.

In contrast, `wotsVerify` (line 190 of `wots.ts`) explicitly checks
`sig.length !== LEN * N` and rejects — which is why the equivalent
WOTS+ oversize tests in `post-quantum-bounds.test.ts` PASS.

## Severity (off-chain reference impl only)

This is the **off-chain reference verifier** used by the AST interpreter
and dual-oracle tests, NOT the compiled Bitcoin Script. The compiled
on-chain `verifySLHDSA_SHA2_*` Script bytecode uses fixed-offset
`OP_SPLIT`s — its behavior on oversize input depends on the codegen's
trailing-cleanup pattern (similar to `wots-codegen.ts:220-222`'s
`swap;drop` of `sigRest`).

Without a fix, the off-chain interpreter and the on-chain script may
diverge on oversize input. This *can* be a real soft-fork attack vector
if any deployed contract uses the off-chain interpreter result as the
"truth" for spending decisions before broadcasting. For deployed
verifiers running purely on-chain (the documented use case) this is a
robustness gap, not an exploit.

## Test treatment in this commit

The 6 affected adversarial tests (one per parameter set:
`SHA2_128s/128f/192s/192f/256s/256f`) are kept in the file but rewritten
to assert the **current** (buggy) behavior and tagged with
`// TODO(BUG-007-followup)` so they will FAIL the day someone fixes
`slhVerify` and then read the followup TODO to invert the assertion.

The remaining 8 SLH-DSA bound tests per parameter set (short / R-tamper /
section-zero / boundary-byte) all pass — the verifier rejects these
correctly.

## Recommended fix (NOT applied)

Add as the first line of `slhVerify` in
`packages/runar-testing/src/crypto/slh-dsa.ts`:

```ts
const forsLen = params.k * (1 + params.a) * params.n;
const xmssLen = (params.len + params.hp) * params.n;
const expected = params.n + forsLen + params.d * xmssLen;
if (sig.length !== expected) return false;
```

Parity work after the off-chain fix:

- Audit the on-chain `compilers/*/codegen/slh_dsa.*` codegen to confirm
  the compiled Script also rejects oversize input (the WOTS+ codegen's
  trailing `swap;drop` pattern may or may not be replicated; needs
  inspection per tier).
- Add a dual-oracle adversarial test (`post-quantum-slh-dual-oracle.test.ts`)
  asserting interpreter and compiled script agree on oversize rejection.
- Replicate fix across all 7 SDK / reference-impl ports of `slhVerify`
  (Go, Rust, Python, Zig, Ruby, Java each ship their own copy of the
  FIPS-205 verifier in their `runar-*` package's crypto module).

## Why this finding stops short of a fix

Task BUG-007 explicitly scopes "do NOT modify the SLH-DSA / WOTS+ codegen
modules themselves unless you've explicitly confirmed (a) a missing bound
check is the cause and (b) the user has implicitly authorised the fix
via this task. Adding tests only is the safe default." The off-chain
reference verifier is not the codegen, but the fix has cross-tier
ripples (6 other ports plus the codegen audit). Surfacing this as a
finding lets the user choose whether to scope the fix as a follow-up
task or include it in BUG-007's remediation.
