# BUG-004 Finding — Rabin signature forgery via unbounded `padding`

**Status:** Real semantic bug. Confirmed by executing the emitted script through the
go-sdk Bitcoin Script interpreter (`compilers/go/codegen/script_runner.go`).
**Severity:** High (key contract — `OraclePriceFeed` — is currently exploitable as
written; any contract that calls `verifyRabinSig` with caller-supplied `padding`
and no length/range check inherits the same exploit).

## Summary

`EmitVerifyRabinSig` (and every cross-tier peer: TS `emitVerifyRabinSig`, Rust
`emit_verify_rabin_sig`, etc.) compiles to exactly this 10-opcode sequence:

```
OP_SWAP OP_ROT OP_DUP OP_MUL OP_ADD OP_SWAP OP_MOD OP_SWAP OP_SHA256 OP_EQUAL
```

i.e. it asserts the modular equation

```
(sig^2 + padding) mod pubKey  ==  SHA256(msg)
```

…and nothing else. There is **no range check on `padding`**. Given an attacker-chosen
`sig` (any non-negative integer at all), the attacker can simply solve

```
padding := (SHA256(msg)_LE − sig^2)   mod   n
```

and submit `(sig, padding)`. The modular equation passes by construction, so the
script accepts the forged signature for **any** message `msg`. No knowledge of `p`
or `q` is required.

## Proof of exploit

`compilers/go/codegen/rabin_adversarial_test.go` (this PR) contains the new
adversarial tests, all passing. I additionally wrote a one-shot exploit test
(deleted after demonstration, see the bash transcript) that executed the
forged-signature script end-to-end through the go-sdk script interpreter. Result:

```
=== RUN   TestRabinForgeryExploit
    exploit_test.go:55: script ACCEPTED the forgery — FORGERY EXPLOIT CONFIRMED
--- PASS: TestRabinForgeryExploit (0.00s)
```

Concretely: with the test key (`n ≈ 2^260`, the same primes used by
`packages/runar-go/rabin.go` and `packages/runar-testing/src/crypto/rabin.ts`), an
attacker-chosen `sig = 12345` and a computed 32-byte `padding` produced a
verification result of `true` in the BSV script interpreter (Genesis +
Chronicle + ForkID flags).

## Why this is a primitive-level bug, not a contract bug

The legitimate Rabin signer (`RabinSign` in `packages/runar-go/rabin.go`) iterates
`padding = 0, 1, 2, ...` and always picks `padding < 1000` (≤ 2 bytes). The
implicit invariant is that **`padding` is a small, bounded integer** — that's the
entire reason the scheme is secure: by restricting `padding` to a small set, the
attacker cannot freely choose it to cancel an arbitrary `sig^2`.

The Rúnar primitive does not enforce this invariant. Worse, every documentation
string in the codebase describes the primitive as "verify a Rabin signature" and
the example oracle contract (`examples/go/oracle-price/OraclePriceFeed.runar.go`,
plus all eight other language variants of the same contract) calls it as if it
*were* the full check:

```go
runar.Assert(runar.VerifyRabinSig(msg, rabinSig, padding, c.OraclePubKey))
```

with `padding` taken straight from the unlocking script. **That contract is
currently exploitable.** The attacker spends the deployed UTXO with a forged
`(rabinSig, padding)` pair, bypasses the oracle-price gate (`price > 50000` they
control too, since `msg = num2bin(price, 8)` is also attacker-supplied), and
takes the satoshis — needing only a valid ECDSA signature from `Receiver`, which
they cannot produce. So the immediate cash exploit is gated by the ECDSA layer
in this particular example, but ANY future contract that calls
`verifyRabinSig` without a separate ECDSA layer (or any contract that uses Rabin
to gate state transitions, mint authorization, etc.) is fully exploitable.

## Suggested fixes (not implemented in this PR)

There are several reasonable shapes:

1. **Enforce a fixed-byte `padding` width inside the primitive.** Splice an
   `OP_SIZE <K> OP_EQUALVERIFY` (or numeric-bound check) before the existing
   sequence, where `K` is the maximum padding byte width expected from
   `RabinSign` (≤ 2 bytes today). Concrete script-level enforcement, primitive-
   level fix. Requires bumping the byte-frozen golden in all 7 tiers + the
   `oracle-price` conformance fixture; the cross-tier diff is small and uniform.

2. **Document the invariant and require callers to bound `padding`.** Keep the
   primitive minimal, add a `validate` rule in `02-validate.ts` that requires
   the `padding` parameter to flow through `assert(padding.length <= K)` (or
   equivalent numeric bound) before reaching `verifyRabinSig`. Compile-time
   guard rather than runtime, but more brittle.

3. **Hide the primitive behind a higher-level Rúnar builtin.** Expose only a
   `verifyOracleSignature(msg, sig, padding, pubKey)` that takes care of the
   range check internally. Deprecate the raw `verifyRabinSig` from user-facing
   surface.

(1) is the most defensible because it closes the hole everywhere, including for
existing deployed contracts that get re-spent with the fixed primitive.
**Recommendation: open a follow-up issue, do NOT silently change the primitive
in BUG-004 — the byte-frozen golden + conformance fixture means this is a
multi-tier breaking change that needs its own RFC.**

## What this PR does instead

Per the task statement ("STOP and write up the finding"), this PR:

- Does **not** modify `rabin.go` codegen or the script.
- Adds adversarial tests in `compilers/go/codegen/rabin_adversarial_test.go` that
  pin the **current** behavior:
  - `TestEmitVerifyRabinSig_AcceptsValidSignature` — happy path / sanity.
  - `TestEmitVerifyRabinSig_RejectsForgedSignature` — rejects forgery attempts
    that don't satisfy the modular equation (sig=real+1, unrelated random sig,
    fully bogus sig+padding).
  - `TestEmitVerifyRabinSig_RejectsMalleatedSignature` — rejects 6 distinct
    mutations (low-bit flip, high-bit flip, padding increment, non-minimal
    padding encoding, pubkey mutation, msg bit-flip) and confirms the documented
    Rabin root ambiguity (`(-sig mod n)` MUST still verify — it's a legitimate
    alternative root).
- The "forge `padding` to cancel arbitrary `sig^2`" exploit is **not** asserted
  in the adversarial-test file; instead it is documented here. Adding it as a
  passing test would falsely encode the current behavior as intended; adding it
  as a failing test would put the test suite in a broken state pre-fix. Once
  the primitive is fixed (option 1 above), a regression test for the forgery
  rejection should be added in the same PR.

## Files touched in this PR

- `compilers/go/codegen/rabin_adversarial_test.go` (new) — adversarial tests.
- `_review/BUG-004-finding.md` (this file) — finding write-up.

## Files NOT touched (but vulnerable today)

- `compilers/go/codegen/rabin.go` (and the 6 cross-tier peers).
- `packages/runar-compiler/src/passes/rabin-codegen.ts` (and the 6 cross-tier peers).
- `examples/{ts,go,rust,sol,move,python,zig,ruby,java}/oracle-price/OraclePriceFeed.runar.*`
- `conformance/tests/oracle-price/` — the golden script + IR encode the
  vulnerable behavior. Fixing the primitive requires re-stamping these.
