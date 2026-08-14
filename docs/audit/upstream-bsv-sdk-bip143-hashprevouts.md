# Upstream defect: `bsv-sdk` (Rust) builds `hashPrevouts` in the wrong order

**Status:** confirmed, pinned in-repo, **not yet filed upstream**
**Affects:** `bsv-sdk` 0.1.72 (our range: `>=0.1, <0.3`, `packages/runar-rs/Cargo.toml:24`)
**Found:** 2026-08-06, while bringing the Rust tier's mock provider to fail-closed
**Our pin:** `packages/runar-rs/tests/mock_broadcast_validation.rs`
`pin_bsv_sdk_cannot_sighash_input_index_above_zero`

This document is written to be **pasted into an upstream issue**. Nothing here
depends on Rúnar-specific context.

---

## Summary

`Spend` computes the BIP-143 `hashPrevouts` as **"the current input's outpoint
first, then the other inputs"**, rather than in transaction input order. Those
two orderings coincide only when `input_index == 0`.

Consequence: a **valid** signature over a correctly-constructed BIP-143 preimage
for any input at index > 0 evaluates to **false**. Conversely, a signature that
`Spend` *does* accept at index > 0 is one no other implementation — and no node —
will accept.

## Why we are confident it is upstream, not us

The signature in the reproducer is produced by **`bsv-sdk`'s own `LocalSigner`**,
so both sides of the comparison come from the same crate. The same transaction,
same key, same input index is **accepted by the Go tier's `go-sdk` script
interpreter** (`github.com/bsv-blockchain/go-sdk/script/interpreter`), which is
an independent implementation of the same consensus rules.

So: two implementations disagree, one of them agrees with the network, and it is
not this one.

## Reproduction

1. Build a transaction with **two** P2PKH inputs and one output.
2. Sign **input 1** (not input 0) with `bsv-sdk`'s `LocalSigner`, using the
   standard BIP-143 preimage for that input.
3. Evaluate input 1 with `bsv::script::spend::Spend`.

**Expected:** script succeeds — the signature is valid for that input.
**Actual:** script evaluates to false.

Signing and evaluating **input 0** of the same transaction succeeds, which is the
discriminator: nothing about the key, the script, or the output set changes.

## Root cause

BIP-143 defines `hashPrevouts` as the double-SHA256 of the serialized outpoints
of **all** transaction inputs, **in transaction order**:

```
hashPrevouts = dSHA256( outpoint(vin[0]) || outpoint(vin[1]) || ... )
```

The order is a property of the transaction, not of the input being signed — it is
identical for every input. `Spend` instead reassembles the input list as
`[current_input] ++ other_inputs`, which equals transaction order **iff** the
current input is already first.

The same reasoning applies to `hashSequence`, which is built from the same
reassembled list — worth checking in the same pass.

## Suggested fix

Reassemble the input list by **splicing the current input back at its original
index** rather than prepending it, before computing `hashPrevouts` /
`hashSequence`. For reference, `@bsv/sdk` (TypeScript) does exactly this in
`TransactionSignature.formatBip143`:

```js
inputs.splice(params.inputIndex, 0, currentInput)
```

## Impact for downstream users

Any consumer signing or validating a **multi-input** transaction is affected. In
practice this means:

- multi-input spends cannot be validated with this crate beyond input 0
- a consumer that validates only input 0 and infers the rest is **silently
  weaker** than it appears

In our case it meant our Rust SDK's broadcast validator had to refuse to draw any
conclusion from inputs at index > 0 — see the linked pin, which is written to go
**red** when this is fixed so we can tighten immediately.

## Related, same crate, same investigation

`Spend::validate()` never returns `false` — every failure path calls
`scriptEvaluationError`, which throws. Downstream `if !spend.validate()` branches
are therefore unreachable. Not a correctness bug, but it invites
"`validate()` returned true, we're fine" reasoning in consumers. Worth either
documenting or changing the signature to reflect it.

---

## For the Rúnar maintainer, before filing

- Confirm the defect still reproduces on the newest published `bsv-sdk` — the pin
  was written against **0.1.72** and our Cargo range admits up to `<0.3`.
- The reproducer in `mock_broadcast_validation.rs` is Rúnar-flavoured; reduce it
  to a standalone `bsv-sdk`-only snippet before filing (it needs nothing from
  this repo).
- Filing is an outward-facing action on a third-party repository and has not been
  done — this document exists so it can be, deliberately, by a human.
