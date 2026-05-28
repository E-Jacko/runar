# BUG-010 RFC — Padding range/length bound for `verifyRabinSig`

**Status:** Implemented across 7 tiers (this PR).
**Severity:** CRITICAL — fixes BUG-004 forgery exploit confirmed on `examples/*/oracle-price/`.
**Scope:** Codegen change only. Off-chain `RabinSign` and the `RabinSig`/`RabinPubKey`
type aliases are unchanged.

## Background

`emitVerifyRabinSig` (TS) and its six cross-tier peers previously compiled to a
fixed 10-opcode sequence asserting the modular equation
`(sig² + padding) mod pubKey == SHA256(msg)` — and **nothing else**.

Because `padding` was a free unlocking-script input with no on-chain bound, an
attacker could pick any `sig` and solve

```
padding := (SHA256(msg)_LE − sig²)  mod  n
```

then submit `(sig, padding)`. The modular equation held by construction. The
exploit was confirmed end-to-end in `_review/BUG-004-finding.md` (script
interpreter ACCEPTED `sig = 12345` plus a 32-byte computed padding).

The legitimate signer (`packages/runar-go/rabin.go::RabinSign`) only ever
produces `padding < 1000` (≤ 2 bytes). The Rabin scheme's security depends on
`padding` being a small, signer-bounded value — restricting the attacker's
freedom to cancel an arbitrary `sig²`.

## Chosen bound

**`0 ≤ padding < 65536`** (numeric, 16-bit unsigned range).

Rationale:

- Matches and exceeds the legitimate-signer ceiling of 1000 by ~65×; gives
  future signer implementations slack without re-stamping the script primitive.
- 2-byte unsigned representation aligns with the "`padding` is a small
  integer" semantic from the literature.
- Reduces the attacker's padding search space from `~n` (≈ 2²⁶⁰) to `2¹⁶`,
  which combined with `n` ≈ 2²⁶⁰ makes the forgery probability per attempt
  `≈ 2¹⁶ / 2²⁶⁰ = 2⁻²⁴⁴` — cryptographically negligible.

## Implementation

The fix splices a single 5-opcode range check into the existing emission. The
new sequence is **15 opcodes** total:

```
OP_SWAP                          ; msg sig pubKey padding
OP_DUP OP_0 <push 65536> OP_WITHIN OP_VERIFY   ; assert 0 <= padding < 65536
OP_ROT                           ; msg pubKey padding sig
OP_DUP OP_MUL                    ; msg pubKey padding sig²
OP_ADD                           ; msg pubKey (sig² + padding)
OP_SWAP                          ; msg (sig² + padding) pubKey
OP_MOD                           ; msg ((sig² + padding) mod pubKey)
OP_SWAP                          ; ((sig² + padding) mod pubKey) msg
OP_SHA256                        ; ((sig² + padding) mod pubKey) SHA256(msg)
OP_EQUAL                         ; bool
```

`OP_WITHIN` is `x min max → (min ≤ x < max)`. The check consumes the
duplicated padding and the two literal bounds; `OP_VERIFY` aborts the script
if the predicate is false. The original `padding` value is left intact for
the rest of the computation by the leading `OP_DUP`.

The `65536` literal is the minimal-encoded script number
`0x03 0x00 0x00 0x01` (3-byte little-endian signed, high bit clear). Total
script-byte cost of the new check (push opcode + 3 data bytes + 5 control
opcodes) is **+9 bytes** over the previous emission. For the
`oracle-price` conformance fixture this is a small fraction of the total
script.

## Alternatives considered

1. **`OP_SIZE OP_2 OP_LESSTHANOREQUAL OP_VERIFY` (byte-size check, 4 opcodes).**
   Cheaper by one opcode and a 3-byte push, but only bounds the *byte width*,
   not the numeric value, and crucially **does not reject negative paddings**.
   A 1-byte negative script-num (e.g. `0x81` = -1, `0xFF` = -127) passes
   `size ≤ 2`. The attacker can then choose padding ∈ [-32767, 32767], which
   doubles the forgery search space and breaks the principled "padding is a
   small *non-negative* integer" invariant. Rejected.

2. **Caller-side validate rule** (require `assert(padding.length ≤ K)` in the
   contract source). Brittle: relies on every contract author writing the
   check; the primitive itself remains exploitable for any contract that
   forgets it. Rejected.

3. **Hide `verifyRabinSig` behind a higher-level `verifyOracleSignature`
   builtin.** Pure surface change; same fix has to land at the codegen layer
   anyway. Rejected as a separate concern.

## Compatibility

This is a **breaking change** for any deployed UTXO whose locking script
embeds the old `verifyRabinSig` emission — those scripts are unchanged on
chain. New deployments and re-spends of state-continuation contracts will
pick up the new emission automatically.

The conformance suite's `oracle-price` golden (`expected-ir.json` +
`expected-script.hex`) is re-stamped to the new bytes. The
`compilers/go/codegen/rabin_test.go::TestEmitVerifyRabinSig_ByteFrozenGolden`
golden is updated to the new 15-opcode sequence. The
`compilers/go/codegen/rabin_adversarial_test.go` flips the forgery-padding
exploit test from "ACCEPTED" → "REJECTED" and adds a positive case asserting
a real `padding < 1000` signature still verifies.

## Files changed

Codegen (one-line cross-tier comment + 5-opcode insertion):

- `packages/runar-compiler/src/passes/rabin-codegen.ts`
- `compilers/go/codegen/rabin.go`
- `compilers/rust/src/codegen/rabin.rs`
- `compilers/python/runar_compiler/codegen/rabin.py`
- `compilers/zig/src/passes/helpers/rabin_emitter.zig`
- `compilers/ruby/lib/runar_compiler/codegen/rabin.rb`
- `compilers/java/src/main/java/runar/compiler/codegen/Rabin.java`

Conformance golden:

- `conformance/tests/oracle-price/expected-ir.json`
- `conformance/tests/oracle-price/expected-script.hex`

Tests:

- `compilers/go/codegen/rabin_test.go` — new byte-frozen golden (15 opcodes).
- `compilers/go/codegen/rabin_adversarial_test.go` — exploit test flipped
  to assert rejection; new positive case for small-padding accept.

Untouched (per scope discipline):

- `packages/runar-go/rabin.go` and peer signers — already produce `padding < 1000`.
- `examples/*/oracle-price/*` — contract source is unchanged; only its
  compiled artifact differs.
- `runar-verification/RunarVerification/Stack/{Rabin,Lower}.lean` — formal
  Lean spec still models the original 10-opcode body. The differential
  workflow exercises the *real* compiler hex through the Lean stack VM, so
  on-chain behavior is still cross-validated; only the Lean spec lemmas
  about `rabinBodyOps` are stale. Re-deriving them is a Phase B10 follow-up.
