# Per-fixture spend witnesses (TS-GAP-004)

Each `<fixture>.json` declares concrete spend attempts for the differential
execution oracle (`packages/runar-testing/src/oracle/differential-execution.ts`).
The oracle compiles the fixture to its **fold-ON deployed bytes**, runs the
declared spend through the ANF interpreter (source semantics) *and* through the
`@bsv/sdk`-backed `ScriptVM` (script semantics), and asserts both engines agree
on accept/reject — catching a bug all seven compilers share (byte-identical but
wrong). Every non-crypto conformance fixture SHOULD have one.

Schema:

    {
      "fixture": "arithmetic",
      "constructorArgs": { "target": "27n" },
      "spends": [
        { "method": "verify", "args": ["3n", "7n"], "expect": "accept",
          "note": "10 + (-4) + 21 + 0 = 27" },
        { "method": "verify", "args": ["3n", "6n"], "expect": "reject",
          "note": "near-miss: result 24 != target 27" }
      ]
    }

- `fixture` — the directory name under `conformance/tests/`. The `.runar.ts`
  source is resolved from that fixture's `source.json` (`sources[".runar.ts"]`).
- `args` and `constructorArgs` use the trailing-`n` convention for bigints
  (`"27n"`, `"-4n"`), `true`/`false` for booleans, and `"0x…"` for byte strings.
- `method` — a `public` method of the contract (a spending entry point). For a
  contract with more than one public method, the oracle appends the compiled
  method-selector index automatically; witness authors only list the method's
  own args.
- Each fixture SHOULD have ≥1 `accept` and ≥1 `reject` (near-miss) spend, where
  a rejecting witness exists. A few contracts have only tautological asserts
  (`x >= 0 || x < 0`) or are anyone-can-spend, so no rejecting witness exists;
  those carry accept-only spends and say so in each `note`.

## Real-crypto execution (`real-crypto/`) — post-mortem remediation #1

The plain differential oracle runs on the in-process `ScriptVM`, whose
`checkSigCallback` defaults to MOCK crypto (`() => true`) and which has NO tx
context — so it can neither verify a real signature nor a real BIP-143 sighash
preimage. Every fixture needing a signature or a tx-context preimage was
therefore routed OUT into `crypto-exempt.json` / `harness-inapplicable.json`
and got **no real execution** — the exact blind spot behind BUG-100 / #99 /
#100 / #44 (all seven tiers agreed on bytes nobody ever ran with real crypto).

`real-crypto/<fixture>.json` closes that gap. Each spec is EXECUTED by
`real-crypto-execution.test.ts` through `@bsv/sdk`'s production `Spend`
interpreter — real secp256k1, real BIP-143 sighash, real `OP_CHECKSIG` /
`OP_CHECKMULTISIG` / `OP_CODESEPARATOR` / `checkPreimage`. Two kinds:

- **`stateless-signed`** — a stateless `SmartContract`. `$sig` args are filled
  with a real DER signature over the real single-input sighash
  (`runStatelessSigned` in `runar-testing`). The accept path is additionally
  cross-checked against the ANF interpreter (source-vs-script agreement); the
  interpreter's `checkSig` does REAL ECDSA over a fixed `TEST_MESSAGE`, so it is
  fed each key's precomputed `testSig`. (`checkMultiSig` is unimplemented in the
  interpreter, so multisig fixtures set `checkInterpreter: false`.)
- **`stateful`** — a `StatefulSmartContract` driven deploy→call through the SDK
  (`RunarContract` + a real `LocalSigner`) and re-validated on `Spend`
  (`runStatefulSpend`). This exercises the real auto-injected `checkPreimage`
  on-chain state binding (BUG-100) plus any user `checkSig`.

Each fixture carries ≥1 accept and ≥1 reject/near-miss. A near-miss is a wrong
key, a wrong signer (`owner` ≠ the call signer), or a **tampered continuation
output** (`tamperOutput: true` — corrupts output 0 so the recomputed sighash no
longer matches the on-stack preimage; the exact BUG-100 property). Because the
interpreter models crypto with real-but-fixed `TEST_MESSAGE` checks it cannot
model an arbitrary tx-context rejection, so a crypto near-miss is a script-only
rejection flagged `cryptoNearMiss: true`.

Placeholders resolve against `runar-testing`'s deterministic `TEST_KEYS`:
`{"$pubkey":"alice"}`, `{"$pkh":"alice"}` (ctor + args), `{"$sig":"alice"}`
(a real signature slot). Scalars use the trailing-`n` bigint convention, bare
hex for byte payloads, `true`/`false`, and `null` for an SDK-auto-signed Sig.
`satoshis` sets a continuation output amount that must match a method's
explicit `addOutput(<sats>, …)`; `lockTime` threads `nLockTime` for
`extractLocktime` / `currentBlockHeight` introspection.

## Exemptions — every fixture is witnessed, executed, OR exempt

`completeness.test.ts` fails CI if any `conformance/tests/<fixture>` is neither
witnessed here, executed in `real-crypto/`, nor listed in one of the two
exemption files (and fails if a `real-crypto/` fixture is ALSO still listed as
exempt — a stale over-claim guard):

- **`crypto-exempt.json`** — fixtures whose spend needs a REAL cryptographic
  witness (ECDSA/Schnorr checkSig, secp256k1 / NIST-P EC, SHA-256 / BLAKE3 /
  RIPEMD / Merkle hash-preimage, Rabin, or a post-quantum SLH-DSA / WOTS+
  signature). The in-process oracle synthesises witnesses from plain args and
  cannot forge a signature or hash preimage, so these are covered by the Go
  `script_execution_test.go` real-crypto path and the per-family codegen
  goldens. Each entry names the primitive.
- **`harness-inapplicable.json`** — non-crypto fixtures the oracle cannot
  execute for a structural reason: (1) **stateful** — a `StatefulSmartContract`
  auto-injects `checkPreimage` + a state-continuation output, which need a
  tx-context BIP-143 sighash preimage witness the tx-less TS `ScriptVM` cannot
  synthesise (covered by the Go `executeScriptWithTx` tx-context path);
  (2) **go-only** — `compilers:[go]` fixtures have no TypeScript codegen;
  (3) **interpreter-unsupported** — the ANF interpreter does not model the
  raw-script (`asm`) intrinsic. Each entry states its cause and reason.
