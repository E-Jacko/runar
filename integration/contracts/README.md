# Integration test contracts (NOT examples)

**TEST-ONLY.** Contracts in this tree exist solely to exercise language
features, builtins, and fund-safety constructs on a real BSV regtest node.
They are not tutorials and must not live under `examples/`.

## Layout

```
integration/contracts/
  coverage-matrix.json   # feature → contract → tier test path
  check-matrix.mjs       # CI checker: files exist for every matrix row
  constructs/            # control-flow / state-shape regressions
  crypto/                # signatures, EC, preimage extractors
  outputs/               # addRawOutput / multi-output layouts
  language/              # operators, loops, booleans (later phases)
  unsafe/                # asm / UnsafeSmartContract (later phases)
  intents/               # intent sugar (later phases)
```

## Rules

1. Header every source with `// TEST-ONLY — not a user example`.
2. Prefer **minimal, single-purpose** contracts (one family per file).
3. Canonical source is **TypeScript** (`.runar.ts`) so all 7 compilers share one path.
4. Regtest-facing data outputs use **1 satoshi**, not 0 — CI SV Node runs
   `acceptnonstdtxn=0` and rejects 0-sat dust OP_RETURN at broadcast.
5. New coverage for a matrix row must land contract + at least TS+Go tests in
   the same PR (other tiers may follow).
6. **Not production templates.** Many fixtures intentionally omit `checkSig` /
   owner auth so compiler constructs stay minimal. Anyone who knows the UTXO
   can call them. Do **not** copy these under `examples/` or deploy mainnet
   value. Production demos with auth live in `examples/`.
7. **On-chain pins.** Matrix rows with `expectedState` / `outputShape` must
   decode the broadcast tx (or re-spend) — not only SDK in-memory state.


## Loading from suites

```ts
// TypeScript
compileContract('integration/contracts/constructs/BranchMergedLocals.runar.ts')
```

```go
// Go
helpers.CompileToSDKArtifact("integration/contracts/constructs/BranchMergedLocals.runar.ts", nil)
```

Paths are relative to the repository root (same as `examples/ts/...` today).

## Coverage matrix

`coverage-matrix.json` lists every feature this tree claims to cover. Run:

```bash
node integration/contracts/check-matrix.mjs
```

Empty tier cells are allowed only with an explicit `"deferred"` reason.
