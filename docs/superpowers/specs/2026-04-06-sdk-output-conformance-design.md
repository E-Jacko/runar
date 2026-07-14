# SDK Output Conformance Tests

## Problem

The compiler conformance suite (`conformance/tests/`) verifies that all 6 compilers (TypeScript, Go, Rust, Python, Zig, Ruby) produce identical ANF IR and template script hex for the same source. But it does not test the SDK deployment path: constructor slot substitution, codeSepIndex slot adjustment, and state serialization.

These are three separate, non-trivial transformations applied at runtime by each SDK's `buildCodeScript()` and `getLockingScript()` methods. A bug in any one SDK (as happened with the Ruby SDK's missing `codeSepIndexSlots` substitution) produces a valid-looking but incorrect locking script that fails on-chain.

There is no cross-SDK test today that verifies all 6 SDKs produce the same deployed locking script for the same artifact + constructor args.

## Solution

Add SDK output conformance tests alongside the existing compiler conformance tests. A conformance runner invokes a small CLI tool in each language, passes it an artifact JSON + constructor args, and asserts that all 6 produce identical locking script hex.

## Architecture

```
conformance/
  sdk-output/
    runner/
      sdk-runner.ts           # Orchestrator
    tests/
      stateful-bytestring/
        input.json            # Artifact + constructor args
        expected-locking.hex  # Golden deployed locking script
      stateful-counter/
        input.json
        expected-locking.hex
      basic-p2pkh/
        input.json
        expected-locking.hex
    tools/
      ts-sdk-tool.ts          # TypeScript CLI
      go-sdk-tool.go          # Go CLI (or directory with go file)
      rs-sdk-tool/            # Rust CLI (small cargo project)
      py-sdk-tool.py          # Python CLI
      zig-sdk-tool.zig        # Zig CLI
      rb-sdk-tool.rb          # Ruby CLI
```

## Input Format

Each test case has an `input.json`:

```json
{
  "artifact": {
    "contractName": "MessageBoard",
    "abi": {
      "constructor": {
        "params": [
          { "name": "message", "type": "ByteString" },
          { "name": "owner", "type": "PubKey" }
        ]
      },
      "methods": [
        { "name": "post", "params": [{ "name": "newMessage", "type": "ByteString" }], "isPublic": true },
        { "name": "burn", "params": [{ "name": "sig", "type": "Sig" }], "isPublic": true }
      ]
    },
    "script": "76009c63...",
    "constructorSlots": [
      { "byteOffset": 310, "paramIndex": 1 }
    ],
    "codeSepIndexSlots": [
      { "byteOffset": 5, "codeSepIndex": 6 },
      { "byteOffset": 150, "codeSepIndex": 256 }
    ],
    "codeSeparatorIndex": 256,
    "codeSeparatorIndices": [6, 256],
    "stateFields": [
      { "name": "message", "type": "ByteString", "index": 0 }
    ]
  },
  "constructorArgs": [
    { "type": "ByteString", "value": "48656c6c6f" },
    { "type": "PubKey", "value": "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798" }
  ]
}
```

Constructor args are typed objects so each SDK tool can construct the correct native value before passing it to `RunarContract`.

## SDK Tools

Each tool is a minimal CLI (~50-100 lines) that:

1. Reads `input.json` path from argv[1]
2. Parses the artifact into the SDK's native `RunarArtifact` type
3. Converts typed constructor args into the SDK's native value types
4. Constructs `RunarContract(artifact, args)`
5. Prints `getLockingScript()` hex to stdout (no trailing newline beyond what's natural)

No network access, signing, or UTXO lookup. Pure substitution + serialization.

### TypeScript tool

```
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts input.json
```

Imports `RunarContract` from `runar-sdk`. Parses `input.json`, converts args using type field (bigint values from string, ByteString/PubKey as hex strings), instantiates contract, prints locking script.

### Go tool

```
go run conformance/sdk-output/tools/go-sdk-tool.go input.json
```

Imports `runar` package. Parses JSON, converts args to `interface{}` values (`*big.Int` for bigint, `string` for hex types, `bool` for bool), calls `NewRunarContract`, prints `GetLockingScript()`.

### Rust tool

```
cargo run --manifest-path conformance/sdk-output/tools/rs-sdk-tool/Cargo.toml -- input.json
```

Depends on `runar` crate. Parses JSON with serde, converts to `SdkValue` variants, calls `RunarContract::new`, prints `get_locking_script()`.

### Python tool

```
python3 conformance/sdk-output/tools/py-sdk-tool.py input.json
```

Imports from `runar.sdk`. Parses JSON, converts args (int for bigint, str for hex types), instantiates `RunarContract`, prints `get_locking_script()`.

### Zig tool

```
conformance/sdk-output/tools/zig-out/bin/zig-sdk-tool input.json
```

Or built via `zig build` in the tools directory. Imports `runar-zig` package. Parses JSON, populates `RunarArtifact` struct, calls `RunarContract.init`, prints `getLockingScript()`.

### Ruby tool

```
ruby conformance/sdk-output/tools/rb-sdk-tool.rb input.json
```

Requires `runar` gem/lib. Parses JSON, converts args, instantiates `RunarContract`, prints `get_locking_script`.

## Runner

`conformance/sdk-output/runner/sdk-runner.ts` follows the same pattern as the existing compiler conformance runner:

1. Discovers test directories under `conformance/sdk-output/tests/`
2. For each test, reads `input.json`
3. Invokes each SDK tool via `execSync`, passing the input.json path
4. Collects stdout (locking script hex) from each tool
5. Normalizes hex (lowercase, trim whitespace)
6. Compares all 6 outputs pairwise
7. Compares against `expected-locking.hex` golden file
8. Reports results (console/json/markdown, same options as compiler runner)

CLI interface:

```
npx tsx conformance/sdk-output/runner/sdk-runner.ts [options]
  --tests-dir <path>     Test directory (default: conformance/sdk-output/tests)
  --filter <pattern>     Filter test names
  --format <fmt>         Output format: console | json | markdown
  --output <file>        Write report to file
  --update-golden        Update expected-locking.hex from TS SDK output
```

Timeout: 30 seconds per tool invocation (consistent with compiler runner).

## Test Cases

### 1. stateful-bytestring (MessageBoard)

Exercises all three substitution paths:
- **Constructor slots**: PubKey `owner` arg baked into code script (33-byte push data replacing 1-byte OP_0)
- **CodeSepIndex slots**: Two slots adjusted for the 32-byte expansion from the PubKey substitution
- **State serialization**: ByteString `message` field after OP_RETURN

This is the pattern that exposed the Ruby SDK `codeSepIndexSlots` bug.

Input artifact: compiled from `conformance/tests/stateful-bytestring/stateful-bytestring.runar.ts` using the TS compiler. Constructor args: a short ByteString message + a known PubKey.

### 2. stateful-counter

Exercises state serialization with bigint (no constructor-only args, no codeSepIndex slots):
- **Constructor slots**: None — the only constructor param (`count`) is a state field, not baked into code
- **CodeSepIndex slots**: None — codeSep indices are hardcoded since no constructor args shift byte offsets
- **State serialization**: bigint `count` field (8-byte LE sign-magnitude)

Input artifact: compiled from `conformance/tests/stateful-counter/stateful-counter.runar.ts`.

### 3. stateless-p2pkh

Exercises constructor slot substitution only, no state, no codeSep:
- **Constructor slots**: `pubKeyHash` (Addr/Ripemd160, 20-byte hex)
- **No state fields**: stateless contract
- **No codeSepIndex slots**: no OP_CODESEPARATOR

Baseline test to verify the simplest substitution path works across all SDKs.

Input artifact: compiled from `conformance/tests/basic-p2pkh/basic-p2pkh.runar.ts`.

## Generating input.json Files

A one-time generation script or manual process:

1. Compile the source with the TS compiler: `npx tsx packages/runar-cli/src/bin.ts compile <source> -o /tmp/artifact`
2. Read the resulting artifact JSON
3. Choose constructor arg values (known test vectors)
4. Assemble `input.json` with artifact + typed constructor args
5. Run the TS SDK tool to produce the initial `expected-locking.hex`

This can be wrapped in a helper script at `conformance/sdk-output/generate-inputs.ts` for convenience.

## CI Integration

Add to `package.json`:

```json
{
  "conformance:sdk": "npx tsx conformance/sdk-output/runner/sdk-runner.ts",
  "conformance:all": "pnpm run conformance:ts && pnpm run conformance:sdk && ..."
}
```

The SDK conformance tests run after the compiler conformance tests in CI. They depend on pre-built SDK tool binaries (Go, Rust, Zig) or fall back to `go run` / `cargo run` / `zig build-exe`.

## Future Extensions

- Add test cases for contracts with property initializers (default values)
- Add test cases with large constructor args that trigger OP_PUSHDATA2/4 encoding
- Add test cases with negative bigint state values (sign-magnitude encoding edge case)
- Test `getSubscriptForSigning()` output across SDKs (the signing subscript after codeSep trimming)
