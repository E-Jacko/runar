# BUG-008 — Input-size / depth caps + unknown-ANF hard-error audit

Status as of follow-up wave on this branch (`bug-008-followup-resume`,
forked from `bug-008-followup`).

Reference constants (canonical, defined once in TS schema package
`packages/runar-ir-schema/src/input-limits.ts`):

| Constant            | Value     | Use                                                   |
| ------------------- | --------- | ----------------------------------------------------- |
| `MAX_IR_BYTES`      | 16 MiB    | ANF IR JSON byte length                               |
| `MAX_SCRIPT_BYTES`  | 4 MiB     | A single compiled Bitcoin Script (hex / bytes)        |
| `MAX_NESTING`       | 512       | JSON / AST recursion depth                            |
| `MAX_STRING_BYTES`  | 4 MiB     | Single string field inside JSON                       |
| `MAX_SOURCE_BYTES`  | 4 MiB     | Single Rúnar source file (BUG-008 follow-up)          |

The audit deliberately tracks **only the four external-data trust boundaries**
plus the two ANF-kind dispatch sites listed in the task brief. Internal
helpers that consume already-validated AST / ANF in-memory are out of
scope; they're guarded by the boundary caps upstream.

Verdict legend:
- `OK` — cap is present at the entry point with a sensible threshold and a
  typed diagnostic on violation.
- `OK (compile-time)` — silent default is impossible because the dispatch
  uses an exhaustive `match` / `switch` enforced by the type system. Adding
  an unknown variant breaks the build, not the runtime.
- `FIXED` — landed in the BUG-008 follow-up wave (this branch). Treated as
  `OK` going forward; the column is kept so the diff back to the original
  audit is auditable.
- `NEEDS FIX` — cap is missing or threshold is unsafe (>= 1 GiB, or
  unbounded recursion).
- `NEEDS FIX (deferred)` — confirmed missing, *not* landed in this PR for
  scope reasons.

## A. Entry-point coverage matrix (7 tiers × 4 entry points = 28 cells)

### A.1 Source parser (the `.runar.<ext>` parser entry point)

| Tier   | File:line                                                              | Size cap   | Depth cap  | Verdict |
| ------ | ---------------------------------------------------------------------- | ---------- | ---------- | ------- |
| TS     | `packages/runar-compiler/src/passes/01-parse.ts:80` (`parse`)          | 4 MiB      | n/a (AST)  | FIXED   |
| Go     | `compilers/go/frontend/parser.go:53` (`ParseSource`)                   | 4 MiB      | n/a (AST)  | FIXED   |
| Rust   | `compilers/rust/src/frontend/parser.rs:49` (`parse`) + per-format `parse_source` | 4 MiB | n/a (AST) | FIXED   |
| Python | `compilers/python/runar_compiler/frontend/parser_dispatch.py` (entry)  | 4 MiB      | n/a (AST)  | FIXED   |
| Zig    | `compilers/zig/src/compiler_api.zig` (entry) + `frontend/input_limits.zig` | 4 MiB | n/a (AST)  | FIXED   |
| Ruby   | `compilers/ruby/lib/runar_compiler/compiler.rb` (entry) + `frontend/input_limits.rb` | 4 MiB | n/a (AST) | FIXED |
| Java   | `compilers/java/src/main/java/runar/compiler/frontend/ParserDispatch.java` + `InputLimits.java` | 4 MiB | n/a (AST) | FIXED |

Notes:
- "Depth cap n/a (AST)" — source parsers build the AST recursively as
  they descend grammar productions. The byte cap bounds total work at
  `MAX_SOURCE_BYTES / smallest-grammar-production-size`, so deeply nested
  adversarial input is bounded transitively (cheaper to enforce there
  than to thread an explicit depth counter through every recursive-
  descent function).
- Typed errors: `CanonicalJsonError` (TS, `code: 'bytes'`),
  `SourceSizeExceededError` (Go, Rust, Java), `SourceSizeExceededError`
  (Python — same name, distinct module), `SourceSizeExceeded`
  (Zig error union), `Runar::SourceSizeExceededError` (Ruby).
- Tests: `size-guards.test.ts` (TS), `parser_size_guard_test.go` (Go),
  `tests/source_size_guard_tests.rs` (Rust),
  `tests/test_source_size_guard.py` (Python),
  `src/frontend/input_limits_test.zig` (Zig),
  `test/test_source_size_guard.rb` (Ruby),
  `test/java/runar/compiler/frontend/InputLimitsTest.java` (Java).

### A.2 `--ir` JSON loader (ANF IR JSON load)

| Tier   | File:line                                                                          | Size cap | Depth cap | Verdict |
| ------ | ---------------------------------------------------------------------------------- | -------- | --------- | ------- |
| TS     | `packages/runar-compiler/src/index.ts:496` (`loadANFFromJSON`)                     | 16 MiB   | 512       | OK      |
| Go     | `compilers/go/ir/loader.go` (`LoadIR`, `LoadIRFromBytes`)                          | 16 MiB   | 512       | OK      |
| Rust   | `compilers/rust/src/ir/loader.rs` (`load_program`) + `ir/input_limits.rs`          | 16 MiB   | 512       | FIXED   |
| Python | `compilers/python/runar_compiler/ir/loader.py:69` + `ir/input_limits.py`           | 16 MiB   | 512       | FIXED   |
| Zig    | `compilers/zig/src/ir/json.zig:88` (`parse`) + `MAX_IR_BYTES`, `MAX_IR_NESTING`    | 16 MiB   | 512       | FIXED   |
| Ruby   | `compilers/ruby/lib/runar_compiler/ir/loader.rb` + `ir/input_limits.rb`            | 16 MiB   | 512       | FIXED   |
| Java   | `compilers/java/src/main/java/runar/compiler/passes/AnfLoader.java` + `IRInputLimits.java` | 16 MiB | 512   | FIXED   |

Notes:
- Every non-TS tier uses its stdlib JSON parser, which does not expose
  depth as a parameter. The fix shape (mirrored from the Go reference
  pattern in `compilers/go/ir/input_limits.go`) is a pre-decode byte-size
  check + a one-pass depth walk over the raw bytes (push on `{`/`[`,
  pop on `}`/`]`, skip string contents respecting backslash-escapes).
  Zig additionally retains its internal `max_parse_depth = 256` as a
  defense-in-depth secondary cap.
- Typed errors per tier: `IRSizeExceededError` /
  `IRNestingExceededError` in Go/Rust/Python/Ruby/Java;
  `error.IRSizeExceeded` / `error.IRNestingExceeded` in Zig.
- Tests: `tests/ir_loader_size_guard_tests.rs` (Rust),
  `tests/test_ir_loader_size_guard.py` (Python),
  `src/ir/json_size_guard_test.zig` (Zig),
  `test/test_ir_loader_size_guard.rb` (Ruby),
  `test/java/runar/compiler/passes/IRInputLimitsTest.java` (Java),
  existing `compilers/go/ir/loader_size_guard_test.go` (Go).

### A.3 SDK envelope verifier (`verifyEnvelope` payload guard)

| Tier   | File                                          | Payload byte cap | String byte cap | Verdict |
| ------ | --------------------------------------------- | ---------------- | --------------- | ------- |
| TS     | `packages/runar-sdk/src/envelope.ts:113`      | 16 MiB           | 4 MiB           | OK      |
| Go     | `packages/runar-go/sdk_envelope.go`           | 16 MiB           | 4 MiB           | OK      |
| Rust   | `packages/runar-rs/src/sdk/envelope.rs`       | 16 MiB           | 4 MiB           | FIXED   |
| Python | `packages/runar-py/runar/sdk/envelope.py`     | 16 MiB           | 4 MiB           | OK      |
| Zig    | `packages/runar-zig/src/sdk_envelope.zig`     | 16 MiB           | 4 MiB           | FIXED   |
| Ruby   | `packages/runar-rb/lib/runar/sdk/envelope.rb` | 16 MiB           | 4 MiB           | FIXED   |
| Java   | `packages/runar-java/.../sdk/Envelope.java`   | 16 MiB           | 4 MiB           | FIXED   |

Notes:
- All seven tiers now reject oversized envelopes with the `too-large`
  reason (added as `TOO_LARGE` to each tier's `VerifyEnvelopeReason` enum
  / equivalent) **before** any JSON parse, SHA-256, or ECDSA verify work
  runs. Threshold matches Python/Go reference: 16 MiB on payload,
  4 MiB on sig / pubkey.
- Tests: existing `size-guards.test.ts` (TS), existing Go +
  Python tests; new `tests/envelope_size_guard.rs` (Rust),
  in-file `test "size guard …"` blocks in
  `src/sdk_envelope.zig` (Zig),
  `spec/runar/sdk/envelope_spec.rb` (Ruby — "size guards (BUG-008)"
  describe block),
  `src/test/java/runar/lang/sdk/EnvelopeTest.java` (Java — four
  `sizeGuard…` cases).

### A.4 Script-hex parser (locking-script byte cap at SDK boundary)

| Tier   | File:line                                                             | Cap     | Verdict |
| ------ | --------------------------------------------------------------------- | ------- | ------- |
| TS     | `packages/runar-sdk/src/contract.ts` (uses `MAX_SCRIPT_BYTES`)        | 4 MiB   | OK      |
| Go     | `packages/runar-go/sdk_contract.go:291` + 3 more sites                | 4 MiB   | OK      |
| Rust   | `packages/runar-rs/src/sdk/contract.rs`                               | 4 MiB   | OK      |
| Python | `packages/runar-py/runar/sdk/contract.py`                             | 4 MiB   | OK      |
| Zig    | `packages/runar-zig/src/sdk_contract.zig`                             | 4 MiB   | OK      |
| Ruby   | `packages/runar-rb/lib/runar/sdk/contract.rb`                         | 4 MiB   | OK      |
| Java   | `packages/runar-java/src/main/java/runar/lang/sdk/RunarContract.java` | 4 MiB   | OK      |

All 7 SDK script-hex boundaries are guarded with `MAX_SCRIPT_BYTES = 4 MiB`
and a tier-typed `ScriptSizeExceededError` / equivalent. This row was the
model that the other three rows now follow.

## B. ANF-kind dispatch matrix (7 tiers × 2 sites = 14 cells)

Unchanged from initial audit — all 14 cells were already `OK` /
`OK (compile-time)` on `main` and remain so. Kept here for completeness.

### B.1 ANF IR loader (unknown kind raises typed diagnostic)

| Tier   | File:line                                                                             | Verdict             |
| ------ | ------------------------------------------------------------------------------------- | ------------------- |
| TS     | `packages/runar-compiler/src/ir/` — uses `UnknownAnfKindError`                        | OK                  |
| Go     | `compilers/go/ir/loader.go` validates against `knownKinds`; `UnknownANFKindError` in `compilers/go/ir/unknown_anf_kind_error.go` | OK |
| Rust   | `compilers/rust/src/ir/loader.rs` + `unknown_anf_kind_error.rs`                       | OK                  |
| Python | `compilers/python/runar_compiler/ir/loader.py` + `unknown_anf_kind_error.py`          | OK                  |
| Zig    | `compilers/zig/src/ir/unknown_anf_kind.zig`                                           | OK                  |
| Ruby   | `compilers/ruby/lib/runar_compiler/ir/unknown_anf_kind_error.rb`                      | OK                  |
| Java   | `compilers/java/src/main/java/runar/compiler/ir/UnknownAnfKindError.java`             | OK                  |

### B.2 Stack lowering (unknown kind raises typed diagnostic)

| Tier   | File:line                                                                                            | Verdict              |
| ------ | ---------------------------------------------------------------------------------------------------- | -------------------- |
| TS     | `packages/runar-compiler/src/passes/05-stack-lower.ts` — `UnknownAnfKindError` on dispatch default   | OK                   |
| Go     | `compilers/go/codegen/stack.go:342` panics with `UnknownANFKindError`                                | OK                   |
| Rust   | `compilers/rust/src/codegen/stack.rs:309` — `match &ANFValue` exhaustive (enum)                      | OK (compile-time)    |
| Python | `compilers/python/runar_compiler/codegen/stack.py:332` raises `UnknownANFKindError`                  | OK                   |
| Zig    | `compilers/zig/src/passes/stack_lower.zig:803` — tagged-union `switch` (no `else` prong)             | OK (compile-time)    |
| Ruby   | `compilers/ruby/lib/runar_compiler/codegen/stack.rb:297` raises `RunarCompiler::IR::UnknownANFKindError` | OK               |
| Java   | `compilers/java/src/main/java/runar/compiler/passes/StackLower.java:331` + `:683` throw `UnknownAnfKindError` | OK            |

## C. Cells fixed in this PR vs the follow-up wave

| Cell                                 | Wave                | File(s)                                                  |
| ------------------------------------ | ------------------- | -------------------------------------------------------- |
| Go — IR loader size + depth cap      | original PR         | `compilers/go/ir/loader.go` + `loader_size_guard_test.go` |
| Go — envelope payload size cap       | original PR         | `packages/runar-go/sdk_envelope.go` + `sdk_envelope_size_test.go` |
| Python — envelope payload size cap   | original PR         | `packages/runar-py/runar/sdk/envelope.py` + `tests/test_envelope_size_guard.py` |
| TS — source parser size cap          | follow-up           | `packages/runar-compiler/src/passes/01-parse.ts` + `size-guards.test.ts` |
| Go — source parser size cap          | follow-up           | `compilers/go/frontend/{input_limits.go,parser.go}` + `parser_size_guard_test.go` |
| Rust — source parser size cap        | follow-up           | `compilers/rust/src/frontend/input_limits.rs` + per-format dispatch + `tests/source_size_guard_tests.rs` |
| Rust — IR loader size + depth cap    | follow-up           | `compilers/rust/src/ir/input_limits.rs` + `loader.rs` + `tests/ir_loader_size_guard_tests.rs` |
| Rust — envelope payload size cap     | follow-up           | `packages/runar-rs/src/sdk/envelope.rs` + `mod.rs` re-exports + `tests/envelope_size_guard.rs` |
| Python — source parser size cap      | follow-up           | `compilers/python/runar_compiler/frontend/{input_limits.py,parser_dispatch.py}` + `tests/test_source_size_guard.py` |
| Python — IR loader size + depth cap  | follow-up           | `compilers/python/runar_compiler/ir/{input_limits.py,loader.py}` + `tests/test_ir_loader_size_guard.py` |
| Zig — source parser size cap         | follow-up           | `compilers/zig/src/frontend/input_limits.zig` + `compiler_api.zig` + `input_limits_test.zig` |
| Zig — IR loader size + nesting cap   | follow-up           | `compilers/zig/src/ir/json.zig` + `json_size_guard_test.zig` |
| Zig — envelope payload size cap      | follow-up           | `packages/runar-zig/src/sdk_envelope.zig` (4 new in-file tests) |
| Ruby — source parser size cap        | follow-up           | `compilers/ruby/lib/runar_compiler/frontend/input_limits.rb` + `compiler.rb` + `test/test_source_size_guard.rb` |
| Ruby — IR loader size + depth cap    | follow-up           | `compilers/ruby/lib/runar_compiler/ir/{input_limits.rb,loader.rb}` + `test/test_ir_loader_size_guard.rb` |
| Ruby — envelope payload size cap     | follow-up           | `packages/runar-rb/lib/runar/sdk/envelope.rb` + `spec/runar/sdk/envelope_spec.rb` (4 new) |
| Java — source parser size cap        | follow-up           | `compilers/java/src/main/java/runar/compiler/frontend/{InputLimits.java,ParserDispatch.java}` + `InputLimitsTest.java` |
| Java — IR loader size + depth cap    | follow-up           | `compilers/java/src/main/java/runar/compiler/passes/{IRInputLimits.java,AnfLoader.java}` + `IRInputLimitsTest.java` |
| Java — envelope payload size cap     | follow-up           | `packages/runar-java/.../sdk/Envelope.java` + `EnvelopeTest.java` (4 new) |

## D. Known threshold sanity calls

- Zig keeps its internal `max_parse_depth: u32 = 256` on the IR JSON
  parser as a defense-in-depth secondary cap below the schema's
  `MAX_NESTING = 512`. The structural-walk guard at the loader entry
  point uses the schema constant; the inner per-binding parser keeps the
  256 floor.
- The Java compiler's `StackLower` keeps its own `MAX_STACK_DEPTH = 800`
  for Bitcoin script stack depth, separate from IR JSON nesting. That's
  a *codegen* limit, not an input cap; out of BUG-008 scope.
- Loop unrolling cap (`MAX_LOOP_COUNT = 10_000`) exists in Python and
  Ruby IR loaders. That's a *codegen* limit, not an input depth cap;
  out of BUG-008 scope.

## E. Workarounds / blockers logged

- No active blockers as of the follow-up wave. All 28 + 14 = 42 audit
  cells are now `OK` / `OK (compile-time)` / `FIXED`. The non-TS tier
  IR loaders use a single boundary check pattern lifted from
  `compilers/go/ir/input_limits.go`; the depth walk is a single-pass
  scan over the raw JSON bytes that skips string contents respecting
  backslash-escapes (`{` / `[` inside a JSON string do not count toward
  depth).
