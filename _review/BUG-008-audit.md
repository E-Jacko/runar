# BUG-008 — Input-size / depth caps + unknown-ANF hard-error audit

Status as of audit run on this worktree (branch `bug-008-input-caps`).

Reference constants (canonical, defined once in TS schema package
`packages/runar-ir-schema/src/input-limits.ts`):

| Constant            | Value     | Use                                                   |
| ------------------- | --------- | ----------------------------------------------------- |
| `MAX_IR_BYTES`      | 16 MiB    | ANF IR JSON byte length                               |
| `MAX_SCRIPT_BYTES`  | 4 MiB     | A single compiled Bitcoin Script (hex / bytes)        |
| `MAX_NESTING`       | 512       | JSON / AST recursion depth                            |
| `MAX_STRING_BYTES`  | 4 MiB     | Single string field inside JSON                       |

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
- `NEEDS FIX` — cap is missing or threshold is unsafe (>= 1 GiB, or
  unbounded recursion).
- `NEEDS FIX (deferred)` — confirmed missing, *not* landed in this PR for
  scope reasons. Documented here so the next agent can land surgically.

## A. Entry-point coverage matrix (7 tiers × 4 entry points = 28 cells)

### A.1 Source parser (the `.runar.<ext>` parser entry point)

| Tier   | File:line                                                              | Size cap   | Depth cap  | Verdict             |
| ------ | ---------------------------------------------------------------------- | ---------- | ---------- | ------------------- |
| TS     | `packages/runar-compiler/src/passes/01-parse.ts` (no entry guard)      | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Go     | `compilers/go/frontend/parser_ts.go` etc. (no entry guard)             | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Rust   | `compilers/rust/src/frontend/parser.rs` (no entry guard)               | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Python | `compilers/python/runar_compiler/frontend/parse.py` (no entry guard)   | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Zig    | `compilers/zig/src/frontend/parser*.zig` (no entry guard)              | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Ruby   | `compilers/ruby/lib/runar_compiler/frontend/parse.rb` (no entry guard) | absent     | n/a (AST)  | NEEDS FIX (deferred)|
| Java   | `compilers/java/src/main/java/runar/compiler/frontend/JavaParser.java` | absent     | n/a (AST)  | NEEDS FIX (deferred)|

Notes:
- The CLI front door (`packages/runar-cli/src/commands/compile.ts`)
  reads source via `fs.readFileSync` with **no `MAX_IR_BYTES` /
  `MAX_SCRIPT_BYTES` style cap** before handing the buffer to the
  compiler. Same shape in every per-tier CLI.
- "Depth cap n/a (AST)" — source parsers build the AST recursively as
  they descend grammar productions. The depth bound that prevents stack
  exhaustion has to live in each parser's recursive-descent functions,
  not as a single entry-point check. Today none of the 7 tiers enforce
  one. Recommended threshold: `MAX_NESTING = 512` matching the schema
  constant.

Recommended fix (deferred to follow-up PR):
- Add `InputLimits.MAX_SOURCE_BYTES = 4 MiB` to
  `packages/runar-ir-schema/src/input-limits.ts` and mirror to all six
  non-TS tier `input_limits` / `InputLimits` / `sdk_errors.*` modules.
- Wire `compileSource()` / `compile()` entry points in all 7 compilers to
  reject `source.length > MAX_SOURCE_BYTES` with a typed
  `SourceSizeExceededError` before lexing.

### A.2 `--ir` JSON loader (ANF IR JSON load)

| Tier   | File:line                                                                          | Size cap | Depth cap | Verdict   |
| ------ | ---------------------------------------------------------------------------------- | -------- | --------- | --------- |
| TS     | `packages/runar-compiler/src/index.ts:496` (`loadANFFromJSON`)                     | 16 MiB   | 512       | OK        |
| Go     | `compilers/go/ir/loader.go:11` (`LoadIR`), `:36` (`LoadIRFromBytes`)               | **absent** | **absent** | NEEDS FIX (landed in B.1) |
| Rust   | `compilers/rust/src/ir/loader.rs` (`load_program`)                                 | absent   | absent    | NEEDS FIX (deferred) |
| Python | `compilers/python/runar_compiler/ir/loader.py:69` (`load_ir`)                      | absent   | absent    | NEEDS FIX (deferred) |
| Zig    | `compilers/zig/src/ir/json.zig:21` (`max_parse_depth = 256`)                       | absent   | **256**   | PARTIAL — depth ok, size NEEDS FIX (deferred) |
| Ruby   | `compilers/ruby/lib/runar_compiler/ir/loader.rb`                                   | absent   | absent    | NEEDS FIX (deferred) |
| Java   | `compilers/java/src/main/java/runar/compiler/passes/AnfLoader.java`                | absent   | absent    | NEEDS FIX (deferred) |

Notes:
- The TS guard lives at the boundary of the compiler package, not at
  every internal call site — that's the right shape (one boundary check,
  not many). The other six tiers need the same shape.
- Zig has a `max_parse_depth: u32 = 256` constant on its IR JSON parser
  (`compilers/zig/src/ir/json.zig:21`) — half the schema's
  `MAX_NESTING = 512`. Tightening Zig **up** to 512 is wrong (depth
  should be `<=` schema constant, not equal); leaving at 256 is fine
  defensively. Flagged for cross-tier review, not changed.

### A.3 SDK envelope verifier (`verifyEnvelope` payload guard)

| Tier   | File                                          | Payload byte cap | String byte cap | Verdict             |
| ------ | --------------------------------------------- | ---------------- | --------------- | ------------------- |
| TS     | `packages/runar-sdk/src/envelope.ts:113`      | 16 MiB           | 4 MiB           | OK                  |
| Go     | `packages/runar-go/sdk_envelope.go`           | absent           | absent          | NEEDS FIX (landed in B.2) |
| Rust   | `packages/runar-rs/src/sdk/envelope.rs`       | absent           | absent          | NEEDS FIX (deferred) |
| Python | `packages/runar-py/runar/sdk/envelope.py`     | absent           | absent          | NEEDS FIX (landed in B.3) |
| Zig    | `packages/runar-zig/src/sdk_envelope.zig`     | absent           | absent          | NEEDS FIX (deferred) |
| Ruby   | `packages/runar-rb/lib/runar/sdk/envelope.rb` | absent           | absent          | NEEDS FIX (deferred) |
| Java   | `packages/runar-java/.../sdk/Envelope.java`   | absent           | absent          | NEEDS FIX (deferred) |

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
and a tier-typed `ScriptSizeExceededError` / equivalent. This row is the
most-mature surface and is the model the other rows should follow.

## B. ANF-kind dispatch matrix (7 tiers × 2 sites = 14 cells)

### B.1 ANF IR loader (unknown kind raises typed diagnostic)

| Tier   | File:line                                                                             | Verdict             |
| ------ | ------------------------------------------------------------------------------------- | ------------------- |
| TS     | `packages/runar-compiler/src/ir/` — uses `UnknownAnfKindError` (size-guards test passes) | OK               |
| Go     | `compilers/go/ir/loader.go` validates against `knownKinds` set; `UnknownANFKindError` ships in `compilers/go/ir/unknown_anf_kind_error.go` (tested by `compilers/go/ir/unknown_anf_kind_test.go`) | OK |
| Rust   | `compilers/rust/src/ir/loader.rs` + `unknown_anf_kind_error.rs` (tested by `tests/unknown_anf_kind_tests.rs`)  | OK |
| Python | `compilers/python/runar_compiler/ir/loader.py` + `unknown_anf_kind_error.py` (tested by `tests/test_unknown_anf_kind.py`) | OK |
| Zig    | `compilers/zig/src/ir/unknown_anf_kind.zig` (tested by `unknown_anf_kind_test.zig`)   | OK                  |
| Ruby   | `compilers/ruby/lib/runar_compiler/ir/unknown_anf_kind_error.rb` (tested by `test/test_unknown_anf_kind.rb`) | OK |
| Java   | `compilers/java/src/main/java/runar/compiler/ir/UnknownAnfKindError.java` (tested by `compilers/java/.../passes/UnknownAnfKindTest.java`) | OK |

### B.2 Stack lowering (unknown kind raises typed diagnostic)

| Tier   | File:line                                                                                            | Verdict              |
| ------ | ---------------------------------------------------------------------------------------------------- | -------------------- |
| TS     | `packages/runar-compiler/src/passes/05-stack-lower.ts` — `UnknownAnfKindError` on dispatch default   | OK                   |
| Go     | `compilers/go/codegen/stack.go:342` panics with `UnknownANFKindError` on default of `collectRefs`    | OK                   |
| Rust   | `compilers/rust/src/codegen/stack.rs:309` — `match &ANFValue` exhaustive (enum)                      | OK (compile-time)    |
| Python | `compilers/python/runar_compiler/codegen/stack.py:332` raises `UnknownANFKindError`                  | OK                   |
| Zig    | `compilers/zig/src/passes/stack_lower.zig:803` — tagged-union `switch` (no `else` prong)             | OK (compile-time)    |
| Ruby   | `compilers/ruby/lib/runar_compiler/codegen/stack.rb:297` raises `RunarCompiler::IR::UnknownANFKindError` | OK               |
| Java   | `compilers/java/src/main/java/runar/compiler/passes/StackLower.java:331` + `:683` throw `UnknownAnfKindError` | OK            |

## C. Cells fixed in this PR

The audit found 4 distinct gap patterns. Surgical fixes landed for the
highest-leverage subset; remaining cells documented as `NEEDS FIX
(deferred)` for follow-up. Rationale: 7-tier cross-cutting hardening at
quality bar is multi-PR work; landing a quarter of the cells correctly
beats landing all of them sloppily.

| Cell                              | Action     | File                                                     |
| --------------------------------- | ---------- | -------------------------------------------------------- |
| Go — IR loader size + depth cap   | LANDED     | `compilers/go/ir/loader.go` + `loader_size_guard_test.go` |
| Go — envelope payload size cap    | LANDED     | `packages/runar-go/sdk_envelope.go` + `sdk_envelope_size_test.go` |
| Python — envelope payload size cap| LANDED     | `packages/runar-py/runar/sdk/envelope.py` + `tests/test_envelope_size_guard.py` |
| All other cells in A.1–A.3        | DEFERRED   | tracked in this doc; next agent should land per-tier with the same shape (typed error type, sensible threshold, one entry-point check) |

## D. Known threshold sanity calls

- The Zig IR JSON parser caps recursion at 256 vs schema's 512. Defensive
  — kept. If a legitimate fixture trips the 256 cap, raise to 512 and
  add a regression fixture.
- The Java compiler's `StackLower` keeps its own `MAX_STACK_DEPTH = 800`
  for Bitcoin script stack depth, separate from IR JSON nesting. That's
  a *codegen* limit, not an input cap; out of BUG-008 scope.
- Loop unrolling cap (`MAX_LOOP_COUNT = 10_000`) exists in Python and
  Ruby IR loaders. That's a *codegen* limit, not an input depth cap;
  out of BUG-008 scope.

## E. Workarounds / blockers logged

None encountered during this audit. The non-TS tier IR loaders all use
their tier's stdlib JSON parser which does not expose depth as a
parameter; the fix shape is a pre-`json.Unmarshal`/`json.loads` byte
size check + a one-pass depth walk after parse (same shape as TS
`assertNestingDepth`). The Go fix in B.1 demonstrates this pattern; the
other six tiers should follow it verbatim.
