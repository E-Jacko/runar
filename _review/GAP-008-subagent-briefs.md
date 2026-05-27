# GAP-008 — Sub-agent dispatch briefs

This directory's orchestrator session does NOT have an `Agent` / `TaskCreate`
tool available. The 6 per-tier sub-agents need to be dispatched from a
session that does (`subagent_type: "general-purpose"`,
`isolation: "worktree"`, `run_in_background: true`).

The orchestrator has completed everything the sub-agents need:
- `spec/script-analyzer-format.md` — normative cross-tier contract
- `conformance/analyzer/<fixture>/expected-analyzer-report.json` — 8 byte-exact goldens
- `conformance/analyzer/run.ts` — conformance driver
- `tools/analyzer-runner/ts.sh` — reference wrapper (proven 8/8 pass)

The 6 sub-agents share a near-identical brief; only the tier name and
target file layout differ.

---

## Shared brief (copy-paste into each sub-agent)

> You are porting the Bitcoin Script static analyzer to the **{TIER}** tier.
>
> **Sources of truth (read these first, then close them and don't re-open):**
> - `spec/script-analyzer-format.md` — the cross-tier contract.
> - `conformance/analyzer/<fixture>/expected-analyzer-report.json` for
>   each of the 8 fixtures: `basic-p2pkh`, `escrow`, `stateful-counter`,
>   `auction`, `covenant-vault`, `ec-demo`, `schnorr-zkp`, `if-else`.
>   These are the only oracle — your output MUST be byte-identical.
> - Input hex lives at `conformance/tests/<fixture>/expected-script.hex`
>   (shared with the main compiler conformance suite).
>
> **FORBIDDEN:** Do not read `packages/runar-testing/src/analyzer/*.ts`.
> The spec is the contract. The goldens are the oracle. Reading the TS
> reference will leak TS-isms (Infinity sentinel, JS shift quirks, etc.)
> that the spec already explicitly captures. If you find the spec
> ambiguous, ASK before reading TS source.
>
> **Per-tier file layout to create:** {LAYOUT}
>
> **Verification gate (mandatory before declaring done):**
> 1. Implement the analyzer per spec (parser → path-analyzer → stack-analyzer
>    → sig-analyzer → opcode-concerns → emit JSON per §3.5).
> 2. Drop a `tools/analyzer-runner/{TIER}.sh` wrapper that takes one
>    argument (hex-file path) and writes JSON to stdout.
> 3. From the repo root run:
>    ```
>    ./node_modules/.pnpm/node_modules/.bin/tsx conformance/analyzer/run.ts --tiers {TIER}
>    ```
>    Result MUST be `pass: 8 fail: 0`. Anything else, fix and re-run.
> 4. Also commit tier-local unit tests (small synthetic scripts that
>    exercise each finding code — at minimum `STACK_UNDERFLOW`,
>    `UNBALANCED_IF_ENDIF`, `UNCONDITIONALLY_SUCCEEDS`, `NO_SIG_CHECK`,
>    `CHECKSIG_RESULT_DROPPED`, `CODESEPARATOR_PRESENT`, `INEFFICIENT_PUSH`,
>    `INCONSISTENT_BRANCH_DEPTH`, `PATHS_TRUNCATED`, `INVALID_TERMINAL_STACK`).
>    For the `LARGE_SCRIPT` finding, construct a synthetic >500_000-byte
>    script of OP_NOPs in a unit test (do NOT add a 9th conformance
>    fixture).
> 5. Implement and unit-test `collapseRawScriptSpans` per spec §12.
>    (None of the 8 goldens exercise it.)
>
> **Commits:** Plain `git commit -m` in the worktree. No push, no PR,
> NO AI attribution (no `Co-Authored-By: Claude`, no "Generated with").
> Group commits logically (e.g. parser → stack → path → sig → concerns →
> orchestrator → wrapper → conformance).
>
> **Pitfalls** (called out in spec §14 — re-read them before coding):
> - Stable sort required. Default sorts in some languages are unstable.
> - Negative `stackDepthAtEnd` / `maxStackDepth` are normal — use signed types.
> - `PATHS_TRUNCATED` arithmetic intentionally uses JS 32-bit shift
>   semantics (`1 << (numBranches & 31)`). The spec calls this out
>   explicitly; reproduce it.
> - JSON formatting is byte-exact. Use a tier-appropriate serializer
>   that produces 2-space indent + LF + trailing newline, OR build the
>   string by hand. Map iteration order is NOT a substitute for the
>   ordered key list in §3.
> - The `LARGE_SCRIPT` `kB` formatting must match JS `(n/1024).toFixed(1)`
>   — round-half-to-even on the tenths digit.
> - Em dash (—) in messages is U+2014, not `--` or `-`.
>
> **Done = green:** `pass: 8 fail: 0` from `run.ts --tiers {TIER}`. Stop
> when that's true.

---

## Per-tier substitutions

### Go (`{TIER}=go`)

```
{LAYOUT}=
  packages/runar-go/analyzer/script_parser.go
  packages/runar-go/analyzer/stack_analyzer.go
  packages/runar-go/analyzer/path_analyzer.go
  packages/runar-go/analyzer/sig_analyzer.go
  packages/runar-go/analyzer/opcode_concerns.go
  packages/runar-go/analyzer/types.go
  packages/runar-go/analyzer/analyzer.go
  packages/runar-go/analyzer/*_test.go
  tools/analyzer-runner/go.sh  (builds and runs the wrapper)
  cmd of choice for the CLI shim that the wrapper invokes
```

Suggested CLI entry: a `go run` against a small `cmd/analyzer/main.go`
in `packages/runar-go/` that reads a hex file and prints the JSON.

### Rust (`{TIER}=rust`)

```
{LAYOUT}=
  packages/runar-rs/src/analyzer/mod.rs
  packages/runar-rs/src/analyzer/script_parser.rs
  packages/runar-rs/src/analyzer/stack_analyzer.rs
  packages/runar-rs/src/analyzer/path_analyzer.rs
  packages/runar-rs/src/analyzer/sig_analyzer.rs
  packages/runar-rs/src/analyzer/opcode_concerns.rs
  packages/runar-rs/src/analyzer/types.rs
  packages/runar-rs/tests/analyzer_*.rs
  packages/runar-rs/src/bin/runar_analyzer.rs  (or similar)
  tools/analyzer-runner/rust.sh
```

### Python (`{TIER}=python`)

```
{LAYOUT}=
  packages/runar-py/runar/analyzer/__init__.py
  packages/runar-py/runar/analyzer/script_parser.py
  packages/runar-py/runar/analyzer/stack_analyzer.py
  packages/runar-py/runar/analyzer/path_analyzer.py
  packages/runar-py/runar/analyzer/sig_analyzer.py
  packages/runar-py/runar/analyzer/opcode_concerns.py
  packages/runar-py/runar/analyzer/types.py
  packages/runar-py/runar/analyzer/__main__.py  (CLI: `python -m runar.analyzer`)
  packages/runar-py/tests/analyzer/test_*.py
  tools/analyzer-runner/python.sh
```

### Zig (`{TIER}=zig`)

```
{LAYOUT}=
  packages/runar-zig/src/analyzer_script_parser.zig
  packages/runar-zig/src/analyzer_stack.zig
  packages/runar-zig/src/analyzer_paths.zig
  packages/runar-zig/src/analyzer_sig.zig
  packages/runar-zig/src/analyzer_opcodes.zig
  packages/runar-zig/src/analyzer.zig
  packages/runar-zig/src/analyzer_cli.zig  (built as an executable)
  packages/runar-zig/src/analyzer_*_test.zig  (or test{} blocks inline)
  tools/analyzer-runner/zig.sh
```

Zig 0.16 toolchain. Use `std.sort.block` (unstable) — pair each finding
with its original-index sidecar to break ties (per spec §11.1).

### Ruby (`{TIER}=ruby`)

```
{LAYOUT}=
  packages/runar-rb/lib/runar/analyzer.rb  (entry point)
  packages/runar-rb/lib/runar/analyzer/script_parser.rb
  packages/runar-rb/lib/runar/analyzer/stack_analyzer.rb
  packages/runar-rb/lib/runar/analyzer/path_analyzer.rb
  packages/runar-rb/lib/runar/analyzer/sig_analyzer.rb
  packages/runar-rb/lib/runar/analyzer/opcode_concerns.rb
  packages/runar-rb/lib/runar/analyzer/types.rb
  packages/runar-rb/spec/analyzer/*_spec.rb
  packages/runar-rb/exe/runar_analyzer  (CLI entry)
  tools/analyzer-runner/ruby.sh
```

### Java (`{TIER}=java`)

```
{LAYOUT}=
  packages/runar-java/src/main/java/runar/lang/analyzer/ScriptParser.java
  packages/runar-java/src/main/java/runar/lang/analyzer/StackAnalyzer.java
  packages/runar-java/src/main/java/runar/lang/analyzer/PathAnalyzer.java
  packages/runar-java/src/main/java/runar/lang/analyzer/SigAnalyzer.java
  packages/runar-java/src/main/java/runar/lang/analyzer/OpcodeConcerns.java
  packages/runar-java/src/main/java/runar/lang/analyzer/Analyzer.java
  packages/runar-java/src/main/java/runar/lang/analyzer/AnalysisFinding.java  (+ types)
  packages/runar-java/src/main/java/runar/lang/analyzer/AnalyzerCli.java
  packages/runar-java/src/test/java/runar/lang/analyzer/*Test.java
  tools/analyzer-runner/java.sh  (gradle run or javac+java; gradle composite-build)
```

---

## After all 6 land

Re-run the full conformance:

```bash
./node_modules/.pnpm/node_modules/.bin/tsx conformance/analyzer/run.ts
# expect: pass 56 / fail 0 (7 tiers × 8 fixtures)
```

Then add a CI step that invokes the same command.
