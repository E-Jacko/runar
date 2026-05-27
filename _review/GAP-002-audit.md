# GAP-002 Audit — source-map plumbing state across the 7 tiers

This audit was produced before any GAP-002 changes were applied. It captures
the as-found state of the existing `SourceMap` schema, where each tier emits
it today, whether the end-to-end pipeline currently produces a non-empty
`sourceMap` artifact field, and the CLI entry point that needs the new
`--emit-source-map=<path>` flag.

## Schema (unchanged by GAP-002)

`packages/runar-ir-schema/src/artifact.ts:52-61`:

```ts
interface SourceMapping { opcodeIndex: number; sourceFile: string; line: number; column: number; }
interface SourceMap     { mappings: SourceMapping[]; }
```

`packages/runar-ir-schema/src/schemas/artifact.schema.json:163-184` declares
`SourceMap` as an object with a single required `mappings` array. Note
`column.minimum` is `0` in the JSON schema — the TS pipeline does emit
`column = 0` for the implicit `0`-column locations of generated statements,
so the canonical structural check is `column >= 0`, not `column >= 1`.

## Fixture-name verification

`ls conformance/tests/ | grep -E '^(basic-p2pkh|stateful-counter|escrow|ec-demo|if-else)$'`
returns all five — names match the brief verbatim.

## Per-tier audit

### TypeScript

- SourceMap is populated end-to-end. `packages/runar-compiler/src/passes/05-stack-lower.ts:384,428,972,982` threads `currentSourceLoc` from `AnfBinding.sourceLoc` onto every emitted `stackOp.sourceLoc`. `packages/runar-compiler/src/passes/06-emit.ts:267,290-306` accumulates the per-opcode mappings, and `packages/runar-compiler/src/artifact/assembler.ts:648-651` wires `compileResult.sourceMappings` into `RunarArtifact.sourceMap.mappings`.
- Compiled `examples/ts/p2pkh/P2PKH.runar.ts` with the TS CLI: `sourceMap.mappings` contains 4 entries with absolute `sourceFile`, line 43, column 4.
- CLI entry point for the new flag: `packages/runar-cli/src/bin.ts:30-40` (the `compile` command) and `packages/runar-cli/src/commands/compile.ts` (the `compileCommand` impl).

### Go

- Plumbing intact. `compilers/go/codegen/emit.go:142-215,247,256,264,286,518` records mappings; `compilers/go/compiler/compiler.go:347-349` attaches them to the artifact ONLY when `opts.IncludeSourceMap` is set.
- Compiled `examples/ts/p2pkh/P2PKH.runar.ts` with the Go CLI: the resulting JSON has NO `sourceMap` field because `main.go` never sets `IncludeSourceMap=true`. This is the latent gap the new flag fixes.
- CLI entry point: `compilers/go/main.go:45-53` (flag declaration block).

### Rust

- ANF→Stack→Emit plumbing exists (`compilers/rust/src/frontend/anf_lower.rs:519,600,610,667,752`; `compilers/rust/src/codegen/stack.rs:79,407,420,903`; `compilers/rust/src/codegen/emit.rs:103,132,189,465,505,526,536`), and `assemble_artifact` wraps non-empty source mappings into `Some(SourceMapData)` at `compilers/rust/src/artifact.rs:246-252`.
- BUT: `compilers/rust/src/lib.rs:348` (and the matching `:496`) explicitly clears `method.source_locs` after the peephole pass with `method.source_locs = vec![None; new_ops.len()]`. Therefore the resulting `sourceMap` is always empty in practice. Compiled `examples/ts/p2pkh/P2PKH.runar.ts` with the Rust CLI: no `sourceMap` key in the output JSON.
- This is a real bug that has to be repaired for Rust source maps to ever be non-empty — see Phase B fix.
- CLI entry point: `compilers/rust/src/main.rs:17-51`.

### Python

- Source maps work end-to-end. `compilers/python/runar_compiler/codegen/emit.py:140-237` collects mappings; `compilers/python/runar_compiler/compiler.py:580-602,665-677` wires them into the artifact and emits the canonical `sourceMap: { mappings: [...] }` JSON.
- Compiled `examples/ts/p2pkh/P2PKH.runar.ts`: 5 mappings, relative `sourceFile`, line 43, column 4.
- CLI entry point: `compilers/python/runar_compiler/__main__.py`.

### Zig

- Plumbing exists from ANF (`compilers/zig/src/passes/anf_lower.zig:251,546`) through stack (`compilers/zig/src/passes/stack_lower.zig:155,177,234,668,687`) to emit (`compilers/zig/src/codegen/emit.zig:347-359`).
- Two issues:
  1. `compilers/zig/src/passes/peephole.zig:96-108` returns a new `StackMethod` that copies `instructions` / `ops` but does NOT carry over `instruction_source_locs` — the optimized stream loses every mapping. Compiled output of `examples/ts/p2pkh/P2PKH.runar.ts` has no `sourceMap` key.
  2. `compilers/zig/src/codegen/emit.zig:678-693` writes a top-level `"sourceMap":[ ... ]` ARRAY — not `"sourceMap":{"mappings":[...]}`. Schema-divergent. Today this never bites because the array is empty (issue 1 swallows it), but the moment we fix peephole the bug becomes visible.
- CLI entry point: `compilers/zig/src/main.zig:23-58`.

### Ruby

- Source maps work end-to-end. `compilers/ruby/lib/runar_compiler/codegen/emit.rb:137-443` records mappings; `compilers/ruby/lib/runar_compiler/compiler.rb:689,714,781-790` produces the canonical `sourceMap: { mappings: [...] }` JSON.
- Compiled `examples/ts/p2pkh/P2PKH.runar.ts`: 5 mappings, relative `sourceFile`, line 43, column 4.
- CLI entry point: `compilers/ruby/lib/runar_compiler/cli.rb`.

### Java

- No SourceMap at all. There is a `runar.compiler.ir.stack.StackSourceLoc` record (`compilers/java/src/main/java/runar/compiler/ir/stack/StackSourceLoc.java`) and every stack op already carries an (always-null) `sourceLoc` field; the AST records carry `SourceLocation`; `AnfBinding(name, value, sourceLoc)` exists. BUT:
  1. `compilers/java/src/main/java/runar/compiler/passes/AnfLower.java:456,461` ALWAYS calls `new AnfBinding(name, value, null)`. The AST `SourceLocation` is never threaded.
  2. `compilers/java/src/main/java/runar/compiler/passes/StackLower.java` never reads `AnfBinding.sourceLoc` and never sets `StackSourceLoc` on emitted ops.
  3. `compilers/java/src/main/java/runar/compiler/passes/Emit.java:181-200` returns only `(scriptHex, rawScriptSpans)` — no `SourceMap` accumulator.
  4. `compilers/java/src/main/java/runar/compiler/Cli.java` does not produce a full artifact JSON either; it only supports `--emit-ir` and `--hex` today. The new `--emit-source-map` flag will be the first artifact-side surface Java exposes.
- CLI entry point: `compilers/java/src/main/java/runar/compiler/Cli.java:506-544` (the `Args.parse` switch).

## Cross-tier implications

`expected-source-map.json` files are intentionally tier-specific: each tier
compiles its own surface syntax (TS reads `.runar.ts`, Go reads `.runar.go`,
…), so the `(line, column)` numbers reflect the tier-native source file and
will not match across tiers. The structural invariants (mapping count
equals opcode count, ascending sorted `opcodeIndex`, no duplicates, in
range) hold per-tier.

## Required repairs identified during the audit

1. Rust: stop wiping `source_locs` after peephole (`compilers/rust/src/lib.rs:348,496`). Replace with an index map produced by the peephole pass so survivors keep their original locs and merged ops fall back to the first input's loc.
2. Zig peephole: thread `instruction_source_locs` through `optimize` so the optimized stream carries the locs of survivor instructions (`compilers/zig/src/passes/peephole.zig`).
3. Zig emit: change the artifact JSON writer so the `sourceMap` field is `{"mappings":[…]}`, matching the schema (`compilers/zig/src/codegen/emit.zig:678-693`).
4. Java: thread `SourceLocation` from AST statements into `AnfBinding.sourceLoc`, propagate to StackOps in `StackLower`, accumulate a `SourceMap` in `Emit`, and expose it via the new CLI flag.
5. Go: add `--emit-source-map=<path>` to `compilers/go/main.go` and set `IncludeSourceMap=true` on that path.
6. All 7 tiers: add `--emit-source-map=<path>` semantics — when present, after a successful compile, write `JSON.stringify(artifact.sourceMap)` (i.e. an object with a `mappings` array) to the given path.
