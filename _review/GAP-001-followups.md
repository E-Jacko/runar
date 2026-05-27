# GAP-001 / BUG-005 follow-ups (docs drift noticed in passing)

Surfaced while editing `docs/testing-guide.md` and `docs/getting-started.md` for the BUG-005 + GAP-001 docs-only pass. **Out of scope for that change — recording here, not fixing.**

## 1. `docs/testing-guide.md` "Cross-Language Testing Comparison" table is 4 tiers stale

Location: `docs/testing-guide.md` ⇒ "Cross-Language Testing Comparison" (immediately after "Running Rust Tests").

The table has columns for **TypeScript, Go, Rust** only. Python, Zig, Ruby, and Java have all shipped equivalent native-test workflows since (see CLAUDE.md "Build & Test" — `examples/python`, `examples/zig` via `packages/runar-zig`, `examples/java` via JUnit 5; Ruby native examples exist under `examples/end2end-example/ruby` and elsewhere). The table should grow four columns or be restructured to a per-tier list.

Specifically missing rows that exist in the underlying code:
- Python: `pytest`, `load_contract` conftest helper, `compile_check` via `runar.compile_check`, snake_case ↔ camelCase parser conversion.
- Zig: `zig build test`, `packages/runar-zig` mock helpers, `CompileCheck` via the Zig package.
- Ruby: `rake test` for compiler + native `runar` gem with mock crypto.
- Java: JUnit 5 (`gradle test`), `runar.lang.sdk.CompileCheck`, `runar.lang.runtime.ContractSimulator` (Java-only off-chain real-hash + real-secp256k1 + mock-sig harness).

## 2. `docs/testing-guide.md` "Conformance Testing Across Compilers" missing Ruby + Java

Location: `docs/testing-guide.md` ⇒ "Running Conformance Tests" code block.

The block lists conformance commands for TS / Go / Rust / Python / Zig but omits Ruby and Java. Per CLAUDE.md, both ship full compiler trees (`compilers/ruby`, `compilers/java`) and both are conformance targets (subject to the per-fixture `compilers` allowlist + the Go-only proof-system primitives carve-out). Should add:

```bash
# Test the Ruby compiler
cd compilers/ruby && rake conformance   # (verify exact task name in compilers/ruby/Rakefile)

# Test the Java compiler
cd compilers/java && gradle conformance # (verify exact task name in compilers/java/build.gradle)
```

Confirm task names before committing the doc change — the Rake / Gradle targets may be named differently from `conformance`.

## 3. `docs/testing-guide.md` "Post-Quantum Signature Testing" tier list is 2 tiers stale

Location: `docs/testing-guide.md` ⇒ "Conformance Golden Files" (under "Post-Quantum Signature Testing").

Current text:
> The maintained compilers with post-quantum support (TS, Go, Rust, Python, Zig) target byte-identical output.

Per CLAUDE.md ⇒ "Style" section: SLH-DSA and WOTS+ codegen modules ship in **all 7 tiers** (`SlhDsa.java`, `Wots.java` are explicitly called out for Java). Ruby is also listed. The doc should say "all 7 maintained compilers" or list them all.

## 4. `docs/testing-guide.md` "Basic Test Structure" header is TypeScript-specific but appears at top level

Cosmetic. Currently reads as if it's the canonical structure for all tiers; the section heading is just "TypeScript Unit Testing with Vitest" which is fine, but the "Native Example Test Runners" subsection (line ~44) is grafted in at H2 depth and breaks the visual hierarchy. Probably wants to be a sibling H2 ("Native-Language Unit Testing") with per-tier subsections — same content as the table fix in (1).

## 5. `docs/getting-started.md` Prerequisites table missing Java

Location: `docs/getting-started.md` ⇒ "Prerequisites" table.

Lists Node / pnpm / Go / Rust / Python / Zig / Ruby. Java is absent. Per CLAUDE.md, Java 17 + Gradle 8.5+ are the toolchain requirements for the Java compiler, SDK, and example tests. Add a row:

| **Java** | 17+ | Only needed if you want to build/use the Java compiler |
| **Gradle** | 8.5+ | Only needed if you want to build/use the Java compiler (no wrapper committed) |

---

Pick these up as a separate "docs drift across the 7-tier expansion" sweep; they're all independently small but they're a coherent set and should ship together rather than dribbling in one column at a time.
