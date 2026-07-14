# SDK Output Conformance Tests — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Verify all 6 SDKs (TypeScript, Go, Rust, Python, Zig, Ruby) produce identical deployed locking scripts from the same compiled artifact + constructor args.

**Architecture:** A TypeScript-based runner discovers test cases in `conformance/sdk-output/tests/`, shells out to a small CLI tool per SDK language, collects the locking script hex from stdout, and asserts cross-SDK equality + golden file match. Each SDK tool is ~50-100 lines that parses an `input.json`, constructs a `RunarContract`, and prints `getLockingScript()`.

**Tech Stack:** TypeScript runner (Node, tsx), Go tool (runar-go SDK), Rust tool (runar-lang crate + serde_json), Python tool (runar.sdk), Zig tool (runar_zig package), Ruby tool (runar gem).

---

## File Structure

```
conformance/sdk-output/
  runner/
    sdk-runner.ts                    # Test orchestrator — discovers tests, invokes tools, compares output
  tests/
    stateful-bytestring/
      input.json                     # Artifact + typed constructor args
      expected-locking.hex           # Golden locking script hex
    stateful-counter/
      input.json
      expected-locking.hex
    basic-p2pkh/
      input.json
      expected-locking.hex
  tools/
    ts-sdk-tool.ts                   # TypeScript SDK tool
    go-sdk-tool.go                   # Go SDK tool (uses conformance go.mod)
    rs-sdk-tool/
      Cargo.toml                     # Minimal crate depending on runar-lang
      src/main.rs                    # Rust SDK tool
    py-sdk-tool.py                   # Python SDK tool
    zig-sdk-tool/
      build.zig                      # Zig build file importing runar_zig
      build.zig.zon                  # Zig package manifest
      src/main.zig                   # Zig SDK tool
    rb-sdk-tool.rb                   # Ruby SDK tool
  generate-inputs.ts                 # One-time helper: compile sources -> input.json
```

---

### Task 1: Create directory structure and generate test inputs

**Files:**
- Create: `conformance/sdk-output/generate-inputs.ts`
- Create: `conformance/sdk-output/tests/stateful-bytestring/input.json`
- Create: `conformance/sdk-output/tests/stateful-counter/input.json`
- Create: `conformance/sdk-output/tests/basic-p2pkh/input.json`

- [ ] **Step 1: Create the directory tree**

```bash
mkdir -p conformance/sdk-output/runner
mkdir -p conformance/sdk-output/tests/stateful-bytestring
mkdir -p conformance/sdk-output/tests/stateful-counter
mkdir -p conformance/sdk-output/tests/basic-p2pkh
mkdir -p conformance/sdk-output/tools/rs-sdk-tool/src
mkdir -p conformance/sdk-output/tools/zig-sdk-tool/src
```

- [ ] **Step 2: Write the input generator script**

Create `conformance/sdk-output/generate-inputs.ts`:

```typescript
import { execFileSync } from 'child_process';
import { readFileSync, writeFileSync, mkdirSync, existsSync } from 'fs';
import { join, basename } from 'path';

const ROOT = join(import.meta.dirname, '../..');
const TESTS_DIR = join(import.meta.dirname, 'tests');

interface TestSpec {
  name: string;
  source: string; // relative to ROOT
  constructorArgs: Array<{ type: string; value: string }>;
}

const TEST_SPECS: TestSpec[] = [
  {
    name: 'stateful-bytestring',
    source: 'conformance/tests/stateful-bytestring/stateful-bytestring.runar.ts',
    constructorArgs: [
      { type: 'ByteString', value: '48656c6c6f' },  // "Hello"
      { type: 'PubKey', value: '0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798' },
    ],
  },
  {
    name: 'stateful-counter',
    source: 'conformance/tests/stateful-counter/stateful-counter.runar.ts',
    constructorArgs: [
      { type: 'bigint', value: '42' },
    ],
  },
  {
    name: 'basic-p2pkh',
    source: 'conformance/tests/basic-p2pkh/basic-p2pkh.runar.ts',
    constructorArgs: [
      { type: 'Addr', value: '89abcdefabbaabbaabbaabbaabbaabbaabbaabba' },
    ],
  },
];

const TMP_DIR = join(import.meta.dirname, '.tmp');
if (!existsSync(TMP_DIR)) mkdirSync(TMP_DIR, { recursive: true });

for (const spec of TEST_SPECS) {
  const sourcePath = join(ROOT, spec.source);
  console.log(`Compiling ${spec.name}...`);
  execFileSync(
    'npx',
    ['tsx', 'packages/runar-cli/src/bin.ts', 'compile', sourcePath, '-o', TMP_DIR],
    { cwd: ROOT, stdio: 'pipe' },
  );

  const sourceBase = basename(spec.source, '.ts');
  const artifactPath = join(TMP_DIR, `${sourceBase}.json`);
  const artifact = JSON.parse(readFileSync(artifactPath, 'utf-8'));

  // Strip fields not needed by SDK tools
  delete artifact.ir;
  delete artifact.anf;
  delete artifact.asm;
  delete artifact.sourceMap;
  delete artifact.buildTimestamp;

  const input = { artifact, constructorArgs: spec.constructorArgs };
  const testDir = join(TESTS_DIR, spec.name);
  if (!existsSync(testDir)) mkdirSync(testDir, { recursive: true });
  writeFileSync(join(testDir, 'input.json'), JSON.stringify(input, null, 2) + '\n');
  console.log(`  Wrote ${spec.name}/input.json`);
}

console.log('\nDone. Run the TS SDK tool on each to generate expected-locking.hex.');
```

- [ ] **Step 3: Run the generator**

```bash
cd /path/to/runar
npx tsx conformance/sdk-output/generate-inputs.ts
```

Expected: Three `input.json` files created under `conformance/sdk-output/tests/`.

- [ ] **Step 4: Verify input.json contents**

Spot-check `conformance/sdk-output/tests/stateful-bytestring/input.json`:
- `artifact.constructorSlots` should be `[{"paramIndex": 1, "byteOffset": 310}]`
- `artifact.codeSepIndexSlots` should be `[{"byteOffset": 85, "codeSepIndex": 6}]`
- `artifact.stateFields` should be `[{"name": "message", "type": "ByteString", "index": 0}]`
- `constructorArgs` should have 2 entries (ByteString + PubKey)

Spot-check `basic-p2pkh/input.json`:
- `artifact.constructorSlots` should be `[{"paramIndex": 0, "byteOffset": 2}]`
- No `codeSepIndexSlots`, no `stateFields`

Spot-check `stateful-counter/input.json`:
- No `constructorSlots`
- `artifact.stateFields` should be `[{"name": "count", "type": "bigint", "index": 0}]`

- [ ] **Step 5: Commit**

```bash
git add conformance/sdk-output/generate-inputs.ts conformance/sdk-output/tests/
git commit -m "feat(conformance): add SDK output test inputs and generator script"
```

---

### Task 2: Write the TypeScript SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/ts-sdk-tool.ts`

This is the reference implementation. Its output will seed the golden `expected-locking.hex` files.

- [ ] **Step 1: Write the tool**

Create `conformance/sdk-output/tools/ts-sdk-tool.ts`:

```typescript
import { readFileSync } from 'fs';
import { RunarContract } from '../../../packages/runar-sdk/src/contract.js';

interface TypedArg {
  type: string;
  value: string;
}

interface Input {
  artifact: Record<string, unknown>;
  constructorArgs: TypedArg[];
}

function convertArg(arg: TypedArg): unknown {
  switch (arg.type) {
    case 'bigint':
    case 'int':
      return BigInt(arg.value);
    case 'bool':
      return arg.value === 'true';
    default:
      // ByteString, PubKey, Addr, Sig, Ripemd160, Sha256, Point — all hex strings
      return arg.value;
  }
}

const inputPath = process.argv[2];
if (!inputPath) {
  process.stderr.write('Usage: ts-sdk-tool <input.json>\n');
  process.exit(1);
}

const input: Input = JSON.parse(readFileSync(inputPath, 'utf-8'));
const args = input.constructorArgs.map(convertArg);
const contract = new RunarContract(input.artifact as any, args);
process.stdout.write(contract.getLockingScript());
```

- [ ] **Step 2: Test the tool on each input**

```bash
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/stateful-bytestring/input.json
```

Expected: A hex string printed to stdout. Verify it's non-empty and longer than the template `artifact.script` (because state is appended after OP_RETURN).

```bash
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: A hex string. The template `76a90088ac` (5 bytes) should become longer because the 1-byte OP_0 placeholder at byte 2 is replaced with a 21-byte push (14-byte Addr push data).

```bash
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/stateful-counter/input.json
```

Expected: Hex ending with `6a` + 16 hex chars (8-byte LE bigint for count=42).

- [ ] **Step 3: Generate golden files from TS output**

```bash
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/stateful-bytestring/input.json > conformance/sdk-output/tests/stateful-bytestring/expected-locking.hex
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/stateful-counter/input.json > conformance/sdk-output/tests/stateful-counter/expected-locking.hex
npx tsx conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/basic-p2pkh/input.json > conformance/sdk-output/tests/basic-p2pkh/expected-locking.hex
```

- [ ] **Step 4: Commit**

```bash
git add conformance/sdk-output/tools/ts-sdk-tool.ts conformance/sdk-output/tests/*/expected-locking.hex
git commit -m "feat(conformance): add TS SDK tool and golden locking script files"
```

---

### Task 3: Write the Go SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/go-sdk-tool.go`
- Modify: `conformance/go.mod` (add runar-go dependency)

- [ ] **Step 1: Add runar-go dependency to conformance go.mod**

```bash
cd conformance
go get github.com/icellan/runar/packages/runar-go
```

Since the workspace `go.work` already includes both `./conformance` and `./packages/runar-go`, this should resolve locally.

- [ ] **Step 2: Write the tool**

Create `conformance/sdk-output/tools/go-sdk-tool.go`:

```go
//go:build ignore

package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	runar "github.com/icellan/runar/packages/runar-go"
)

type TypedArg struct {
	Type  string `json:"type"`
	Value string `json:"value"`
}

type Input struct {
	Artifact        json.RawMessage `json:"artifact"`
	ConstructorArgs []TypedArg      `json:"constructorArgs"`
}

func convertArg(arg TypedArg) interface{} {
	switch arg.Type {
	case "bigint", "int":
		n := new(big.Int)
		n.SetString(arg.Value, 10)
		return n
	case "bool":
		return arg.Value == "true"
	default:
		// ByteString, PubKey, Addr, Sig, Ripemd160, Sha256, Point — hex strings
		return arg.Value
	}
}

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "Usage: go-sdk-tool <input.json>")
		os.Exit(1)
	}

	data, err := os.ReadFile(os.Args[1])
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading file: %v\n", err)
		os.Exit(1)
	}

	var input Input
	if err := json.Unmarshal(data, &input); err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing JSON: %v\n", err)
		os.Exit(1)
	}

	artifact, err := runar.LoadArtifactFromJSON(input.Artifact)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error loading artifact: %v\n", err)
		os.Exit(1)
	}

	args := make([]interface{}, len(input.ConstructorArgs))
	for i, a := range input.ConstructorArgs {
		args[i] = convertArg(a)
	}

	contract := runar.NewRunarContract(artifact, args)
	fmt.Print(contract.GetLockingScript())
}
```

Note: Verify that `runar.LoadArtifactFromJSON` is the actual function name. Check `packages/runar-go/sdk_types.go` for how `RunarArtifact` is loaded from JSON. It might be `runar.ParseArtifact()` or direct `json.Unmarshal` into `runar.RunarArtifact{}`. Adjust accordingly.

- [ ] **Step 3: Test the tool**

```bash
go run conformance/sdk-output/tools/go-sdk-tool.go conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: Hex output matching `conformance/sdk-output/tests/basic-p2pkh/expected-locking.hex`.

```bash
go run conformance/sdk-output/tools/go-sdk-tool.go conformance/sdk-output/tests/stateful-bytestring/input.json
```

Expected: Hex output matching `conformance/sdk-output/tests/stateful-bytestring/expected-locking.hex`.

```bash
go run conformance/sdk-output/tools/go-sdk-tool.go conformance/sdk-output/tests/stateful-counter/input.json
```

Expected: Hex output matching `conformance/sdk-output/tests/stateful-counter/expected-locking.hex`.

- [ ] **Step 4: If any output differs from golden, debug**

Compare byte-by-byte:
```bash
diff <(go run conformance/sdk-output/tools/go-sdk-tool.go conformance/sdk-output/tests/stateful-bytestring/input.json) conformance/sdk-output/tests/stateful-bytestring/expected-locking.hex
```

If there's a mismatch, it's a real SDK conformance bug — investigate the Go SDK's `buildCodeScript()` or `SerializeState()`.

- [ ] **Step 5: Commit**

```bash
git add conformance/sdk-output/tools/go-sdk-tool.go conformance/go.mod conformance/go.sum
git commit -m "feat(conformance): add Go SDK conformance tool"
```

---

### Task 4: Write the Rust SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/rs-sdk-tool/Cargo.toml`
- Create: `conformance/sdk-output/tools/rs-sdk-tool/src/main.rs`

- [ ] **Step 1: Write Cargo.toml**

Create `conformance/sdk-output/tools/rs-sdk-tool/Cargo.toml`:

```toml
[package]
name = "rs-sdk-tool"
version = "0.1.0"
edition = "2021"

[dependencies]
runar-lang = { path = "../../../../packages/runar-rs" }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
```

- [ ] **Step 2: Write main.rs**

Create `conformance/sdk-output/tools/rs-sdk-tool/src/main.rs`:

```rust
use serde::Deserialize;
use std::env;
use std::fs;

use runar_lang::sdk::{RunarContract, RunarArtifact, SdkValue};

#[derive(Deserialize)]
struct TypedArg {
    #[serde(rename = "type")]
    arg_type: String,
    value: String,
}

#[derive(Deserialize)]
struct Input {
    artifact: serde_json::Value,
    #[serde(rename = "constructorArgs")]
    constructor_args: Vec<TypedArg>,
}

fn convert_arg(arg: &TypedArg) -> SdkValue {
    match arg.arg_type.as_str() {
        "bigint" | "int" => {
            let n: i64 = arg.value.parse().expect("invalid bigint");
            SdkValue::Int(n)
        }
        "bool" => SdkValue::Bool(arg.value == "true"),
        _ => {
            // ByteString, PubKey, Addr, Sig, Ripemd160, Sha256, Point — hex strings
            SdkValue::Bytes(arg.value.clone())
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: rs-sdk-tool <input.json>");
        std::process::exit(1);
    }

    let data = fs::read_to_string(&args[1]).expect("failed to read input file");
    let input: Input = serde_json::from_str(&data).expect("failed to parse JSON");

    let artifact: RunarArtifact =
        serde_json::from_value(input.artifact).expect("failed to parse artifact");

    let sdk_args: Vec<SdkValue> = input.constructor_args.iter().map(convert_arg).collect();

    let contract = RunarContract::new(artifact, sdk_args);
    print!("{}", contract.get_locking_script());
}
```

Note: The exact import paths (`runar_lang::sdk::*`) and type names (`SdkValue::Int`, `SdkValue::Bytes`) must match what `packages/runar-rs` exports. Check `packages/runar-rs/src/sdk/mod.rs` and `packages/runar-rs/src/sdk/contract.rs` for the actual public API. Adjust imports if needed — the key types are `RunarContract`, `RunarArtifact`, and `SdkValue`.

- [ ] **Step 3: Build and test**

```bash
cd conformance/sdk-output/tools/rs-sdk-tool
cargo build --release
```

Expected: Successful compilation.

```bash
cargo run --release -- ../../../../conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: Hex output matching `expected-locking.hex`.

Test all three:
```bash
for test in basic-p2pkh stateful-bytestring stateful-counter; do
  echo "=== $test ==="
  diff <(cargo run --release -- ../../../../conformance/sdk-output/tests/$test/input.json) ../../../../conformance/sdk-output/tests/$test/expected-locking.hex
done
```

Expected: No diff output for any test.

- [ ] **Step 4: Commit**

```bash
git add conformance/sdk-output/tools/rs-sdk-tool/
git commit -m "feat(conformance): add Rust SDK conformance tool"
```

---

### Task 5: Write the Python SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/py-sdk-tool.py`

- [ ] **Step 1: Write the tool**

Create `conformance/sdk-output/tools/py-sdk-tool.py`:

```python
#!/usr/bin/env python3
import json
import sys
import os

# Add runar-py to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'packages', 'runar-py'))

from runar.sdk import RunarContract, RunarArtifact


def convert_arg(arg: dict):
    t = arg['type']
    v = arg['value']
    if t in ('bigint', 'int'):
        return int(v)
    if t == 'bool':
        return v == 'true'
    # ByteString, PubKey, Addr, Sig, Ripemd160, Sha256, Point — hex strings
    return v


def main():
    if len(sys.argv) < 2:
        print('Usage: py-sdk-tool.py <input.json>', file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1]) as f:
        data = json.load(f)

    artifact = RunarArtifact.from_dict(data['artifact'])
    args = [convert_arg(a) for a in data['constructorArgs']]

    contract = RunarContract(artifact, args)
    sys.stdout.write(contract.get_locking_script())


if __name__ == '__main__':
    main()
```

Note: Check that `RunarArtifact.from_dict()` is the actual factory method in `packages/runar-py/runar/sdk/`. If the class takes a dict directly in `__init__`, use `RunarArtifact(data['artifact'])` instead. Verify by reading the class definition.

- [ ] **Step 2: Test the tool**

```bash
PYTHONPATH=packages/runar-py python3 conformance/sdk-output/tools/py-sdk-tool.py conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: Hex matching golden file.

```bash
for test in basic-p2pkh stateful-bytestring stateful-counter; do
  echo "=== $test ==="
  diff <(PYTHONPATH=packages/runar-py python3 conformance/sdk-output/tools/py-sdk-tool.py conformance/sdk-output/tests/$test/input.json) conformance/sdk-output/tests/$test/expected-locking.hex
done
```

Expected: No diff.

- [ ] **Step 3: Commit**

```bash
git add conformance/sdk-output/tools/py-sdk-tool.py
git commit -m "feat(conformance): add Python SDK conformance tool"
```

---

### Task 6: Write the Zig SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/zig-sdk-tool/build.zig`
- Create: `conformance/sdk-output/tools/zig-sdk-tool/build.zig.zon`
- Create: `conformance/sdk-output/tools/zig-sdk-tool/src/main.zig`

- [ ] **Step 1: Write build.zig.zon**

Create `conformance/sdk-output/tools/zig-sdk-tool/build.zig.zon`:

```zig
.{
    .name = "zig-sdk-tool",
    .version = "0.1.0",
    .dependencies = .{
        .runar_zig = .{
            .path = "../../../../packages/runar-zig",
        },
    },
    .paths = .{"."},
}
```

Note: Verify the dependency name matches what `packages/runar-zig/build.zig.zon` exports. The package name there is `runar_zig`.

- [ ] **Step 2: Write build.zig**

Create `conformance/sdk-output/tools/zig-sdk-tool/build.zig`:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const runar_dep = b.dependency("runar_zig", .{
        .target = target,
        .optimize = optimize,
    });

    const exe = b.addExecutable(.{
        .name = "zig-sdk-tool",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    exe.root_module.addImport("runar", runar_dep.module("runar_zig"));
    b.installArtifact(exe);
}
```

Note: Verify the module name exposed by runar-zig. Check `packages/runar-zig/build.zig` for `addModule` or `root_module` to see what name is exported. Adjust `runar_dep.module("runar_zig")` accordingly.

- [ ] **Step 3: Write main.zig**

Create `conformance/sdk-output/tools/zig-sdk-tool/src/main.zig`:

```zig
const std = @import("std");
const runar = @import("runar");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {
        try std.io.getStdErr().writer().writeAll("Usage: zig-sdk-tool <input.json>\n");
        std.process.exit(1);
    }

    const data = try std.fs.cwd().readFileAlloc(allocator, args[1], 10 * 1024 * 1024);
    defer allocator.free(data);

    const parsed = try std.json.parseFromSlice(std.json.Value, allocator, data, .{});
    defer parsed.deinit();

    const root = parsed.value.object;

    // Parse artifact
    const artifact_json = root.get("artifact").?;
    var artifact = try runar.sdk_types.RunarArtifact.fromJsonValue(allocator, artifact_json);
    defer artifact.deinit(allocator);

    // Parse constructor args
    const args_array = root.get("constructorArgs").?.array;
    var constructor_args = try allocator.alloc(runar.sdk_types.StateValue, args_array.items.len);
    defer allocator.free(constructor_args);

    for (args_array.items, 0..) |item, i| {
        const obj = item.object;
        const arg_type = obj.get("type").?.string;
        const value_str = obj.get("value").?.string;

        if (std.mem.eql(u8, arg_type, "bigint") or std.mem.eql(u8, arg_type, "int")) {
            constructor_args[i] = .{ .int = try std.fmt.parseInt(i64, value_str, 10) };
        } else if (std.mem.eql(u8, arg_type, "bool")) {
            constructor_args[i] = .{ .bool = std.mem.eql(u8, value_str, "true") };
        } else {
            constructor_args[i] = .{ .bytes = try allocator.dupe(u8, value_str) };
        }
    }

    var contract = try runar.sdk_contract.RunarContract.init(allocator, &artifact, constructor_args);
    defer contract.deinit();

    const locking_script = try contract.getLockingScript();
    defer allocator.free(locking_script);

    try std.io.getStdOut().writeAll(locking_script);
}
```

Note: The exact import paths (`runar.sdk_types`, `runar.sdk_contract`) and type names (`StateValue`, `RunarArtifact.fromJsonValue`) must match the runar-zig package's public API. Check `packages/runar-zig/src/sdk_types.zig` and `packages/runar-zig/src/sdk_contract.zig` for the actual struct and method names. Adjust as needed.

- [ ] **Step 4: Build and test**

```bash
cd conformance/sdk-output/tools/zig-sdk-tool
zig build
```

Expected: Successful build producing `zig-out/bin/zig-sdk-tool`.

```bash
./zig-out/bin/zig-sdk-tool ../../../../conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: Hex matching golden file.

Test all three from project root:
```bash
for test in basic-p2pkh stateful-bytestring stateful-counter; do
  echo "=== $test ==="
  diff <(conformance/sdk-output/tools/zig-sdk-tool/zig-out/bin/zig-sdk-tool conformance/sdk-output/tests/$test/input.json) conformance/sdk-output/tests/$test/expected-locking.hex
done
```

- [ ] **Step 5: Add zig build artifacts to .gitignore**

Create `conformance/sdk-output/tools/zig-sdk-tool/.gitignore`:

```
zig-out/
.zig-cache/
```

- [ ] **Step 6: Commit**

```bash
git add conformance/sdk-output/tools/zig-sdk-tool/
git commit -m "feat(conformance): add Zig SDK conformance tool"
```

---

### Task 7: Write the Ruby SDK tool

**Files:**
- Create: `conformance/sdk-output/tools/rb-sdk-tool.rb`

- [ ] **Step 1: Write the tool**

Create `conformance/sdk-output/tools/rb-sdk-tool.rb`:

```ruby
#!/usr/bin/env ruby
require 'json'

$LOAD_PATH.unshift(File.join(__dir__, '..', '..', '..', 'packages', 'runar-rb', 'lib'))
require 'runar'

def convert_arg(arg)
  case arg['type']
  when 'bigint', 'int'
    arg['value'].to_i
  when 'bool'
    arg['value'] == 'true'
  else
    # ByteString, PubKey, Addr, Sig, Ripemd160, Sha256, Point �� hex strings
    arg['value']
  end
end

if ARGV.length < 1
  $stderr.puts 'Usage: rb-sdk-tool.rb <input.json>'
  exit 1
end

data = JSON.parse(File.read(ARGV[0]))
artifact = Runar::SDK::RunarArtifact.from_hash(data['artifact'])
args = data['constructorArgs'].map { |a| convert_arg(a) }

contract = Runar::SDK::RunarContract.new(artifact, args)
$stdout.write(contract.get_locking_script)
```

Note: Verify the artifact factory method. Check `packages/runar-rb/lib/runar/sdk/types.rb` for how `RunarArtifact` is constructed from a hash. It might be `RunarArtifact.new(data['artifact'])` or `RunarArtifact.from_json(...)`. Adjust accordingly.

- [ ] **Step 2: Test the tool**

```bash
ruby conformance/sdk-output/tools/rb-sdk-tool.rb conformance/sdk-output/tests/basic-p2pkh/input.json
```

Expected: Hex matching golden file.

```bash
for test in basic-p2pkh stateful-bytestring stateful-counter; do
  echo "=== $test ==="
  diff <(ruby conformance/sdk-output/tools/rb-sdk-tool.rb conformance/sdk-output/tests/$test/input.json) conformance/sdk-output/tests/$test/expected-locking.hex
done
```

Expected: No diff.

- [ ] **Step 3: Commit**

```bash
git add conformance/sdk-output/tools/rb-sdk-tool.rb
git commit -m "feat(conformance): add Ruby SDK conformance tool"
```

---

### Task 8: Write the conformance runner

**Files:**
- Create: `conformance/sdk-output/runner/sdk-runner.ts`

- [ ] **Step 1: Write the runner**

Create `conformance/sdk-output/runner/sdk-runner.ts`:

```typescript
import { execFileSync } from 'child_process';
import { readdirSync, readFileSync, writeFileSync, existsSync, accessSync, constants } from 'fs';
import { join, resolve } from 'path';

const ROOT = resolve(join(import.meta.dirname, '..', '..', '..'));

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

interface SdkResult {
  sdk: string;
  hex: string;
  success: boolean;
  error?: string;
  durationMs: number;
}

interface TestResult {
  testName: string;
  sdkResults: SdkResult[];
  allMatch: boolean;
  goldenMatch: boolean;
  errors: string[];
}

// ---------------------------------------------------------------------------
// SDK tool definitions
// ---------------------------------------------------------------------------

interface SdkTool {
  name: string;
  cmd: string;
  args: (inputPath: string) => string[];
  env?: Record<string, string>;
  cwd?: string;
  /** If set, build this tool before first run */
  preBuild?: () => void;
}

function isExecutable(path: string): boolean {
  try {
    accessSync(path, constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

function buildSdkTools(): SdkTool[] {
  const toolsDir = join(ROOT, 'conformance', 'sdk-output', 'tools');
  const tools: SdkTool[] = [
    {
      name: 'typescript',
      cmd: 'npx',
      args: (input) => ['tsx', join(toolsDir, 'ts-sdk-tool.ts'), input],
    },
    {
      name: 'go',
      cmd: 'go',
      args: (input) => ['run', join(toolsDir, 'go-sdk-tool.go'), input],
    },
    {
      name: 'python',
      cmd: 'python3',
      args: (input) => [join(toolsDir, 'py-sdk-tool.py'), input],
      env: { PYTHONPATH: join(ROOT, 'packages', 'runar-py') },
    },
    {
      name: 'ruby',
      cmd: 'ruby',
      args: (input) => [join(toolsDir, 'rb-sdk-tool.rb'), input],
    },
  ];

  // Rust: prefer pre-built binary, fall back to cargo run
  const rsBin = join(toolsDir, 'rs-sdk-tool', 'target', 'release', 'rs-sdk-tool');
  if (isExecutable(rsBin)) {
    tools.push({
      name: 'rust',
      cmd: rsBin,
      args: (input) => [input],
    });
  } else {
    tools.push({
      name: 'rust',
      cmd: 'cargo',
      args: (input) => [
        'run', '--release',
        '--manifest-path', join(toolsDir, 'rs-sdk-tool', 'Cargo.toml'),
        '--', input,
      ],
    });
  }

  // Zig: prefer pre-built binary, fall back to zig build + run
  const zigBin = join(toolsDir, 'zig-sdk-tool', 'zig-out', 'bin', 'zig-sdk-tool');
  if (isExecutable(zigBin)) {
    tools.push({
      name: 'zig',
      cmd: zigBin,
      args: (input) => [input],
    });
  } else {
    tools.push({
      name: 'zig',
      cmd: zigBin,
      args: (input) => [input],
      preBuild: () => {
        execFileSync('zig', ['build'], {
          cwd: join(toolsDir, 'zig-sdk-tool'),
          stdio: 'pipe',
          timeout: 60_000,
        });
      },
    });
  }

  return tools;
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

function runSdkTool(tool: SdkTool, inputPath: string): SdkResult {
  const start = Date.now();
  try {
    if (tool.preBuild) {
      tool.preBuild();
      tool.preBuild = undefined; // only build once
    }
    const toolArgs = tool.args(inputPath);
    const env = { ...process.env, ...tool.env };
    const output = execFileSync(tool.cmd, toolArgs, {
      cwd: tool.cwd ?? ROOT,
      timeout: 30_000,
      maxBuffer: 10 * 1024 * 1024,
      env,
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    return {
      sdk: tool.name,
      hex: output.toString().trim().toLowerCase(),
      success: true,
      durationMs: Date.now() - start,
    };
  } catch (err: unknown) {
    const e = err as { stderr?: Buffer; message?: string };
    return {
      sdk: tool.name,
      hex: '',
      success: false,
      error: e.stderr?.toString().slice(0, 500) || e.message || 'unknown error',
      durationMs: Date.now() - start,
    };
  }
}

function runTest(testDir: string, tools: SdkTool[]): TestResult {
  const testName = testDir.split('/').pop()!;
  const inputPath = join(testDir, 'input.json');
  const goldenPath = join(testDir, 'expected-locking.hex');

  const sdkResults = tools.map((tool) => runSdkTool(tool, inputPath));
  const errors: string[] = [];

  // Check for failures
  for (const r of sdkResults) {
    if (!r.success) {
      errors.push(`${r.sdk}: FAILED - ${r.error}`);
    }
  }

  // Cross-SDK comparison
  const successful = sdkResults.filter((r) => r.success);
  let allMatch = true;
  if (successful.length >= 2) {
    const reference = successful[0]!.hex;
    for (let i = 1; i < successful.length; i++) {
      if (successful[i]!.hex !== reference) {
        allMatch = false;
        errors.push(
          `MISMATCH: ${successful[0]!.sdk} vs ${successful[i]!.sdk}` +
          ` (${reference.slice(0, 40)}... vs ${successful[i]!.hex.slice(0, 40)}...)`,
        );
      }
    }
  } else if (successful.length < 2) {
    allMatch = false;
  }

  // Golden file comparison
  let goldenMatch = true;
  if (existsSync(goldenPath)) {
    const golden = readFileSync(goldenPath, 'utf-8').trim().toLowerCase();
    for (const r of successful) {
      if (r.hex !== golden) {
        goldenMatch = false;
        errors.push(`${r.sdk}: does not match golden file`);
      }
    }
  } else {
    goldenMatch = false;
    errors.push('No expected-locking.hex golden file found');
  }

  return { testName, sdkResults, allMatch, goldenMatch, errors };
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

function parseArgs(argv: string[]): {
  testsDir: string;
  filter?: string;
  format: 'console' | 'json' | 'markdown';
  output?: string;
  updateGolden: boolean;
} {
  const args = argv.slice(2);
  let testsDir = join(ROOT, 'conformance', 'sdk-output', 'tests');
  let filter: string | undefined;
  let format: 'console' | 'json' | 'markdown' = 'console';
  let output: string | undefined;
  let updateGolden = false;

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--tests-dir':
        testsDir = resolve(args[++i]!);
        break;
      case '--filter':
        filter = args[++i];
        break;
      case '--format':
        format = args[++i] as 'console' | 'json' | 'markdown';
        break;
      case '--output':
        output = args[++i];
        break;
      case '--update-golden':
        updateGolden = true;
        break;
    }
  }

  return { testsDir, filter, format, output, updateGolden };
}

function main(): void {
  const opts = parseArgs(process.argv);
  const tools = buildSdkTools();

  // Discover tests
  let testDirs = readdirSync(opts.testsDir, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => join(opts.testsDir, d.name))
    .filter((d) => existsSync(join(d, 'input.json')));

  if (opts.filter) {
    testDirs = testDirs.filter((d) => d.includes(opts.filter!));
  }

  console.log(`Running SDK output conformance: ${testDirs.length} tests x ${tools.length} SDKs\n`);

  const results: TestResult[] = [];
  let anyFail = false;

  for (const dir of testDirs) {
    const result = runTest(dir, tools);
    results.push(result);

    if (!result.allMatch || !result.goldenMatch || result.errors.length > 0) {
      anyFail = true;
    }

    // Console output
    if (opts.format === 'console') {
      const status = result.allMatch && result.goldenMatch ? 'PASS' : 'FAIL';
      const icon = status === 'PASS' ? '+' : 'x';
      console.log(`[${icon}] ${result.testName}: ${status}`);
      for (const r of result.sdkResults) {
        const s = r.success ? `OK (${r.durationMs}ms)` : `FAIL: ${r.error}`;
        console.log(`    ${r.sdk}: ${s}`);
      }
      for (const e of result.errors) {
        console.log(`    ERROR: ${e}`);
      }
      console.log();
    }

    // Update golden files from TypeScript output
    if (opts.updateGolden) {
      const tsResult = result.sdkResults.find((r) => r.sdk === 'typescript' && r.success);
      if (tsResult) {
        writeFileSync(join(dir, 'expected-locking.hex'), tsResult.hex + '\n');
        console.log(`  Updated golden: ${result.testName}/expected-locking.hex`);
      }
    }
  }

  // JSON/Markdown output
  if (opts.format === 'json') {
    const out = JSON.stringify(results, null, 2);
    if (opts.output) writeFileSync(opts.output, out);
    else console.log(out);
  } else if (opts.format === 'markdown') {
    let md = '# SDK Output Conformance Results\n\n';
    md += `| Test | ${tools.map((t) => t.name).join(' | ')} | Match |\n`;
    md += `|------|${tools.map(() => '---').join('|')}|-------|\n`;
    for (const r of results) {
      const cols = tools.map((t) => {
        const sr = r.sdkResults.find((s) => s.sdk === t.name);
        return sr?.success ? 'OK' : 'FAIL';
      });
      const match = r.allMatch && r.goldenMatch ? 'PASS' : 'FAIL';
      md += `| ${r.testName} | ${cols.join(' | ')} | ${match} |\n`;
    }
    if (opts.output) writeFileSync(opts.output, md);
    else console.log(md);
  }

  process.exit(anyFail ? 1 : 0);
}

main();
```

- [ ] **Step 2: Test the runner with all tools**

```bash
npx tsx conformance/sdk-output/runner/sdk-runner.ts
```

Expected output (all PASS):
```
Running SDK output conformance: 3 tests x 6 SDKs

[+] basic-p2pkh: PASS
    typescript: OK (Xms)
    go: OK (Xms)
    python: OK (Xms)
    ruby: OK (Xms)
    rust: OK (Xms)
    zig: OK (Xms)

[+] stateful-bytestring: PASS
    ...

[+] stateful-counter: PASS
    ...
```

- [ ] **Step 3: Test the filter option**

```bash
npx tsx conformance/sdk-output/runner/sdk-runner.ts --filter stateful
```

Expected: Only the two stateful tests run.

- [ ] **Step 4: Commit**

```bash
git add conformance/sdk-output/runner/sdk-runner.ts
git commit -m "feat(conformance): add SDK output conformance runner"
```

---

### Task 9: Add package.json script and final integration

**Files:**
- Modify: `package.json` (root)

- [ ] **Step 1: Add conformance:sdk script**

Add to the `"scripts"` section in root `package.json`:

```json
"conformance:sdk": "npx tsx conformance/sdk-output/runner/sdk-runner.ts"
```

- [ ] **Step 2: Update conformance:all to include SDK tests**

Find the existing `"conformance:all"` script and append `&& pnpm run conformance:sdk` to it.

- [ ] **Step 3: Run via pnpm to verify**

```bash
pnpm run conformance:sdk
```

Expected: All 3 tests pass across all 6 SDKs.

- [ ] **Step 4: Commit**

```bash
git add package.json
git commit -m "feat(conformance): add conformance:sdk script to package.json"
```

---

### Task 10: Clean up .tmp and .gitignore

**Files:**
- Create: `conformance/sdk-output/.gitignore`

- [ ] **Step 1: Add .gitignore for generated files**

Create `conformance/sdk-output/.gitignore`:

```
.tmp/
tools/rs-sdk-tool/target/
tools/zig-sdk-tool/zig-out/
tools/zig-sdk-tool/.zig-cache/
```

- [ ] **Step 2: Clean up .tmp from generate-inputs**

```bash
rm -rf conformance/sdk-output/.tmp
```

- [ ] **Step 3: Final full run**

```bash
pnpm run conformance:sdk
```

Expected: All 3 tests x 6 SDKs = 18 checks, all PASS.

- [ ] **Step 4: Commit**

```bash
git add conformance/sdk-output/.gitignore
git commit -m "chore(conformance): add .gitignore for SDK tool build artifacts"
```
