package compiler

// Port of the TypeScript reference test
// packages/runar-compiler/src/__tests__/loop-outer-refs.test.ts.
//
// Stack lowering across unrolled for-loops — outer-scope refs (method params,
// pre-loop consts) must survive loop unrolling:
//
//	(a) a const defined before a loop and referenced inside it (including only
//	    inside a nested if-branch) used to fail compilation with
//	    "Value 'X' not found on stack" — the first iteration consumed it;
//	(b) worse, a method PARAM referenced after an unrolled loop whose body also
//	    references it was silently lowered to an empty push (OP_0): compilation
//	    succeeded, the env-based interpreter passed, but the emitted Script
//	    failed at runtime (silent interpreter <-> Script divergence).
//
// The fix: lowerLoop collects outer refs deeply (nested branches included) and
// protects them in non-final iterations, and in the final iteration whenever
// the enclosing scope still references them after the loop. The old silent
// OP_0 fallbacks are now hard errors.

import (
	"strings"
	"testing"
)

const loopWalkSource = `import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class LoopWalk extends SmartContract {
  readonly pad00: ByteString = "00" as ByteString;

  constructor() {
    super();
  }

  public walk(data: ByteString) {
    let off = 5n;
    for (let i = 0n; i < 3n; i++) {
      if (i < bin2num(cat(substr(data, 4n, 1n), this.pad00))) {
        const sl = bin2num(cat(substr(data, off + 36n, 1n), this.pad00));
        assert(sl < 253n);
        off = off + 36n + 1n + sl + 4n;
      }
    }
    const tail = bin2num(cat(substr(data, off, 1n), this.pad00));
    assert(tail === 7n);
  }
}
`

const constBeforeLoopSource = `import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ConstLoop extends SmartContract {
  readonly pad00: ByteString = "00" as ByteString;

  constructor() {
    super();
  }

  public probe(data: ByteString) {
    const base = 5n;
    let acc = 0n;
    for (let i = 0n; i < 3n; i++) {
      const b = bin2num(cat(substr(data, base + i, 1n), this.pad00));
      acc = acc + b;
    }
    assert(acc === 6n);
  }
}
`

func TestLoopOuterRefs_ParamAfterLoopIsNotEmptyPush(t *testing.T) {
	result := CompileFromSourceStrWithResult(loopWalkSource, "LoopWalk.runar.ts", CompileOptions{})
	if !result.Success {
		t.Fatalf("compilation failed: %v", result.Diagnostics)
	}
	if result.Artifact == nil {
		t.Fatal("no artifact produced")
	}

	// The post-loop code (after the last OP_ENDIF) reads `data` via
	// substr(data, off, 1n). With the bug, `data` was emitted as OP_0 right
	// after the final OP_ENDIF; the fixed code brings the real param up.
	asm := result.Artifact.ASM
	idx := strings.LastIndex(asm, "OP_ENDIF")
	if idx < 0 {
		t.Fatalf("expected the unrolled loop to emit at least one OP_ENDIF; asm:\n%s", asm)
	}
	postLoop := asm[idx:]
	if strings.Contains(postLoop, "OP_0") {
		t.Fatalf("post-loop region should not contain a silent OP_0 for the param; post-loop asm:\n%s", postLoop)
	}
}

func TestLoopOuterRefs_ConstBeforeLoopCompiles(t *testing.T) {
	// Previously: "Value 'base' not found on stack (...)".
	result := CompileFromSourceStrWithResult(constBeforeLoopSource, "ConstLoop.runar.ts", CompileOptions{})
	if !result.Success {
		t.Fatalf("compilation failed for a const referenced inside a loop: %v", result.Diagnostics)
	}
	if result.Artifact == nil || result.Artifact.Script == "" {
		t.Fatal("expected a compiled artifact with a script")
	}
}

func TestLoopOuterRefs_UnsatisfiableLoadParamIsHardError(t *testing.T) {
	// Hand-written ANF referencing a parameter the method does not have — the
	// old code silently emitted OP_0 here.
	irJSON := `{
		"contractName": "Broken",
		"properties": [],
		"methods": [{
			"name": "run",
			"isPublic": true,
			"params": [{"name": "x", "type": "bigint"}],
			"body": [
				{"name": "t0", "value": {"kind": "load_param", "name": "ghost"}},
				{"name": "t1", "value": {"kind": "assert", "value": "t0"}}
			]
		}]
	}`

	_, err := CompileFromIRBytes([]byte(irJSON))
	if err == nil {
		t.Fatal("expected a hard error for an unsatisfiable load_param, got nil")
	}
	if !strings.Contains(err.Error(), "Refusing to emit a silent OP_0") {
		t.Fatalf("expected a 'Refusing to emit a silent OP_0' error; got: %v", err)
	}
}
