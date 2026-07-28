package compiler

import "testing"

// TestPrivateMethodVarLenStateRead_MatchesDirectRead is the regression test
// for deep-review finding C18 (P1 funds-safety bug).
//
// methodReadsVarLenState (compilers/go/codegen/stack.go) did not recurse
// through private method_call targets the way its sibling
// methodUsesCheckPreimage already does. Private methods are INLINED into the
// caller's stack context, so a public method whose only read of a mutable
// variable-length (ByteString) state field happens inside a private helper
// computed usesCodePart = false. That meant _codePart was never pushed as
// the implicit stack parameter, and lowerDeserializeState's variable-length
// branch took its "terminal method, skip deserialization" shortcut — the
// method would silently read the deploy-time constructor placeholder instead
// of the live on-chain state.
//
// The two contracts below are semantically identical: one reads
// len(this.tag) directly, the other reads it through a private helper. Their
// compiled scripts MUST be byte-identical.
func TestPrivateMethodVarLenStateRead_MatchesDirectRead(t *testing.T) {
	directSource := `import { StatefulSmartContract, assert, len } from 'runar-lang';

class VarLenDirectRead extends StatefulSmartContract {
  tag: ByteString;

  constructor(tag: ByteString) {
    super(tag);
    this.tag = tag;
  }

  public check(expected: bigint): void {
    assert(len(this.tag) == expected);
  }
}
`

	helperSource := `import { StatefulSmartContract, assert, len } from 'runar-lang';

class VarLenPrivateRead extends StatefulSmartContract {
  tag: ByteString;

  constructor(tag: ByteString) {
    super(tag);
    this.tag = tag;
  }

  private tagLen(): bigint {
    return len(this.tag);
  }

  public check(expected: bigint): void {
    assert(this.tagLen() == expected);
  }
}
`

	opts := CompileOptions{DisableConstantFolding: true}

	directResult := CompileFromSourceStrWithResult(directSource, "VarLenDirectRead.runar.ts", opts)
	if !directResult.Success {
		t.Fatalf("direct-read compilation failed: %v", directResult.Diagnostics)
	}
	helperResult := CompileFromSourceStrWithResult(helperSource, "VarLenPrivateRead.runar.ts", opts)
	if !helperResult.Success {
		t.Fatalf("private-helper compilation failed: %v", helperResult.Diagnostics)
	}

	if got, want := helperResult.Artifact.Script, directResult.Artifact.Script; got != want {
		t.Fatalf("private-helper variant diverges from direct-read control:\n  helper: %s\n  direct: %s\n  (helper asm: %s)",
			got, want, helperResult.Artifact.ASM)
	}
}
