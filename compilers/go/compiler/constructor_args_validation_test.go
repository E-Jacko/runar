package compiler

// Port of the TypeScript reference test
// packages/runar-compiler/src/__tests__/constructor-args-validation.test.ts.
//
// applyConstructorArgs must reject inputs that would silently bake nothing and
// emit placeholder scripts that fail opaquely at runtime:
//
//	(a) positional arrays — N/A for the Go tier: ConstructorArgs is a typed
//	    map[string]interface{}, so a positional array cannot reach the API.
//	    (The dynamically-typed tiers guard this explicitly.)
//	(b) keys that match no contract property (typos)
//	(c) referenced readonly properties left unbaked after applying the args
//
// The placeholder path (no ConstructorArgs) stays unchecked / byte-identical.

import (
	"math/big"
	"strings"
	"testing"

	"github.com/icellan/runar/compilers/go/frontend"
)

const hashLockSource = `import { SmartContract, assert, sha256 } from 'runar-lang';
import type { ByteString, Sha256 } from 'runar-lang';

class HashLock extends SmartContract {
  readonly hashValue: Sha256;

  constructor(hashValue: Sha256) {
    super(hashValue);
    this.hashValue = hashValue;
  }

  public unlock(preimage: ByteString) {
    assert(sha256(preimage) === this.hashValue);
  }
}
`

const twoPropSource = `import { SmartContract, assert } from 'runar-lang';

class TwoProp extends SmartContract {
  readonly target: bigint;
  readonly unused: bigint;

  constructor(target: bigint, unused: bigint) {
    super(target, unused);
    this.target = target;
    this.unused = unused;
  }

  public check(x: bigint) {
    assert(x === this.target);
  }
}
`

const hashHex = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" // "aa" * 32

func errorMessages(result *CompileResult) string {
	var msgs []string
	for _, d := range result.Diagnostics {
		if d.Severity == frontend.SeverityError {
			msgs = append(msgs, d.Message)
		}
	}
	return strings.Join(msgs, "\n")
}

func TestConstructorArgs_RejectsUnknownKey(t *testing.T) {
	result := CompileFromSourceStrWithResult(hashLockSource, "HashLock.runar.ts", CompileOptions{
		ConstructorArgs: map[string]interface{}{"hashVal": hashHex}, // typo: hashValue
	})

	if result.Success {
		t.Fatalf("expected compilation to fail for an unknown constructorArgs key")
	}
	msgs := errorMessages(result)
	if !strings.Contains(msgs, "'hashVal'") {
		t.Errorf("error should name the offending key 'hashVal'; got:\n%s", msgs)
	}
	if !strings.Contains(msgs, "hashValue") {
		t.Errorf("error should list the valid property 'hashValue'; got:\n%s", msgs)
	}
}

func TestConstructorArgs_RejectsUnbakedReferencedReadonly(t *testing.T) {
	// 'target' is referenced by check() but not provided; only 'unused' is baked.
	result := CompileFromSourceStrWithResult(twoPropSource, "TwoProp.runar.ts", CompileOptions{
		ConstructorArgs: map[string]interface{}{"unused": big.NewInt(1)},
	})

	if result.Success {
		t.Fatalf("expected compilation to fail when a referenced readonly stays unbaked")
	}
	msgs := errorMessages(result)
	if !strings.Contains(msgs, "'target'") {
		t.Errorf("error should name the unbaked referenced property 'target'; got:\n%s", msgs)
	}
	if !strings.Contains(msgs, "placeholder") {
		t.Errorf("error should mention the OP_0 placeholder hazard; got:\n%s", msgs)
	}
}

func TestConstructorArgs_AcceptsUnreferencedUnbakedReadonly(t *testing.T) {
	// 'unused' is never referenced by a method — DCE eliminates it, so leaving
	// it unbaked is fine.
	result := CompileFromSourceStrWithResult(twoPropSource, "TwoProp.runar.ts", CompileOptions{
		ConstructorArgs: map[string]interface{}{"target": big.NewInt(42)},
	})

	if !result.Success {
		t.Fatalf("expected success (unused readonly is unreferenced); diagnostics:\n%s", errorMessages(result))
	}
	if result.Artifact == nil || result.Artifact.Script == "" {
		t.Errorf("expected a compiled artifact with a script")
	}
}

func TestConstructorArgs_AcceptsCompleteRecord(t *testing.T) {
	result := CompileFromSourceStrWithResult(hashLockSource, "HashLock.runar.ts", CompileOptions{
		ConstructorArgs: map[string]interface{}{"hashValue": hashHex},
	})

	if !result.Success {
		t.Fatalf("expected success for a complete named record; diagnostics:\n%s", errorMessages(result))
	}
	if result.Artifact == nil {
		t.Fatal("expected a compiled artifact")
	}
	if !strings.Contains(result.Artifact.Script, hashHex) {
		t.Errorf("baked script should contain the hash bytes %s; got script:\n%s", hashHex, result.Artifact.Script)
	}
	if len(result.Artifact.ConstructorSlots) != 0 {
		t.Errorf("a fully baked contract should carry no constructor slots; got %d", len(result.Artifact.ConstructorSlots))
	}
}

func TestConstructorArgs_NoArgsStillProducesPlaceholderSlots(t *testing.T) {
	// The no-args placeholder path stays unchecked and byte-identical to before.
	result := CompileFromSourceStrWithResult(hashLockSource, "HashLock.runar.ts", CompileOptions{})

	if !result.Success {
		t.Fatalf("expected success for placeholder compilation; diagnostics:\n%s", errorMessages(result))
	}
	if result.Artifact == nil || len(result.Artifact.ConstructorSlots) < 1 {
		t.Errorf("placeholder compilation should carry at least one constructor slot")
	}
}
