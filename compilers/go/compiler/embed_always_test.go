package compiler

import (
	"strings"
	"testing"
)

// Issue #109 — `/** @embedAlways */` readonly-field DCE opt-out (Go tier).
//
// A readonly field no method references is normally eliminated by ANF
// dead-binding DCE (the dead load_prop is dropped, so no constructor slot is
// emitted), silently removing deploy-time metadata an author intends to recover
// from the on-chain script later. The @embedAlways directive forces the field
// into the locking script (a constructor slot). Golden hexes are the TypeScript
// reference output (fold-OFF) — the Go tier must be byte-identical.

func metaSource(directive string) string {
	return `
import { SmartContract, assert, Addr, PubKey, Sig, ByteString, hash160, checkSig } from 'runar-lang';
class Meta extends SmartContract {
  readonly pubKeyHash: Addr;
  ` + directive + `
  readonly metadataId: ByteString;
  constructor(pubKeyHash: Addr, metadataId: ByteString) {
    super(pubKeyHash, metadataId);
    this.pubKeyHash = pubKeyHash;
    this.metadataId = metadataId;
  }
  public unlock(sig: Sig, pubKey: PubKey) {
    assert(hash160(pubKey) === this.pubKeyHash);
    assert(checkSig(sig, pubKey));
  }
}
`
}

// TS-reference golden scripts (fold-OFF).
const (
	metaPlainGoldenScript = "76a90088ac"
	metaEmbedGoldenScript = "0078a900887b7bac77"
)

func TestEmbedAlways_UnannotatedFieldEliminated(t *testing.T) {
	r := CompileFromSourceStrWithResult(metaSource(""), "Meta.runar.ts", CompileOptions{DisableConstantFolding: true})
	if !r.Success {
		t.Fatalf("compile failed: %v", diagMessages(r))
	}
	if r.ScriptHex != metaPlainGoldenScript {
		t.Fatalf("plain script mismatch:\n  got %s\n  want %s", r.ScriptHex, metaPlainGoldenScript)
	}
	names := slotNames(r)
	if contains(names, "metadataId") {
		t.Fatalf("un-annotated metadataId should be eliminated; slots=%v", names)
	}
	if !contains(names, "pubKeyHash") {
		t.Fatalf("pubKeyHash slot missing; slots=%v", names)
	}
}

func TestEmbedAlways_AnnotatedFieldPreservedByteIdenticalToTS(t *testing.T) {
	r := CompileFromSourceStrWithResult(metaSource("/** @embedAlways */"), "Meta.runar.ts", CompileOptions{DisableConstantFolding: true})
	if !r.Success {
		t.Fatalf("compile failed: %v", diagMessages(r))
	}
	if r.ScriptHex != metaEmbedGoldenScript {
		t.Fatalf("embed script mismatch (Go != TS):\n  got %s\n  want %s", r.ScriptHex, metaEmbedGoldenScript)
	}
	names := slotNames(r)
	// Both slots present; metadataId first (injected preservation load precedes
	// the pubKeyHash read in unlock) — matches TS constructorSlots order.
	if len(names) != 2 || names[0] != "metadataId" || names[1] != "pubKeyHash" {
		t.Fatalf("constructor slot order mismatch; got %v want [metadataId pubKeyHash]", names)
	}
}

func TestEmbedAlways_LineCommentForm(t *testing.T) {
	r := CompileFromSourceStrWithResult(metaSource("// @embedAlways"), "Meta.runar.ts", CompileOptions{DisableConstantFolding: true})
	if !r.Success {
		t.Fatalf("compile failed: %v", diagMessages(r))
	}
	if r.ScriptHex != metaEmbedGoldenScript {
		t.Fatalf("line-comment embed script mismatch:\n  got %s\n  want %s", r.ScriptHex, metaEmbedGoldenScript)
	}
}

func TestEmbedAlways_WarnsOnStrippedUnannotatedField(t *testing.T) {
	r := CompileFromSourceStrWithResult(metaSource(""), "Meta.runar.ts", CompileOptions{DisableConstantFolding: true})
	if !r.Success {
		t.Fatalf("compile failed: %v", diagMessages(r))
	}
	if !anyWarnContains(r, "metadataId") || !anyWarnContains(r, "@embedAlways") {
		t.Fatalf("expected DCE warning naming metadataId + @embedAlways; diags=%v", diagMessages(r))
	}
}

func TestEmbedAlways_NoWarnWhenAnnotated(t *testing.T) {
	r := CompileFromSourceStrWithResult(metaSource("/** @embedAlways */"), "Meta.runar.ts", CompileOptions{DisableConstantFolding: true})
	if anyWarnContains(r, "metadataId") {
		t.Fatalf("annotated field should not warn; diags=%v", diagMessages(r))
	}
}

// --- helpers ---

func slotNames(r *CompileResult) []string {
	if r.Artifact == nil {
		return nil
	}
	params := r.Artifact.ABI.Constructor.Params
	out := make([]string, 0, len(r.Artifact.ConstructorSlots))
	for _, s := range r.Artifact.ConstructorSlots {
		if s.ParamIndex >= 0 && s.ParamIndex < len(params) {
			out = append(out, params[s.ParamIndex].Name)
		}
	}
	return out
}

func contains(xs []string, x string) bool {
	for _, s := range xs {
		if s == x {
			return true
		}
	}
	return false
}

func diagMessages(r *CompileResult) []string {
	out := make([]string, 0, len(r.Diagnostics))
	for _, d := range r.Diagnostics {
		out = append(out, string(d.Severity)+": "+d.Message)
	}
	return out
}

func anyWarnContains(r *CompileResult, sub string) bool {
	for _, d := range r.Diagnostics {
		if d.Severity == "warning" && strings.Contains(d.Message, sub) {
			return true
		}
	}
	return false
}
