package runar

import (
	"strings"
	"testing"
)

// Issue #132: the OP_CODESEPARATOR offset used for a covenant input's OP_PUSH_TX
// signature must be derived by byte-walking the REAL code script when it is
// present (chain-loaded, or a deploy script already built from real constructor
// args) — mirroring getSubscriptForSigning — NOT recomputed from the in-memory
// constructor args (which are placeholders on the restore path).
//
// Go centralises this in getCodeSepIndex, which byte-walks codeScript via
// findCodesepOffsets whenever codeScript is set and only falls back to the
// template adjustCodeSepOffset when codeScript == "" (deploy-time). This test
// pins the invariant: with a real codeScript present, the resolved offset is the
// byte-walked position and is independent of the (placeholder) constructor args.
func TestGetCodeSepIndex_ByteWalksRealCodeScript_Issue132(t *testing.T) {
	// A deliberately WRONG template index (5) so that if the template path were
	// taken it would diverge from the byte-walked answer.
	tmpl := 5
	// codeScript: eight single-byte opcodes (OP_1..OP_8) then OP_CODESEPARATOR
	// (0xab) at byte offset 8, then a trailing opcode. findCodesepOffsets must
	// report offset 8.
	codeScript := "5152535455565758" + "ab" + "51"
	realOffset := 8
	if got := findCodesepOffsets(codeScript); len(got) != 1 || got[0] != realOffset {
		t.Fatalf("findCodesepOffsets(codeScript) = %v, want [%d]", got, realOffset)
	}

	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: []ABIParam{{Name: "owner", Type: "PubKey"}}},
		Methods:     []ABIMethod{{Name: "spend", Params: nil, IsPublic: true}},
	}, func(a *RunarArtifact) {
		a.CodeSeparatorIndices = []int{tmpl}
		a.StateFields = []StateField{{Name: "count", Type: "bigint", Index: 0}}
	})

	// Placeholder constructor args (a zero-ish PubKey) — deliberately NOT the
	// real deployed value.
	placeholder := strings.Repeat("00", 33)
	c := NewRunarContract(artifact, []interface{}{placeholder})
	c.codeScript = codeScript // real code script present

	got := c.getCodeSepIndex(0)
	if got != realOffset {
		t.Errorf("getCodeSepIndex byte-walk returned %d, want %d (issue #132: must byte-walk the real code script, not use the template/args)", got, realOffset)
	}
	if got == c.adjustCodeSepOffset(tmpl) && c.adjustCodeSepOffset(tmpl) != realOffset {
		t.Errorf("getCodeSepIndex used the template adjust path (%d) instead of the byte-walk (%d)", c.adjustCodeSepOffset(tmpl), realOffset)
	}

	// Without a code script, the template (deploy-time) path is used.
	c2 := NewRunarContract(artifact, []interface{}{placeholder})
	if c2.getCodeSepIndex(0) != c2.adjustCodeSepOffset(tmpl) {
		t.Errorf("with no codeScript, expected the template adjust path")
	}
}
