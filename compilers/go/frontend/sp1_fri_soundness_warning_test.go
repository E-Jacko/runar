package frontend

import "testing"

// The deployable SP1 FRI verifier is not sound at the PoC parameter set: the
// per-query chain is never emitted, so forged Merkle openings are ACCEPTED
// on-chain (docs/sp1-fri-verifier.md, pinned by
// compilers/go/compiler/sp1_fri_negative_test.go).
//
// A developer who just calls the built-in reads neither of those, so the
// validator raises it as a compile-time warning. These tests pin that it
// actually fires, and — just as importantly — that it does NOT fire for
// contracts that never touch the built-in, so it cannot decay into noise
// everyone learns to ignore.

func sp1WarningPresent(t *testing.T, contract *ContractNode) bool {
	t.Helper()
	res := Validate(contract)
	for _, d := range res.Warnings {
		if d.Severity == SeverityWarning && containsSubstr(d.Message, "NOT a sound proof verifier") {
			return true
		}
	}
	return false
}

func containsSubstr(haystack, needle string) bool {
	if len(needle) > len(haystack) {
		return false
	}
	for i := 0; i+len(needle) <= len(haystack); i++ {
		if haystack[i:i+len(needle)] == needle {
			return true
		}
	}
	return false
}

func TestSP1FriSoundnessWarning_FiresWhenBuiltinIsCalled(t *testing.T) {
	contract := &ContractNode{
		Name: "UsesSP1",
		Methods: []MethodNode{{
			Name:       "spend",
			Visibility: "public",
			Body: []Statement{
				ExpressionStmt{Expr: CallExpr{
					Callee: Identifier{Name: "assert"},
					Args: []Expression{
						CallExpr{
							Callee: Identifier{Name: "verifySP1FRI"},
							Args: []Expression{
								Identifier{Name: "proof"},
								Identifier{Name: "publicValues"},
								Identifier{Name: "vkHash"},
							},
						},
					},
				}},
			},
		}},
	}
	if !sp1WarningPresent(t, contract) {
		t.Fatal("expected the SP1 FRI soundness warning; a caller of the built-in would " +
			"otherwise get no signal that the emitted script accepts forged Merkle openings")
	}
}

func TestSP1FriSoundnessWarning_SilentForUnrelatedContracts(t *testing.T) {
	contract := &ContractNode{
		Name: "NoSP1",
		Methods: []MethodNode{{
			Name:       "spend",
			Visibility: "public",
			Body: []Statement{
				ExpressionStmt{Expr: CallExpr{
					Callee: Identifier{Name: "assert"},
					Args: []Expression{
						BinaryExpr{Op: ">", Left: Identifier{Name: "a"}, Right: Identifier{Name: "b"}},
					},
				}},
			},
		}},
	}
	if sp1WarningPresent(t, contract) {
		t.Fatal("the SP1 FRI warning fired for a contract that never calls the built-in; " +
			"a warning that fires everywhere is a warning nobody reads")
	}
}
