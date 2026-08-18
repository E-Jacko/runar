package frontend

// Compile-time disclosure for the SP1 FRI verifier's on-chain soundness gap.
//
// `EmitFullSP1FriVerifierBody` samples each FRI query index and immediately
// drops it — its own Step 10 comment says "For the deployable verifier we
// sample-and-drop". The input-batch MMCS verify, the FRI fold chain and the
// final-poly Horner equality are therefore NEVER EMITTED into the locking
// script. Replaying the corruption fixtures through the compiled covenant
// shows `bad_merkle`, `bad_folding` and `bad_final_poly` are ACCEPTED on-chain
// while the off-chain reference verifier rejects all three: a spender can
// supply forged Merkle openings — arbitrary opened values with arbitrary
// authentication paths — and the covenant accepts. On-chain soundness
// currently rests on the Fiat-Shamir transcript, not on the proof.
//
// That is written up in docs/sp1-fri-verifier.md and pinned by
// compilers/go/compiler/sp1_fri_negative_test.go, but a developer who simply
// calls the built-in would read neither. A gap this size must be impossible to
// miss, so the compiler says it every time the built-in is used.
//
// Remove this warning when the per-query verification chain lands.

const sp1FriSoundnessError = "verifySP1FRI: REFUSING to emit a known-unsound proof verifier. " +
	"The per-query chain (input-batch MMCS verify, FRI fold, final-poly equality) is not emitted, so " +
	"the locking script ACCEPTS forged Merkle openings — an attacker spends with a fabricated proof. " +
	"Replaying the corruption fixtures through the compiled covenant shows bad_merkle, bad_folding and " +
	"bad_final_poly all ACCEPTED on-chain while the off-chain reference rejects them. This is NOT usable " +
	"for a value-bearing covenant. If you are working on the verifier itself, add the comment directive " +
	"@acknowledgeUnsoundSP1FriVerifier to the contract source to compile it anyway. See " +
	"docs/sp1-fri-verifier.md."

const sp1FriSoundnessWarning = "verifySP1FRI: the emitted locking script is NOT a sound proof " +
	"verifier at the PoC parameter set. The per-query chain (input-batch MMCS verify, FRI fold, " +
	"final-poly equality) is not emitted, so FORGED Merkle openings are ACCEPTED on-chain — only " +
	"the Fiat-Shamir transcript binding is enforced. Do not use this for a value-bearing " +
	"covenant. See docs/sp1-fri-verifier.md."

// contractCallsSP1FriVerifier reports whether any method body calls
// `verifySP1FRI`, at any nesting depth.
func contractCallsSP1FriVerifier(contract *ContractNode) bool {
	for i := range contract.Methods {
		if statementsCallSP1Fri(contract.Methods[i].Body) {
			return true
		}
	}
	return false
}

func statementsCallSP1Fri(stmts []Statement) bool {
	for _, st := range stmts {
		switch v := st.(type) {
		case VariableDeclStmt:
			if exprCallsSP1Fri(v.Init) {
				return true
			}
		case *VariableDeclStmt:
			if exprCallsSP1Fri(v.Init) {
				return true
			}
		case AssignmentStmt:
			if exprCallsSP1Fri(v.Value) {
				return true
			}
		case *AssignmentStmt:
			if exprCallsSP1Fri(v.Value) {
				return true
			}
		case ExpressionStmt:
			if exprCallsSP1Fri(v.Expr) {
				return true
			}
		case *ExpressionStmt:
			if exprCallsSP1Fri(v.Expr) {
				return true
			}
		case IfStmt:
			if exprCallsSP1Fri(v.Condition) || statementsCallSP1Fri(v.Then) || statementsCallSP1Fri(v.Else) {
				return true
			}
		case *IfStmt:
			if exprCallsSP1Fri(v.Condition) || statementsCallSP1Fri(v.Then) || statementsCallSP1Fri(v.Else) {
				return true
			}
		case ForStmt:
			if exprCallsSP1Fri(v.Condition) || statementsCallSP1Fri(v.Body) {
				return true
			}
		case *ForStmt:
			if exprCallsSP1Fri(v.Condition) || statementsCallSP1Fri(v.Body) {
				return true
			}
		case ReturnStmt:
			if exprCallsSP1Fri(v.Value) {
				return true
			}
		case *ReturnStmt:
			if exprCallsSP1Fri(v.Value) {
				return true
			}
		}
	}
	return false
}

func exprCallsSP1Fri(e Expression) bool {
	if e == nil {
		return false
	}
	switch v := e.(type) {
	case CallExpr:
		return callExprIsSP1Fri(v)
	case *CallExpr:
		return callExprIsSP1Fri(*v)
	case BinaryExpr:
		return exprCallsSP1Fri(v.Left) || exprCallsSP1Fri(v.Right)
	case *BinaryExpr:
		return exprCallsSP1Fri(v.Left) || exprCallsSP1Fri(v.Right)
	case UnaryExpr:
		return exprCallsSP1Fri(v.Operand)
	case *UnaryExpr:
		return exprCallsSP1Fri(v.Operand)
	}
	return false
}

func callExprIsSP1Fri(c CallExpr) bool {
	switch callee := c.Callee.(type) {
	case Identifier:
		if callee.Name == "verifySP1FRI" {
			return true
		}
	case *Identifier:
		if callee.Name == "verifySP1FRI" {
			return true
		}
	}
	for _, a := range c.Args {
		if exprCallsSP1Fri(a) {
			return true
		}
	}
	return false
}
