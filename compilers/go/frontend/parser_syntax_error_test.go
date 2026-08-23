package frontend

import (
	"strings"
	"testing"
)

// Malformed source must be REJECTED, not silently repaired.
//
// tree-sitter is an error-tolerant parser: given `this.value = ;` it still
// returns a tree, marking the bad region with an ERROR node. The Rúnar parser
// walked that tree and, when a statement's operands did not resolve, returned
// nil from the statement parser — and a nil statement is simply not appended.
// The malformed line VANISHED and compilation continued.
//
// Measured on the repro below (audits, Codex second pass): the Go tier emitted
// a complete locking script for a stateful contract whose state update had
// been dropped, while ts / rust / zig / python / ruby / java all rejected it.
// That breaks the frontend-parity invariant in CLAUDE.md, which admits no
// exceptions, and it is a silent miscompile: the dropped statement could as
// easily be an `assert` guarding the spend.
//
// The fix is not to special-case assignment. Any ERROR or MISSING node in the
// tree means the source is not valid Rúnar, so the parser refuses the whole
// file — one check that covers every malformed shape, not just this one.

const emptyAssignmentSrc = `import { StatefulSmartContract, assert } from 'runar-lang';

class EmptyAssignment extends StatefulSmartContract {
  value: bigint;

  constructor(value: bigint) {
    super(value);
    this.value = value;
  }

  public set(next: bigint) {
    this.value = ;
    this.value = next;
    assert(true);
  }
}
`

// The statement that vanished was the state update; here the dropped line is
// the only thing standing between a spender and the contract's funds.
const droppedGuardSrc = `import { SmartContract, assert } from 'runar-lang';

class DroppedGuard extends SmartContract {
  readonly owner: bigint;

  constructor(owner: bigint) {
    super(owner);
    this.owner = owner;
  }

  public spend(claim: bigint) {
    assert(claim ==);
    assert(true);
  }
}
`

func parseErrorsFor(t *testing.T, src, name string) []Diagnostic {
	t.Helper()
	res := ParseSource([]byte(src), name)
	if res == nil {
		t.Fatalf("ParseSource returned nil for %s", name)
	}
	return res.Errors
}

func TestParser_RejectsEmptyAssignment(t *testing.T) {
	errs := parseErrorsFor(t, emptyAssignmentSrc, "EmptyAssignment.runar.ts")
	if len(errs) == 0 {
		t.Fatal("malformed `this.value = ;` was accepted; the statement is silently " +
			"dropped and the tier emits a locking script for a program every other tier rejects")
	}
	if !strings.Contains(strings.ToLower(errs[0].Message), "syntax") {
		t.Fatalf("expected a syntax diagnostic, got %q", errs[0].Message)
	}
}

func TestParser_RejectsMalformedAssert(t *testing.T) {
	errs := parseErrorsFor(t, droppedGuardSrc, "DroppedGuard.runar.ts")
	if len(errs) == 0 {
		t.Fatal("malformed `assert(claim ==)` was accepted; a dropped assert removes " +
			"a spending guard from the emitted script")
	}
}

// A diagnostic that fires on valid sources is worse than none: it would be
// switched off. Every checked-in example must still parse clean.
func TestParser_AcceptsWellFormedSource(t *testing.T) {
	const ok = `import { SmartContract, assert } from 'runar-lang';

class Fine extends SmartContract {
  readonly a: bigint;

  constructor(a: bigint) {
    super(a);
    this.a = a;
  }

  public go(x: bigint) {
    assert(this.a > 0n);
    assert(x > 0n);
  }
}
`
	errs := parseErrorsFor(t, ok, "Fine.runar.ts")
	if len(errs) != 0 {
		t.Fatalf("well-formed source rejected: %v", errs)
	}
}
