package compiler

// Port of the TypeScript reference test
// packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts.
//
// A conditional that declares outputs and does ANYTHING ELSE the parent scope
// can still observe is an unsupported shape and must be a HARD COMPILE ERROR.
//
// An `if` expression carries exactly ONE value. When a branch contains an
// output intrinsic that value is already spoken for — it is the output concat
// the continuation hash consumes (appendBranchOutputConcat). Anything else the
// arm leaves behind breaks one of two invariants nothing downstream enforces:
//
//	INV-A  the parent registers the if-expression's value as the branch's
//	       contribution to the continuation hash, so "the branch's output bytes"
//	       really means "whatever the arm's LAST binding is".
//	INV-B  an arm that emits an output AND leaves any other nameable slot — a
//	       second merged local, a property write, a rebound local still read
//	       after the `if` — leaves 2+ results against ONE registered stackMap
//	       name.
//
// Before the 2026-08-05 fixes the compiler emitted anyway, so the locking script
// was permanently unspendable — or, quieter, the continuation committed a bare
// script number where a serialized output belonged and the off-chain
// interpreter agreed with it.
//
// The Go tier raises the refusal as a panic out of frontend.LowerToANF. Pass 4
// is wrapped by lowerToANFRecovering, so the refusal reaches the user as an
// ordinary error / diagnostic carrying the original message — the same shape as
// the pass-5 and pass-6 refusals beside it. These tests pin that: an escaping
// panic is a test failure, not the expected behaviour.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/icellan/runar/compilers/go/frontend"
)

// REJECTED: `if` with an output intrinsic in each arm, and two locals (`na`,
// `nb`) merged ASYMMETRICALLY across the branch — the then-arm reassigns `na`,
// the else-arm reassigns `nb`.
const outputsAndMergedLocalsSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsAndMergedLocals extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, nb);
    } else {
      nb = bidAmount;
      this.addOutput(bidAmount, this.closed, na, nb);
    }
  }
}
`

// REJECTED (INV-A): each arm emits its output and THEN rebinds a local, so the
// arm's terminal binding — the one the parent registers as the branch's output
// bytes — is a bare script number, and the real serialized output is dropped by
// the residue drain.
const outputsThenRebindSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsThenRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
    assert(na > 0n);
  }
}
`

// REJECTED (INV-A, local DEAD after the `if`): identical to the above minus the
// post-`if` read. Pins that INV-A is independent of liveness, which is why the
// predicate cannot be liveness-only.
const outputsThenRebindDeadSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsThenRebindDead extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
  }
}
`

// REJECTED (INV-A, ZERO merged locals): each arm emits a data output and THEN
// writes a property, so the receipt bytes are no longer on top and the drain
// deletes them.
const outputsThenPropWriteSource = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class OutputsThenPropWrite extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public pay(payload: ByteString): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.addDataOutput(0n, payload);
      this.b = 1n;
    } else {
      this.addDataOutput(0n, payload);
      this.b = 2n;
    }
    this.a = this.a + 1n;
  }
}
`

// REJECTED (INV-B, ZERO merged locals): the property write comes BEFORE the
// output, so each arm DOES end with its output intrinsic and the ANF-shape
// invariant holds — and it is still unrepresentable. This is the case that
// rules out "arm ends with its output" as a sufficient predicate.
const propWriteThenOutputsSource = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class PropWriteThenOutputs extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public pay(payload: ByteString): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.b = 1n;
      this.addDataOutput(0n, payload);
    } else {
      this.b = 2n;
      this.addDataOutput(0n, payload);
    }
    this.a = this.a + 1n;
  }
}
`

// REJECTED (INV-B, K=1): each arm rebinds one local BEFORE its output, and the
// local is READ after the `if`, so add_output picks instead of rolling it and
// the arm ends two deep against one registered stackMap name.
const outputsWithLiveRebindSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithLiveRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(na === bidAmount);
  }
}
`

// ACCEPTED control: the same two asymmetrically merged locals, with the
// addOutput moved after the `if` — the documented workaround, and the shape the
// guard must NOT fire on.
const outputsAfterMergedLocalsSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsAfterMergedLocals extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a === 0n) {
      na = bidAmount;
    } else {
      nb = bidAmount;
    }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`

// ACCEPTED control: the live-rebind shape with the local DEAD after the `if`,
// so add_output consumes the arm's own copy on last use and the arm leaves
// exactly one result.
const outputsWithDeadRebindSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithDeadRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
  }
}
`

// ACCEPTED control / baseline: each arm emits its output and touches nothing
// else. If this ever stops compiling the predicate has been written far too
// wide.
const outputsOnlySource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsOnly extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
    }
  }
}
`

// ACCEPTED control: a pre-`if` local IS live across the `if`, but it is not one
// the arms bind.
const outputsWithUnrelatedLiveLocalSource = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithUnrelatedLiveLocal extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let guard = this.closed;
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(guard === 0n);
  }
}
`

// compileMergedLocalsErrors runs a full source compile and reports the joined
// error-severity diagnostics ("" when the source compiled cleanly). A panic
// escaping the pipeline fails the test outright: a pass-4 refusal must reach the
// caller as a diagnostic, exactly like the pass-5 / pass-6 refusals beside it.
func compileMergedLocalsErrors(t *testing.T, source, fileName string) string {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("ANF lowering panicked out of the compiler instead of reporting a diagnostic: %v", r)
		}
	}()

	result := CompileFromSourceStrWithResult(source, fileName)
	var errs []string
	for _, d := range result.Diagnostics {
		if d.Severity == frontend.SeverityError {
			errs = append(errs, d.Message)
		}
	}
	if len(errs) > 0 && result.Success {
		t.Fatal("result reported Success alongside error-severity diagnostics")
	}
	return strings.Join(errs, "\n")
}

func TestConditionalWithOutputsAndExtraResultsIsRejected(t *testing.T) {
	cases := []struct {
		label    string
		source   string
		fileName string
		reason   string
	}{
		{"merges >=2 locals", outputsAndMergedLocalsSource, "OutputsAndMergedLocals.runar.ts",
			"merges 2 local variables (na, nb)"},
		{"rebinds a local after its output (INV-A)", outputsThenRebindSource, "OutputsThenRebind.runar.ts",
			"continues past its output in the then-branch"},
		{"rebinds a dead local after its output (INV-A)", outputsThenRebindDeadSource, "OutputsThenRebindDead.runar.ts",
			"continues past its output in the then-branch"},
		{"writes a property after its output (INV-A)", outputsThenPropWriteSource, "OutputsThenPropWrite.runar.ts",
			"continues past its output in the then-branch"},
		{"writes a property before its output (INV-B)", propWriteThenOutputsSource, "PropWriteThenOutputs.runar.ts",
			"assigns contract properties (b) inside the branch"},
		{"rebinds a local read after the if (INV-B)", outputsWithLiveRebindSource, "OutputsWithLiveRebind.runar.ts",
			"reassigns local variables read after it (na)"},
	}

	for _, tc := range cases {
		t.Run(tc.label, func(t *testing.T) {
			msg := compileMergedLocalsErrors(t, tc.source, tc.fileName)
			if msg == "" {
				t.Fatalf("expected a compile failure for a conditional that %s", tc.label)
			}
			if !strings.Contains(msg, "Cannot compile conditional that both declares outputs and") {
				t.Errorf("expected the branch-outputs diagnostic, got: %s", msg)
			}
			if !strings.Contains(msg, tc.reason) {
				t.Errorf("diagnostic should name the reason %q, got: %s", tc.reason, msg)
			}
			// Only the workaround that actually works is advertised. The rejected
			// sources already give each branch its own complete addOutput, so the
			// old "or give each branch its own complete addOutput" advice was a
			// dead end.
			if !strings.Contains(msg, "Move the addOutput/addRawOutput/addDataOutput call after the if-statement") {
				t.Errorf("diagnostic should advertise moving the call after the if, got: %s", msg)
			}
			if strings.Contains(msg, "give each branch its own complete addOutput") {
				t.Errorf("diagnostic must not advertise the dead-end workaround, got: %s", msg)
			}
			// ...and attributes it to the pass that raised it, matching the
			// "stack lowering panic: " / "emit panic: " wording beside it.
			if !strings.Contains(msg, "anf lowering panic: ") {
				t.Errorf("diagnostic should be attributed to ANF lowering, got: %s", msg)
			}
		})
	}
}

// The CLI compiles through CompileFromSource (see compilers/go/main.go), not
// through the *WithResult diagnostic collectors, so that path must surface the
// refusal as an ordinary error too — never as an unrecovered panic + stack
// trace.
func TestConditionalWithOutputsAndMergedLocalsFailsCLIPath(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "OutputsAndMergedLocals.runar.ts")
	if err := os.WriteFile(path, []byte(outputsAndMergedLocalsSource), 0o600); err != nil {
		t.Fatalf("writing temp source: %v", err)
	}

	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("CompileFromSource panicked instead of returning an error: %v", r)
		}
	}()

	artifact, err := CompileFromSource(path)
	if err == nil {
		t.Fatal("expected CompileFromSource to reject the outputs+merged-locals conditional")
	}
	if artifact != nil {
		t.Error("expected no artifact for a rejected contract")
	}
	if !strings.Contains(err.Error(), "both declares outputs and merges") {
		t.Errorf("expected the merged-locals-with-outputs message, got: %v", err)
	}
	if !strings.Contains(err.Error(), "(na, nb)") {
		t.Errorf("error should name the merged locals (na, nb), got: %v", err)
	}

	// CompileSourceToIR (the --emit-ir path) stops at pass 4, so it is the one
	// entry point where the refusal is the *only* thing that can go wrong.
	program, irErr := CompileSourceToIR(path)
	if irErr == nil {
		t.Fatal("expected CompileSourceToIR to reject the outputs+merged-locals conditional")
	}
	if program != nil {
		t.Error("expected no ANF program for a rejected contract")
	}
	if !strings.Contains(irErr.Error(), "(na, nb)") {
		t.Errorf("CompileSourceToIR error should name the merged locals (na, nb), got: %v", irErr)
	}
}

func TestConditionalWithOutputsAcceptedShapesCompile(t *testing.T) {
	cases := []struct {
		label    string
		source   string
		fileName string
	}{
		{"the addOutput moves after the if", outputsAfterMergedLocalsSource, "OutputsAfterMergedLocals.runar.ts"},
		{"the rebound local is dead after the if", outputsWithDeadRebindSource, "OutputsWithDeadRebind.runar.ts"},
		{"each arm emits its output and nothing else", outputsOnlySource, "OutputsOnly.runar.ts"},
		{"a live local across the if is not one the arms bind", outputsWithUnrelatedLiveLocalSource,
			"OutputsWithUnrelatedLiveLocal.runar.ts"},
	}

	for _, tc := range cases {
		t.Run(tc.label, func(t *testing.T) {
			msg := compileMergedLocalsErrors(t, tc.source, tc.fileName)
			if msg != "" {
				t.Fatalf("this shape must compile, got: %s", msg)
			}

			result := CompileFromSourceStrWithResult(tc.source, tc.fileName)
			if !result.Success {
				t.Fatal("expected success for the accepted control")
			}
			if result.Artifact == nil || result.Artifact.Script == "" {
				t.Fatal("expected a non-empty locking script for the accepted control")
			}
		})
	}
}
