//! A conditional that declares outputs and does ANYTHING ELSE the parent scope
//! can still observe is an unsupported shape and must be a HARD COMPILE ERROR.
//! Port of the TypeScript reference test
//! `packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts`.
//!
//! An `if` expression carries exactly ONE value. When a branch contains an
//! output intrinsic that value is already spoken for — it is the output concat
//! the continuation hash consumes (`append_branch_output_concat`). Anything else
//! the arm leaves behind breaks one of two invariants nothing downstream
//! enforces:
//!
//!   - INV-A: the parent registers the if-expression's value as the branch's
//!     contribution to the continuation hash, so "the branch's output bytes"
//!     really means "whatever the arm's LAST binding is".
//!   - INV-B: an arm that emits an output AND leaves any other nameable slot — a
//!     second merged local, a property write, a rebound local still read after
//!     the `if` — leaves 2+ results against ONE registered stack-map name.
//!
//! Before the 2026-08-05 fixes the compiler emitted anyway, so the locking
//! script was permanently unspendable (OP_NUM2BIN / OP_NUMEQUALVERIFY / OP_ADD
//! landing on the wrong slot) — or, quieter, the continuation committed a bare
//! script number where a serialized output belonged and the off-chain
//! interpreter agreed with it.
//!
//! The Rust tier raises the refusal as a `panic!` out of
//! `anf_lower::lower_to_anf`. `anf_lower::try_lower_to_anf` is the pass-4
//! `catch_unwind` boundary — the same wrapper idiom `codegen::stack::
//! lower_to_stack` uses for pass 5 — so the refusal reaches the caller as an
//! ordinary `Err(String)` / diagnostic carrying the original message. These
//! tests pin that: an escaping panic is a test failure, not the expected
//! behaviour.

use runar_compiler_rust::{
    compile_from_source_str_with_options, compile_from_source_str_with_result, CompileOptions,
};

/// REJECTED: `if` with an output intrinsic in each arm, and two locals (`na`,
/// `nb`) merged ASYMMETRICALLY across the branch — the then-arm reassigns
/// `na`, the else-arm reassigns `nb`.
const OUTPUTS_AND_MERGED_LOCALS: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// REJECTED (INV-A): each arm emits its output and THEN rebinds a local, so the
/// arm's terminal binding — the one the parent registers as the branch's output
/// bytes — is a bare script number, and the real serialized output is dropped by
/// the residue drain.
const OUTPUTS_THEN_REBIND: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// REJECTED (INV-A, local DEAD after the `if`): identical to the above minus the
/// post-`if` read. Pins that INV-A is independent of liveness, which is why the
/// predicate cannot be liveness-only.
const OUTPUTS_THEN_REBIND_DEAD: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// REJECTED (INV-A, ZERO merged locals): each arm emits a data output and THEN
/// writes a property, so the receipt bytes are no longer on top and the drain
/// deletes them.
const OUTPUTS_THEN_PROP_WRITE: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';
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
"#;

/// REJECTED (INV-B, ZERO merged locals): the property write comes BEFORE the
/// output, so each arm DOES end with its output intrinsic and the ANF-shape
/// invariant holds — and it is still unrepresentable. This is the case that
/// rules out "arm ends with its output" as a sufficient predicate.
const PROP_WRITE_THEN_OUTPUTS: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';
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
"#;

/// REJECTED (INV-B, K=1): each arm rebinds one local BEFORE its output, and the
/// local is READ after the `if`, so `add_output` picks instead of rolling it and
/// the arm ends two deep against one registered stack-map name.
const OUTPUTS_WITH_LIVE_REBIND: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// ACCEPTED control: the same two asymmetrically merged locals, with the
/// `addOutput` moved after the `if` — the documented workaround, and the shape
/// the guard must NOT fire on.
const OUTPUTS_AFTER_MERGED_LOCALS: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// ACCEPTED control: the live-rebind shape with the local DEAD after the `if`,
/// so `add_output` consumes the arm's own copy on last use and the arm leaves
/// exactly one result.
const OUTPUTS_WITH_DEAD_REBIND: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// ACCEPTED control / baseline: each arm emits its output and touches nothing
/// else. If this ever stops compiling the predicate has been written far too
/// wide.
const OUTPUTS_ONLY: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// ACCEPTED control: a pre-`if` local IS live across the `if`, but it is not one
/// the arms bind.
const OUTPUTS_WITH_UNRELATED_LIVE_LOCAL: &str = r#"import { StatefulSmartContract, assert } from 'runar-lang';

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
"#;

/// Run `f` with the default panic hook silenced. `catch_unwind` does not stop
/// the hook from printing the payload, and pass 4 raises its refusal as a
/// panic, so every path below would otherwise spray the test log.
fn quietly<T>(f: impl FnOnce() -> T) -> T {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = f();
    std::panic::set_hook(previous);
    out
}

/// Compile and report the joined error diagnostics, `None` when the source
/// compiled cleanly. A panic escaping the pipeline fails outright: a pass-4
/// refusal must reach the caller as a diagnostic, exactly like the pass-5 /
/// pass-6 refusals beside it.
fn compile_failure(source: &str, file_name: &str) -> Option<String> {
    let opts = CompileOptions::default();
    let caught = quietly(|| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compile_from_source_str_with_result(source, Some(file_name), &opts)
        }))
    });

    let result = caught.unwrap_or_else(|payload| {
        let text = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&'static str>().map(|s| (*s).to_string()))
            .unwrap_or_else(|| "<non-string panic payload>".to_string());
        panic!("compile panicked out of the pipeline instead of reporting a diagnostic: {text}");
    });

    if result.success {
        None
    } else {
        Some(
            result
                .diagnostics
                .iter()
                .map(|d| d.message.clone())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

#[test]
fn conditional_with_outputs_and_extra_results_is_rejected() {
    // (label, source, file name, reason clause the diagnostic must name)
    let cases: [(&str, &str, &str, &str); 6] = [
        (
            "merges >=2 locals",
            OUTPUTS_AND_MERGED_LOCALS,
            "OutputsAndMergedLocals.runar.ts",
            "merges 2 local variables (na, nb)",
        ),
        (
            "rebinds a local after its output (INV-A)",
            OUTPUTS_THEN_REBIND,
            "OutputsThenRebind.runar.ts",
            "continues past its output in the then-branch",
        ),
        (
            "rebinds a dead local after its output (INV-A)",
            OUTPUTS_THEN_REBIND_DEAD,
            "OutputsThenRebindDead.runar.ts",
            "continues past its output in the then-branch",
        ),
        (
            "writes a property after its output (INV-A)",
            OUTPUTS_THEN_PROP_WRITE,
            "OutputsThenPropWrite.runar.ts",
            "continues past its output in the then-branch",
        ),
        (
            "writes a property before its output (INV-B)",
            PROP_WRITE_THEN_OUTPUTS,
            "PropWriteThenOutputs.runar.ts",
            "assigns contract properties (b) inside the branch",
        ),
        (
            "rebinds a local read after the if (INV-B)",
            OUTPUTS_WITH_LIVE_REBIND,
            "OutputsWithLiveRebind.runar.ts",
            "reassigns local variables read after it (na)",
        ),
    ];

    for (label, source, file_name, reason) in cases {
        let msg = compile_failure(source, file_name)
            .unwrap_or_else(|| panic!("a conditional that {label} must not compile"));
        assert!(
            msg.contains("Cannot compile conditional that both declares outputs and"),
            "[{label}] expected the branch-outputs diagnostic, got: {msg}"
        );
        assert!(
            msg.contains(reason),
            "[{label}] diagnostic should name the reason {reason:?}, got: {msg}"
        );
        // Only the workaround that actually works is advertised. The rejected
        // sources already give each branch its own complete addOutput, so the
        // old "or give each branch its own complete addOutput" advice was a
        // dead end.
        assert!(
            msg.contains(
                "Move the addOutput/addRawOutput/addDataOutput call after the if-statement"
            ),
            "[{label}] diagnostic should advertise moving the call after the if, got: {msg}"
        );
        assert!(
            !msg.contains("give each branch its own complete addOutput"),
            "[{label}] diagnostic must not advertise the dead-end workaround, got: {msg}"
        );
        // ...and is attributed to the pass that raised it, matching the
        // "stack lowering: " / "emit: " prefixes beside it.
        assert!(
            msg.contains("anf lowering: "),
            "[{label}] diagnostic should be attributed to ANF lowering, got: {msg}"
        );
    }
}

/// The CLI compiles through `compile_from_source_str_with_options` (see
/// `src/main.rs`), not through the diagnostic-collecting `*_with_result`, so
/// that path must surface the refusal as an ordinary `Err` too — never as an
/// unwind that aborts the process.
#[test]
fn conditional_with_outputs_and_merged_locals_fails_cli_path() {
    let opts = CompileOptions::default();
    let caught = quietly(|| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compile_from_source_str_with_options(
                OUTPUTS_AND_MERGED_LOCALS,
                Some("OutputsAndMergedLocals.runar.ts"),
                &opts,
            )
        }))
    });

    let result = caught
        .unwrap_or_else(|_| panic!("compile panicked out of the CLI path instead of returning Err"));
    let err = result.expect_err("the CLI path must reject the outputs+merged-locals conditional");
    assert!(
        err.contains("both declares outputs and merges"),
        "expected the merged-locals-with-outputs message, got: {err}"
    );
    assert!(
        err.contains("(na, nb)"),
        "error should name the merged locals (na, nb), got: {err}"
    );
}

#[test]
fn conditional_with_outputs_accepted_shapes_compile() {
    let cases: [(&str, &str, &str); 4] = [
        (
            "the addOutput moves after the if",
            OUTPUTS_AFTER_MERGED_LOCALS,
            "OutputsAfterMergedLocals.runar.ts",
        ),
        (
            "the rebound local is dead after the if",
            OUTPUTS_WITH_DEAD_REBIND,
            "OutputsWithDeadRebind.runar.ts",
        ),
        (
            "each arm emits its output and nothing else",
            OUTPUTS_ONLY,
            "OutputsOnly.runar.ts",
        ),
        (
            "a live local across the if is not one the arms bind",
            OUTPUTS_WITH_UNRELATED_LIVE_LOCAL,
            "OutputsWithUnrelatedLiveLocal.runar.ts",
        ),
    ];

    for (label, source, file_name) in cases {
        let opts = CompileOptions::default();
        let result = compile_from_source_str_with_result(source, Some(file_name), &opts);
        assert!(
            result.success,
            "[{label}] this shape must compile; diagnostics: {:?}",
            result
                .diagnostics
                .iter()
                .map(|d| d.message.clone())
                .collect::<Vec<_>>()
        );
        assert!(
            result.script_hex.is_some_and(|h| !h.is_empty()),
            "[{label}] expected a non-empty locking script for the accepted control"
        );
    }
}
