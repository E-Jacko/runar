"""A conditional that declares outputs and does ANYTHING ELSE the parent scope
can still observe is an unsupported shape and must be a HARD COMPILE ERROR.

Mirrors packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts.

An ``if`` expression carries exactly ONE value. When a branch contains an output
intrinsic that value is already spoken for -- it is the output concat the
continuation hash consumes (``_append_branch_output_concat``). Anything else the
arm leaves behind breaks one of two invariants nothing downstream enforces:

INV-A
    the parent registers the if-expression's value as the branch's contribution
    to the continuation hash, so "the branch's output bytes" really means
    "whatever the arm's LAST binding is".
INV-B
    an arm that emits an output AND leaves any other nameable slot -- a second
    merged local, a property write, a rebound local still read after the ``if``
    -- leaves 2+ results against ONE registered stack-map name.

Before the 2026-08-05 fixes the compiler emitted anyway, so the locking script
was permanently unspendable (OP_NUM2BIN / OP_NUMEQUALVERIFY / OP_ADD landing on
the wrong slot) -- or, quieter, the continuation committed a bare script number
where a serialized output belonged and the off-chain interpreter agreed with it.

The Python tier raises ``ValueError`` from ``_lower_to_anf``; pass 4 is wrapped,
so it surfaces as an ``ANF lowering error: ...`` error diagnostic.
"""

from __future__ import annotations

import textwrap

import pytest

from runar_compiler.compiler import compile_from_source_str_with_result
from runar_compiler.frontend.diagnostic import Severity


# ---------------------------------------------------------------------------
# Sources (TypeScript surface). Kept byte-identical across all seven tiers.
# ---------------------------------------------------------------------------

# REJECTED: `if` with an output intrinsic in each arm, and two locals (`na`,
# `nb`) merged ASYMMETRICALLY across the branch -- the then-arm reassigns `na`,
# the else-arm reassigns `nb`.
OUTPUTS_AND_MERGED_LOCALS = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# REJECTED (INV-A): each arm emits its output and THEN rebinds a local, so the
# arm's terminal binding -- the one the parent registers as the branch's output
# bytes -- is a bare script number, and the real serialized output is dropped by
# the residue drain.
OUTPUTS_THEN_REBIND = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# REJECTED (INV-A, local DEAD after the `if`): identical to the above minus the
# post-`if` read. Pins that INV-A is independent of liveness, which is why the
# predicate cannot be liveness-only.
OUTPUTS_THEN_REBIND_DEAD = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# REJECTED (INV-A, ZERO merged locals): each arm emits a data output and THEN
# writes a property, so the receipt bytes are no longer on top and the drain
# deletes them.
OUTPUTS_THEN_PROP_WRITE = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';
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
""")

# REJECTED (INV-B, ZERO merged locals): the property write comes BEFORE the
# output, so each arm DOES end with its output intrinsic and the ANF-shape
# invariant holds -- and it is still unrepresentable. This is the case that
# rules out "arm ends with its output" as a sufficient predicate.
PROP_WRITE_THEN_OUTPUTS = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';
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
""")

# REJECTED (INV-B, K=1): each arm rebinds one local BEFORE its output, and the
# local is READ after the `if`, so add_output picks instead of rolling it and the
# arm ends two deep against one registered stack-map name.
OUTPUTS_WITH_LIVE_REBIND = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# ACCEPTED control: the same two asymmetrically merged locals, with the
# addOutput moved after the `if` -- the documented workaround, and the shape the
# guard must NOT fire on.
OUTPUTS_AFTER_MERGED_LOCALS = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# ACCEPTED control: the live-rebind shape with the local DEAD after the `if`, so
# add_output consumes the arm's own copy on last use and the arm leaves exactly
# one result.
OUTPUTS_WITH_DEAD_REBIND = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# ACCEPTED control / baseline: each arm emits its output and touches nothing
# else. If this ever stops compiling the predicate has been written far too wide.
OUTPUTS_ONLY = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")

# ACCEPTED control: a pre-`if` local IS live across the `if`, but it is not one
# the arms bind.
OUTPUTS_WITH_UNRELATED_LIVE_LOCAL = textwrap.dedent("""\
    import { StatefulSmartContract, assert } from 'runar-lang';

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
""")


REJECTED_CASES = [
    ("merges >=2 locals", OUTPUTS_AND_MERGED_LOCALS, "OutputsAndMergedLocals.runar.ts",
     "merges 2 local variables (na, nb)"),
    ("rebinds a local after its output (INV-A)", OUTPUTS_THEN_REBIND,
     "OutputsThenRebind.runar.ts", "continues past its output in the then-branch"),
    ("rebinds a dead local after its output (INV-A)", OUTPUTS_THEN_REBIND_DEAD,
     "OutputsThenRebindDead.runar.ts", "continues past its output in the then-branch"),
    ("writes a property after its output (INV-A)", OUTPUTS_THEN_PROP_WRITE,
     "OutputsThenPropWrite.runar.ts", "continues past its output in the then-branch"),
    ("writes a property before its output (INV-B)", PROP_WRITE_THEN_OUTPUTS,
     "PropWriteThenOutputs.runar.ts", "assigns contract properties (b) inside the branch"),
    ("rebinds a local read after the if (INV-B)", OUTPUTS_WITH_LIVE_REBIND,
     "OutputsWithLiveRebind.runar.ts", "reassigns local variables read after it (na)"),
]

ACCEPTED_CASES = [
    ("the addOutput moves after the if", OUTPUTS_AFTER_MERGED_LOCALS,
     "OutputsAfterMergedLocals.runar.ts"),
    ("the rebound local is dead after the if", OUTPUTS_WITH_DEAD_REBIND,
     "OutputsWithDeadRebind.runar.ts"),
    ("each arm emits its output and nothing else", OUTPUTS_ONLY, "OutputsOnly.runar.ts"),
    ("a live local across the if is not one the arms bind",
     OUTPUTS_WITH_UNRELATED_LIVE_LOCAL, "OutputsWithUnrelatedLiveLocal.runar.ts"),
]


def _error_text(result) -> str:
    return "\n".join(
        d.message for d in result.diagnostics if d.severity == Severity.ERROR
    )


class TestBranchOutputsMergedLocals:
    @pytest.mark.parametrize(
        "label,source,file_name,reason",
        REJECTED_CASES,
        ids=[c[0] for c in REJECTED_CASES],
    )
    def test_conditional_with_outputs_and_extra_results_is_rejected(
        self, label, source, file_name, reason
    ):
        result = compile_from_source_str_with_result(source, file_name)

        assert not result.success
        assert result.artifact is None

        msg = _error_text(result)
        assert "Cannot compile conditional that both declares outputs and" in msg, msg
        assert reason in msg, msg
        # Only the workaround that actually works is advertised. The rejected
        # sources already give each branch its own complete addOutput, so the old
        # "or give each branch its own complete addOutput" advice was a dead end.
        assert (
            "Move the addOutput/addRawOutput/addDataOutput call after the if-statement"
            in msg
        ), msg
        assert "give each branch its own complete addOutput" not in msg, msg

    @pytest.mark.parametrize(
        "label,source,file_name",
        ACCEPTED_CASES,
        ids=[c[0] for c in ACCEPTED_CASES],
    )
    def test_conditional_with_outputs_accepted_shapes_compile(
        self, label, source, file_name
    ):
        result = compile_from_source_str_with_result(source, file_name)

        assert result.success, _error_text(result)
        assert result.script_hex
