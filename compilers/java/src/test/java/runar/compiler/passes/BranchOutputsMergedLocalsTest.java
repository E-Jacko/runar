package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * A conditional that declares outputs and does ANYTHING ELSE the parent scope
 * can still observe is an unsupported shape and must be a HARD COMPILE ERROR.
 * Port of the TypeScript reference test
 * {@code packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts}.
 *
 * <p>An {@code if} expression carries exactly ONE value. When a branch contains
 * an output intrinsic that value is already spoken for — it is the output concat
 * the continuation hash consumes ({@code appendBranchOutputConcat}). Anything
 * else the arm leaves behind breaks one of two invariants nothing downstream
 * enforces:
 *
 * <ul>
 *   <li>INV-A: the parent registers the if-expression's value as the branch's
 *       contribution to the continuation hash, so "the branch's output bytes"
 *       really means "whatever the arm's LAST binding is".</li>
 *   <li>INV-B: an arm that emits an output AND leaves any other nameable slot —
 *       a second merged local, a property write, a rebound local still read
 *       after the {@code if} — leaves 2+ results against ONE registered
 *       stack-map name.</li>
 * </ul>
 *
 * <p>Before the 2026-08-05 fixes the compiler emitted anyway, so the locking
 * script was permanently unspendable (OP_NUM2BIN / OP_NUMEQUALVERIFY / OP_ADD
 * landing on the wrong slot) — or, quieter, the continuation committed a bare
 * script number where a serialized output belonged and the off-chain interpreter
 * agreed with it.
 *
 * <p>The Java tier raises {@link IllegalStateException} from
 * {@code AnfLower.run}.
 */
class BranchOutputsMergedLocalsTest {

    /**
     * REJECTED: {@code if} with an output intrinsic in each arm, and two locals
     * ({@code na}, {@code nb}) merged ASYMMETRICALLY across the branch — the
     * then-arm reassigns {@code na}, the else-arm reassigns {@code nb}.
     */
    private static final String OUTPUTS_AND_MERGED_LOCALS =
        """
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
        """;

    /**
     * REJECTED (INV-A): each arm emits its output and THEN rebinds a local, so
     * the arm's terminal binding — the one the parent registers as the branch's
     * output bytes — is a bare script number, and the real serialized output is
     * dropped by the residue drain.
     */
    private static final String OUTPUTS_THEN_REBIND =
        """
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
        """;

    /**
     * REJECTED (INV-A, local DEAD after the {@code if}): identical to the above
     * minus the post-{@code if} read. Pins that INV-A is independent of
     * liveness, which is why the predicate cannot be liveness-only.
     */
    private static final String OUTPUTS_THEN_REBIND_DEAD =
        """
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
        """;

    /**
     * REJECTED (INV-A, ZERO merged locals): each arm emits a data output and
     * THEN writes a property, so the receipt bytes are no longer on top and the
     * drain deletes them.
     */
    private static final String OUTPUTS_THEN_PROP_WRITE =
        """
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
        """;

    /**
     * REJECTED (INV-B, ZERO merged locals): the property write comes BEFORE the
     * output, so each arm DOES end with its output intrinsic and the ANF-shape
     * invariant holds — and it is still unrepresentable. This is the case that
     * rules out "arm ends with its output" as a sufficient predicate.
     */
    private static final String PROP_WRITE_THEN_OUTPUTS =
        """
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
        """;

    /**
     * REJECTED (INV-B, K=1): each arm rebinds one local BEFORE its output, and
     * the local is READ after the {@code if}, so add_output picks instead of
     * rolling it and the arm ends two deep against one registered stack-map
     * name.
     */
    private static final String OUTPUTS_WITH_LIVE_REBIND =
        """
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
        """;

    /**
     * ACCEPTED control: the same two asymmetrically merged locals, with the
     * addOutput moved after the {@code if} — the documented workaround, and the
     * shape the guard must NOT fire on.
     */
    private static final String OUTPUTS_AFTER_MERGED_LOCALS =
        """
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
        """;

    /**
     * ACCEPTED control: the live-rebind shape with the local DEAD after the
     * {@code if}, so add_output consumes the arm's own copy on last use and the
     * arm leaves exactly one result.
     */
    private static final String OUTPUTS_WITH_DEAD_REBIND =
        """
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
        """;

    /**
     * ACCEPTED control / baseline: each arm emits its output and touches nothing
     * else. If this ever stops compiling the predicate has been written far too
     * wide.
     */
    private static final String OUTPUTS_ONLY =
        """
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
        """;

    /**
     * ACCEPTED control: a pre-{@code if} local IS live across the {@code if},
     * but it is not one the arms bind.
     */
    private static final String OUTPUTS_WITH_UNRELATED_LIVE_LOCAL =
        """
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
        """;

    /** A shape the compiler must refuse, and the reason clause it must name. */
    private record RejectedCase(String label, String source, String fileName, String reason) {}

    private record AcceptedCase(String label, String source, String fileName) {}

    private static final List<RejectedCase> REJECTED_CASES = List.of(
        new RejectedCase("merges >=2 locals", OUTPUTS_AND_MERGED_LOCALS,
            "OutputsAndMergedLocals.runar.ts", "merges 2 local variables (na, nb)"),
        new RejectedCase("rebinds a local after its output (INV-A)", OUTPUTS_THEN_REBIND,
            "OutputsThenRebind.runar.ts", "continues past its output in the then-branch"),
        new RejectedCase("rebinds a dead local after its output (INV-A)", OUTPUTS_THEN_REBIND_DEAD,
            "OutputsThenRebindDead.runar.ts", "continues past its output in the then-branch"),
        new RejectedCase("writes a property after its output (INV-A)", OUTPUTS_THEN_PROP_WRITE,
            "OutputsThenPropWrite.runar.ts", "continues past its output in the then-branch"),
        new RejectedCase("writes a property before its output (INV-B)", PROP_WRITE_THEN_OUTPUTS,
            "PropWriteThenOutputs.runar.ts", "assigns contract properties (b) inside the branch"),
        new RejectedCase("rebinds a local read after the if (INV-B)", OUTPUTS_WITH_LIVE_REBIND,
            "OutputsWithLiveRebind.runar.ts", "reassigns local variables read after it (na)"));

    private static final List<AcceptedCase> ACCEPTED_CASES = List.of(
        new AcceptedCase("the addOutput moves after the if", OUTPUTS_AFTER_MERGED_LOCALS,
            "OutputsAfterMergedLocals.runar.ts"),
        new AcceptedCase("the rebound local is dead after the if", OUTPUTS_WITH_DEAD_REBIND,
            "OutputsWithDeadRebind.runar.ts"),
        new AcceptedCase("each arm emits its output and nothing else", OUTPUTS_ONLY,
            "OutputsOnly.runar.ts"),
        new AcceptedCase("a live local across the if is not one the arms bind",
            OUTPUTS_WITH_UNRELATED_LIVE_LOCAL, "OutputsWithUnrelatedLiveLocal.runar.ts"));

    @Test
    void conditionalWithOutputsAndExtraResultsIsRejected() {
        for (RejectedCase tc : REJECTED_CASES) {
            IllegalStateException err = assertThrows(
                IllegalStateException.class,
                () -> PipelineTestSupport.hex(tc.source(), tc.fileName()),
                "a conditional that " + tc.label() + " must not compile");

            String msg = String.valueOf(err.getMessage());
            assertTrue(
                msg.contains("Cannot compile conditional that both declares outputs and"),
                "[" + tc.label() + "] expected the branch-outputs diagnostic, got: " + msg);
            assertTrue(msg.contains(tc.reason()),
                "[" + tc.label() + "] diagnostic should name the reason '" + tc.reason()
                    + "', got: " + msg);
            // Only the workaround that actually works is advertised. The
            // rejected sources already give each branch its own complete
            // addOutput, so the old "or give each branch its own complete
            // addOutput" advice was a dead end.
            assertTrue(
                msg.contains(
                    "Move the addOutput/addRawOutput/addDataOutput call after the if-statement"),
                "[" + tc.label() + "] diagnostic should advertise moving the call after the if, "
                    + "got: " + msg);
            assertFalse(msg.contains("give each branch its own complete addOutput"),
                "[" + tc.label() + "] diagnostic must not advertise the dead-end workaround, got: "
                    + msg);
        }
    }

    @Test
    void conditionalWithOutputsAcceptedShapesCompile() throws Exception {
        for (AcceptedCase tc : ACCEPTED_CASES) {
            String hex = PipelineTestSupport.hex(tc.source(), tc.fileName());
            assertNotNull(hex, "[" + tc.label() + "] expected a locking script");
            assertFalse(hex.isEmpty(),
                "[" + tc.label() + "] expected a non-empty locking script");
        }
    }
}
