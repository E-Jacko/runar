package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import org.junit.jupiter.api.Test;
import runar.compiler.Cli;
import runar.compiler.frontend.ParserDispatch;
import runar.compiler.ir.anf.AnfProgram;
import runar.compiler.ir.ast.ContractNode;
import runar.compiler.ir.stack.OpcodeOp;
import runar.compiler.ir.stack.PushOp;
import runar.compiler.ir.stack.PushValue;
import runar.compiler.ir.stack.RollOp;
import runar.compiler.ir.stack.StackOp;
import runar.compiler.ir.stack.StackProgram;

/**
 * Regression test for deep-review finding C17 (unsound {@code not-not-elim}).
 *
 * <p>{@code OP_NOT OP_NOT} is boolean NORMALISATION, not numeric identity: for a
 * non-canonical operand (say 5) the pair yields 1, while deleting it leaves 5.
 * Truthiness survives, the VALUE does not — and a downstream {@code OP_EQUAL} /
 * {@code OP_NUMEQUAL} consumes the value, so the optimised and unoptimised
 * programs disagree on accept/reject.
 *
 * <p>The old rule was an unguarded 2-op window. Composed with the sibling
 * {@code PUSH 0; OP_NUMEQUAL → OP_NOT} rewrite — which manufactures a fresh
 * {@code OP_NOT} sitting on an ARBITRARY script number — it collapsed
 * {@code x !== 0n} all the way down to {@code x}: the fold-OFF script
 * {@code 007c7c9c91517c7c9c} optimised to {@code 519c} (compare the witness
 * against 1 instead of against "x is non-zero"), rejecting the valid spend
 * {@code x = 5}.
 *
 * <p>The rule is now a 3-op window that includes the PRODUCER of the negated
 * value and only fires when that producer provably leaves a canonical 0/1.
 */
class C17NotNotGuardTest {

    /** The boolean is consumed by value (=== true), so the collapse is observable. */
    private static final String SRC =
        "import { SmartContract, assert } from 'runar-lang';\n"
        + "class C17Check extends SmartContract {\n"
        + "  constructor() { super(); }\n"
        + "  public check(x: bigint): void { assert((x !== 0n) === true); }\n"
        + "}\n";

    private static StackProgram lower(String src, String file) throws Exception {
        ContractNode contract = ParserDispatch.parse(src, file);
        Validate.run(contract);
        contract = ExpandFixedArrays.run(contract);
        Typecheck.run(contract);
        AnfProgram anf = AnfLower.run(contract);
        anf = Cli.optimizeAnf(anf, true); // fold-OFF, matching the conformance goldens
        return StackLower.run(anf);
    }

    /**
     * End-to-end: with the peephole ON the emitted script must still compute
     * "x is non-zero" rather than degenerating into "x". The unguarded rule
     * produced {@code 519c}; the guarded one keeps the {@code OP_NOT OP_NOT}
     * normalisation as {@code 9191519c}.
     */
    @Test
    void notEqualsZeroSurvivesThePeephole() throws Exception {
        StackProgram raw = lower(SRC, "C17Check.runar.ts");
        String foldOffPeepholeOff = Emit.run(raw);
        String foldOffPeepholeOn = Emit.run(Peephole.run(raw));

        assertEquals("007c7c9c91517c7c9c", foldOffPeepholeOff,
            "baseline (peephole OFF) must be PUSH0 SWAP SWAP NUMEQUAL NOT PUSH1 SWAP SWAP NUMEQUAL");
        assertEquals("9191519c", foldOffPeepholeOn,
            "peephole ON must keep the OP_NOT OP_NOT boolean normalisation (C17)");
    }

    /** The same statement, at the Stack-IR level: the NOT pair must survive. */
    @Test
    void peepholeKeepsTheNotPairInLoweredOps() throws Exception {
        List<StackOp> ops = Peephole.optimize(lower(SRC, "C17Check.runar.ts").methods().get(0).ops());
        long nots = ops.stream().filter(o -> o instanceof OpcodeOp c && "OP_NOT".equals(c.code())).count();
        assertEquals(2, nots, "both OP_NOTs must remain — deleting them changes the compared VALUE");
    }

    /**
     * Guard: the producer is a stack shuffle, so its provenance is invisible to
     * this local window. The pair must survive.
     */
    @Test
    void nonCanonicalProducerKeepsTheNotPair() {
        List<StackOp> r = Peephole.optimize(List.of(
            new RollOp(3), new OpcodeOp("OP_NOT"), new OpcodeOp("OP_NOT")));
        assertEquals(3, r.size(), "OP_NOT OP_NOT over a rolled (arbitrary) value must not be deleted");
        assertTrue(r.get(1) instanceof OpcodeOp a && "OP_NOT".equals(a.code()));
        assertTrue(r.get(2) instanceof OpcodeOp b && "OP_NOT".equals(b.code()));
    }

    /** Guard: a bare pair with no visible producer is equally unprovable. */
    @Test
    void bareNotPairWithNoVisibleProducerSurvives() {
        List<StackOp> r = Peephole.optimize(List.of(new OpcodeOp("OP_NOT"), new OpcodeOp("OP_NOT")));
        assertEquals(2, r.size());
    }

    /**
     * NEGATIVE case — the rule must not become dead. A provably canonical
     * producer still gets its redundant normalisation removed.
     */
    @Test
    void canonicalProducerStillCollapses() {
        for (String producer : new String[] {
            "OP_EQUAL", "OP_NUMEQUAL", "OP_NUMNOTEQUAL", "OP_LESSTHAN", "OP_GREATERTHAN",
            "OP_LESSTHANOREQUAL", "OP_GREATERTHANOREQUAL", "OP_BOOLAND", "OP_BOOLOR",
            "OP_WITHIN", "OP_NOT", "OP_0NOTEQUAL", "OP_CHECKSIG", "OP_CHECKMULTISIG"
        }) {
            List<StackOp> r = Peephole.optimize(List.of(
                new OpcodeOp(producer), new OpcodeOp("OP_NOT"), new OpcodeOp("OP_NOT")));
            assertEquals(1, r.size(), producer + " leaves a canonical bool — the NOT pair is redundant");
            assertTrue(r.get(0) instanceof OpcodeOp o && producer.equals(o.code()));
        }
    }

    /** Literal boolean / 0 / 1 pushes are canonical producers too. */
    @Test
    void canonicalLiteralPushesStillCollapse() {
        for (PushValue v : new PushValue[] {
            PushValue.of(true), PushValue.of(false), PushValue.of(0), PushValue.of(1)
        }) {
            List<StackOp> r = Peephole.optimize(List.of(
                new PushOp(v), new OpcodeOp("OP_NOT"), new OpcodeOp("OP_NOT")));
            assertEquals(1, r.size(), v + " is already canonical");
            assertTrue(r.get(0) instanceof PushOp);
        }
    }

    /** A non-canonical literal push must keep the pair (PUSH 5 NOT NOT != PUSH 5). */
    @Test
    void nonCanonicalLiteralPushKeepsTheNotPair() {
        List<StackOp> r = Peephole.optimize(List.of(
            new PushOp(PushValue.of(5)), new OpcodeOp("OP_NOT"), new OpcodeOp("OP_NOT")));
        assertEquals(3, r.size(), "PUSH 5 OP_NOT OP_NOT yields 1, not 5");
    }

    /**
     * The exact composition that made this a bug: the sibling
     * {@code PUSH 0; OP_NUMEQUAL → OP_NOT} rewrite must not hand the unguarded
     * rule a second OP_NOT to eat.
     */
    @Test
    void push0NumequalNotChainKeepsBothNots() {
        List<StackOp> r = Peephole.optimize(List.of(
            new RollOp(3),
            new PushOp(PushValue.of(0)),
            new OpcodeOp("OP_NUMEQUAL"),
            new OpcodeOp("OP_NOT")));
        assertEquals(3, r.size(), "expected Roll(3) OP_NOT OP_NOT, got " + r);
        assertTrue(r.get(0) instanceof RollOp);
        assertTrue(r.get(1) instanceof OpcodeOp a && "OP_NOT".equals(a.code()));
        assertTrue(r.get(2) instanceof OpcodeOp b && "OP_NOT".equals(b.code()));
    }
}
