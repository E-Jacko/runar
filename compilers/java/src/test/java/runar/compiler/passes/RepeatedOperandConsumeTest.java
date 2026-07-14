package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;
import runar.compiler.Cli;
import runar.compiler.ir.anf.AnfProgram;
import runar.compiler.ir.stack.StackProgram;

/**
 * Repeated-operand consume bug (hand-written ANF via AnfLoader / CLI --ir).
 *
 * <p>Mirrors packages/runar-compiler/src/__tests__/repeated-operand-consume.test.ts.
 *
 * <p>A binding whose ANF value reads the SAME ref at more than one operand
 * position used to make an independent last-use consume decision per load; a
 * consume-mode bringToTop of a ref already on top of the stack is a no-op, so
 * {@code t := x + x} left a single stack slot for OP_ADD (underflow at
 * runtime), or paired the opcode with the wrong slot when the ref was buried.
 * Canonical rule: an operand load may consume (ROLL) its ref only when this
 * binding is the ref's last use AND the ref occurs exactly once in the value's
 * FULL operand list. Repeated refs copy (PICK / DUP) at every position.
 * Unreachable from the frontend (every operand gets a fresh temp); reachable
 * via hand-written IR.
 */
class RepeatedOperandConsumeTest {

    private static String programJson(String params, String body) {
        return """
            {
              "contractName": "Repeat",
              "properties": [{"name": "target", "type": "bigint", "readonly": true}],
              "methods": [
                {
                  "name": "unlock",
                  "params": [%s],
                  "body": [%s],
                  "isPublic": true
                }
              ]
            }
            """.formatted(params, body);
    }

    /** Mirror the CLI --ir --hex --disable-constant-folding pipeline. */
    private static String compileIrToHex(String json) {
        AnfProgram anf = AnfLoader.parse(json);
        anf = Cli.optimizeAnf(anf, true);
        StackProgram stack = StackLower.run(anf);
        StackProgram optimised = Peephole.run(stack);
        return Emit.run(optimised);
    }

    @Test
    void binOpSameRefTwice() {
        // unlock(x) { assert(x + x === target) }
        String json = programJson(
            "{\"name\": \"x\", \"type\": \"bigint\"}",
            """
            {"name": "t0", "value": {"kind": "bin_op", "op": "+", "left": "x", "right": "x"}},
            {"name": "t1", "value": {"kind": "load_prop", "name": "target"}},
            {"name": "t2", "value": {"kind": "bin_op", "op": "===", "left": "t0", "right": "t1"}},
            {"name": "t3", "value": {"kind": "assert", "value": "t2"}}
            """);
        // Both loads of x must COPY: DUP DUP ADD <placeholder OP_0> NUMEQUAL NIP.
        // Cross-tier canonical hex, byte-identical with the TS tier.
        assertEquals("767693009c77", compileIrToHex(json));
    }

    @Test
    void callSameRefInTwoArgPositions() {
        // unlock(x) { assert(min(x, x) === target) }
        String json = programJson(
            "{\"name\": \"x\", \"type\": \"bigint\"}",
            """
            {"name": "t0", "value": {"kind": "call", "func": "min", "args": ["x", "x"]}},
            {"name": "t1", "value": {"kind": "load_prop", "name": "target"}},
            {"name": "t2", "value": {"kind": "bin_op", "op": "===", "left": "t0", "right": "t1"}},
            {"name": "t3", "value": {"kind": "assert", "value": "t2"}}
            """);
        // DUP DUP MIN <placeholder OP_0> NUMEQUAL NIP
        assertEquals("7676a3009c77", compileIrToHex(json));
    }

    @Test
    void repeatedRefBuriedBelowLiveSlot() {
        // unlock(x, y) { assert(x + x + y === target) } — at t0 the stack is
        // [x, y]: x sits at depth 1, so a naive rule pairs OP_ADD with the
        // wrong slot instead of copying x twice.
        String json = programJson(
            "{\"name\": \"x\", \"type\": \"bigint\"}, {\"name\": \"y\", \"type\": \"bigint\"}",
            """
            {"name": "t0", "value": {"kind": "bin_op", "op": "+", "left": "x", "right": "x"}},
            {"name": "t1", "value": {"kind": "bin_op", "op": "+", "left": "t0", "right": "y"}},
            {"name": "t2", "value": {"kind": "load_prop", "name": "target"}},
            {"name": "t3", "value": {"kind": "bin_op", "op": "===", "left": "t1", "right": "t2"}},
            {"name": "t4", "value": {"kind": "assert", "value": "t3"}}
            """);
        // OVER DUP ADD SWAP ADD OP_0 NUMEQUAL NIP — byte-identical with TS.
        assertEquals("7876937c93009c77", compileIrToHex(json));
    }

    @Test
    void distinctRefsUnchanged() {
        // Frontend-shaped ANF (fresh temp per operand) must not shift bytes.
        String json = programJson(
            "{\"name\": \"x\", \"type\": \"bigint\"}",
            """
            {"name": "t0", "value": {"kind": "load_param", "name": "x"}},
            {"name": "t1", "value": {"kind": "load_param", "name": "x"}},
            {"name": "t2", "value": {"kind": "bin_op", "op": "+", "left": "t0", "right": "t1"}},
            {"name": "t3", "value": {"kind": "load_prop", "name": "target"}},
            {"name": "t4", "value": {"kind": "bin_op", "op": "===", "left": "t2", "right": "t3"}},
            {"name": "t5", "value": {"kind": "assert", "value": "t4"}}
            """);
        // DUP SWAP ADD <placeholder OP_0> NUMEQUAL — canonical frontend Dbl shape.
        assertEquals("767c93009c", compileIrToHex(json));
    }
}
