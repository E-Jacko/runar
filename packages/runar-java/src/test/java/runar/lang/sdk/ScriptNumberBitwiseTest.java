package runar.lang.sdk;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Truth table pinning the ANF interpreter's bigint {@code & | ^ ~ << >>} to
 * Bitcoin Script byte-array semantics.
 *
 * <p>These operators compile to OP_AND/OP_OR/OP_XOR/OP_INVERT/OP_LSHIFT/
 * OP_RSHIFT, which operate on the operands' MINIMAL script-number bytes, not
 * their numeric value (AND/OR/XOR require equal-length operands and abort
 * otherwise; shifts preserve byte length; negative shifts abort). The
 * interpreter must agree with the deployed script byte-for-byte, so the naive
 * native {@code BigInteger} results (255&lt;&lt;1 == 510, ~5 == -6, 255&amp;1 == 1)
 * are wrong. Mirrors the TS reference
 * {@code packages/runar-testing/src/vm/utils.ts scriptNumber*} +
 * {@code packages/runar-testing/src/__tests__/script-number-bitwise.test.ts}.
 */
class ScriptNumberBitwiseTest {

    private static BigInteger v(long n) {
        return BigInteger.valueOf(n);
    }

    @Test
    void leftShift() {
        assertEquals(v(254), AnfInterpreter.scriptNumberShift("<<", v(255), v(1))); // NOT 510
        assertEquals(v(512), AnfInterpreter.scriptNumberShift("<<", v(256), v(1)));
        assertEquals(v(40),  AnfInterpreter.scriptNumberShift("<<", v(5),   v(3)));
    }

    @Test
    void rightShift() {
        assertEquals(v(4),    AnfInterpreter.scriptNumberShift(">>", v(32),  v(3)));
        assertEquals(v(-127), AnfInterpreter.scriptNumberShift(">>", v(255), v(1)));
    }

    @Test
    void invert() {
        assertEquals(v(-122),   AnfInterpreter.scriptNumberInvert(v(5)));   // NOT -6
        assertEquals(v(-32512), AnfInterpreter.scriptNumberInvert(v(255)));
        assertEquals(v(0),      AnfInterpreter.scriptNumberInvert(v(0)));
    }

    @Test
    void bitwiseAndOrXor() {
        assertEquals(v(1), AnfInterpreter.scriptNumberBitwise("&", v(5),  v(3)));
        assertEquals(v(1), AnfInterpreter.scriptNumberBitwise("&", v(-1), v(5))); // NOT 5
    }

    @Test
    void abortsOnLengthMismatch() {
        assertThrows(AnfInterpreter.InterpreterException.class,
            () -> AnfInterpreter.scriptNumberBitwise("&", v(255), v(1)));
        assertThrows(AnfInterpreter.InterpreterException.class,
            () -> AnfInterpreter.scriptNumberBitwise("|", v(7), v(0)));
    }

    @Test
    void abortsOnNegativeShift() {
        assertThrows(AnfInterpreter.InterpreterException.class,
            () -> AnfInterpreter.scriptNumberShift("<<", v(5), v(-1)));
    }

    // ------------------------------------------------------------------
    // Chained byte-array-op semantics (the CHAINED bug fixed by the side map)
    // ------------------------------------------------------------------
    //
    // A single op on minimal operands was already correct (the truth-table
    // tests above pin that). But a shift/bitwise RESULT is a fixed-length,
    // possibly NON-minimal byte array on-chain (`2 << 8` leaves a 1-byte 0x00;
    // the minimal encoding of 0 is empty). Feeding that result to a
    // length-sensitive `& | ^`/shift makes a naive re-minimising interpreter
    // decide length WRONG — a spend/no-spend divergence from the deployed
    // script. These run whole chained ANF programs through the interpreter so
    // the per-binding side map is actually exercised.

    @Test
    void chainedShiftThenOrKeepsResultLength() {
        // On-chain: OP_LSHIFT([0x02], 8) = [0x00]; OP_OR([0x00], [0x05]) = [0x05].
        // Buggy re-minimise: 0 -> empty -> OP_OR length-mismatch -> abort.
        assertEquals(v(5), runChain("""
            {"name":"a","value":{"kind":"load_const","value":2}},
            {"name":"sh","value":{"kind":"load_const","value":8}},
            {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"sh"}},
            {"name":"five","value":{"kind":"load_const","value":5}},
            {"name":"t1","value":{"kind":"bin_op","op":"|","left":"t0","right":"five"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"t1"}}
            """));
    }

    @Test
    void chainedShiftThenAndAbortsOnLengthMismatch() {
        // On-chain: OP_LSHIFT([0x01], 8) = [0x00]; OP_AND([0x00], []) -> abort.
        // Buggy: 0 & 0 = 0 (funds-loss — spends where the script aborts).
        AnfInterpreter.InterpreterException ex = assertThrows(
            AnfInterpreter.InterpreterException.class,
            () -> runChain("""
                {"name":"a","value":{"kind":"load_const","value":1}},
                {"name":"sh","value":{"kind":"load_const","value":8}},
                {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"sh"}},
                {"name":"zero","value":{"kind":"load_const","value":0}},
                {"name":"t1","value":{"kind":"bin_op","op":"&","left":"t0","right":"zero"}},
                {"name":"w","value":{"kind":"update_prop","name":"out","value":"t1"}}
                """));
        assertTrue(ex.getMessage().contains("same length"),
            "expected a length-mismatch abort, got: " + ex.getMessage());
    }

    @Test
    void chainedInvertOfShiftResult() {
        // On-chain: OP_LSHIFT([0x02], 8) = [0x00]; OP_INVERT([0x00]) = [0xff] = -127.
        // Buggy: ~(minimal 0) inverts empty/[] -> 0, not -127.
        assertEquals(v(-127), runChain("""
            {"name":"a","value":{"kind":"load_const","value":2}},
            {"name":"sh","value":{"kind":"load_const","value":8}},
            {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"sh"}},
            {"name":"t1","value":{"kind":"unary_op","op":"~","operand":"t0"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"t1"}}
            """));
    }

    @Test
    void chainedTwoByteShiftThenAnd() {
        // 256 encodes to the 2-byte [0x00,0x01]; OP_LSHIFT by 8 -> [0x01,0x00];
        // OP_AND([0x01,0x00], [0x00,0x01]) = [0x00,0x00] = 0.
        assertEquals(v(0), runChain("""
            {"name":"a","value":{"kind":"load_const","value":256}},
            {"name":"sh","value":{"kind":"load_const","value":8}},
            {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"sh"}},
            {"name":"c","value":{"kind":"load_const","value":256}},
            {"name":"t1","value":{"kind":"bin_op","op":"&","left":"t0","right":"c"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"t1"}}
            """));
    }

    /**
     * Run a synthetic chained ANF program: wraps {@code bodyJson} (a list of
     * bindings ending in an {@code update_prop} onto the mutable {@code out}
     * property) in a one-method stateful contract, executes it through the
     * interpreter, and returns the resulting {@code out} value. Going through
     * {@code computeNewState} (not the byte helpers directly) is what exercises
     * the per-binding side map that threads non-minimal chained intermediates.
     */
    private static BigInteger runChain(String bodyJson) {
        String json = "{\"anf\":{"
            + "\"contractName\":\"ShiftChain\","
            + "\"properties\":[{\"name\":\"out\",\"readonly\":false}],"
            + "\"methods\":[{\"name\":\"compute\",\"params\":[],\"isPublic\":true,"
            + "\"body\":[" + bodyJson + "]}]}}";
        Map<String, Object> anf = AnfInterpreter.loadAnf(json);
        Map<String, Object> newState = AnfInterpreter.computeNewState(
            anf, "compute", Map.of("out", BigInteger.ZERO), Map.of(), List.of());
        Object out = newState.get("out");
        if (out instanceof BigInteger b) return b;
        if (out instanceof Long l) return BigInteger.valueOf(l);
        return new BigInteger(String.valueOf(out));
    }
}
