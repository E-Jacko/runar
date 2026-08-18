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

    // --- NON-MINIMAL numeric operands (funds-loss: the interpreter reports a
    // VALID spend for a script that aborts on chain). A shift preserves its
    // operand's byte LENGTH, so `1 >> 1` leaves the 1-byte [0x00] — a
    // NON-minimal zero (minimal zero is empty). Every numeric consumer decodes
    // with fRequireMinimal = true and ABORTS on it: OP_ADD/OP_SUB/OP_MUL/OP_DIV/
    // OP_MOD, OP_NUMEQUAL and the relational ops, and a shift's COUNT operand.
    // The byte-array ops `& | ^` and a shift's VALUE operand are exempt — they
    // take raw bytes and only require equal length. ---

    @Test
    void nonMinimalOperandAbortsNumericEquality() {
        // On-chain: OP_RSHIFT([0x01], 1) = [0x00]; OP_NUMEQUAL then aborts with
        // "non-minimally encoded script number". The buggy path decoded [0x00]
        // to 0 and answered `true` — a funds-loss spend.
        assertThrows(
            AnfInterpreter.InterpreterException.class,
            () -> runChainRaw("""
                {"name":"n","value":{"kind":"load_const","value":1}},
                {"name":"one","value":{"kind":"load_const","value":1}},
                {"name":"sh","value":{"kind":"bin_op","op":">>","left":"n","right":"one"}},
                {"name":"z","value":{"kind":"load_const","value":0}},
                {"name":"eq","value":{"kind":"bin_op","op":"===","left":"sh","right":"z"}},
                {"name":"w","value":{"kind":"update_prop","name":"out","value":"eq"}}
                """),
            "(1>>1)===0 must abort");
    }

    @Test
    void nonMinimalOperandAbortsAddition() {
        // OP_ADD is a numeric consumer too.
        assertThrows(
            AnfInterpreter.InterpreterException.class,
            () -> runChainRaw("""
                {"name":"n","value":{"kind":"load_const","value":1}},
                {"name":"one","value":{"kind":"load_const","value":1}},
                {"name":"sh","value":{"kind":"bin_op","op":">>","left":"n","right":"one"}},
                {"name":"z","value":{"kind":"load_const","value":0}},
                {"name":"sum","value":{"kind":"bin_op","op":"+","left":"sh","right":"z"}},
                {"name":"w","value":{"kind":"update_prop","name":"out","value":"sum"}}
                """),
            "(1>>1)+0 must abort");
    }

    @Test
    void nonMinimalShiftCountAborts() {
        // A shift's COUNT operand is read as a number, so a non-minimal count
        // aborts even though the VALUE operand need not be minimal.
        assertThrows(
            AnfInterpreter.InterpreterException.class,
            () -> runChainRaw("""
                {"name":"n","value":{"kind":"load_const","value":1}},
                {"name":"one","value":{"kind":"load_const","value":1}},
                {"name":"cnt","value":{"kind":"bin_op","op":">>","left":"n","right":"one"}},
                {"name":"four","value":{"kind":"load_const","value":4}},
                {"name":"t","value":{"kind":"bin_op","op":">>","left":"four","right":"cnt"}},
                {"name":"w","value":{"kind":"update_prop","name":"out","value":"t"}}
                """),
            "4>>(1>>1) must abort");
    }

    @Test
    void minimalShiftResultStillAccepted() {
        // CONTROL — `2 >> 1` leaves [0x01], the minimal encoding of 1, so
        // OP_NUMEQUAL is happy and the spend stays valid.
        assertEquals(Boolean.TRUE, runChainRaw("""
            {"name":"two","value":{"kind":"load_const","value":2}},
            {"name":"one","value":{"kind":"load_const","value":1}},
            {"name":"sh","value":{"kind":"bin_op","op":">>","left":"two","right":"one"}},
            {"name":"c1","value":{"kind":"load_const","value":1}},
            {"name":"eq","value":{"kind":"bin_op","op":"===","left":"sh","right":"c1"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"eq"}}
            """));
    }

    @Test
    void bitwiseOnNonMinimalOperandsStillAccepted() {
        // CONTROL — `& | ^` still take non-minimal equal-length operands:
        // OP_OR([0x00], [0x05]) = [0x05], which IS minimal for 5, so the
        // following `=== 5` accepts. Pinned by
        // conformance/fuzz-regressions/entries/2026-07-14-chained-shift-or-nonminimal
        // — a fix that rejects this is WRONG.
        assertEquals(Boolean.TRUE, runChainRaw("""
            {"name":"a","value":{"kind":"load_const","value":2}},
            {"name":"sh","value":{"kind":"load_const","value":8}},
            {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"sh"}},
            {"name":"five","value":{"kind":"load_const","value":5}},
            {"name":"t1","value":{"kind":"bin_op","op":"|","left":"t0","right":"five"}},
            {"name":"c5","value":{"kind":"load_const","value":5}},
            {"name":"eq","value":{"kind":"bin_op","op":"===","left":"t1","right":"c5"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"eq"}}
            """));
    }

    // -----------------------------------------------------------------------
    // NON-MINIMAL operands reaching a UNARY op or a numeric BUILTIN.
    //
    // The binary-op gate above only sees a value consumed by a BINARY numeric
    // op. A non-minimal shift result can reach a UNARY op or a numeric BUILTIN
    // without passing through one, and those opcodes decode with
    // fRequireMinimal = true as well: OP_ABS, OP_0NOTEQUAL (`bool`), OP_NOT
    // (`!`), OP_NEGATE (unary `-`). With n = 1 the shift leaves the 1-byte
    // [0x00]; reading only the decoded value re-minimises it to 0, reports a
    // VALID spend, and the deployed script aborts — the UTXO is unspendable.
    //
    // Mirrors the TS reference widening at the toBigInt / toBool funnels in
    // packages/runar-testing/src/interpreter/interpreter.ts.
    // -----------------------------------------------------------------------

    /** Bindings binding {@code sh} = {@code 1 >> 1} — raw stack bytes [0x00]. */
    private static final String NON_MINIMAL_PREFIX = """
        {"name":"n","value":{"kind":"load_const","value":1}},
        {"name":"one","value":{"kind":"load_const","value":1}},
        {"name":"sh","value":{"kind":"bin_op","op":">>","left":"n","right":"one"}},
        {"name":"z","value":{"kind":"load_const","value":0}},
        """;

    @Test
    void nonMinimalOperandAbortsThroughNumericBuiltin() {
        // Every numeric builtin reads its operand through the same
        // fRequireMinimal decode a binary numeric op does.
        String[][] cases = {
            {"abs", "{\"kind\":\"call\",\"func\":\"abs\",\"args\":[\"sh\"]}"},
            {"bool", "{\"kind\":\"call\",\"func\":\"bool\",\"args\":[\"sh\"]}"},
            {"sign", "{\"kind\":\"call\",\"func\":\"sign\",\"args\":[\"sh\"]}"},
            {"min-left", "{\"kind\":\"call\",\"func\":\"min\",\"args\":[\"sh\",\"one\"]}"},
            {"min-right", "{\"kind\":\"call\",\"func\":\"min\",\"args\":[\"one\",\"sh\"]}"},
            {"max", "{\"kind\":\"call\",\"func\":\"max\",\"args\":[\"sh\",\"one\"]}"},
            {"within", "{\"kind\":\"call\",\"func\":\"within\",\"args\":[\"sh\",\"z\",\"one\"]}"},
            {"safediv", "{\"kind\":\"call\",\"func\":\"safediv\",\"args\":[\"sh\",\"one\"]}"},
            {"clamp", "{\"kind\":\"call\",\"func\":\"clamp\",\"args\":[\"sh\",\"z\",\"one\"]}"},
        };
        for (String[] c : cases) {
            String body = NON_MINIMAL_PREFIX
                + "{\"name\":\"r\",\"value\":" + c[1] + "},"
                + "{\"name\":\"w\",\"value\":{\"kind\":\"update_prop\",\"name\":\"out\",\"value\":\"z\"}}";
            assertThrows(
                AnfInterpreter.InterpreterException.class,
                () -> runChainRaw(body),
                c[0] + "(1>>1) must abort");
        }
    }

    @Test
    void nonMinimalOperandAbortsThroughUnaryOp() {
        // `-` lowers to OP_NEGATE and `!` to OP_NOT — both fRequireMinimal.
        String[][] cases = {
            {"-", "{\"kind\":\"unary_op\",\"op\":\"-\",\"operand\":\"sh\"}"},
            {"!", "{\"kind\":\"unary_op\",\"op\":\"!\",\"operand\":\"sh\"}"},
        };
        for (String[] c : cases) {
            String body = NON_MINIMAL_PREFIX
                + "{\"name\":\"r\",\"value\":" + c[1] + "},"
                + "{\"name\":\"w\",\"value\":{\"kind\":\"update_prop\",\"name\":\"out\",\"value\":\"z\"}}";
            assertThrows(
                AnfInterpreter.InterpreterException.class,
                () -> runChainRaw(body),
                c[0] + "(1>>1) must abort");
        }
    }

    @Test
    void nonMinimalOperandAbortsThroughAliasedBuiltin() {
        // The shape the lowering actually emits: a named local is an `@ref:`
        // alias, so the alias must carry the threaded bytes into the builtin.
        assertThrows(
            AnfInterpreter.InterpreterException.class,
            () -> runChainRaw("""
                {"name":"n","value":{"kind":"load_const","value":1}},
                {"name":"one","value":{"kind":"load_const","value":1}},
                {"name":"sh","value":{"kind":"bin_op","op":">>","left":"n","right":"one"}},
                {"name":"s","value":{"kind":"load_const","value":"@ref:sh"}},
                {"name":"r","value":{"kind":"call","func":"abs","args":["s"]}},
                {"name":"w","value":{"kind":"update_prop","name":"out","value":"r"}}
                """),
            "abs(alias of 1>>1) must abort");
    }

    @Test
    void minimalOperandThroughBuiltinStillAccepted() {
        // CONTROL — `2 >> 1` leaves [0x01], the minimal encoding of 1, so
        // OP_ABS is legal on-chain and the spend stays valid.
        assertEquals(BigInteger.ONE, runChainRaw("""
            {"name":"two","value":{"kind":"load_const","value":2}},
            {"name":"one","value":{"kind":"load_const","value":1}},
            {"name":"sh","value":{"kind":"bin_op","op":">>","left":"two","right":"one"}},
            {"name":"r","value":{"kind":"call","func":"abs","args":["sh"]}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"r"}}
            """));
    }

    @Test
    void invertOfNonMinimalStillAcceptedAfterWidening() {
        // CONTROL — `~` is a byte op with its own path and must NOT be gated:
        // `~(2 << 8)` inverts the non-minimal [0x00] to [0xff] = -127.
        assertEquals(Boolean.TRUE, runChainRaw("""
            {"name":"two","value":{"kind":"load_const","value":2}},
            {"name":"eight","value":{"kind":"load_const","value":8}},
            {"name":"sh","value":{"kind":"bin_op","op":"<<","left":"two","right":"eight"}},
            {"name":"inv","value":{"kind":"unary_op","op":"~","operand":"sh"}},
            {"name":"m127","value":{"kind":"load_const","value":-127}},
            {"name":"eq","value":{"kind":"bin_op","op":"===","left":"inv","right":"m127"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"eq"}}
            """));
    }

    @Test
    void aliasedBitwiseOnNonMinimalStillAccepted() {
        // CONTROL — `(2 << 8) | 5 === 5` through a named-local alias. OP_OR
        // takes non-minimal bytes and only requires equal length; rejecting
        // this is WRONG (pinned by conformance/fuzz-regressions/entries/
        // 2026-07-14-chained-shift-or-nonminimal). Also pins that the alias
        // carries the threaded bytes — dropping them makes OP_OR see a length
        // mismatch the chain never sees.
        assertEquals(Boolean.TRUE, runChainRaw("""
            {"name":"a","value":{"kind":"load_const","value":2}},
            {"name":"eight","value":{"kind":"load_const","value":8}},
            {"name":"t0","value":{"kind":"bin_op","op":"<<","left":"a","right":"eight"}},
            {"name":"s","value":{"kind":"load_const","value":"@ref:t0"}},
            {"name":"five","value":{"kind":"load_const","value":5}},
            {"name":"t1","value":{"kind":"bin_op","op":"|","left":"s","right":"five"}},
            {"name":"c5","value":{"kind":"load_const","value":5}},
            {"name":"eq","value":{"kind":"bin_op","op":"===","left":"t1","right":"c5"}},
            {"name":"w","value":{"kind":"update_prop","name":"out","value":"eq"}}
            """));
    }

    /** Like {@link #runChain}, but returns the raw {@code out} value so a
     *  boolean-valued comparison result can be asserted directly. */
    private static Object runChainRaw(String bodyJson) {
        String json = "{\"anf\":{"
            + "\"contractName\":\"ShiftChain\","
            + "\"properties\":[{\"name\":\"out\",\"readonly\":false}],"
            + "\"methods\":[{\"name\":\"compute\",\"params\":[],\"isPublic\":true,"
            + "\"body\":[" + bodyJson + "]}]}}";
        Map<String, Object> anf = AnfInterpreter.loadAnf(json);
        return AnfInterpreter.computeNewState(
            anf, "compute", Map.of("out", BigInteger.ZERO), Map.of(), List.of()).get("out");
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
