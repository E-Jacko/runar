package runar.lang.sdk;

import java.math.BigInteger;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
}
