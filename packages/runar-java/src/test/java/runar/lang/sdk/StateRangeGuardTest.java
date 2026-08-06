package runar.lang.sdk;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import runar.lang.sdk.RunarArtifact.FixedArrayMeta;
import runar.lang.sdk.RunarArtifact.StateField;

import static org.junit.jupiter.api.Assertions.*;

/**
 * A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
 * little-endian sign-magnitude word must be REFUSED, not silently truncated.
 *
 * <p>{@code num2bin-le8} gives a bigint state field exactly 63 bits of
 * magnitude (bytes 0..6 plus the low 7 bits of byte 7) and one sign bit (0x80
 * of byte 7). {@code serialize} wrote the low 8 bytes and dropped everything
 * above, then OR-ed the sign bit in on top of whatever landed there. Measured
 * in the TS reference before the guard:
 *
 * <pre>
 * value       bytes written       reads back as
 * 2^63        0000000000000080    0    (negative zero)
 * 2^63 + 5    0500000000000080    -5   (SIGN FLIP)
 * 2^64        0000000000000000    0
 * </pre>
 *
 * <p>{@link BigInteger} is arbitrary-precision, so this tier has the identical
 * defect: the deploy succeeds and the UTXO is unspendable, because the covenant
 * rebuilds the continuation with the compiler's own OP_NUM2BIN 8, which cannot
 * produce those bytes from that number, so hash256(outputs) never matches.
 *
 * <p>Expected bytes below are derived BY HAND from the sign-magnitude rule,
 * never read off the serializer.
 */
class StateRangeGuardTest {

    /** 2^63 — one past the largest magnitude the 63 magnitude bits can hold. */
    private static final BigInteger TWO_63 = BigInteger.ONE.shiftLeft(63);
    /** 2^63 - 1 — the largest magnitude that DOES fit. */
    private static final BigInteger MAX_MAGNITUDE = TWO_63.subtract(BigInteger.ONE);

    private static List<StateField> countField() {
        return List.of(new StateField("count", "bigint", 0, null, null));
    }

    private static String encode(Object value) {
        Map<String, Object> values = new HashMap<>();
        values.put("count", value);
        return StateSerializer.serialize(countField(), values);
    }

    private static void assertRefused(Object value) {
        IllegalArgumentException e =
            assertThrows(IllegalArgumentException.class, () -> encode(value));
        assertTrue(
            e.getMessage().contains("does not fit"),
            "unexpected message: " + e.getMessage());
    }

    // ------------------------------------------------------------------
    // Rejecting
    // ------------------------------------------------------------------

    @Test
    void rejectsExactlyTwoPow63() {
        assertRefused(TWO_63);
    }

    @Test
    void rejectsExactlyNegativeTwoPow63() {
        assertRefused(TWO_63.negate());
    }

    /** -2^63 arrives as a plain {@code Long} too, and has magnitude 2^63. */
    @Test
    void rejectsLongMinValue() {
        assertRefused(Long.MIN_VALUE);
    }

    /** The sign-flip case: used to write 0500000000000080, read back as -5. */
    @Test
    void rejectsTwoPow63Plus5() {
        assertRefused(TWO_63.add(BigInteger.valueOf(5)));
    }

    @Test
    void rejectsTwoPow64() {
        assertRefused(BigInteger.ONE.shiftLeft(64));
    }

    @Test
    void rejectsTwoPow70BothSigns() {
        assertRefused(BigInteger.ONE.shiftLeft(70));
        assertRefused(BigInteger.ONE.shiftLeft(70).negate());
    }

    /** The unrevived-JSON path: a {@code "...n"} BigInt string. */
    @Test
    void rejectsOutOfRangeBigIntString() {
        assertRefused(TWO_63 + "n");
    }

    @Test
    void namesTheFieldAndTheValueItRefused() {
        IllegalArgumentException e =
            assertThrows(IllegalArgumentException.class, () -> encode(TWO_63));
        assertTrue(e.getMessage().contains("count"), "must name the field: " + e.getMessage());
        assertTrue(
            e.getMessage().contains(TWO_63.toString()),
            "must quote the value: " + e.getMessage());
    }

    @Test
    void rejectsOutOfRangeFixedArrayElement() {
        List<StateField> fields = List.of(new StateField(
            "slots",
            "FixedArray<bigint, 2>",
            0,
            null,
            new FixedArrayMeta("bigint", 2, List.of("slots__0", "slots__1"))));
        Map<String, Object> values = new HashMap<>();
        values.put("slots", List.of(BigInteger.ONE, TWO_63));
        IllegalArgumentException e = assertThrows(
            IllegalArgumentException.class, () -> StateSerializer.serialize(fields, values));
        assertTrue(
            e.getMessage().contains("does not fit"),
            "unexpected message: " + e.getMessage());
    }

    // ------------------------------------------------------------------
    // Accepting controls — byte-exact, and they must stay byte-exact
    // ------------------------------------------------------------------

    @Test
    void acceptsMaxMagnitudeAndWritesFfffffffffffff7f() {
        // magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (all seven magnitude
        // bits set, sign bit clear).
        assertEquals("ffffffffffffff7f", encode(MAX_MAGNITUDE));
        assertEquals("ffffffffffffff7f", encode(Long.MAX_VALUE));
        assertEquals("ffffffffffffff7f", encode(MAX_MAGNITUDE + "n"));
        assertEquals(
            MAX_MAGNITUDE,
            StateSerializer.deserialize(countField(), "ffffffffffffff7f").get("count"));
    }

    @Test
    void acceptsNegativeMaxMagnitudeAndWritesFfffffffffffffff() {
        // same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
        assertEquals("ffffffffffffffff", encode(MAX_MAGNITUDE.negate()));
        assertEquals("ffffffffffffffff", encode(-Long.MAX_VALUE));
        assertEquals("ffffffffffffffff", encode("-" + MAX_MAGNITUDE + "n"));
        assertEquals(
            MAX_MAGNITUDE.negate(),
            StateSerializer.deserialize(countField(), "ffffffffffffffff").get("count"));
    }

    @Test
    void acceptsTheSmallValuesEveryShippedContractUses() {
        assertEquals("0000000000000000", encode(BigInteger.ZERO));
        assertEquals("0100000000000000", encode(BigInteger.ONE));
        assertEquals("0100000000000080", encode(BigInteger.ONE.negate()));
        assertEquals("7f00000000000000", encode(BigInteger.valueOf(127)));
        assertEquals("7f00000000000080", encode(BigInteger.valueOf(-127)));
        assertEquals("8000000000000000", encode(BigInteger.valueOf(128)));
        assertEquals("8000000000000080", encode(BigInteger.valueOf(-128)));
    }
}
