package runar.lang.sdk;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import runar.lang.sdk.RunarArtifact.StateField;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The state section is framed {@code <len><data>}, never MINIMALDATA.
 *
 * <p>{@code SCRIPT_VERIFY_MINIMALDATA} applies to pushes the interpreter
 * EXECUTES — unlocking scripts and spliced constructor args, which
 * {@code ScriptUtils.encodePushData} still handles (see ScriptUtilsTest). The
 * state section is raw data after {@code OP_RETURN} in the locking script:
 * never executed, never MINIMALDATA-checked, and read back by the compiler's
 * on-chain state codec ({@code emitPushDataEncode} in 05-stack-lower.ts),
 * which understands only {@code <len><data>}.
 *
 * <p>#110 applied the MINIMALDATA short-circuit to the state serializer in all
 * seven SDKs and none of the seven compilers. A 1-byte {@code 0x05} state
 * field then serialised off-chain as {@code 55} while the script rebuilt it as
 * {@code 0105}, so the continuation hash never matched (unspendable), and a
 * contract DEPLOYED with such a value could not be spent at all (the on-chain
 * reader takes {@code 0x55} as a length-85 push).
 */
class StatePushFramingTest {

    private static final List<StateField> FIELDS =
        List.of(new StateField("b", "ByteString", 0, null, null));

    private static String encode(String payload) {
        return StateSerializer.serialize(FIELDS, Map.of("b", payload));
    }

    @Test
    void opNRangeSingleBytesStayDirectPushes() {
        for (int n = 1; n <= 16; n++) {
            String payload = String.format("%02x", n);
            assertEquals("01" + payload, encode(payload),
                "1-byte state value 0x" + payload + " must stay <len><data>, not OP_" + n);
        }
    }

    @Test
    void singleByte0x81IsNotOp1Negate() {
        assertEquals("0181", encode("81"));
    }

    @Test
    void singleZeroByteIsADirectPush() {
        assertEquals("0100", encode("00"));
    }

    @Test
    void emptyIsAZeroLengthPush() {
        assertEquals("00", encode(""));
    }

    @Test
    void valuesOutsideTheOpNRangeAreUnchanged() {
        assertEquals("0111", encode("11"));
        assertEquals("020011", encode("0011"));
    }

    @Test
    void roundTripsForEverySingleByteValue() {
        for (int b = 0; b <= 0xff; b++) {
            String payload = String.format("%02x", b);
            Map<String, Object> decoded = StateSerializer.deserialize(FIELDS, encode(payload));
            assertEquals(payload, decoded.get("b"), "roundtrip 0x" + payload);
        }
    }
}
