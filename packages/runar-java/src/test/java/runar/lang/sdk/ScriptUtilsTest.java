package runar.lang.sdk;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ScriptUtilsTest {

    @Test
    void encodePushDataUsesDirectPushForSmallPayload() {
        assertEquals("02aabb", ScriptUtils.encodePushData("aabb"));
    }

    @Test
    void encodePushDataUsesOp_PUSHDATA1For76PlusBytes() {
        String data = "aa".repeat(76);
        String out = ScriptUtils.encodePushData(data);
        assertEquals("4c4c" + data, out);
    }

    // MINIMALDATA (SCRIPT_VERIFY_MINIMALDATA): a 1-byte payload in
    // {0x00, 0x01..0x10, 0x81} must use the minimal opcode, not a direct push.
    @Test
    void encodePushDataMinimalDataSingleByte() {
        assertEquals("00", ScriptUtils.encodePushData("00")); // OP_0
        assertEquals("55", ScriptUtils.encodePushData("05")); // OP_5
        assertEquals("4f", ScriptUtils.encodePushData("81")); // OP_1NEGATE
        for (int n = 1; n <= 16; n++) {
            assertEquals(String.format("%02x", 0x50 + n),
                ScriptUtils.encodePushData(String.format("%02x", n)));
        }
    }

    @Test
    void encodePushDataMinimalDataBoundariesStillDirectPush() {
        // Single bytes outside the OP_N range still direct-push.
        for (int b : new int[]{0x11, 0x4f, 0x50, 0x60, 0x80, 0x82, 0xff}) {
            assertEquals(String.format("01%02x", b),
                ScriptUtils.encodePushData(String.format("%02x", b)));
        }
        // Two-byte payloads are unaffected.
        assertEquals("020011", ScriptUtils.encodePushData("0011"));
    }

    @Test
    void decodePushDataRoundTrips() {
        String data = "deadbeef";
        String encoded = ScriptUtils.encodePushData(data);
        ScriptUtils.DecodedPush got = ScriptUtils.decodePushData(encoded, 0);
        assertEquals(data, got.dataHex());
        assertEquals(encoded.length(), got.hexCharsConsumed());
    }

    @Test
    void findLastOpReturnSkipsPushData() {
        // Directly push a 0x6a byte, then a real OP_RETURN afterwards.
        String script = ScriptUtils.encodePushData("6a") + "6a";
        int pos = ScriptUtils.findLastOpReturn(script);
        assertEquals(script.length() - 2, pos);
    }

    @Test
    void buildP2PKHFromPubKeyHashHex() {
        String pkh = "00".repeat(20);
        assertEquals("76a914" + pkh + "88ac", ScriptUtils.buildP2PKHScript(pkh));
    }

    @Test
    void reverseHexFlipsByteOrder() {
        assertEquals("ddccbbaa", ScriptUtils.reverseHex("aabbccdd"));
    }

    @Test
    void varIntRoundTrip() {
        // Values at the boundaries of each width.
        assertEquals("00", ScriptUtils.encodeVarInt(0));
        assertEquals("fc", ScriptUtils.encodeVarInt(0xfc));
        assertEquals("fdfd00", ScriptUtils.encodeVarInt(0xfd));
        assertEquals("fdffff", ScriptUtils.encodeVarInt(0xffff));
    }
}
