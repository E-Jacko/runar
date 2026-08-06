package runar.lang.sdk;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import runar.lang.sdk.RunarArtifact.ABI;
import runar.lang.sdk.RunarArtifact.ABIConstructor;
import runar.lang.sdk.RunarArtifact.ABIParam;
import runar.lang.sdk.RunarArtifact.ConstructorSlot;
import runar.lang.sdk.RunarArtifact.StateField;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Deep-review C9 + S1: the MINIMALDATA push-data codec must round-trip.
 *
 * <p>C9 — the state serializer short-circuits a 1-byte variable-length
 * (ByteString) field to {@code OP_0 / OP_1..OP_16 / OP_1NEGATE}, but
 * {@link ScriptUtils#decodePushData} only understood direct pushes and
 * {@code OP_PUSHDATA1/2/4}, so those values came back EMPTY.
 *
 * <p>S1 — the same wrong short-circuit sits on the constructor-arg encode
 * path, and {@code ContractScript.decodeSlotValue} reconstructed the OP_N
 * opcodes as script <em>numbers</em> for every ABI type, so a 1-byte
 * ByteString ctor arg restored as {@code BigInteger} (or {@code ""}) instead
 * of its hex byte.
 *
 * <p>The crux: {@code OP_0} pushes the EMPTY byte array, NOT a 1-byte
 * {@code 0x00}. The minimal encoding of a 1-byte {@code 0x00} payload is the
 * direct push {@code 01 00} — matching the compiler's {@code encodePushBytesHex}.
 */
class MinimalDataRoundTripTest {

    // ------------------------------------------------------------------
    // C9 — state path
    // ------------------------------------------------------------------
    //
    // round-trip only — absolute pin:
    // packages/runar-java/src/test/java/runar/lang/sdk/StatePushFramingTest.java
    // (this file also carries two REAL absolute pins of its own -- see
    // encodePushDataMatchesCompilerEncodePushBytesHex and
    // decodePushDataInvertsTheMinimalDataOpcodes below -- so label this file
    // precisely rather than wholesale: only the two round-trip methods in
    // this section are smoke, not evidence).

    @ParameterizedTest(name = "state ByteString payload [{0}]")
    @ValueSource(strings = {"00", "01", "05", "10", "81", "aabbccdd", ""})
    void varLenStateFieldRoundTrips(String payload) {
        List<StateField> fields = List.of(new StateField("blob", "ByteString", 0, null, null));

        String stateHex = StateSerializer.serialize(fields, Map.of("blob", payload));
        Map<String, Object> restored = StateSerializer.deserialize(fields, stateHex);

        assertEquals(payload, restored.get("blob"),
            "var-length state field must round-trip (encoded as " + stateHex + ")");
    }

    // ------------------------------------------------------------------
    // S1 — constructor-arg path
    // ------------------------------------------------------------------
    //
    // round-trip only — absolute pin: encodePushDataMatchesCompilerEncodePushBytesHex
    // (below, this file). This method exercises ContractScript's ctor-arg
    // splice/restore round trip; the literal expected bytes for the encoder
    // it shares with the unlocking-script path are pinned by the method
    // below, not here.

    @ParameterizedTest(name = "ctor ByteString payload [{0}]")
    @ValueSource(strings = {"00", "01", "05", "10", "81", "aabbccdd", ""})
    void byteStringConstructorArgRoundTrips(String payload) {
        // Synthetic artifact: OP_2 filler, ByteString ctor slot at byte offset 1,
        // OP_CHECKSIG filler.
        String template = "52" + "00" + "ac";
        ABI abi = new ABI(
            new ABIConstructor(List.of(new ABIParam("blob", "ByteString", null))),
            List.of());
        RunarArtifact artifact = new RunarArtifact(
            "1", "test", "Synthetic", abi, template, "", "",
            List.of(),
            List.of(new ConstructorSlot(0, 1)),
            List.of(), null, List.of());

        String deployed = ContractScript.renderLockingScript(artifact, List.of(payload), null);
        List<Object> recovered = ContractScript.extractConstructorArgs(artifact, deployed);

        assertEquals(payload, recovered.get(0),
            "ByteString ctor arg must round-trip (deployed script " + deployed + ")");
    }

    // ------------------------------------------------------------------
    // Codec-level assertions (parity with the compiler's encodePushBytesHex)
    // ------------------------------------------------------------------
    //
    // ABSOLUTE PIN (not round-trip) — literal expected bytes derived from the
    // compiler's encodePushBytesHex first, then asserted. This is the Java
    // tier's local KAT for the unlocking-script encoder (mirrors
    // packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts,
    // packages/runar-rs/tests/encode_push_data_minimaldata.rs).

    @Test
    void encodePushDataMatchesCompilerEncodePushBytesHex() {
        // OP_0 pushes []; a 1-byte 0x00 payload's minimal encoding is `01 00`.
        assertEquals("0100", ScriptUtils.encodePushData("00"));
        assertEquals("51", ScriptUtils.encodePushData("01"));
        assertEquals("55", ScriptUtils.encodePushData("05"));
        assertEquals("60", ScriptUtils.encodePushData("10"));
        assertEquals("4f", ScriptUtils.encodePushData("81"));
        assertEquals("04aabbccdd", ScriptUtils.encodePushData("aabbccdd"));
    }

    // ABSOLUTE PIN (not round-trip) — the input opcodes are computed
    // (0x50 + n), not decoded from a prior encode call, and the expected
    // output is the independently-known payload byte n; this pins the DECODE
    // direction against the spec, not against ScriptUtils' own encoder.
    @Test
    void decodePushDataInvertsTheMinimalDataOpcodes() {
        for (int n = 1; n <= 16; n++) {
            String encoded = String.format("%02x", 0x50 + n);
            ScriptUtils.DecodedPush got = ScriptUtils.decodePushData(encoded, 0);
            assertEquals(String.format("%02x", n), got.dataHex(), "OP_" + n);
            assertEquals(2, got.hexCharsConsumed(), "OP_" + n + " consumes exactly its own byte");
        }
        ScriptUtils.DecodedPush neg = ScriptUtils.decodePushData("4f", 0);
        assertEquals("81", neg.dataHex(), "OP_1NEGATE");
        assertEquals(2, neg.hexCharsConsumed());

        // OP_0 still decodes as the EMPTY byte array — its true semantics.
        ScriptUtils.DecodedPush zero = ScriptUtils.decodePushData("00", 0);
        assertEquals("", zero.dataHex(), "OP_0 pushes []");
        assertEquals(2, zero.hexCharsConsumed());
    }
}
