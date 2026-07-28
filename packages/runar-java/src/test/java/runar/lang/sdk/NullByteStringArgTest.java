package runar.lang.sdk;

import java.util.Arrays;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * G6 — a {@code null} call arg is only auto-resolved for {@code Sig}
 * (auto-signed) and {@code PubKey} (taken from the signer).
 *
 * <p>The Java tier resolves nothing else, so a {@code null} for a
 * {@code ByteString} param used to fall through to
 * {@link ContractScript#encodeConstructorArg}, whose last resort is
 * {@code encodePushData(String.valueOf(value))}. With a null value that is
 * {@code encodePushData("null")} → the literal string {@code "02null"} spliced
 * into the unlocking-script hex: non-hex garbage, emitted with no exception
 * anywhere. Fail at build time instead, naming the parameter.
 */
class NullByteStringArgTest {

    private static RunarArtifact artifactWithByteStringParam(String byteStringParamName) {
        String json =
            "{"
            + "\"version\":\"runar-v0.1.0\","
            + "\"compilerVersion\":\"0.1.0\","
            + "\"contractName\":\"NullByteStringArgTest\","
            + "\"script\":\"51\","
            + "\"asm\":\"\","
            + "\"abi\":{"
                + "\"constructor\":{\"params\":[]},"
                + "\"methods\":[{\"name\":\"move\",\"isPublic\":true,\"params\":["
                    + "{\"name\":\"sig\",\"type\":\"Sig\"},"
                    + "{\"name\":\"" + byteStringParamName + "\",\"type\":\"ByteString\"}"
                + "]}]"
            + "},"
            + "\"buildTimestamp\":\"2026-05-18T00:00:00.000Z\""
            + "}";
        return RunarArtifact.fromJson(json);
    }

    private static RunarContract setupContract(RunarArtifact artifact) {
        RunarContract contract = new RunarContract(artifact, List.of());
        contract.setCurrentUtxo(new UTXO("ab".repeat(32), 0, 10_000L, "51"));
        return contract;
    }

    @Test
    void nullByteStringArgIsRejectedNamingTheParameter() {
        RunarContract contract = setupContract(artifactWithByteStringParam("memo"));
        MockProvider provider = new MockProvider();

        IllegalArgumentException err = assertThrows(
            IllegalArgumentException.class,
            () -> contract.prepareCall(
                "move", Arrays.asList(null, null), null, provider, new MockSigner())
        );
        assertTrue(err.getMessage().contains("memo"),
            "error must name the offending parameter, got: " + err.getMessage());
    }

    @Test
    void nullByteStringArgNeverEmitsGarbageHex() {
        // Guards the concrete regression: encodePushData("null") == "02null".
        RunarContract contract = setupContract(artifactWithByteStringParam("memo"));
        MockProvider provider = new MockProvider();
        String txHex;
        try {
            txHex = contract.prepareCall(
                "move", Arrays.asList(null, null), null, provider, new MockSigner()).txHex();
        } catch (IllegalArgumentException expected) {
            return; // rejected at build time — nothing to inspect
        }
        assertFalse(txHex.contains("null"),
            "unlocking script hex must never contain the literal \"null\": " + txHex);
    }

    @Test
    void nullSigArgStillAutoSigns() {
        RunarContract contract = setupContract(artifactWithByteStringParam("memo"));
        MockProvider provider = new MockProvider();
        // Only the Sig slot is null; the ByteString slot carries a real value.
        contract.prepareCall(
            "move", Arrays.asList(null, "deadbeef"), null, provider, new MockSigner());
    }
}
