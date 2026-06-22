package runar.lang.sdk;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Issue #100: a terminal method that reads variable-length (ByteString) state
 * must receive {@code _codePart} in its unlocking script. Without it the
 * on-chain var-length deserialization is skipped and the read returns the
 * deploy-time initial value instead of the live state.
 *
 * <p>The compiler stamps {@code usesCodePart=true} on such methods; the SDK
 * reads the flag and prefixes the unlock with the codePart push. codePart is
 * ~470 bytes, so its push begins with PUSHDATA2 (0x4d); without the fix the
 * unlock would begin with the ~72-byte opSig push (0x48).
 */
class Issue100Test {

    private static final String PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";

    @Test
    void terminalVarLenStateReadGetsCodePart() throws Exception {
        RunarArtifact artifact;
        try (var in = Issue100Test.class.getClassLoader()
                .getResourceAsStream("artifacts/state-read.runar.json")) {
            assertTrue(in != null, "state-read artifact resource must exist");
            artifact = RunarArtifact.fromJson(new String(in.readAllBytes()));
        }

        // The compiler must have stamped the authoritative flag.
        RunarArtifact.ABIMethod termCheck = artifact.abi().methods().stream()
            .filter(m -> m.name().equals("termCheck")).findFirst().orElseThrow();
        assertEquals(Boolean.TRUE, termCheck.usesCodePart(),
            "termCheck reads a mutable ByteString field -> usesCodePart must be true");

        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();
        provider.addUtxo(signer.address(),
            new UTXO("ff".repeat(32), 0, 500_000L,
                ScriptUtils.buildP2PKHScript(signer.address())));

        String init = "00".repeat(8) + "cc".repeat(20);
        String live = "11".repeat(8) + "dd".repeat(20);

        // Deploy with the initial state, then update to the live state so the
        // contract UTXO carries the live var-length field.
        RunarContract contract = new RunarContract(artifact, List.of(init));
        contract.deploy(provider, signer, 10_000L, signer.address());

        Map<String, Object> updates = new HashMap<>();
        updates.put("s", live);
        contract.call("update", List.of(live), updates, provider, signer);

        // Terminal read of the live var-length field.
        contract.call("termCheck", List.of("dd".repeat(20)), null, provider, signer);

        List<String> txs = provider.getBroadcastedTxs();
        String unlock = input0Unlock(txs.get(txs.size() - 1));
        // PUSHDATA2 (0x4d) prefix => codePart push leads the unlock (issue #100).
        assertEquals("4d", unlock.substring(0, 2),
            "termCheck unlock must begin with the codePart push (PUSHDATA2); "
                + "got prefix " + unlock.substring(0, Math.min(6, unlock.length())));
    }

    /** Parse input[0]'s unlocking-script hex out of a raw transaction hex. */
    private static String input0Unlock(String txHex) {
        int i = 8;          // skip 4-byte version
        i += 2;             // input count varint (single contract input first)
        i += 64 + 8;        // txid (32) + vout (4)
        int slen = Integer.parseInt(txHex.substring(i, i + 2), 16);
        i += 2;
        if (slen == 0xfd) {
            slen = Integer.parseInt(txHex.substring(i + 2, i + 4), 16) * 256
                 + Integer.parseInt(txHex.substring(i, i + 2), 16);
            i += 4;
        }
        return txHex.substring(i, i + slen * 2);
    }
}
