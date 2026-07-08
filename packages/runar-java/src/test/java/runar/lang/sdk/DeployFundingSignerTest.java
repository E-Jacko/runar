package runar.lang.sdk;

import java.util.HexFormat;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Issue #134 (deploy path) — the P2PKH funding inputs of a deploy tx must be
 * signable by a key that differs from the connected deploy signer.
 *
 * <p>{@code deploy()} signed every funding input with the deploy signer and
 * pushed that signer's pubkey. When the funding UTXO is owned by a DIFFERENT
 * key, the scriptSig's pubkey fails OP_EQUALVERIFY against the coin's PKH.
 * {@link DeployOptions#fundingSigner} lets the real owner sign; the funding
 * lookup / change address still come from the deploy signer (TS parity).
 */
class DeployFundingSignerTest {

    private static final String METHOD_PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";
    private static final String FUNDING_PRIV =
        "0000000000000000000000000000000000000000000000000000000000000abc";

    private static RunarArtifact loadArtifact(String leaf) throws Exception {
        var in = DeployFundingSignerTest.class.getClassLoader()
            .getResourceAsStream("artifacts/" + leaf);
        assertNotNull(in, "test artifact not found on classpath: " + leaf);
        try (in) {
            return RunarArtifact.fromJson(new String(in.readAllBytes(),
                java.nio.charset.StandardCharsets.UTF_8));
        }
    }

    private static RunarContract freshContract(LocalSigner methodSigner) throws Exception {
        RunarArtifact artifact = loadArtifact("basic-p2pkh.runar.json");
        String pkhHex = HexFormat.of().formatHex(Hash160.hash160(methodSigner.pubKey()));
        return new RunarContract(artifact, List.of(pkhHex));
    }

    /**
     * Registers the funding coin under the DEPLOY signer's address bucket
     * (so the provider lookup at {@code signer.address()} finds it) but scripts
     * it to the FUNDING signer's PKH — so only the funding signer can spend it.
     * Mirrors the TS #134 test's {@code fundingCoinUnderMethodAddress}.
     */
    private static void fundingCoinUnderMethodAddress(
        MockProvider provider, LocalSigner methodSigner, String fundingScript, long sats) {
        provider.addUtxo(methodSigner.address(),
            new UTXO("a1".repeat(32), 0, sats, fundingScript));
    }

    @Test
    void deployWithoutFundingSignerPushesTheDeploySignerPubkey() throws Exception {
        LocalSigner methodSigner = new LocalSigner(METHOD_PRIV);
        LocalSigner fundingSigner = new LocalSigner(FUNDING_PRIV);
        String fundingScript = ScriptUtils.buildP2PKHScript(fundingSigner.address());

        MockProvider provider = new MockProvider();
        fundingCoinUnderMethodAddress(provider, methodSigner, fundingScript, 100_000L);

        RunarContract contract = freshContract(methodSigner);
        RunarContract.DeployOutcome out = contract.deploy(provider, methodSigner, 1_000L);

        RawTx tx = RawTxParser.parse(out.rawTxHex());
        String fundInputScriptSig = tx.inputs.get(0).scriptSigHex;
        String methodPubHex = ScriptUtils.bytesToHex(methodSigner.pubKey());
        String fundingPubHex = ScriptUtils.bytesToHex(fundingSigner.pubKey());
        // Default: signed by the deploy signer → pushes the deploy signer's
        // pubkey, which would fail OP_EQUALVERIFY against the funding coin's PKH.
        assertTrue(fundInputScriptSig.contains(methodPubHex),
            "default deploy funding input pushes the deploy signer's pubkey");
        assertFalse(fundInputScriptSig.contains(fundingPubHex),
            "default deploy funding input must NOT push the funding signer's pubkey");
    }

    @Test
    void deployWithFundingSignerProducesValidFundingInputSig() throws Exception {
        LocalSigner methodSigner = new LocalSigner(METHOD_PRIV);
        LocalSigner fundingSigner = new LocalSigner(FUNDING_PRIV);
        String fundingScript = ScriptUtils.buildP2PKHScript(fundingSigner.address());

        MockProvider provider = new MockProvider();
        fundingCoinUnderMethodAddress(provider, methodSigner, fundingScript, 100_000L);

        RunarContract contract = freshContract(methodSigner);
        DeployOptions opts = new DeployOptions().withSatoshis(1_000L).withFundingSigner(fundingSigner);
        RunarContract.DeployOutcome out = contract.deploy(provider, methodSigner, opts);

        RawTx tx = RawTxParser.parse(out.rawTxHex());
        String fundInputScriptSig = tx.inputs.get(0).scriptSigHex;
        String methodPubHex = ScriptUtils.bytesToHex(methodSigner.pubKey());
        String fundingPubHex = ScriptUtils.bytesToHex(fundingSigner.pubKey());

        // The funding input pushes the FUNDING signer's pubkey (satisfies
        // OP_EQUALVERIFY against the coin's PKH), not the deploy signer's.
        assertTrue(fundInputScriptSig.contains(fundingPubHex),
            "funding input must push the funding signer's pubkey");
        assertFalse(fundInputScriptSig.contains(methodPubHex),
            "funding input must NOT push the deploy signer's pubkey");

        // And the pushed signature is the funding signer's valid, deterministic
        // (RFC 6979) signature over the funding input's BIP-143 sighash — the
        // canonical bytes would fail CHECKSIG under any other key.
        byte[] sighash = tx.sighashBIP143(
            0, fundingScript, 100_000L, RawTx.SIGHASH_ALL_FORKID);
        String expectedSigHex = ScriptUtils.bytesToHex(fundingSigner.sign(sighash, null))
            + String.format("%02x", RawTx.SIGHASH_ALL_FORKID);
        assertTrue(fundInputScriptSig.contains(expectedSigHex),
            "funding input must carry the funding signer's valid BIP-143 signature");
        // A signature by the deploy signer over the same digest would differ.
        String wrongSigHex = ScriptUtils.bytesToHex(methodSigner.sign(sighash, null))
            + String.format("%02x", RawTx.SIGHASH_ALL_FORKID);
        assertFalse(fundInputScriptSig.contains(wrongSigHex),
            "funding input must NOT carry the deploy signer's signature");
    }
}
