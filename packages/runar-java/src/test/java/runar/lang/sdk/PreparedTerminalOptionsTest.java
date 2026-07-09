package runar.lang.sdk;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Gap 2 — the multi-signer {@code prepareCall}/{@code finalizeCall} terminal
 * path must honour the same funding options as the primary
 * {@code callWithOptions} terminal path:
 *
 * <ul>
 *   <li>#131 — {@code sequence} (non-final default under a non-zero locktime)</li>
 *   <li>#134 — {@code fundingSigner} (fee/funding inputs signed by their owner)</li>
 *   <li>#118 — {@code feeUtxo} (extra P2PKH fee input at index 1)</li>
 * </ul>
 *
 * <p>With a deterministic (RFC 6979) local signer the two paths must build a
 * byte-identical transaction for the same inputs.
 */
class PreparedTerminalOptionsTest {

    private static final String METHOD_PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";
    private static final String FUNDING_PRIV =
        "0000000000000000000000000000000000000000000000000000000000000abc";

    private static RunarArtifact loadArtifact(String leaf) throws Exception {
        var in = PreparedTerminalOptionsTest.class.getClassLoader()
            .getResourceAsStream("artifacts/" + leaf);
        assertNotNull(in, "test artifact not found on classpath: " + leaf);
        try (in) {
            return RunarArtifact.fromJson(new String(in.readAllBytes(),
                java.nio.charset.StandardCharsets.UTF_8));
        }
    }

    private static RunarContract deployedContract(LocalSigner methodSigner) throws Exception {
        RunarArtifact artifact = loadArtifact("basic-p2pkh.runar.json");
        String pkhHex = HexFormat.of().formatHex(Hash160.hash160(methodSigner.pubKey()));
        RunarContract contract = new RunarContract(artifact, List.of(pkhHex));
        contract.setCurrentUtxo(new UTXO("ab".repeat(32), 0, 10_000L, contract.lockingScript()));
        return contract;
    }

    @Test
    void preparedTerminalHonorsSequenceFundingSignerAndFeeUtxoMatchingPrimaryPath() throws Exception {
        LocalSigner methodSigner = new LocalSigner(METHOD_PRIV);
        LocalSigner fundingSigner = new LocalSigner(FUNDING_PRIV);
        MockProvider provider = new MockProvider();

        // Terminal output pays out the full contract balance → the fee must come
        // from the feeUtxo (issue #118), owned/signed by the funding key (#134).
        List<CallOptions.TerminalOutput> outs = List.of(
            new CallOptions.TerminalOutput(BigInteger.valueOf(10_000L), methodSigner.address(), null));
        UTXO feeUtxo = new UTXO("fe".repeat(32), 3, 5_000L,
            ScriptUtils.buildP2PKHScript(fundingSigner.address()));
        // Non-zero locktime → inputs default to 0xfffffffe (issue #131).
        CallOptions opts = CallOptions.terminal(outs)
            .withFeeUtxo(feeUtxo)
            .withFundingSigner(fundingSigner)
            .withLocktime(500_000);

        // ---- Primary path ----
        RunarContract primary = deployedContract(methodSigner);
        RunarContract.CallOutcome primaryOut = primary.callWithOptions(
            "unlock", Arrays.asList(null, null), opts, provider, methodSigner);

        // ---- Multi-signer prepare/finalize path ----
        RunarContract prep = deployedContract(methodSigner);
        PreparedCall prepared = prep.prepareCallWithOptions(
            "unlock", Arrays.asList(null, null), opts, provider, methodSigner);
        assertEquals(1, prepared.sigIndices().size(), "one Sig placeholder expected");
        // External sign step (simulated): the connected signer signs the digest.
        byte[] der = methodSigner.sign(prepared.sighashes().get(0), null);
        RunarContract.CallOutcome preparedOut = prep.finalizeCall(prepared, List.of(der), provider);

        // The two paths must produce a byte-identical transaction.
        assertEquals(primaryOut.rawTxHex(), preparedOut.rawTxHex(),
            "prepare/finalize terminal tx must match the primary callWithOptions tx byte-for-byte");

        // Structural checks on the prepared/finalized tx.
        RawTx tx = RawTxParser.parse(preparedOut.rawTxHex());
        assertEquals(2, tx.inputs.size(), "terminal tx = contract input + fee input");
        assertEquals(feeUtxo.txid(), tx.inputs.get(1).prevTxid, "fee input sits at index 1 (#118)");
        assertEquals(feeUtxo.outputIndex(), tx.inputs.get(1).prevVout);
        assertEquals(1, tx.outputs.size(), "no change output on a terminal fee-utxo tx");
        assertEquals(500_000, tx.locktime);
        for (RawTx.Input in : tx.inputs) {
            assertEquals(0xfffffffeL, in.sequence,
                "a non-zero locktime must make every input non-final (#131)");
        }
        // Fee = (contract + feeUtxo) - outputs = (10000 + 5000) - 10000 = 5000.
        long inSats = 10_000L + 5_000L;
        long outSats = tx.outputs.stream().mapToLong(o -> o.satoshis).sum();
        assertEquals(5_000L, inSats - outSats, "the feeUtxo is consumed entirely as fee");

        // Fee input pushes the FUNDING signer's pubkey (#134), not the method's.
        String feeUnlock = tx.inputs.get(1).scriptSigHex;
        assertTrue(feeUnlock.contains(ScriptUtils.bytesToHex(fundingSigner.pubKey())),
            "fee input must be signed with (and push) the funding signer's pubkey");
        assertFalse(feeUnlock.contains(ScriptUtils.bytesToHex(methodSigner.pubKey())),
            "fee input must NOT push the method signer's pubkey");
    }
}
