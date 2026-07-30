package runar.lang.sdk;

import java.math.BigInteger;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Funds/relay bug, Java tier only: {@code call()} lays the transaction out —
 * and therefore fixes the change output, and therefore the fee — against a
 * PLACEHOLDER unlocking script whose {@code SigHashPreimage} argument is a
 * fixed {@code "00".repeat(181)}.
 *
 * <p>181 bytes is the BIP-143 preimage length for a 24-byte scriptCode:
 * 4 (nVersion) + 32 (hashPrevouts) + 32 (hashSequence) + 36 (outpoint)
 * + 1 (scriptCode varint) + 24 (scriptCode) + 8 (amount) + 4 (nSequence)
 * + 32 (hashOutputs) + 4 (nLocktime) + 4 (sighash type) = 181.
 *
 * <p>A real Rúnar contract's scriptCode is its own locking script (for a
 * stateful contract, everything after OP_CODESEPARATOR) — typically ~1 KB, not
 * 24 bytes. Both of Java's layout passes use the placeholder, and the real
 * unlock is spliced in afterwards via {@code tx.setUnlockingScript(0, ...)}
 * with NO further layout. The broadcast transaction is therefore roughly
 * {@code realPreimageLen - 181} bytes larger than the one whose fee was
 * computed, so it under-pays the miner and does not relay.
 *
 * <p>The other six SDK tiers all re-run their transaction builder against the
 * REAL unlocking script before broadcasting (TypeScript {@code contract.ts}
 * rebuild, Go {@code BuildCallTransaction} rebuild, Rust
 * {@code build_call_transaction_ext} rebuild, Python/Zig/Ruby equivalents), so
 * their change output is sized for the bytes they actually send. Java is the
 * outlier.
 */
class CallFeeCoversBroadcastSizeTest {

    private static final String PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";
    private static final String FUND_TXID = "ff".repeat(32);
    private static final long FUND_SATS = 5_000_000L;

    /** Fee the miner requires for a transaction of this size, at the quoted rate. */
    private static long requiredFee(String txHex, long feeRatePerKb) {
        long bytes = txHex.length() / 2;
        return Math.max(1L, (bytes * feeRatePerKb + 999) / 1000);
    }

    @Test
    void callPaysAtLeastTheRelayFeeForTheTxItBroadcasts() throws Exception {
        RunarArtifact artifact;
        try (var in = CallFeeCoversBroadcastSizeTest.class.getClassLoader()
                .getResourceAsStream("artifacts/stateful-counter.runar.json")) {
            assertTrue(in != null, "stateful-counter artifact resource must exist");
            artifact = RunarArtifact.fromJson(new String(in.readAllBytes()));
        }
        assertTrue(artifact.isStateful(), "fixture must be a StatefulSmartContract");

        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();
        provider.addUtxo(signer.address(),
            new UTXO(FUND_TXID, 0, FUND_SATS,
                ScriptUtils.buildP2PKHScript(signer.address())));

        RunarContract contract = new RunarContract(artifact, List.of(BigInteger.valueOf(5)));
        contract.deploy(provider, signer, 100_000L, signer.address());
        String deployTxid = contract.currentUtxo().txid();

        contract.call("increment", List.of(), null, provider, signer);

        List<String> txs = provider.getBroadcastedTxs();
        assertEquals(2, txs.size(), "one deploy + one call broadcast");
        RawTx deployTx = RawTxParser.parse(txs.get(0));
        String callTxHex = txs.get(1);
        RawTx callTx = RawTxParser.parse(callTxHex);

        long inSats = 0;
        for (RawTx.Input in : callTx.inputs) {
            if (in.prevTxid.equals(deployTxid)) {
                inSats += deployTx.outputs.get(in.prevVout).satoshis;
            } else if (in.prevTxid.equals(FUND_TXID)) {
                inSats += FUND_SATS;
            } else {
                throw new AssertionError("unresolved input source " + in.prevTxid);
            }
        }
        long outSats = 0;
        for (RawTx.Output o : callTx.outputs) outSats += o.satoshis;

        long paid = inSats - outSats;
        long needed = requiredFee(callTxHex, provider.getFeeRate());

        assertTrue(paid >= needed,
            "call tx must pay at least the relay fee for its own broadcast size: paid "
                + paid + " sat, needs " + needed + " sat for " + (callTxHex.length() / 2)
                + " bytes at " + provider.getFeeRate() + " sat/KB (short by "
                + (needed - paid) + ")");
    }

    /**
     * Pins the arithmetic the bug rests on: the fixture's real BIP-143 preimage
     * is far longer than the 181-byte placeholder the layout passes assume, so
     * the shortfall is structural rather than a rounding artefact.
     */
    @Test
    void realPreimageIsMuchLongerThanThePlaceholder() throws Exception {
        RunarArtifact artifact;
        try (var in = CallFeeCoversBroadcastSizeTest.class.getClassLoader()
                .getResourceAsStream("artifacts/stateful-counter.runar.json")) {
            artifact = RunarArtifact.fromJson(new String(in.readAllBytes()));
        }
        String scriptHex = artifact.scriptHex();
        Integer csiBox = artifact.codeSeparatorIndex();
        int csi = csiBox == null ? -1 : csiBox;
        String scriptCodeHex = csi >= 0 ? scriptHex.substring((csi + 1) * 2) : scriptHex;
        int scriptCodeLen = scriptCodeHex.length() / 2;
        int varintLen = scriptCodeLen < 0xfd ? 1 : scriptCodeLen <= 0xffff ? 3 : 5;
        int realPreimageLen = 156 + varintLen + scriptCodeLen;

        assertTrue(scriptCodeLen > 24,
            "fixture must have a scriptCode bigger than the placeholder's 24 bytes, got "
                + scriptCodeLen);
        assertTrue(realPreimageLen > 181 + 100,
            "real preimage (" + realPreimageLen + " bytes) must exceed the old 181-byte "
                + "placeholder by enough that the fee gap is structural, not rounding");

        // And the SDK's own sizing helper must agree with that arithmetic —
        // it is what the layout passes now use in place of the constant.
        assertEquals(realPreimageLen, RunarContract.bip143PreimageLen(scriptCodeHex),
            "bip143PreimageLen must match the BIP-143 field layout");
    }
}
