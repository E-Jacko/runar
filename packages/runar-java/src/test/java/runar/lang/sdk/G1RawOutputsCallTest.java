package runar.lang.sdk;

import java.math.BigInteger;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Deep-review finding G1 (P1) — spending a method that calls
 * {@code this.addRawOutput(...)} via the SDK must build a transaction whose
 * outputs match the covenant's continuation {@code hashOutputs}, or input 0's
 * state-check OP_VERIFY fails and the funds are stranded.
 *
 * <p>The shipped example {@code RawOutputTest.sendToScript} emits, in SOURCE
 * order:
 *
 * <pre>{@code
 *     this.addRawOutput(1000L, scriptBytes);  // raw output FIRST
 *     this.count = this.count + 1;
 *     this.addOutput(0L, this.count);         // state continuation SECOND (0 sats)
 * }</pre>
 *
 * <p>The compiler folds BOTH into the continuation {@code hashOutputs} in that
 * order, so the on-chain output layout the covenant reconstructs is
 * {@code [raw(1000, scriptBytes)] [stateContinuation(0)] [change]}. The SDK
 * must emit exactly that ordering; emitting only the state continuation (the
 * pre-fix behaviour) drops the raw output and mismatches hashOutputs.
 *
 * <p>Java ships no ScriptVM, so this test asserts the built call tx's outputs
 * are in the required order with the required scripts + values, and that the
 * continuation UTXO is tracked at its real (non-zero) output index.
 */
class G1RawOutputsCallTest {

    private static final String PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";

    // Caller-supplied raw locking script: a plain P2PKH (76a914 <20 bytes> 88ac).
    private static final String RAW_SCRIPT = "76a914" + "ab".repeat(20) + "88ac";

    @Test
    void sendToScriptBuildsRawThenStateThenChangeInSourceOrder() throws Exception {
        RunarArtifact artifact;
        try (var in = G1RawOutputsCallTest.class.getClassLoader()
                .getResourceAsStream("artifacts/raw-output.runar.json")) {
            assertTrue(in != null, "raw-output artifact resource must exist");
            artifact = RunarArtifact.fromJson(new String(in.readAllBytes()));
        }
        assertTrue(artifact.isStateful(), "RawOutputTest is a StatefulSmartContract");

        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();
        provider.addUtxo(signer.address(),
            new UTXO("ff".repeat(32), 0, 500_000L,
                ScriptUtils.buildP2PKHScript(signer.address())));

        // Deploy with count = 0 and 50_000 sats in the contract UTXO.
        RunarContract contract = new RunarContract(artifact, List.of(BigInteger.ZERO));
        contract.deploy(provider, signer, 50_000L, signer.address());
        String deployScript = contract.currentUtxo().scriptHex();
        String codePart = ContractScript.extractCodePart(deployScript);

        // Call sendToScript(scriptBytes) — raw output first, state continuation second.
        contract.call("sendToScript", List.of(RAW_SCRIPT), null, provider, signer);

        // State advanced 0 -> 1 (this.count = this.count + 1).
        assertEquals(BigInteger.ONE, contract.state().get("count"),
            "count must advance 0 -> 1");

        // --- Output ordering: [0] raw, [1] state continuation, [2] change. ---
        List<String> txs = provider.getBroadcastedTxs();
        RawTx callTx = RawTxParser.parse(txs.get(txs.size() - 1));
        assertEquals(3, callTx.outputs.size(),
            "expected exactly [raw][state][change]; a missing raw output (pre-fix) yields 2");

        // [0] raw output: 1000 sats, script === the caller-supplied bytes.
        RawTx.Output raw = callTx.outputs.get(0);
        assertEquals(1000L, raw.satoshis, "output 0 must be the raw output (1000 sats)");
        assertEquals(RAW_SCRIPT, raw.scriptPubKeyHex,
            "output 0's script must be exactly the scriptBytes argument");

        // [1] state continuation: 0 sats, codePart + OP_RETURN (6a) + serialized count.
        RawTx.Output state = callTx.outputs.get(1);
        assertEquals(0L, state.satoshis, "output 1 (state continuation) must carry 0 sats");
        assertNotEquals(RAW_SCRIPT, state.scriptPubKeyHex,
            "output 1 must be the state continuation, not the raw script");
        assertTrue(state.scriptPubKeyHex.startsWith(codePart),
            "output 1 must reuse the contract codePart");
        assertTrue(state.scriptPubKeyHex.contains("6a"),
            "output 1 must carry the OP_RETURN (6a) state separator");

        // [2] change: a P2PKH output (76a9…88ac) carrying the remainder.
        RawTx.Output change = callTx.outputs.get(2);
        assertTrue(change.scriptPubKeyHex.startsWith("76a914")
                && change.scriptPubKeyHex.endsWith("88ac"),
            "output 2 must be a P2PKH change output");
        assertTrue(change.satoshis > 0, "change output must carry the remainder");

        // The SDK must track the continuation UTXO at its REAL index (1, behind
        // the raw output), not the legacy always-0, and at its real 0-sats value.
        UTXO next = contract.currentUtxo();
        assertEquals(1, next.outputIndex(),
            "continuation UTXO must be tracked at output index 1 (behind the raw output)");
        assertEquals(0L, next.satoshis(),
            "continuation UTXO carries the continuation's 0 sats, not the input value");
        assertEquals(state.scriptPubKeyHex, next.scriptHex(),
            "tracked continuation script must equal the emitted state-continuation output");
    }
}
