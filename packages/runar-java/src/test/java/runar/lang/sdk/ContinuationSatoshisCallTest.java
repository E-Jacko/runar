package runar.lang.sdk;

import java.math.BigInteger;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Deep-review follow-on (SDK funds bug, separate from the C20/C27 compiler
 * cluster): the stateful CALL path must build the state continuation at the
 * amount the contract's explicit {@code this.addOutput(<sats>, ...)} specifies —
 * NOT default it to the spent input's value.
 *
 * <p>The ANF interpreter already records the addOutput satoshis (finding G1
 * reads it, but ONLY on the raw-output-present branch). A stateful method whose
 * ONLY output is {@code this.addOutput(1000, this.count)} therefore had its
 * continuation built at the input value (e.g. 1 sat), so the covenant's
 * hashOutputs binding rejected the spend — funds stranded. This generalizes G1
 * to the no-raw single-continuation path.
 *
 * <pre>{@code
 *     class SatCounter extends StatefulSmartContract {
 *       count: bigint;
 *       inc() { this.count = this.count + 1n; this.addOutput(1000n, this.count); }
 *     }
 * }</pre>
 *
 * <p>Deployed at the default (1 sat) and called with NO satoshis option, the
 * built call tx's continuation output (index 0) must carry 1000 sats.
 */
class ContinuationSatoshisCallTest {

    private static final String PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";

    @Test
    void continuationCarriesExplicitAddOutputAmountNotInputValue() throws Exception {
        RunarArtifact artifact;
        try (var in = ContinuationSatoshisCallTest.class.getClassLoader()
                .getResourceAsStream("artifacts/sat-counter.runar.json")) {
            assertTrue(in != null, "sat-counter artifact resource must exist");
            artifact = RunarArtifact.fromJson(new String(in.readAllBytes()));
        }
        assertTrue(artifact.isStateful(), "SatCounter is a StatefulSmartContract");

        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();
        // Funding UTXO covers the 1000-sat continuation + fee.
        provider.addUtxo(signer.address(),
            new UTXO("ff".repeat(32), 0, 500_000L,
                ScriptUtils.buildP2PKHScript(signer.address())));

        // Deploy at the default (1 sat); the call's addOutput(1000) must OVERRIDE it.
        RunarContract contract = new RunarContract(artifact, List.of(BigInteger.valueOf(5)));
        contract.deploy(provider, signer, 1L, signer.address());

        // Call inc() WITHOUT any satoshis option (3rd arg is stateUpdates → null).
        contract.call("inc", List.of(), null, provider, signer);

        // State advanced 5 -> 6 (this.count = this.count + 1).
        assertEquals(BigInteger.valueOf(6), contract.state().get("count"),
            "count must advance 5 -> 6");

        // Continuation output (index 0) must carry the addOutput amount (1000),
        // NOT the spent input's value (1). RED before the fix: got 1, want 1000.
        List<String> txs = provider.getBroadcastedTxs();
        RawTx callTx = RawTxParser.parse(txs.get(txs.size() - 1));
        RawTx.Output cont = callTx.outputs.get(0);
        assertEquals(1000L, cont.satoshis,
            "continuation output 0 must carry the explicit addOutput(1000) amount, "
                + "not the input value");

        // The SDK must also track the continuation UTXO at its real value.
        assertEquals(1000L, contract.currentUtxo().satoshis(),
            "tracked continuation UTXO must carry 1000 sats, not the input value");
    }
}
