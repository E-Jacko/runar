package runar.lang.sdk;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TransactionBuilderTest {

    private static final String PRIV =
        "18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725";

    @Test
    void deployTxParsesBackToMatchingInputsAndOutputs() {
        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();

        // Fund the signer's address with a single P2PKH UTXO.
        String fundingScript = ScriptUtils.buildP2PKHScript(signer.address());
        UTXO funding = new UTXO("ab".repeat(32), 0, 100_000L, fundingScript);
        provider.addUtxo(signer.address(), funding);

        // Contract locking script: OP_RETURN-preceded data is irrelevant; use a
        // minimal P2PKH-shaped script for structural testing.
        String contractScript = ScriptUtils.buildP2PKHScript("00".repeat(20));

        TransactionBuilder.DeployResult result =
            TransactionBuilder.buildDeployWithLockingScript(
                contractScript, provider, signer, 10_000L, null
            );

        // Structural parse-back.
        RawTx parsed = RawTxParser.parse(result.txHex());
        assertEquals(1, parsed.inputs.size(), "one funding input");
        assertEquals("ab".repeat(32), parsed.inputs.get(0).prevTxid);
        assertEquals(0, parsed.inputs.get(0).prevVout);
        assertEquals(2, parsed.outputs.size(), "contract + change outputs");
        assertEquals(10_000L, parsed.outputs.get(0).satoshis);
        assertEquals(contractScript, parsed.outputs.get(0).scriptPubKeyHex);
        // Change equals totalIn - contract - fee (reasonable upper bound test).
        assertTrue(parsed.outputs.get(1).satoshis > 0 && parsed.outputs.get(1).satoshis < 100_000L);
        // Signed input: scriptSig is <sig><pubkey>.
        assertFalse(parsed.inputs.get(0).scriptSigHex.isEmpty(), "input must be signed");
    }

    @Test
    void deployRejectsInsufficientFunds() {
        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();

        String fundingScript = ScriptUtils.buildP2PKHScript(signer.address());
        provider.addUtxo(signer.address(), new UTXO("cd".repeat(32), 0, 100L, fundingScript));

        assertThrows(IllegalStateException.class, () ->
            TransactionBuilder.buildDeployWithLockingScript(
                ScriptUtils.buildP2PKHScript("00".repeat(20)),
                provider, signer, 10_000L, null
            )
        );
    }

    @Test
    void callTxLocktimeOverrideAppearsInTx() {
        // Issue #40: a caller-supplied non-zero locktime must appear in the
        // built call tx's nLockTime field.
        UTXO contractUtxo = new UTXO("ab".repeat(32), 0, 100_000L,
            ScriptUtils.buildP2PKHScript("00".repeat(20)));
        UTXO funding = new UTXO("cd".repeat(32), 0, 50_000L,
            ScriptUtils.buildP2PKHScript("11".repeat(20)));

        TransactionBuilder.CallTxResult result =
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo, "51", null, 0L, List.of(),
                List.of(funding), "22".repeat(20),
                100L, 800_000
            );

        RawTx parsed = RawTxParser.parse(result.tx().toHex());
        assertEquals(800_000, parsed.locktime);
    }

    @Test
    void callTxLocktimeDefaultsToZero() {
        // Default (no locktime arg) must still write 0 — back-compatible.
        UTXO contractUtxo = new UTXO("ab".repeat(32), 0, 100_000L,
            ScriptUtils.buildP2PKHScript("00".repeat(20)));
        UTXO funding = new UTXO("cd".repeat(32), 0, 50_000L,
            ScriptUtils.buildP2PKHScript("11".repeat(20)));

        TransactionBuilder.CallTxResult result =
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo, "51", null, 0L, List.of(),
                List.of(funding), "22".repeat(20),
                100L
            );

        RawTx parsed = RawTxParser.parse(result.tx().toHex());
        assertEquals(0, parsed.locktime);
    }

    // ------------------------------------------------------------------
    // Finding C3 — fail closed ONLY on genuinely underfunded calls
    // ------------------------------------------------------------------

    /** Contract UTXO shaped like a deployed contract output. */
    private static UTXO contractUtxo(long satoshis) {
        return new UTXO("ab".repeat(32), 0, satoshis,
            ScriptUtils.buildP2PKHScript("00".repeat(20)));
    }

    @Test
    void exactCoverZeroFeeContinuationIsBuiltNotRejected() {
        // Issue #116 class: the continuation keeps the FULL input value, there
        // is no funding UTXO and no change output, so the tx pays zero fee and
        // change == -fee (negative). The covenant accepts a no-change spend, so
        // the other six SDK tiers build this tx. Java must not reject it just
        // because change < 0 — the only value-invalid case is
        // totalInput < contractOutputSats.
        TransactionBuilder.CallTxResult result = assertDoesNotThrow(() ->
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo(50_000L), "51", "52", 50_000L, List.of(),
                List.of(), "22".repeat(20), 100L
            )
        );

        RawTx parsed = RawTxParser.parse(result.tx().toHex());
        assertEquals(1, parsed.inputs.size(), "contract input only");
        assertEquals(1, parsed.outputs.size(), "continuation only — no change output");
        assertEquals(50_000L, parsed.outputs.get(0).satoshis, "full input forwarded");
        assertEquals("52", parsed.outputs.get(0).scriptPubKeyHex);
        assertTrue(result.fundingUtxos().isEmpty(), "no funding selected");
        assertEquals(0L, result.changeAmount(), "changeAmount clamped to 0 (TS/Go parity)");
    }

    @Test
    void exactCoverZeroFeeContinuationIsBuiltNotRejectedOrdered() {
        // Same case through the finding-G1 ordered path.
        TransactionBuilder.CallTxResult result = assertDoesNotThrow(() ->
            TransactionBuilder.buildCallTransactionFullOrdered(
                contractUtxo(50_000L), "51",
                List.of(new TransactionBuilder.ContractOutput(50_000L, "52")),
                List.of(), List.of(), "22".repeat(20), 100L, 0
            )
        );

        RawTx parsed = RawTxParser.parse(result.tx().toHex());
        assertEquals(1, parsed.outputs.size(), "continuation only — no change output");
        assertEquals(50_000L, parsed.outputs.get(0).satoshis);
        assertEquals(0L, result.changeAmount());
    }

    @Test
    void underfundedContinuationStillFailsClosed() {
        // Genuinely underfunded: the continuation demands more than every input
        // provides, so the tx spends more than it takes in and can never
        // confirm. Must still throw.
        IllegalStateException e = assertThrows(IllegalStateException.class, () ->
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo(40_000L), "51", "52", 50_000L, List.of(),
                List.of(), "22".repeat(20), 100L
            )
        );
        assertTrue(e.getMessage().contains("insufficient funds"), e.getMessage());
    }

    @Test
    void underfundedContinuationStillFailsClosedOrdered() {
        IllegalStateException e = assertThrows(IllegalStateException.class, () ->
            TransactionBuilder.buildCallTransactionFullOrdered(
                contractUtxo(40_000L), "51",
                List.of(new TransactionBuilder.ContractOutput(50_000L, "52")),
                List.of(), List.of(), "22".repeat(20), 100L, 0
            )
        );
        assertTrue(e.getMessage().contains("insufficient funds"), e.getMessage());
    }

    @Test
    void dataOutputsCountTowardTheUnderfundedGuard() {
        // Exact-cover continuation PLUS a data output that nothing pays for:
        // totalInput (50_000) < contract output (50_000) + data output (1).
        IllegalStateException e = assertThrows(IllegalStateException.class, () ->
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo(50_000L), "51", "52", 50_000L,
                List.of(new TransactionBuilder.DataOutput(1L, "6a01ff")),
                List.of(), "22".repeat(20), 100L
            )
        );
        assertTrue(e.getMessage().contains("insufficient funds"), e.getMessage());
    }

    @Test
    void fundedCallStillSelectsUtxosAndEmitsChange() {
        // Selection strategy unchanged: funding is still pulled in largest-first
        // until the fee is covered, and the surplus still becomes change.
        UTXO small = new UTXO("cd".repeat(32), 0, 500L,
            ScriptUtils.buildP2PKHScript("11".repeat(20)));
        UTXO large = new UTXO("ef".repeat(32), 1, 20_000L,
            ScriptUtils.buildP2PKHScript("11".repeat(20)));

        TransactionBuilder.CallTxResult result =
            TransactionBuilder.buildCallTransactionFull(
                contractUtxo(50_000L), "51", "52", 50_000L, List.of(),
                List.of(small, large), "22".repeat(20), 100L
            );

        assertEquals(1, result.fundingUtxos().size(), "largest-first: one UTXO suffices");
        assertEquals(20_000L, result.fundingUtxos().get(0).satoshis());
        assertTrue(result.changeAmount() > 0, "surplus becomes change");
        RawTx parsed = RawTxParser.parse(result.tx().toHex());
        assertEquals(2, parsed.inputs.size());
        assertEquals(2, parsed.outputs.size(), "continuation + change");
        assertEquals(result.changeAmount(), parsed.outputs.get(1).satoshis);
    }

    @Test
    void deployUsesDefaultChangeAddressFromSignerWhenUnspecified() {
        LocalSigner signer = new LocalSigner(PRIV);
        MockProvider provider = new MockProvider();
        String fundingScript = ScriptUtils.buildP2PKHScript(signer.address());
        provider.addUtxo(signer.address(), new UTXO("ee".repeat(32), 0, 50_000L, fundingScript));

        TransactionBuilder.DeployResult r = TransactionBuilder.buildDeployWithLockingScript(
            ScriptUtils.buildP2PKHScript("11".repeat(20)),
            provider, signer, 1_000L, null
        );
        RawTx parsed = RawTxParser.parse(r.txHex());
        // Change output's script must be P2PKH to signer's own address.
        String expectedChangeScript = ScriptUtils.buildP2PKHScript(signer.address());
        assertEquals(expectedChangeScript, parsed.outputs.get(1).scriptPubKeyHex);
    }
}
