package runar.lang.sdk;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

/**
 * Testing-gap remediation Phase A5 (Java tier).
 *
 * <p>The Java tier ships NO Bitcoin Script VM — there is no canonical upstream
 * BSV Java SDK whose script interpreter could be wrapped, and project policy
 * forbids hand-rolling one (root CLAUDE.md, "Off-chain Script VM").
 *
 * <p>So these tests do NOT claim script-level validation. They pin the checks
 * that ARE genuinely available at the broadcast boundary and that a real node
 * would also apply:
 *
 * <ol>
 *   <li>STRUCTURAL — the payload must actually parse as a transaction.</li>
 *   <li>NON-VACUITY — at least one spent outpoint must be known to the
 *       provider, so the gate can never pass by checking nothing.</li>
 *   <li>VALUE CONSERVATION — when every input's outpoint is known, the outputs
 *       must not exceed the inputs.</li>
 *   <li>SCRIPT-SIZE — output scripts stay under MAX_SCRIPT_BYTES.</li>
 * </ol>
 *
 * <p>Signature/covenant validity in this tier is proven VERTICALLY instead:
 * absolute-hex pins against the other tiers' goldens, the off-chain
 * {@code ContractSimulator}, and the on-chain integration spends in
 * {@code integration/java}. See README, "How fund-path tests fail closed in the
 * Java tier".
 */
class MockBroadcastValidationTest {

    private static final String ANYONE_CAN_SPEND = "51"; // OP_TRUE
    private static final String PREV_A = "aa".repeat(32);
    private static final String PREV_B = "bb".repeat(32);

    /** One-input, one-OP_TRUE-output transaction spending {@code prevTxid:0}. */
    private static String oneInputTx(String prevTxid, long outSats) {
        RawTx tx = new RawTx();
        tx.addInput(prevTxid, 0, "");
        tx.addOutput(outSats, ANYONE_CAN_SPEND);
        return tx.toHex();
    }

    private static MockProvider seeded(String prevTxid, long satoshis, String script) {
        MockProvider p = new MockProvider();
        p.addKnownOutpoint(prevTxid, 0, script, satoshis);
        return p;
    }

    // --- acceptance ------------------------------------------------------

    @Test
    void acceptsWellFormedValueConservingSpendOfAKnownOutpoint() {
        MockProvider p = seeded(PREV_A, 10_000L, ANYONE_CAN_SPEND);
        String txid = p.broadcastRaw(oneInputTx(PREV_A, 9_000L));

        assertEquals(64, txid.length());
        assertEquals(1, p.lastValidatedInputCount());
        assertEquals(1, p.getBroadcastedTxs().size());

        MockProvider.ValidationReport r = p.lastValidationReport();
        // The tier makes NO script-validity claim. If a Java ScriptVM ever
        // lands, this expectation must change deliberately, not by accident.
        assertEquals(0, r.scriptsExecuted());
        assertEquals(1, r.totalInputs());
        assertTrue(r.valueConserved());
    }

    @Test
    void aBroadcastRegistersItsOwnOutputsSoAChainedSpendIsCheckable() {
        MockProvider p = seeded(PREV_A, 10_000L, ANYONE_CAN_SPEND);
        String first = p.broadcastRaw(oneInputTx(PREV_A, 9_000L));
        String second = p.broadcastRaw(oneInputTx(first, 8_000L));

        assertEquals(64, second.length());
        assertEquals(1, p.lastValidatedInputCount());
    }

    // --- rejection -------------------------------------------------------

    @Test
    void rejectsAPayloadThatIsNotAParseableTransaction() {
        MockProvider p = new MockProvider();
        BroadcastRejectedException e = assertThrows(
            BroadcastRejectedException.class, () -> p.broadcastRaw("deadbeef"));
        assertTrue(e.getMessage().contains("not a parseable Bitcoin transaction"), e.getMessage());
        assertEquals(MockProvider.RejectionReason.NOT_A_TRANSACTION, p.lastRejection());
    }

    @Test
    void rejectsATransactionWhoseOutputsExceedItsKnownInputs() {
        MockProvider p = seeded(PREV_A, 1_000L, ANYONE_CAN_SPEND);
        BroadcastRejectedException e = assertThrows(
            BroadcastRejectedException.class, () -> p.broadcastRaw(oneInputTx(PREV_A, 5_000L)));
        assertTrue(e.getMessage().contains("underfunded"), e.getMessage());
        assertEquals(MockProvider.RejectionReason.UNDERFUNDED, p.lastRejection());
    }

    @Test
    void rejectsATransactionNoneOfWhoseInputsItKnows() {
        MockProvider p = new MockProvider();
        BroadcastRejectedException e = assertThrows(
            BroadcastRejectedException.class, () -> p.broadcastRaw(oneInputTx(PREV_B, 1_000L)));
        assertTrue(e.getMessage().contains("checked 0 of 1 input"), e.getMessage());
        assertEquals(MockProvider.RejectionReason.NOTHING_CHECKED, p.lastRejection());
        // And the report proves the gate really had nothing to check.
        assertEquals(0, p.lastValidationReport().knownInputs());
        assertEquals(1, p.lastValidationReport().totalInputs());
    }

    // --- the governed opt-out --------------------------------------------

    @Test
    void alwaysAckProviderSkipsEveryCheck() {
        MockProvider p = MockProvider.alwaysAck();
        assertEquals(64, p.broadcastRaw("deadbeef").length());
    }

    @Test
    void disableAndEnableBroadcastValidationTogglesTheGate() {
        MockProvider p = new MockProvider();
        assertThrows(BroadcastRejectedException.class, () -> p.broadcastRaw("deadbeef"));
        p.disableBroadcastValidation();
        assertEquals(64, p.broadcastRaw("deadbeef").length());
        p.enableBroadcastValidation(true);
        assertThrows(BroadcastRejectedException.class, () -> p.broadcastRaw("deadbeef"));
    }
}
