package runar.lang.sdk;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * In-memory {@link Provider} for tests. Parity with
 * {@code packages/runar-go/sdk_provider.go} {@code MockProvider}.
 *
 * <p>Tests inject UTXOs via {@link #addUtxo(String, UTXO)} and inspect
 * broadcasts via {@link #getBroadcastedTxs()}.
 *
 * <p>Broadcast validation is DEFAULT-ON (testing-gap remediation Phase A5).
 * This tier has NO Bitcoin Script VM, so it makes no script-validity claim —
 * see {@link #validateBroadcast(String)} for exactly what it does and does not
 * check, and README "How fund-path tests fail closed in the Java tier".
 */
public final class MockProvider implements Provider {

    /** Why a broadcast was refused. */
    public enum RejectionReason {
        NONE,
        /** The payload does not parse as a Bitcoin transaction at all. */
        NOT_A_TRANSACTION,
        /**
         * No spent outpoint is known to this provider, so validation would
         * have checked NOTHING and passed vacuously.
         */
        NOTHING_CHECKED,
        /** Every input is known and the outputs exceed them. */
        UNDERFUNDED
    }

    /**
     * What a validating broadcast actually checked.
     *
     * <p>{@code scriptsExecuted} is ALWAYS 0 in this tier and is present
     * precisely so that fact stays visible: Java ships no Bitcoin Script VM
     * (root CLAUDE.md, "Off-chain Script VM" — there is no canonical upstream
     * BSV Java SDK to wrap, and project policy forbids hand-rolling an
     * interpreter). If a Java ScriptVM ever lands, extend this record rather
     * than silently implying coverage that does not exist.
     */
    public record ValidationReport(
        int scriptsExecuted,
        int knownInputs,
        int totalInputs,
        boolean valueConserved
    ) {
        static final ValidationReport EMPTY = new ValidationReport(0, 0, 0, false);
    }

    private record KnownOutpoint(String scriptHex, long satoshis) {}

    private final Map<String, List<UTXO>> utxosByAddress = new HashMap<>();
    private final Map<String, UTXO> utxosByOutpoint = new HashMap<>();
    private final Map<String, KnownOutpoint> knownOutpoints = new HashMap<>();
    private final List<String> broadcasted = new ArrayList<>();
    private final String network;
    private int broadcastCount = 0;
    private long feeRate = 100L;
    /**
     * Gates the fail-closed check in {@link #broadcastRaw(String)}. Default
     * true; the opt-out is governed by {@code always_ack_allowlist.json} (see
     * {@code AlwaysAckAllowlistTest}).
     */
    private boolean validateBroadcasts = true;
    private ValidationReport lastReport = ValidationReport.EMPTY;
    private RejectionReason lastRejection = RejectionReason.NONE;

    public MockProvider() {
        this("testnet");
    }

    public MockProvider(String network) {
        this.network = (network == null || network.isEmpty()) ? "testnet" : network;
    }

    /**
     * A MockProvider whose {@link #broadcastRaw(String)} never validates — the
     * pre-Phase-A5 behaviour.
     *
     * <p>FOR ALLOWLISTED TESTS ONLY: every test file that calls this (or the
     * other opt-outs) must carry a matching entry in
     * {@code always_ack_allowlist.json}, enforced by
     * {@code AlwaysAckAllowlistTest}. Fund-path deploy/call tests must not use
     * it.
     */
    public static MockProvider alwaysAck() {
        return alwaysAck("testnet");
    }

    /** @see #alwaysAck() */
    public static MockProvider alwaysAck(String network) {
        MockProvider p = new MockProvider(network);
        p.validateBroadcasts = false;
        return p;
    }

    /**
     * Turn the fail-closed broadcast check on or off. Passing {@code false} is
     * an allowlisted opt-out — see {@link #alwaysAck()}.
     */
    public void enableBroadcastValidation(boolean enabled) {
        this.validateBroadcasts = enabled;
    }

    /** Restore the legacy always-ack broadcast. Allowlisted opt-out. */
    public void disableBroadcastValidation() {
        this.validateBroadcasts = false;
    }

    /**
     * Report from the most recent validating broadcast. Exposed so a test can
     * assert its gate is NOT vacuous.
     */
    public ValidationReport lastValidationReport() {
        return lastReport;
    }

    /**
     * Number of spent outpoints the most recent validating broadcast actually
     * recognised and checked.
     */
    public int lastValidatedInputCount() {
        return lastReport.knownInputs();
    }

    /** Why the most recent broadcast was refused ({@code NONE} if it was not). */
    public RejectionReason lastRejection() {
        return lastRejection;
    }

    public String getNetwork() {
        return network;
    }

    public void addUtxo(String address, UTXO utxo) {
        utxosByAddress.computeIfAbsent(address, k -> new ArrayList<>()).add(utxo);
        utxosByOutpoint.put(outpointKey(utxo.txid(), utxo.outputIndex()), utxo);
        addKnownOutpoint(utxo.txid(), utxo.outputIndex(), utxo.scriptHex(), utxo.satoshis());
    }

    /**
     * Record an outpoint's script + value so broadcast validation can reason
     * about it. Needed when a contract UTXO is injected straight into a
     * {@code RunarContract} rather than discovered through this provider.
     */
    public void addKnownOutpoint(String txid, int vout, String scriptHex, long satoshis) {
        if (txid == null || txid.isEmpty() || scriptHex == null || scriptHex.isEmpty()) return;
        knownOutpoints.put(outpointKey(txid, vout), new KnownOutpoint(scriptHex, satoshis));
    }

    /** @see #addKnownOutpoint(String, int, String, long) */
    public void addKnownOutpoint(UTXO utxo) {
        if (utxo == null) return;
        addKnownOutpoint(utxo.txid(), utxo.outputIndex(), utxo.scriptHex(), utxo.satoshis());
    }

    public List<String> getBroadcastedTxs() {
        return Collections.unmodifiableList(broadcasted);
    }

    public void setFeeRate(long rate) {
        this.feeRate = rate;
    }

    @Override
    public long getFeeRate() {
        return feeRate;
    }

    @Override
    public List<UTXO> listUtxos(String address) {
        List<UTXO> utxos = new ArrayList<>(utxosByAddress.getOrDefault(address, Collections.emptyList()));
        // DoS-bound: reject pathological scripts at the provider boundary.
        for (UTXO u : utxos) {
            if (u.scriptHex() == null || u.scriptHex().isEmpty()) continue;
            ScriptSizeExceededError.assertScriptHexUnderLimit(
                u.scriptHex(), InputLimits.MAX_SCRIPT_BYTES,
                "MockProvider.listUtxos(" + address + ")"
            );
        }
        return utxos;
    }

    /**
     * Validate the transaction (unless validation has been opted out of) and
     * then record it, returning a deterministic fake txid.
     *
     * <p>Fail-closed by default (testing-gap remediation Phase A5). This tier
     * has NO Bitcoin Script VM, so it makes no script-validity claim — see
     * {@link #validateBroadcast(String)}.
     *
     * @throws BroadcastRejectedException when the payload is not a
     *     transaction, no spent outpoint is known (vacuous validation), or the
     *     outputs exceed the known inputs.
     */
    @Override
    public String broadcastRaw(String txHex) {
        RawTx parsed = null;
        if (validateBroadcasts) {
            parsed = validateBroadcast(txHex);
        }
        broadcasted.add(txHex);
        broadcastCount++;
        String prefix = txHex.length() >= 16 ? txHex.substring(0, 16) : txHex;
        String fakeTxid = mockHash64("mock-broadcast-" + broadcastCount + "-" + prefix);
        if (parsed != null) {
            // Register this tx's own outputs so a chained call (spending the
            // continuation this broadcast just created) is checkable too.
            for (int i = 0; i < parsed.outputs.size(); i++) {
                RawTx.Output out = parsed.outputs.get(i);
                addKnownOutpoint(fakeTxid, i, out.scriptPubKeyHex, out.satoshis);
            }
        }
        return fakeTxid;
    }

    /**
     * Fail-closed broadcast validation (testing-gap remediation Phase A5).
     *
     * <p>WHAT THIS CHECKS — and, just as importantly, what it does not.
     *
     * <p>The Java tier ships no Bitcoin Script VM: there is no canonical
     * upstream BSV Java SDK whose script interpreter could be wrapped, and
     * project policy forbids hand-rolling one (root CLAUDE.md, "Off-chain
     * Script VM"). So this method makes NO claim about signature or covenant
     * validity. It applies the checks that are genuinely available from the
     * serialized bytes alone:
     *
     * <ol>
     *   <li>STRUCTURAL — the payload must parse as a Bitcoin transaction.</li>
     *   <li>NON-VACUITY — at least one spent outpoint must be known here, so
     *       the gate can never pass by checking nothing.</li>
     *   <li>VALUE CONSERVATION — when every input is known, outputs &le;
     *       inputs.</li>
     *   <li>SCRIPT-SIZE — every output script stays under
     *       {@link InputLimits#MAX_SCRIPT_BYTES}.</li>
     * </ol>
     *
     * <p>Script-level correctness for this tier is proven VERTICALLY instead:
     * absolute-hex pins against the peer tiers' goldens, the off-chain
     * {@code ContractSimulator}, and the on-chain integration spends in
     * {@code integration/java}.
     */
    private RawTx validateBroadcast(String txHex) {
        lastRejection = RejectionReason.NONE;
        lastReport = ValidationReport.EMPTY;

        RawTx tx;
        try {
            tx = RawTxParser.parse(txHex);
        } catch (RuntimeException e) {
            lastRejection = RejectionReason.NOT_A_TRANSACTION;
            throw new BroadcastRejectedException(
                "MockProvider: refusing to broadcast — payload is not a parseable Bitcoin "
                + "transaction (" + (txHex == null ? 0 : txHex.length() / 2) + " byte(s)): "
                + e + ". A real node would reject it outright.");
        }
        if (tx.inputs.isEmpty()) {
            lastRejection = RejectionReason.NOT_A_TRANSACTION;
            throw new BroadcastRejectedException(
                "MockProvider: refusing to broadcast — parsed transaction has no inputs. "
                + "A real node would reject it outright.");
        }

        int knownInputs = 0;
        long totalKnownIn = 0;
        boolean allInputsKnown = true;
        for (RawTx.Input in : tx.inputs) {
            KnownOutpoint ko = knownOutpoints.get(outpointKey(in.prevTxid, in.prevVout));
            if (ko == null) {
                allInputsKnown = false;
            } else {
                knownInputs++;
                totalKnownIn += ko.satoshis();
            }
        }

        long totalOut = 0;
        for (int i = 0; i < tx.outputs.size(); i++) {
            RawTx.Output out = tx.outputs.get(i);
            if (out.scriptPubKeyHex != null && !out.scriptPubKeyHex.isEmpty()) {
                ScriptSizeExceededError.assertScriptHexUnderLimit(
                    out.scriptPubKeyHex, InputLimits.MAX_SCRIPT_BYTES,
                    "MockProvider.broadcastRaw output " + i);
            }
            totalOut += out.satoshis;
        }

        lastReport = new ValidationReport(
            0, // this tier has no Script VM — see the javadoc above
            knownInputs, tx.inputs.size(), allInputsKnown);

        if (knownInputs == 0) {
            // A gate that validates nothing is worse than no gate.
            lastRejection = RejectionReason.NOTHING_CHECKED;
            throw new BroadcastRejectedException(
                "MockProvider: refusing to broadcast — checked 0 of " + tx.inputs.size()
                + " input(s): no spent outpoint is known to this provider, so validation "
                + "would pass vacuously. Seed the spent outpoints via addUtxo / "
                + "addKnownOutpoint, or use MockProvider.alwaysAck() (allowlisted) if this "
                + "test genuinely needs always-ack");
        }
        if (allInputsKnown && totalOut > totalKnownIn) {
            lastRejection = RejectionReason.UNDERFUNDED;
            throw new BroadcastRejectedException(
                "MockProvider: refusing to broadcast invalid transaction: underfunded: "
                + "outputs (" + totalOut + " sats) exceed known inputs ("
                + totalKnownIn + " sats)");
        }
        return tx;
    }

    @Override
    public UTXO getUtxo(String txid, int vout) {
        UTXO u = utxosByOutpoint.get(outpointKey(txid, vout));
        if (u != null && u.scriptHex() != null && !u.scriptHex().isEmpty()) {
            ScriptSizeExceededError.assertScriptHexUnderLimit(
                u.scriptHex(), InputLimits.MAX_SCRIPT_BYTES,
                "MockProvider.getUtxo(" + txid + ":" + vout + ")"
            );
        }
        return u;
    }

    private static String outpointKey(String txid, int vout) {
        return txid + ":" + vout;
    }

    // ------------------------------------------------------------------
    // Deterministic mock hash (matches Go mockHash64)
    // ------------------------------------------------------------------

    static String mockHash64(String input) {
        int h0 = 0x6a09e667;
        int h1 = 0xbb67ae85;
        int h2 = 0x3c6ef372;
        int h3 = 0xa54ff53a;
        for (int i = 0; i < input.length(); i++) {
            int c = input.charAt(i) & 0xff;
            h0 = (h0 ^ c) * 0x01000193;
            h1 = (h1 ^ c) * 0x01000193;
            h2 = (h2 ^ c) * 0x01000193;
            h3 = (h3 ^ c) * 0x01000193;
        }
        int[] parts = {h0, h1, h2, h3, h0 ^ h2, h1 ^ h3, h0 ^ h1, h2 ^ h3};
        StringBuilder sb = new StringBuilder(64);
        for (int p : parts) {
            sb.append(String.format("%08x", p));
        }
        return sb.toString();
    }
}
