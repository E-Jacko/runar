package runar.lang.sdk;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HexFormat;
import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * Issue #106 — {@code EMPTY_SIG} producer-side convention for OR-CHECKSIG
 * branched authorization. An OR-CHECKSIG method runs BOTH {@code OP_CHECKSIG}
 * branches ({@code ||} lowers to the non-lazy {@code OP_BOOLOR}); the failing
 * branch MUST push an empty signature (OP_0) or BIP146 NULLFAIL rejects the
 * spend. {@code EMPTY_SIG} is distinct from {@code null} (auto-sign): it is
 * never signed and encodes as OP_0.
 */
class EmptySigTest {

    private static final String ALICE = "0000000000000000000000000000000000000000000000000000000000000003";
    private static final String BOB = "0000000000000000000000000000000000000000000000000000000000000007";

    @Test
    void encodesEmptySigAsOp0() {
        assertEquals("00", ContractScript.encodeConstructorArg(RunarContract.EMPTY_SIG, "Sig"));
        assertTrue(RunarContract.isEmptySig(RunarContract.EMPTY_SIG));
        assertFalse(RunarContract.isEmptySig(null));
        assertFalse(RunarContract.isEmptySig("00"));
    }

    /** Decode the data pushes of a scriptSig. OP_0 (0x00) yields an empty push. */
    private static List<String> parsePushes(String scriptHex) {
        List<String> pushes = new ArrayList<>();
        int p = 0;
        int n = scriptHex.length() / 2;
        while (p < n) {
            int op = Integer.parseInt(scriptHex.substring(p * 2, p * 2 + 2), 16);
            p += 1;
            if (op == 0x00) {
                pushes.add(""); // OP_0 -> empty push
            } else if (op >= 0x01 && op <= 0x4b) {
                pushes.add(scriptHex.substring(p * 2, (p + op) * 2));
                p += op;
            } else if (op == 0x4c) {
                int len = Integer.parseInt(scriptHex.substring(p * 2, p * 2 + 2), 16);
                p += 1;
                pushes.add(scriptHex.substring(p * 2, (p + len) * 2));
                p += len;
            } else {
                pushes.add(""); // bare opcode (not expected here)
            }
        }
        return pushes;
    }

    private RunarContract deployOrChecksig(MockProvider provider, LocalSigner alice, LocalSigner bob)
            throws Exception {
        RunarArtifact artifact = RunarArtifact.fromJson(
            new String(EmptySigTest.class.getClassLoader()
                .getResourceAsStream("artifacts/or-checksig.runar.json").readAllBytes()));
        String pkA = HexFormat.of().formatHex(alice.pubKey());
        String pkB = HexFormat.of().formatHex(bob.pubKey());
        // Fund the caller so the stateless call can pay its fee.
        provider.addUtxo(alice.address(),
            new UTXO("ff".repeat(32), 0, 500_000L, ScriptUtils.buildP2PKHScript(alice.address())));
        RunarContract contract = new RunarContract(artifact, List.of(pkA, pkB));
        UTXO utxo = new UTXO("ab".repeat(32), 0, 50_000L, contract.lockingScript());
        contract.setCurrentUtxo(utxo);
        // Phase A5 non-vacuity: the fail-closed MockProvider must also know the
        // outpoint this call spends — injecting it straight into the contract
        // bypasses the provider, which would then have nothing to check.
        provider.addKnownOutpoint(utxo);
        return contract;
    }

    @Test
    void greenBranchBUsesOp0EmptySig() throws Exception {
        MockProvider provider = new MockProvider();
        LocalSigner alice = new LocalSigner(ALICE);
        LocalSigner bob = new LocalSigner(BOB);
        RunarContract contract = deployOrChecksig(provider, alice, bob);

        // Alice signs branch A (null -> auto); branch B is deliberately empty.
        ArrayList<Object> args = new ArrayList<>();
        args.add(null);
        args.add(RunarContract.EMPTY_SIG);
        RunarContract.CallOutcome out = contract.call("execute", args, null, provider, alice);

        RawTx tx = RawTxParser.parse(out.rawTxHex());
        List<String> pushes = parsePushes(tx.inputs.get(0).scriptSigHex);
        // Exactly one real signature and exactly one empty (OP_0) push.
        long empties = pushes.stream().filter(String::isEmpty).count();
        long realSigs = pushes.stream().filter(s -> s.startsWith("30")).count();
        assertEquals(1, empties, "branch B must be OP_0 (empty); pushes=" + pushes);
        assertEquals(1, realSigs, "branch A must carry one real DER signature; pushes=" + pushes);
    }

    @Test
    void redBaselineNullNullFillsBothBranchesWithNonEmptySigs() throws Exception {
        MockProvider provider = new MockProvider();
        LocalSigner alice = new LocalSigner(ALICE);
        LocalSigner bob = new LocalSigner(BOB);
        RunarContract contract = deployOrChecksig(provider, alice, bob);

        // Both slots auto -> the SDK fills BOTH with Alice's signature. The
        // non-matching branch's non-empty invalid sig is exactly the byte
        // pattern BIP146 NULLFAIL rejects (wire-level RED baseline).
        ArrayList<Object> args = new ArrayList<>();
        args.add(null);
        args.add(null);
        RunarContract.CallOutcome out = contract.call("execute", args, null, provider, alice);

        RawTx tx = RawTxParser.parse(out.rawTxHex());
        List<String> pushes = parsePushes(tx.inputs.get(0).scriptSigHex);
        long empties = pushes.stream().filter(String::isEmpty).count();
        long realSigs = pushes.stream().filter(s -> s.startsWith("30")).count();
        assertEquals(0, empties, "no OP_0 branch under [null, null]; pushes=" + pushes);
        assertEquals(2, realSigs, "both branches carry a non-empty signature; pushes=" + pushes);
    }
}
