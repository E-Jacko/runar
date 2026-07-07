package runar.lang.sdk;

import java.math.BigInteger;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Coverage for the restore-path SDK fixes:
 *
 * <ul>
 *   <li>#119 — fromUtxo recovers real constructor args from the deployed script
 *       (via {@link ContractScript#extractConstructorArgs}) instead of leaving
 *       them empty/zero.</li>
 *   <li>#132 — {@link RunarContract#getCodeSepIndex} byte-walks the live script,
 *       so a chain-loaded contract's OP_CODESEPARATOR offset is correct even
 *       when the in-memory constructor args are placeholders.</li>
 * </ul>
 */
class RunarContractRestoreFixesTest {

    // ------------------------------------------------------------------
    // #119 — fromUtxo recovers real constructor args
    // ------------------------------------------------------------------

    @Test
    void extractConstructorArgsRoundTrips() {
        // Synthetic artifact: template with two OP_0 placeholders — a ByteString
        // slot (paramIndex 0, byte offset 1) and a bigint slot (paramIndex 1,
        // byte offset 3). renderLockingScript substitutes real args; the
        // extractor must recover them from the deployed script.
        String template = "52" + "00" + "76" + "00" + "ac"; // filler,slot0,filler,slot1,filler
        RunarArtifact.ABI abi = new RunarArtifact.ABI(
            new RunarArtifact.ABIConstructor(List.of(
                new RunarArtifact.ABIParam("pkh", "Ripemd160", null),
                new RunarArtifact.ABIParam("amt", "bigint", null))),
            List.of());
        RunarArtifact artifact = new RunarArtifact(
            "1", "test", "Synthetic", abi, template, "", "",
            List.of(),  // no state fields
            List.of(new RunarArtifact.ConstructorSlot(0, 1),
                    new RunarArtifact.ConstructorSlot(1, 3)),
            List.of(), null, List.of());

        String pkh = "aa".repeat(20);
        List<Object> args = List.of(pkh, BigInteger.valueOf(1000));
        String deployed = ContractScript.renderLockingScript(artifact, args, null);

        List<Object> recovered = ContractScript.extractConstructorArgs(artifact, deployed);
        assertEquals(2, recovered.size());
        assertEquals(pkh, recovered.get(0), "ByteString ctor arg recovered as hex");
        assertEquals(BigInteger.valueOf(1000), recovered.get(1), "bigint ctor arg recovered as script number");
    }

    @Test
    void extractConstructorArgsFallsBackToZeroForMissingSlot() {
        // A param with no constructor slot (a mutable state field, whose value
        // lives in the OP_RETURN state section) falls back to 0.
        String template = "52" + "00" + "ac";  // one slot at byte offset 1
        RunarArtifact.ABI abi = new RunarArtifact.ABI(
            new RunarArtifact.ABIConstructor(List.of(
                new RunarArtifact.ABIParam("baked", "bigint", null),
                new RunarArtifact.ABIParam("stateOnly", "bigint", null))),
            List.of());
        RunarArtifact artifact = new RunarArtifact(
            "1", "test", "Synthetic", abi, template, "", "",
            List.of(),
            List.of(new RunarArtifact.ConstructorSlot(0, 1)),  // only param 0 has a slot
            List.of(), null, List.of());

        String deployed = ContractScript.renderLockingScript(
            artifact, List.of(BigInteger.valueOf(7), BigInteger.valueOf(99)), null);
        List<Object> recovered = ContractScript.extractConstructorArgs(artifact, deployed);
        assertEquals(BigInteger.valueOf(7), recovered.get(0));
        assertEquals(BigInteger.ZERO, recovered.get(1), "slotless param falls back to 0");
    }

    // ------------------------------------------------------------------
    // #132 — getCodeSepIndex byte-walks the live script, ignoring in-memory args
    // ------------------------------------------------------------------

    @Test
    void codeSepIndexByteWalksLiveScriptRegardlessOfArgs() {
        // Template: <slot@0> ab(OP_CODESEPARATOR@1) 75(OP_DROP@2) — a constructor
        // slot sits BEFORE the OP_CODESEPARATOR, so a multi-byte arg push shifts
        // the real codesep position past the template's index. adjustCodeSepOffset
        // would recompute the shift from in-memory args; the byte-walk reads the
        // true on-chain position. Two contracts sharing the same deployed script
        // but holding DIFFERENT in-memory args must resolve the SAME codesep index.
        String template = "00" + "ab" + "75";
        RunarArtifact.ABI abi = new RunarArtifact.ABI(
            new RunarArtifact.ABIConstructor(List.of(
                new RunarArtifact.ABIParam("amt", "bigint", null))),
            List.of(new RunarArtifact.ABIMethod("m", List.of(), true, false, null)));
        RunarArtifact artifact = new RunarArtifact(
            "1", "test", "Synthetic", abi, template, "", "",
            List.of(),
            List.of(new RunarArtifact.ConstructorSlot(0, 0)),
            List.of(), 1, List.of(1));  // codeSeparatorIndex/indices = template offset 1

        // Deploy from the REAL arg (1000 → a 3-byte push, shifting codesep by +2).
        String deployed = ContractScript.renderLockingScript(artifact, List.of(BigInteger.valueOf(1000)), null);
        UTXO utxo = new UTXO("aa".repeat(32), 0, 1000L, deployed);

        RunarContract real = new RunarContract(artifact, List.of(BigInteger.valueOf(1000)));
        real.setCurrentUtxo(utxo);
        RunarContract placeholder = new RunarContract(artifact, List.of(BigInteger.ZERO));
        placeholder.setCurrentUtxo(utxo);

        int realOffset = real.getCodeSepIndex(0);
        int placeholderOffset = placeholder.getCodeSepIndex(0);
        assertEquals(realOffset, placeholderOffset,
            "getCodeSepIndex must byte-walk the live script, so wrong in-memory args do not change it");
        // The OP_CODESEPARATOR sits after the 3-byte (02 e8 03) arg push at byte
        // offset 3 in the deployed script.
        assertEquals(3, realOffset, "byte-walked codesep offset reflects the real on-chain push width");
    }
}
