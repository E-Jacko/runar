package runar.lang.sdk;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Issue #42: terminal-method sighash subscript byte-walker.
 *
 * <p>The on-chain script trims its sighash subscript at the method's
 * OP_CODESEPARATOR. {@link RunarContract#findCodesepOffsets(String)} must
 * recover the true byte position by walking the script, correctly skipping
 * push-data (which may itself contain a 0xab byte) and all BSV push opcodes.
 */
class CodesepOffsetsTest {

    @Test
    void returnsRealBytePositionSkippingPushData() {
        // 51            OP_1
        // 02 ab cd      push 2 bytes (0xab inside push-data, must be ignored)
        // ab            OP_CODESEPARATOR  <- real, byte offset 4
        // ac            OP_CHECKSIG
        assertEquals(List.of(4), RunarContract.findCodesepOffsets("5102abcdabac"));
    }

    @Test
    void handlesPushData1() {
        // 4c (OP_PUSHDATA1) 02 (len) abab (data, contains 0xab) ab (real codesep)
        assertEquals(List.of(4), RunarContract.findCodesepOffsets("4c02ababab"));
    }

    @Test
    void trimsSubscriptAtRealCodesepBytePosition() {
        String fullScript = "5102abcdabac"; // real codesep at byte index 4
        List<Integer> offsets = RunarContract.findCodesepOffsets(fullScript);
        assertEquals(List.of(4), offsets);
        int codeSepIdx = offsets.get(0);
        String subscript = fullScript.substring((codeSepIdx + 1) * 2);
        // Only the OP_CHECKSIG (ac) after the separator remains.
        assertEquals("ac", subscript);
    }

    @Test
    void returnsEmptyWhenNoCodesep() {
        assertEquals(List.of(),
            RunarContract.findCodesepOffsets("76a914" + "00".repeat(20) + "88ac"));
    }

    // ------------------------------------------------------------------
    // C11 — the codesep scan must stop at the OP_RETURN state separator.
    //
    // Everything after OP_RETURN is raw state DATA, not script. Several state
    // field types are serialised WITHOUT a push prefix (StateSerializer:
    // int/bigint -> 8 raw little-endian bytes, PubKey/Sha256/Point -> the raw
    // value), so walking the state region as if it were code decodes arbitrary
    // payload bytes as opcodes. TS (`_codeScript`, contract.ts:2126) and Go
    // (`codeScript`, sdk_contract.go:1495) both bound the walk at the last
    // OP_RETURN; Java walked the whole UTXO script.
    // ------------------------------------------------------------------

    /** Code part: OP_1 | OP_CODESEPARATOR@1 | OP_DROP. One real separator at byte 1. */
    private static final String CODE_PART = "51" + "ab" + "75";

    private static RunarArtifact statefulArtifact(
        String stateFieldType, Integer codeSepIndex, List<Integer> codeSepIndices
    ) {
        RunarArtifact.ABI abi = new RunarArtifact.ABI(
            new RunarArtifact.ABIConstructor(List.of()),
            List.of(new RunarArtifact.ABIMethod("first", List.of(), true, false, null),
                    new RunarArtifact.ABIMethod("second", List.of(), true, false, null)));
        return new RunarArtifact(
            "1", "test", "Synthetic", abi, CODE_PART, "", "",
            List.of(new RunarArtifact.StateField("v", stateFieldType, 0, null, null)),
            List.of(), List.of(), codeSepIndex, codeSepIndices);
    }

    private static RunarContract restoredWithState(RunarArtifact artifact, String stateHex) {
        String deployed = CODE_PART + "6a" + stateHex;
        RunarContract c = new RunarContract(artifact, List.of());
        c.setCurrentUtxo(new UTXO("aa".repeat(32), 0, 1000L, deployed));
        return c;
    }

    @Test
    void codeSepScanDoesNotWalkRawStateBytesAsOpcodes() {
        // A PubKey state field holds 33 RAW bytes (no push prefix). This one is a
        // well-formed compressed key, but bytes 4..8 of the payload happen to read
        // as OP_PUSHDATA4 with a length whose top bit is set. Java's byte-walker
        // stores that length in a signed int, so the cursor jumps *backwards* by
        // ~1.5 GB — past the start of the string — and byteAt() blows up with
        // StringIndexOutOfBoundsException. ~0.9% of random compressed pubkeys hit
        // this (measured over the real `auction` artifact), i.e. roughly 1 in 113
        // restored contracts becomes uncallable from the Java SDK.
        String pubKey = "03ed20494e472dcfd0e8ab5cd7ddfc0755c59fa80177fc5b28bc663daaa5aedf66";
        RunarContract c = restoredWithState(
            statefulArtifact("PubKey", 1, List.of(1, 1)), pubKey);

        assertEquals(1, c.getCodeSepIndex(0),
            "codesep resolution must ignore the raw state blob entirely");
    }

    @Test
    void codeSepIndexNeverPointsIntoTheStateRegion() {
        // A bigint state field is serialised as 8 raw little-endian bytes, so the
        // value 171 emits a bare 0xab — byte-identical to OP_CODESEPARATOR — at
        // byte 4, inside the state region.
        //
        // The artifact here declares two separators but the deployed code part
        // carries one (artifact/script skew: the byte-walk exists precisely to
        // cope with an artifact that no longer matches the deployed bytes). With
        // the walk unbounded, the state byte pads realOffsets to length 2 and
        // method 1 resolves to a byte position inside the state blob, producing a
        // garbage sighash subscript. Bounded, the walk yields one offset, the
        // guard fails, and resolution falls back to the template offset.
        String stateHex = "ab00000000000000"; // 171 as OP_NUM2BIN(8) little-endian
        RunarContract c = restoredWithState(
            statefulArtifact("bigint", 1, List.of(1, 1)), stateHex);

        int opReturnPos = ScriptUtils.findLastOpReturn(c.currentUtxo().scriptHex());
        int resolved = c.getCodeSepIndex(1);
        assertTrue(resolved < opReturnPos / 2,
            "getCodeSepIndex returned byte " + resolved + ", which is at/after the "
                + "OP_RETURN state separator (byte " + opReturnPos / 2 + ")");
    }

    @Test
    void statelessContractsStillScanTheWholeScript() {
        // Parity with TS contract.ts:2129-2131 / Go sdk_contract.go:1499-1501: the
        // OP_RETURN bound only applies to contracts that actually carry state.
        RunarArtifact.ABI abi = new RunarArtifact.ABI(
            new RunarArtifact.ABIConstructor(List.of()),
            List.of(new RunarArtifact.ABIMethod("m", List.of(), true, false, null)));
        RunarArtifact stateless = new RunarArtifact(
            "1", "test", "Synthetic", abi, CODE_PART, "", "",
            List.of(), List.of(), List.of(), 1, List.of(1));

        RunarContract c = new RunarContract(stateless, List.of());
        c.setCurrentUtxo(new UTXO("aa".repeat(32), 0, 1000L, CODE_PART));
        assertEquals(1, c.getCodeSepIndex(0));
    }
}
