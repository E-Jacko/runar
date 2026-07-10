package runar.lang.sdk;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import java.util.Arrays;
import org.junit.jupiter.api.Test;

/**
 * Issue #123 — BIP-143 scope threading in the hand-rolled OP_PUSH_TX preimage.
 * A non-default @sighash mode zeroes the appropriate fields and appends its flag
 * byte. OpPushTx.preimage and RawTx.sighashBIP143 must stay in lock step.
 */
class OpPushTxSighashTest {

    private static final int ALL = 0x41;
    private static final int NONE = 0x42;
    private static final int SINGLE = 0x43;
    private static final int ACP = 0xc1; // ALL|ANYONECANPAY|FORKID

    private static final String SUBSCRIPT = "76a914" + "11".repeat(20) + "88ac";
    private static final long SATS = 10_000L;
    private static final byte[] ZERO32 = new byte[32];

    private static RawTx sampleTx() {
        RawTx tx = new RawTx();
        tx.version = 2;
        tx.locktime = 0;
        tx.addInput("ab".repeat(32), 0, "");
        tx.addInput("cd".repeat(32), 1, "");
        tx.inputs.get(1).sequence = 0xfffffffeL;
        tx.addOutput(7_000L, "76a914" + "11".repeat(20) + "88ac");
        tx.addOutput(2_500L, "76a914" + "22".repeat(20) + "88ac");
        return tx;
    }

    private static byte[] preimage(RawTx tx, int flag) {
        return OpPushTx.preimage(tx, 0, ScriptUtils.hexToBytes(SUBSCRIPT), SATS, flag);
    }

    // preimage layout: version(4) hashPrevouts(32) hashSequence(32) outpoint(36)
    // varint+scriptCode satoshis(8) sequence(4) hashOutputs(32) locktime(4) sighashType(4)
    private static byte[] hashPrevouts(byte[] p) { return Arrays.copyOfRange(p, 4, 36); }
    private static byte[] hashSequence(byte[] p) { return Arrays.copyOfRange(p, 36, 68); }
    private static byte[] hashOutputs(byte[] p) { return Arrays.copyOfRange(p, p.length - 40, p.length - 8); }
    private static int sighashByte(byte[] p) { return p[p.length - 4] & 0xff; }

    @Test
    void defaultAllForkidTailByteIs0x41() {
        assertEquals(0x41, sighashByte(preimage(sampleTx(), ALL)));
    }

    @Test
    void singleTailByteIs0x43() {
        assertEquals(0x43, sighashByte(preimage(sampleTx(), SINGLE)));
    }

    @Test
    void anyonecanpayZeroesHashPrevouts() {
        RawTx tx = sampleTx();
        assertArrayEquals(ZERO32, hashPrevouts(preimage(tx, ACP)));
        // ...and a non-ACP mode does NOT zero it.
        assertFalse(Arrays.equals(ZERO32, hashPrevouts(preimage(tx, ALL))));
        assertEquals(0xc1, sighashByte(preimage(tx, ACP)));
    }

    @Test
    void noneZeroesHashOutputs() {
        assertArrayEquals(ZERO32, hashOutputs(preimage(sampleTx(), NONE)));
    }

    @Test
    void hashSequenceCommittedOnlyUnderPureAll() {
        RawTx tx = sampleTx();
        assertFalse(Arrays.equals(ZERO32, hashSequence(preimage(tx, ALL))));
        // SINGLE / NONE / ANYONECANPAY all zero hashSequence.
        assertArrayEquals(ZERO32, hashSequence(preimage(tx, SINGLE)));
        assertArrayEquals(ZERO32, hashSequence(preimage(tx, NONE)));
        assertArrayEquals(ZERO32, hashSequence(preimage(tx, ACP)));
    }

    @Test
    void singleHashesOnlyTheSameIndexOutput() {
        RawTx tx = sampleTx();
        // SINGLE (input 0) commits to hash256(output[0]) ALONE, not the whole set.
        byte[] out0 = ScriptUtils.hexToBytes(
            ScriptUtils.toLittleEndian64(tx.outputs.get(0).satoshis)
            + ScriptUtils.encodeVarInt(tx.outputs.get(0).scriptPubKeyHex.length() / 2)
            + tx.outputs.get(0).scriptPubKeyHex);
        byte[] expected = Hash160.doubleSha256(out0);
        assertArrayEquals(expected, hashOutputs(preimage(tx, SINGLE)));
        // It must NOT equal the ALL digest over both outputs.
        assertFalse(Arrays.equals(hashOutputs(preimage(tx, ALL)), hashOutputs(preimage(tx, SINGLE))));
    }

    @Test
    void singleWithNoSameIndexOutputIsZero32() {
        RawTx tx = new RawTx();
        tx.version = 2;
        tx.addInput("ab".repeat(32), 0, "");
        tx.addInput("cd".repeat(32), 1, "");
        // Spend input index 1, but only ONE output -> no same-index output.
        tx.addOutput(7_000L, "76a914" + "11".repeat(20) + "88ac");
        byte[] p = OpPushTx.preimage(tx, 1, ScriptUtils.hexToBytes(SUBSCRIPT), SATS, SINGLE);
        assertArrayEquals(ZERO32, hashOutputs(p));
    }

    @Test
    void preimageMatchesRawTxSighashAcrossModes() {
        RawTx tx = sampleTx();
        for (int flag : new int[] {ALL, NONE, SINGLE, ACP}) {
            byte[] expected = tx.sighashBIP143(0, SUBSCRIPT, SATS, flag);
            byte[] got = Hash160.doubleSha256(preimage(tx, flag));
            assertArrayEquals(expected, got, "mode 0x" + Integer.toHexString(flag));
        }
    }

    @Test
    void computePushTxSigAppendsTheDeclaredFlagByte() {
        RawTx tx = sampleTx();
        byte[] sig41 = OpPushTx.computePushTxSig(tx, 0, SUBSCRIPT, SATS, ALL);
        byte[] sig43 = OpPushTx.computePushTxSig(tx, 0, SUBSCRIPT, SATS, SINGLE);
        assertEquals(0x41, sig41[sig41.length - 1] & 0xff);
        assertEquals(0x43, sig43[sig43.length - 1] & 0xff);
        // Default overload (no flag) stays 0x41.
        byte[] sigDefault = OpPushTx.computePushTxSig(tx, 0, SUBSCRIPT, SATS);
        assertEquals(0x41, sigDefault[sigDefault.length - 1] & 0xff);
    }
}
