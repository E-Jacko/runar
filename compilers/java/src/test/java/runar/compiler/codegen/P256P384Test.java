package runar.compiler.codegen;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import org.junit.jupiter.api.Test;
import runar.compiler.ir.stack.IfOp;
import runar.compiler.ir.stack.StackMethod;
import runar.compiler.ir.stack.StackOp;
import runar.compiler.ir.stack.StackProgram;
import runar.compiler.passes.Emit;

/**
 * Byte-identical parity tests for {@link P256P384} against the Go reference
 * codegen.
 *
 * <p>Goldens (op count, hex byte length, SHA-256 of hex) were produced by
 * running {@code compilers/go/codegen/p256_p384.go}'s {@code EmitP*} entry
 * points through {@code codegen.EmitMethod} on the same commit as this port.
 * Any divergence means the Java emitter has drifted from the reference and
 * will produce non-conforming Bitcoin Script.
 */
class P256P384Test {

    // --------------------------------------------------------------
    // P-256
    // --------------------------------------------------------------

    @Test
    void p256AddParity() {
        assertParity("p256Add",
            P256P384::emitP256Add,
            6642, 19885,
            "d7c5d987ba1b857ae5138c692cf199b4fe98489af91cc7aa84e122eb8a7acd81");
    }

    @Test
    void p256MulParity() {
        assertParity("p256Mul",
            P256P384::emitP256Mul,
            140036, 459746,
            "3f491aae5052651c50af692d7a2c16984e329bf5c790d18249af27171c442e17");
    }

    @Test
    void p256MulGenParity() {
        assertParity("p256MulGen",
            P256P384::emitP256MulGen,
            140038, 459812,
            "4e6e4fc58b14b14e9ab6c42a6adf8882d562d73b3754d6c28178a80b9b43a54a");
    }

    @Test
    void p256NegateParity() {
        assertParity("p256Negate",
            P256P384::emitP256Negate,
            945, 1018,
            "92527f4c693de2e9ad7207842fc80cae1735abcef68bf26ce32b14a70dec6c2f");
    }

    @Test
    void p256OnCurveParity() {
        assertParity("p256OnCurve",
            P256P384::emitP256OnCurve,
            559, 858,
            "3ae633ac4a1039e19b9c79e993e6f3567199a6d138d9e71f62edb58e8f124219");
    }

    @Test
    void p256EncodeCompressedParity() {
        assertParity("p256EncodeCompressed",
            P256P384::emitP256EncodeCompressed,
            16, 19,
            "a4481881396c90da361f987c4adc581125b09103bfb6bd11f3d5acc5be1635d1");
    }

    @Test
    void verifyEcdsaP256Parity() {
        assertParity("verifyECDSA_P256",
            P256P384::emitVerifyECDSA_P256,
            297188, 973648,
            "fe6de26a521351ca374521aeb8d741cc87f2ef1870888c5f306015e9ce716642");
    }

    // --------------------------------------------------------------
    // P-384
    // --------------------------------------------------------------

    @Test
    void p384AddParity() {
        assertParity("p384Add",
            P256P384::emitP384Add,
            11448, 46689,
            "e4a7b0993055924a891d69401784b9ba416f26370bb57d3e4b802cfc4bc75f84");
    }

    @Test
    void p384MulParity() {
        assertParity("p384Mul",
            P256P384::emitP384Mul,
            211178, 927350,
            "ca64d51df61e1ba9f5fd26113cbff649036ee96c00d2d1d27442486e93520fb4");
    }

    @Test
    void p384MulGenParity() {
        assertParity("p384MulGen",
            P256P384::emitP384MulGen,
            211180, 927449,
            "5a5149b884fac627c5b46488bfcb55c7bf5f275b255ed83026c193e8cb42250a");
    }

    @Test
    void p384NegateParity() {
        assertParity("p384Negate",
            P256P384::emitP384Negate,
            1393, 1498,
            "147e2c655c23973481673628c1d0151034a5945462fb26828a6c8c1748b15cdc");
    }

    @Test
    void p384OnCurveParity() {
        assertParity("p384OnCurve",
            P256P384::emitP384OnCurve,
            783, 1227,
            "2d8d5ea7a9f059dc3087b62564feed5fac7c24c795e2142c2252e499b18bffe7");
    }

    @Test
    void p384EncodeCompressedParity() {
        assertParity("p384EncodeCompressed",
            P256P384::emitP384EncodeCompressed,
            16, 19,
            "e32d98f40a17d26f70ce433663a01e3c476073419ab6109964d00cfbb57d6eae");
    }

    @Test
    void verifyEcdsaP384Parity() {
        assertParity("verifyECDSA_P384",
            P256P384::emitVerifyECDSA_P384,
            452910, 1986651,
            "b5797efd8692bf9d8ae28e4d0dc1a89a590f5ed43087d83cf550d207807d243c");
    }

    // --------------------------------------------------------------
    // Curve constants sanity
    // --------------------------------------------------------------

    @Test
    void p256ConstantsAreCorrect() {
        // p (NIST P-256) = 2^256 - 2^224 + 2^192 + 2^96 - 1
        BigInteger expectedP = BigInteger.TWO.pow(256)
            .subtract(BigInteger.TWO.pow(224))
            .add(BigInteger.TWO.pow(192))
            .add(BigInteger.TWO.pow(96))
            .subtract(BigInteger.ONE);
        assertEquals(expectedP, P256P384.P256_P);
        assertEquals(P256P384.P256_P.subtract(BigInteger.TWO), P256P384.P256_P_MINUS_2);
        assertEquals(P256P384.P256_N.subtract(BigInteger.TWO), P256P384.P256_N_MINUS_2);
    }

    @Test
    void p384ConstantsAreCorrect() {
        // p (NIST P-384) = 2^384 - 2^128 - 2^96 + 2^32 - 1
        BigInteger expectedP = BigInteger.TWO.pow(384)
            .subtract(BigInteger.TWO.pow(128))
            .subtract(BigInteger.TWO.pow(96))
            .add(BigInteger.TWO.pow(32))
            .subtract(BigInteger.ONE);
        assertEquals(expectedP, P256P384.P384_P);
        assertEquals(P256P384.P384_P.subtract(BigInteger.TWO), P256P384.P384_P_MINUS_2);
        assertEquals(P256P384.P384_N.subtract(BigInteger.TWO), P256P384.P384_N_MINUS_2);
    }

    // --------------------------------------------------------------
    // Dispatch
    // --------------------------------------------------------------

    @Test
    void dispatchRecognisesAllNistBuiltins() {
        String[] names = {
            "p256Add", "p256Mul", "p256MulGen", "p256Negate", "p256OnCurve",
            "p256EncodeCompressed",
            "p384Add", "p384Mul", "p384MulGen", "p384Negate", "p384OnCurve",
            "p384EncodeCompressed"
        };
        for (String n : names) {
            assertTrue(P256P384.isNistEcBuiltin(n), n + " should be a NIST EC builtin");
        }
        assertFalse(P256P384.isNistEcBuiltin("ecAdd"));
        assertFalse(P256P384.isNistEcBuiltin("p999Add"));
    }

    @Test
    void verifyDispatchRecognisesEcdsa() {
        assertTrue(P256P384.isVerifyEcdsaBuiltin("verifyECDSA_P256"));
        assertTrue(P256P384.isVerifyEcdsaBuiltin("verifyECDSA_P384"));
        assertFalse(P256P384.isVerifyEcdsaBuiltin("verifyECDSA"));
        assertFalse(P256P384.isVerifyEcdsaBuiltin("checkSig"));
    }

    @Test
    void dispatchThrowsOnUnknown() {
        assertThrows(RuntimeException.class,
            () -> P256P384.dispatch("p256Banana", op -> {}));
    }

    // --------------------------------------------------------------
    // Helpers
    // --------------------------------------------------------------

    /**
     * Total number of {@link StackOp}s in {@code ops}, INCLUDING the bodies of
     * {@code if} ops.
     *
     * <p>A flat {@code ops.size()} cannot see inside a branch, so any emitter
     * whose work sits in an {@code if} body — the scalar ladders emit 257 / 385
     * conditional additions, WOTS+ and SLH-DSA are almost entirely conditional —
     * reports a count that barely moves no matter what the branch contains.
     * Adding +1.3 KB of script inside the ladder's last step left the
     * {@code p256Mul} / {@code p384Mul} goldens byte-identical. Recursing is what
     * makes the golden a gate.
     */
    private static int countOpTree(List<StackOp> ops) {
        int total = 0;
        for (StackOp op : ops) {
            total++;
            if (op instanceof IfOp ifOp) {
                if (ifOp.thenBranch() != null) total += countOpTree(ifOp.thenBranch());
                if (ifOp.elseBranch() != null) total += countOpTree(ifOp.elseBranch());
            }
        }
        return total;
    }

    private static void assertParity(String label, Consumer<Consumer<StackOp>> emitter,
                                     int expectedOpCount, int expectedHexBytes,
                                     String expectedHexSha256) {
        List<StackOp> ops = new ArrayList<>();
        emitter.accept(ops::add);
        assertEquals(expectedOpCount, countOpTree(ops), label + " op count drift");

        String hex = emitHex(ops);
        assertEquals(expectedHexBytes, hex.length() / 2, label + " hex byte count drift");
        assertEquals(expectedHexSha256, sha256Hex(hex), label + " hex bytes drift");
    }

    private static String emitHex(List<StackOp> ops) {
        StackProgram prog = new StackProgram("Test",
            List.of(new StackMethod("run", ops, 0L)));
        return Emit.run(prog);
    }

    private static String sha256Hex(String hex) {
        try {
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] digest = md.digest(hex.getBytes(java.nio.charset.StandardCharsets.US_ASCII));
            StringBuilder sb = new StringBuilder(digest.length * 2);
            for (byte b : digest) sb.append(String.format("%02x", b & 0xff));
            return sb.toString();
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    }
}
