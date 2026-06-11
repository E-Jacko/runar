package runar.examples.oracleprice;

import java.math.BigInteger;
import java.security.MessageDigest;

import org.junit.jupiter.api.Test;
import runar.lang.runtime.ContractSimulator;
import runar.lang.types.Bigint;
import runar.lang.types.ByteString;
import runar.lang.types.PubKey;
import runar.lang.types.RabinPubKey;
import runar.lang.types.RabinSig;
import runar.lang.types.Sig;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

class OraclePriceFeedTest {

    // Rabin test primes, both ≡ 3 (mod 4) so square roots are computable via
    // a^((p+1)/4) mod p. Same key as runar.lang.runtime.RabinPaddingBoundTest.
    // MockCrypto.verifyRabinSig performs REAL Rabin verification (with the
    // on-chain padding bound), so the oracle signature must be honestly
    // produced — garbage (sig, padding) pairs no longer verify. Mirrors the
    // TS example test, which signs with runar-testing's RABIN_TEST_KEY.
    private static final BigInteger P = new BigInteger("1361129467683753853853498429727072846227");
    private static final BigInteger Q = new BigInteger("1361129467683753853853498429727082846007");
    private static final BigInteger N = P.multiply(Q);

    private static final RabinPubKey ORACLE_PK = new RabinPubKey(N);
    private static final PubKey      RECEIVER = PubKey.fromHex("020000000000000000000000000000000000000000000000000000000000000001");
    private static final Sig         SIG = Sig.fromHex("30440220" + "00".repeat(32) + "0220" + "00".repeat(32));

    @Test
    void contractInstantiates() {
        OraclePriceFeed c = new OraclePriceFeed(ORACLE_PK, RECEIVER);
        assertNotNull(c);
        assertEquals(ORACLE_PK, c.oraclePubKey);
        assertEquals(RECEIVER, c.receiver);
    }

    @Test
    void settleSucceedsWhenPriceExceedsThreshold() {
        OraclePriceFeed c = new OraclePriceFeed(ORACLE_PK, RECEIVER);
        ContractSimulator sim = ContractSimulator.stateless(c);
        BigInteger[] sigAndPad = sign(priceMsg(100_000));
        sim.call("settle", Bigint.of(100_000),
                new RabinSig(sigAndPad[0]),
                new ByteString(unsignedToLE(sigAndPad[1])),
                SIG);
    }

    @Test
    void settleFailsWhenPriceBelowThreshold() {
        OraclePriceFeed c = new OraclePriceFeed(ORACLE_PK, RECEIVER);
        ContractSimulator sim = ContractSimulator.stateless(c);
        // Honestly signed price so the Rabin layer passes and the failure is
        // attributable to the threshold assert, not the signature check.
        BigInteger[] sigAndPad = sign(priceMsg(40_000));
        assertThrows(
            AssertionError.class,
            () -> sim.call("settle", Bigint.of(40_000),
                    new RabinSig(sigAndPad[0]),
                    new ByteString(unsignedToLE(sigAndPad[1])),
                    SIG)
        );
    }

    @Test
    void settleFailsWithForgedOracleSignature() {
        OraclePriceFeed c = new OraclePriceFeed(ORACLE_PK, RECEIVER);
        ContractSimulator sim = ContractSimulator.stateless(c);
        // Price exceeds the threshold but the oracle signature is garbage —
        // the Rabin layer must reject it.
        assertThrows(
            AssertionError.class,
            () -> sim.call("settle", Bigint.of(100_000),
                    new RabinSig(BigInteger.valueOf(67890)),
                    ByteString.fromHex(""),
                    SIG)
        );
    }

    // --- honest signer (test-only; mirrors RabinPaddingBoundTest) ---------

    /** The message the contract verifies: num2bin(price, 8) — 8-byte little-endian. */
    private static byte[] priceMsg(long price) {
        byte[] msg = new byte[8];
        for (int i = 0; i < 8; i++) {
            msg[i] = (byte) (price >>> (8 * i));
        }
        return msg;
    }

    /** Returns {sig, padding} with padding < 65536 such that (sig^2 + padding) mod n == H(msg) mod n. */
    private static BigInteger[] sign(byte[] msg) {
        BigInteger hashBN = leToUnsigned(sha256(msg));
        BigInteger hashModN = hashBN.mod(N);

        for (long pad = 0; pad < 65536; pad++) {
            BigInteger padBig = BigInteger.valueOf(pad);
            BigInteger target = hashModN.subtract(padBig).mod(N);
            BigInteger root = sqrtModPQ(target);
            if (root != null) {
                BigInteger check = root.multiply(root).add(padBig).mod(N);
                if (check.equals(hashModN)) {
                    return new BigInteger[]{root, padBig};
                }
            }
        }
        throw new IllegalStateException("no valid padding < 65536 found for test message");
    }

    /** sqrt of a mod n=p*q via CRT, or null if not a quadratic residue. */
    private static BigInteger sqrtModPQ(BigInteger a) {
        BigInteger rp = sqrtMod3(a, P);
        if (rp == null) return null;
        BigInteger rq = sqrtMod3(a, Q);
        if (rq == null) return null;
        BigInteger qInvP = Q.modInverse(P);
        BigInteger pInvQ = P.modInverse(Q);
        BigInteger t1 = rp.multiply(Q).multiply(qInvP);
        BigInteger t2 = rq.multiply(P).multiply(pInvQ);
        return t1.add(t2).mod(N);
    }

    /** sqrt of a mod prime p where p ≡ 3 (mod 4); null if a is not a QR. */
    private static BigInteger sqrtMod3(BigInteger a, BigInteger p) {
        a = a.mod(p);
        if (a.signum() == 0) return BigInteger.ZERO;
        BigInteger r = a.modPow(p.add(BigInteger.ONE).shiftRight(2), p);
        return r.multiply(r).mod(p).equals(a) ? r : null;
    }

    // --- byte helpers ------------------------------------------------------

    private static byte[] sha256(byte[] data) {
        try {
            return MessageDigest.getInstance("SHA-256").digest(data);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /** Unsigned little-endian bytes to BigInteger. */
    private static BigInteger leToUnsigned(byte[] le) {
        byte[] be = new byte[le.length];
        for (int i = 0; i < le.length; i++) be[le.length - 1 - i] = le[i];
        return new BigInteger(1, be);
    }

    /** BigInteger to minimal unsigned little-endian bytes. */
    private static byte[] unsignedToLE(BigInteger n) {
        if (n.signum() == 0) return new byte[]{0};
        byte[] be = n.toByteArray();           // big-endian, may have leading 0x00 sign byte
        int start = (be.length > 1 && be[0] == 0) ? 1 : 0;
        int len = be.length - start;
        byte[] le = new byte[len];
        for (int i = 0; i < len; i++) le[i] = be[be.length - 1 - i];
        return le;
    }
}
