package runar.end2end;

import java.math.BigInteger;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.jupiter.api.Test;
import runar.lang.runtime.ContractSimulator;
import runar.lang.sdk.CompileCheck;
import runar.lang.types.Bigint;
import runar.lang.types.ByteString;
import runar.lang.types.PubKey;
import runar.lang.types.RabinPubKey;
import runar.lang.types.RabinSig;
import runar.lang.types.Sig;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * End-to-end PriceBet tests. Mirrors the TypeScript / Go / Python /
 * Ruby / Rust / Zig PriceBet test suites under
 * {@code examples/end2end-example/}.
 *
 * <p>Two layers of coverage:
 *
 * <ol>
 *   <li>Business logic via {@link ContractSimulator} (mocked Rabin/ECDSA
 *       crypto — every branch of {@code settle} and {@code cancel} is
 *       exercised).</li>
 *   <li>Compiler frontend via {@link CompileCheck} (the contract parses,
 *       validates, and typechecks through the real Rúnar pipeline).</li>
 * </ol>
 *
 * <p>The on-chain (regtest) flow lives in {@code integration/java} —
 * the dedicated PriceBet regtest case can be added there once a
 * Rabin-aware {@code IntegrationWallet} helper lands; this file
 * intentionally stays node-free so {@code gradle test} works in any
 * environment, matching the Go {@code PriceBet_test.go} pattern.
 */
class PriceBetTest {

    // Rabin test primes, both ≡ 3 (mod 4) so square roots are computable via
    // a^((p+1)/4) mod p. Same shared cross-tier test key as
    // runar.lang.runtime.RabinPaddingBoundTest and the examples/java
    // OraclePriceFeedTest. MockCrypto.verifyRabinSig performs REAL Rabin
    // verification (with the on-chain padding bound), so the oracle
    // signature must be honestly produced — garbage (sig, padding) pairs
    // no longer verify.
    private static final BigInteger P = new BigInteger("1361129467683753853853498429727072846227");
    private static final BigInteger Q = new BigInteger("1361129467683753853853498429727082846007");
    private static final BigInteger N = P.multiply(Q);

    private static final RabinPubKey ORACLE_PK = new RabinPubKey(N);

    private static final PubKey ALICE = PubKey.fromHex(
        "0202020202020202020202020202020202020202020202020202020202020202aa"
    );
    private static final PubKey BOB = PubKey.fromHex(
        "0303030303030303030303030303030303030303030303030303030303030303bb"
    );
    // 72-byte placeholder DER signatures — the simulator's checkSig is
    // mocked, so the bytes only have to be the right size.
    private static final Sig ALICE_SIG = Sig.fromHex("30440220" + "aa".repeat(32) + "0220" + "aa".repeat(32));
    private static final Sig BOB_SIG   = Sig.fromHex("30440220" + "bb".repeat(32) + "0220" + "bb".repeat(32));

    private static final Bigint STRIKE = Bigint.of(50_000);

    private static PriceBet makeBet() {
        return new PriceBet(ALICE, BOB, ORACLE_PK, STRIKE);
    }

    @Test
    void contractInstantiates() {
        PriceBet bet = makeBet();
        assertNotNull(bet);
    }

    @Test
    void settleAlicewinsWhenPriceExceedsStrike() {
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        BigInteger[] sigAndPad = sign(priceMsg(60_000));
        sim.call("settle",
            Bigint.of(60_000), new RabinSig(sigAndPad[0]),
            new ByteString(unsignedToLE(sigAndPad[1])),
            ALICE_SIG, BOB_SIG
        );
    }

    @Test
    void settleBobWinsWhenPriceBelowStrike() {
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        BigInteger[] sigAndPad = sign(priceMsg(30_000));
        sim.call("settle",
            Bigint.of(30_000), new RabinSig(sigAndPad[0]),
            new ByteString(unsignedToLE(sigAndPad[1])),
            ALICE_SIG, BOB_SIG
        );
    }

    @Test
    void settleBobWinsAtStrike() {
        // price == strike → bob wins (the contract's else branch).
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        BigInteger[] sigAndPad = sign(priceMsg(50_000));
        sim.call("settle",
            STRIKE, new RabinSig(sigAndPad[0]),
            new ByteString(unsignedToLE(sigAndPad[1])),
            ALICE_SIG, BOB_SIG
        );
    }

    @Test
    void settleRejectsZeroPrice() {
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        // Honestly signed zero price so the failure is attributable to the
        // price > 0 assert, not the signature layer.
        BigInteger[] sigAndPad = sign(priceMsg(0));
        assertThrows(AssertionError.class, () ->
            sim.call("settle",
                Bigint.of(0), new RabinSig(sigAndPad[0]),
                new ByteString(unsignedToLE(sigAndPad[1])),
                ALICE_SIG, BOB_SIG
            )
        );
    }

    @Test
    void settleRejectsForgedOracleSignature() {
        // Price exceeds the strike but the oracle signature is garbage —
        // the Rabin layer must reject it (regression for the stub-era
        // mock values this test previously relied on).
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        assertThrows(AssertionError.class, () ->
            sim.call("settle",
                Bigint.of(60_000), new RabinSig(BigInteger.ONE),
                ByteString.fromHex("00"),
                ALICE_SIG, BOB_SIG
            )
        );
    }

    @Test
    void cancelSucceedsWithBothSignatures() {
        PriceBet bet = makeBet();
        ContractSimulator sim = ContractSimulator.stateless(bet);
        sim.call("cancel", ALICE_SIG, BOB_SIG);
    }

    @Test
    void compileCheckPasses() throws Exception {
        // Run the contract through the real Rúnar frontend (parse +
        // validate + typecheck) and confirm it produces a valid
        // artifact. Mirrors the Go TestPriceBet_Compile case.
        Path source = Paths.get(System.getProperty("user.dir"))
            .resolve("src/main/java/runar/end2end/PriceBet.runar.java");
        CompileCheck.run(source);
    }

    // --- honest signer (test-only; mirrors examples/java OraclePriceFeedTest) ---

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

    private static byte[] sha256(byte[] data) {
        try {
            return java.security.MessageDigest.getInstance("SHA-256").digest(data);
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
