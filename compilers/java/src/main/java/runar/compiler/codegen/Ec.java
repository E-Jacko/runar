package runar.compiler.codegen;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import runar.compiler.ir.stack.DropOp;
import runar.compiler.ir.stack.DupOp;
import runar.compiler.ir.stack.IfOp;
import runar.compiler.ir.stack.NipOp;
import runar.compiler.ir.stack.OpcodeOp;
import runar.compiler.ir.stack.OverOp;
import runar.compiler.ir.stack.PickOp;
import runar.compiler.ir.stack.PushOp;
import runar.compiler.ir.stack.PushValue;
import runar.compiler.ir.stack.RollOp;
import runar.compiler.ir.stack.RotOp;
import runar.compiler.ir.stack.StackOp;
import runar.compiler.ir.stack.SwapOp;

/**
 * secp256k1 EC codegen for Bitcoin Script.
 *
 * <p>Direct port of {@code compilers/python/runar_compiler/codegen/ec.py}.
 * Exposes emitters for the full secp256k1 builtin surface: {@code ecAdd},
 * {@code ecMul}, {@code ecMulGen}, {@code ecNegate}, {@code ecOnCurve},
 * {@code ecModReduce}, {@code ecEncodeCompressed}, {@code ecMakePoint},
 * {@code ecPointX}, {@code ecPointY}.
 *
 * <p>Point representation is 64 bytes (x[32] || y[32], big-endian unsigned,
 * no prefix byte). Internal scalar multiplication uses Jacobian coordinates.
 *
 * <p>Every helper here preserves the {@code ECTracker} name-slot contract
 * from the Python reference so the emitted {@link StackOp} stream is
 * byte-for-byte identical.
 */
public final class Ec {

    private Ec() {}

    // ------------------------------------------------------------------
    // Curve constants
    // ------------------------------------------------------------------

    /** secp256k1 field prime p = 2^256 - 2^32 - 977. */
    public static final BigInteger EC_FIELD_P = new BigInteger(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16);

    /** p - 2, used for Fermat's little theorem modular inverse. */
    public static final BigInteger EC_FIELD_P_MINUS_2 =
        EC_FIELD_P.subtract(BigInteger.TWO);

    /** secp256k1 generator x-coordinate. */
    public static final BigInteger EC_GEN_X = new BigInteger(
        "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16);

    /** secp256k1 generator y-coordinate. */
    public static final BigInteger EC_GEN_Y = new BigInteger(
        "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16);

    /** secp256k1 group order n. */
    public static final BigInteger EC_CURVE_N = new BigInteger(
        "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16);

    private static byte[] bigintToBytes32(BigInteger n) {
        byte[] src = n.toByteArray();
        byte[] out = new byte[32];
        int copyLen = Math.min(src.length, 32);
        int srcOff = src.length > 32 ? src.length - 32 : 0;
        int dstOff = 32 - copyLen;
        System.arraycopy(src, srcOff, out, dstOff, copyLen);
        return out;
    }

    static String hexOf(byte[] b) {
        StringBuilder sb = new StringBuilder(b.length * 2);
        for (byte x : b) sb.append(String.format("%02x", x & 0xff));
        return sb.toString();
    }

    // ==================================================================
    // ECTracker: named stack slot tracker (mirrors Python ECTracker)
    // ==================================================================

    static final class ECTracker {
        final List<String> nm;
        final Consumer<StackOp> e;

        ECTracker(List<String> init, Consumer<StackOp> emit) {
            this.nm = new ArrayList<>(init);
            this.e = emit;
        }

        int findDepth(String name) {
            for (int i = nm.size() - 1; i >= 0; i--) {
                if (name.equals(nm.get(i))) return nm.size() - 1 - i;
            }
            throw new RuntimeException("ECTracker: '" + name + "' not on stack " + nm);
        }

        void pushBytes(String n, byte[] v) {
            e.accept(new PushOp(PushValue.ofHex(hexOf(v))));
            nm.add(n);
        }

        void pushBigInt(String n, BigInteger v) {
            e.accept(new PushOp(PushValue.of(v)));
            nm.add(n);
        }

        void pushInt(String n, long v) {
            e.accept(new PushOp(PushValue.of(v)));
            nm.add(n);
        }

        void dup(String n) {
            e.accept(new DupOp());
            nm.add(n);
        }

        void drop() {
            e.accept(new DropOp());
            if (!nm.isEmpty()) nm.remove(nm.size() - 1);
        }

        void nip() {
            e.accept(new NipOp());
            int L = nm.size();
            if (L >= 2) {
                String top = nm.get(L - 1);
                nm.remove(L - 1);
                nm.remove(L - 2);
                nm.add(top);
            }
        }

        void over(String n) {
            e.accept(new OverOp());
            nm.add(n);
        }

        void swap() {
            e.accept(new SwapOp());
            int L = nm.size();
            if (L >= 2) {
                String t = nm.get(L - 1);
                nm.set(L - 1, nm.get(L - 2));
                nm.set(L - 2, t);
            }
        }

        void rot() {
            e.accept(new RotOp());
            int L = nm.size();
            if (L >= 3) {
                String r = nm.get(L - 3);
                nm.remove(L - 3);
                nm.add(r);
            }
        }

        void op(String code) {
            e.accept(new OpcodeOp(code));
        }

        void roll(int d) {
            if (d == 0) return;
            if (d == 1) { swap(); return; }
            if (d == 2) { rot(); return; }
            e.accept(new PushOp(PushValue.of(d)));
            nm.add("");
            e.accept(new RollOp(d));
            nm.remove(nm.size() - 1); // pop push placeholder
            int idx = nm.size() - 1 - d;
            String r = nm.get(idx);
            nm.remove(idx);
            nm.add(r);
        }

        void pick(int d, String n) {
            if (d == 0) { dup(n); return; }
            if (d == 1) { over(n); return; }
            e.accept(new PushOp(PushValue.of(d)));
            nm.add("");
            e.accept(new PickOp(d));
            nm.remove(nm.size() - 1);
            nm.add(n);
        }

        void toTop(String name) {
            roll(findDepth(name));
        }

        void copyToTop(String name, String n) {
            pick(findDepth(name), n);
        }

        void toAlt() {
            op("OP_TOALTSTACK");
            if (!nm.isEmpty()) nm.remove(nm.size() - 1);
        }

        void fromAlt(String n) {
            op("OP_FROMALTSTACK");
            nm.add(n);
        }

        void rename(String n) {
            if (!nm.isEmpty()) nm.set(nm.size() - 1, n);
        }

        /**
         * Emit raw opcodes; tracker only records net stack effect. *produce*
         * = "" means no output pushed.
         */
        void rawBlock(List<String> consume, String produce, Consumer<Consumer<StackOp>> fn) {
            for (int i = 0; i < consume.size(); i++) {
                if (!nm.isEmpty()) nm.remove(nm.size() - 1);
            }
            fn.accept(this.e);
            if (produce != null && !produce.isEmpty()) {
                nm.add(produce);
            }
        }

        /** Emit if/else with tracked stack effect. resultName="" => no result. */
        void emitIf(String condName,
                    Consumer<Consumer<StackOp>> thenFn,
                    Consumer<Consumer<StackOp>> elseFn,
                    String resultName) {
            toTop(condName);
            // condition consumed
            if (!nm.isEmpty()) nm.remove(nm.size() - 1);
            List<StackOp> thenOps = new ArrayList<>();
            List<StackOp> elseOps = new ArrayList<>();
            thenFn.accept(thenOps::add);
            elseFn.accept(elseOps::add);
            this.e.accept(new IfOp(thenOps, elseOps));
            if (resultName != null && !resultName.isEmpty()) {
                nm.add(resultName);
            }
        }
    }

    // ==================================================================
    // Field arithmetic helpers (mod p)
    // ==================================================================

    private static void pushFieldP(ECTracker t, String name) {
        t.pushBigInt(name, EC_FIELD_P);
    }

    private static void fieldMod(ECTracker t, String aName, String resultName) {
        t.toTop(aName);
        pushFieldP(t, "_fmod_p");
        t.rawBlock(List.of(aName, "_fmod_p"), resultName, e -> {
            e.accept(new OpcodeOp("OP_2DUP"));
            e.accept(new OpcodeOp("OP_MOD"));
            e.accept(new RotOp());
            e.accept(new DropOp());
            e.accept(new OverOp());
            e.accept(new OpcodeOp("OP_ADD"));
            e.accept(new SwapOp());
            e.accept(new OpcodeOp("OP_MOD"));
        });
    }

    private static void fieldAdd(ECTracker t, String aName, String bName, String resultName) {
        t.toTop(aName);
        t.toTop(bName);
        t.rawBlock(List.of(aName, bName), "_fadd_sum", e -> e.accept(new OpcodeOp("OP_ADD")));
        fieldMod(t, "_fadd_sum", resultName);
    }

    private static void fieldSub(ECTracker t, String aName, String bName, String resultName) {
        t.toTop(aName);
        t.toTop(bName);
        t.rawBlock(List.of(aName, bName), "_fsub_diff", e -> e.accept(new OpcodeOp("OP_SUB")));
        fieldMod(t, "_fsub_diff", resultName);
    }

    private static void fieldMul(ECTracker t, String aName, String bName, String resultName) {
        t.toTop(aName);
        t.toTop(bName);
        t.rawBlock(List.of(aName, bName), "_fmul_prod", e -> e.accept(new OpcodeOp("OP_MUL")));
        fieldMod(t, "_fmul_prod", resultName);
    }

    private static void fieldMulConst(ECTracker t, String aName, long c, String resultName) {
        t.toTop(aName);
        t.rawBlock(List.of(aName), "_fmc_prod", e -> {
            if (c == 2L) {
                e.accept(new OpcodeOp("OP_2MUL"));
            } else {
                e.accept(new PushOp(PushValue.of(c)));
                e.accept(new OpcodeOp("OP_MUL"));
            }
        });
        fieldMod(t, "_fmc_prod", resultName);
    }

    private static void fieldSqr(ECTracker t, String aName, String resultName) {
        t.copyToTop(aName, "_fsqr_copy");
        fieldMul(t, aName, "_fsqr_copy", resultName);
    }

    /** Compute a^(p-2) mod p via square-and-multiply. Consumes {@code aName}. */
    private static void fieldInv(ECTracker t, String aName, String resultName) {
        // p-2 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2D
        // Bits 255..32: 222 bits of 1 + bit 32 which is 0 (handled below).

        // Start: result = a (bit 255 = 1)
        t.copyToTop(aName, "_inv_r");
        // Bits 254 down to 33: all 1's (222 bits). Bit 32 is 0.
        for (int i = 0; i < 222; i++) {
            fieldSqr(t, "_inv_r", "_inv_r2");
            t.rename("_inv_r");
            t.copyToTop(aName, "_inv_a");
            fieldMul(t, "_inv_r", "_inv_a", "_inv_m");
            t.rename("_inv_r");
        }
        // Bit 32 is 0: square only (no multiply)
        fieldSqr(t, "_inv_r", "_inv_r2");
        t.rename("_inv_r");
        // Bits 31..0 of p-2
        long lowBits = EC_FIELD_P_MINUS_2.and(BigInteger.valueOf(0xffffffffL)).longValueExact();
        for (int i = 31; i >= 0; i--) {
            fieldSqr(t, "_inv_r", "_inv_r2");
            t.rename("_inv_r");
            if (((lowBits >> i) & 1L) == 1L) {
                t.copyToTop(aName, "_inv_a");
                fieldMul(t, "_inv_r", "_inv_a", "_inv_m");
                t.rename("_inv_r");
            }
        }
        // Clean up original input and rename result
        t.toTop(aName);
        t.drop();
        t.toTop("_inv_r");
        t.rename(resultName);
    }

    // ==================================================================
    // Point decompose / compose
    // ==================================================================

    static void emitReverse32(Consumer<StackOp> e) {
        e.accept(new OpcodeOp("OP_0"));
        e.accept(new SwapOp());
        for (int i = 0; i < 32; i++) {
            e.accept(new PushOp(PushValue.of(1)));
            e.accept(new OpcodeOp("OP_SPLIT"));
            e.accept(new RotOp());
            e.accept(new RotOp());
            e.accept(new SwapOp());
            e.accept(new OpcodeOp("OP_CAT"));
            e.accept(new SwapOp());
        }
        e.accept(new DropOp());
    }

    private static void decomposePoint(ECTracker t, String pointName, String xName, String yName) {
        t.toTop(pointName);
        t.rawBlock(List.of(pointName), "", e -> {
            e.accept(new PushOp(PushValue.of(32)));
            e.accept(new OpcodeOp("OP_SPLIT"));
        });
        // Manually track the two new items
        t.nm.add("_dp_xb");
        t.nm.add("_dp_yb");

        // Convert y_bytes (on top) to num
        t.rawBlock(List.of("_dp_yb"), yName, e -> {
            emitReverse32(e);
            e.accept(new PushOp(PushValue.ofHex("00")));
            e.accept(new OpcodeOp("OP_CAT"));
            e.accept(new OpcodeOp("OP_BIN2NUM"));
        });

        // Convert x_bytes to num
        t.toTop("_dp_xb");
        t.rawBlock(List.of("_dp_xb"), xName, e -> {
            emitReverse32(e);
            e.accept(new PushOp(PushValue.ofHex("00")));
            e.accept(new OpcodeOp("OP_CAT"));
            e.accept(new OpcodeOp("OP_BIN2NUM"));
        });

        // Stack: [yName, xName] -> swap to [xName, yName]
        t.swap();
    }

    private static void composePoint(ECTracker t, String xName, String yName, String resultName) {
        t.toTop(xName);
        t.rawBlock(List.of(xName), "_cp_xb", e -> {
            e.accept(new PushOp(PushValue.of(33)));
            e.accept(new OpcodeOp("OP_NUM2BIN"));
            e.accept(new PushOp(PushValue.of(32)));
            e.accept(new OpcodeOp("OP_SPLIT"));
            e.accept(new DropOp());
            emitReverse32(e);
        });

        t.toTop(yName);
        t.rawBlock(List.of(yName), "_cp_yb", e -> {
            e.accept(new PushOp(PushValue.of(33)));
            e.accept(new OpcodeOp("OP_NUM2BIN"));
            e.accept(new PushOp(PushValue.of(32)));
            e.accept(new OpcodeOp("OP_SPLIT"));
            e.accept(new DropOp());
            emitReverse32(e);
        });

        t.toTop("_cp_xb");
        t.toTop("_cp_yb");
        t.rawBlock(List.of("_cp_xb", "_cp_yb"), resultName,
            e -> e.accept(new OpcodeOp("OP_CAT")));
    }

    // ==================================================================
    // Affine point addition (for ecAdd)
    // ==================================================================

    private static void affineAdd(ECTracker t) {
        // The chord slope s = (qy - py) / (qx - px) is undefined when P == Q:
        // the denominator is zero and the correct slope is the TANGENT,
        // 3px^2 / (2py). Without this, ecAdd(P, P) silently produced a wrong
        // point, so every contract that doubled deployed an unspendable script.
        //
        // Both cases are `s = num / den`, so only the NUMERATOR and DENOMINATOR
        // are selected and the single expensive fieldInv still runs once.
        // rx and ry below are already correct for doubling.
        //
        //   cond = (px == qx)
        //   num  = cond ? 3*px^2 : (qy - py)
        //   den  = cond ? 2*py   : (qx - px)
        //
        // selected as `b + cond*(a - b)`, which needs no branch and keeps the
        // emitted op sequence identical on both paths.
        //
        // NOT handled: P == -Q, whose true result is the point at infinity,
        // which affine coordinates cannot represent.
        t.copyToTop("px", "_px_eq");
        t.copyToTop("qx", "_qx_eq");
        t.rawBlock(List.of("_px_eq", "_qx_eq"), "_cond",
            e -> e.accept(new OpcodeOp("OP_NUMEQUAL")));

        // chord numerator / denominator
        t.copyToTop("qy", "_qy1");
        t.copyToTop("py", "_py1");
        fieldSub(t, "_qy1", "_py1", "_num_chord");
        t.copyToTop("qx", "_qx1");
        t.copyToTop("px", "_px1");
        fieldSub(t, "_qx1", "_px1", "_den_chord");

        // tangent numerator / denominator: 3*px^2 and 2*py
        t.copyToTop("px", "_px_t");
        fieldSqr(t, "_px_t", "_px_sq");
        fieldMulConst(t, "_px_sq", 3, "_num_tan");
        t.copyToTop("py", "_py_t");
        fieldMulConst(t, "_py_t", 2, "_den_tan");

        // num = num_chord + cond*(num_tan - num_chord)
        t.copyToTop("_num_chord", "_num_chord_c");
        fieldSub(t, "_num_tan", "_num_chord_c", "_num_diff");
        t.copyToTop("_cond", "_cond_n");
        fieldMul(t, "_num_diff", "_cond_n", "_num_sel");
        fieldAdd(t, "_num_chord", "_num_sel", "_s_num");

        // den = den_chord + cond*(den_tan - den_chord)
        t.copyToTop("_den_chord", "_den_chord_c");
        fieldSub(t, "_den_tan", "_den_chord_c", "_den_diff");
        t.toTop("_cond");
        t.rename("_cond_d");
        fieldMul(t, "_den_diff", "_cond_d", "_den_sel");
        fieldAdd(t, "_den_chord", "_den_sel", "_s_den");

        // s = s_num / s_den mod p
        fieldInv(t, "_s_den", "_s_den_inv");
        fieldMul(t, "_s_num", "_s_den_inv", "_s");

        // rx = s^2 - px - qx mod p
        t.copyToTop("_s", "_s_keep");
        fieldSqr(t, "_s", "_s2");
        t.copyToTop("px", "_px2");
        fieldSub(t, "_s2", "_px2", "_rx1");
        t.copyToTop("qx", "_qx2");
        fieldSub(t, "_rx1", "_qx2", "rx");

        // ry = s * (px - rx) - py mod p
        t.copyToTop("px", "_px3");
        t.copyToTop("rx", "_rx2");
        fieldSub(t, "_px3", "_rx2", "_px_rx");
        fieldMul(t, "_s_keep", "_px_rx", "_s_px_rx");
        t.copyToTop("py", "_py2");
        fieldSub(t, "_s_px_rx", "_py2", "ry");

        // Clean up original points
        t.toTop("px"); t.drop();
        t.toTop("py"); t.drop();
        t.toTop("qx"); t.drop();
        t.toTop("qy"); t.drop();
    }

    // ==================================================================
    // Projective point operations (for ecMul) — RCB complete formulas, a = 0
    // ==================================================================

    /**
     * Reduce TOS mod n (the curve ORDER, not the field prime), non-negative.
     *
     * <p>Same shape as fieldMod but with a different modulus. This defines the
     * scalar domain of ecMul over the whole of script-number space: negative
     * scalars and scalars >= n both reduce into [0, n-1], and k = 0 / k = n
     * give the point at infinity. Under the old ladder anything outside
     * [1, n-1] was undefined behaviour.
     */
    private static void scalarModN(ECTracker t, String aName, String resultName) {
        t.toTop(aName);
        t.pushBigInt("_smod_n", EC_CURVE_N);
        t.rawBlock(List.of(aName, "_smod_n"), resultName, e -> {
            e.accept(new OpcodeOp("OP_2DUP"));
            e.accept(new OpcodeOp("OP_MOD"));
            e.accept(new RotOp());
            e.accept(new DropOp());
            e.accept(new OverOp());
            e.accept(new OpcodeOp("OP_ADD"));
            e.accept(new SwapOp());
            e.accept(new OpcodeOp("OP_MOD"));
        });
    }

    /**
     * Projective point doubling — RCB Algorithm 9 (a = 0), 6M + 2S + 1 m_3b.
     * Expects jx, jy, jz on the tracker; replaces them with the doubled point.
     *
     * <p>Complete: doubling the point at infinity (0 : 1 : 0) yields
     * (0 : 1 : 0).
     *
     * <p>Deviations from the paper, both exact mod p and strictly cheaper here
     * (a multiply by a small constant costs one push + OP_MUL, an addition
     * costs a full reduce): line 2-4's Z3 = 8*t0 is one mulConst rather than
     * three doublings, and line 11-12's t2 = 3*t2 is one mulConst rather than
     * two adds.
     */
    private static void projectiveDouble(ECTracker t) {
        // Copies of the inputs that outlive their first consumer.
        t.copyToTop("jy", "_d_yz");       // t1 = Y*Z
        t.copyToTop("jy", "_d_xy");       // t1 = X*Y  (line 16)
        t.copyToTop("jz", "_d_zz_src");   // t2 = Z*Z

        fieldSqr(t, "jy", "_d_t0");                       // t0 = Y^2
        t.copyToTop("_d_t0", "_d_t0a");
        fieldMulConst(t, "_d_t0a", 8, "_d_Z3");           // Z3 = 8*t0
        fieldMul(t, "_d_yz", "jz", "_d_t1");              // t1 = Y*Z
        fieldSqr(t, "_d_zz_src", "_d_zz");                // Z^2
        fieldMulConst(t, "_d_zz", 21, "_d_t2");           // t2 = b3*Z^2 (b3 = 3*7)

        t.copyToTop("_d_t2", "_d_t2a");
        t.copyToTop("_d_Z3", "_d_Z3a");
        fieldMul(t, "_d_t2a", "_d_Z3a", "_d_X3");         // X3 = t2*Z3

        t.copyToTop("_d_t0", "_d_t0b");
        t.copyToTop("_d_t2", "_d_t2b");
        fieldAdd(t, "_d_t0b", "_d_t2b", "_d_Y3");         // Y3 = t0+t2

        fieldMul(t, "_d_t1", "_d_Z3", "_d_Z3n");          // Z3 = t1*Z3
        fieldMulConst(t, "_d_t2", 3, "_d_t2c");           // t2 = 3*t2
        fieldSub(t, "_d_t0", "_d_t2c", "_d_t0n");         // t0 = t0-t2

        t.copyToTop("_d_t0n", "_d_t0na");
        fieldMul(t, "_d_t0na", "_d_Y3", "_d_Y3b");        // Y3 = t0*Y3
        fieldAdd(t, "_d_X3", "_d_Y3b", "_d_Y3c");         // Y3 = X3+Y3

        fieldMul(t, "jx", "_d_xy", "_d_xyv");             // t1 = X*Y
        fieldMul(t, "_d_t0n", "_d_xyv", "_d_X3b");        // X3 = t0*t1
        fieldMulConst(t, "_d_X3b", 2, "_d_X3c");          // X3 = X3+X3

        t.toTop("_d_X3c"); t.rename("jx");
        t.toTop("_d_Y3c"); t.rename("jy");
        t.toTop("_d_Z3n"); t.rename("jz");
    }

    /**
     * Projective to affine. Consumes jx, jy, jz; produces rxName, ryName.
     *
     * <p>fieldInv is Fermat exponentiation, so inv(0) = 0: the point at
     * infinity (Z = 0) converts to (0, 0), which is the all-zero Point blob.
     * That is the agreed encoding for infinity — it is not a curve point, so
     * it cannot be confused with a real result.
     */
    private static void projectiveToAffine(ECTracker t, String rxName, String ryName) {
        fieldInv(t, "jz", "_zinv");
        t.copyToTop("_zinv", "_zinv_b");
        fieldMul(t, "jx", "_zinv", rxName);
        fieldMul(t, "jy", "_zinv_b", ryName);
    }

    // ==================================================================
    // Projective mixed addition (P_projective + Q_affine)
    // ==================================================================

    /**
     * Build complete mixed-add ops for use inside OP_IF — RCB Algorithm 8
     * (a = 0), 11M + 2 m_3b. Adds the affine base point (ax, ay) into the
     * accumulator.
     *
     * <p>Complete: no exceptional cases. In particular
     * <ul>
     *   <li>accumulator == Q -> correctly doubles (this is the case that broke
     *       ecMul(P, 2n): the old Jacobian mixed-add computed H = R = 0 and
     *       returned the zero point, which then absorbed every remaining
     *       iteration)</li>
     *   <li>accumulator == -Q -> correctly yields the point at infinity</li>
     *   <li>accumulator == infinity -> correctly yields Q</li>
     * </ul>
     *
     * <p>Uses an inner ECTracker cloned from the outer one, because the ops run
     * under OP_IF: the outer tracker's model must describe the stack for BOTH
     * branches, so this block has to be stack-shape neutral — same names, same
     * depths, with jx/jy/jz replaced in place.
     *
     * <p>Stack layout: [..., ax, ay, _k, jx, jy, jz]
     * <br>After:       [..., ax, ay, _k, jx', jy', jz']
     */
    private static void buildProjectiveAddMixedInline(Consumer<StackOp> e, ECTracker t) {
        ECTracker it = new ECTracker(t.nm, e);

        // The affine base survives every iteration, so only ever consume copies.
        it.copyToTop("ax", "_m_x2a");   // t0 = X1*X2
        it.copyToTop("ax", "_m_x2b");   // X2+Y2
        it.copyToTop("ax", "_m_x2c");   // X2*Z1
        it.copyToTop("ay", "_m_y2a");   // t1 = Y1*Y2
        it.copyToTop("ay", "_m_y2b");   // X2+Y2
        it.copyToTop("ay", "_m_y2c");   // Y2*Z1
        it.copyToTop("jx", "_m_x1a");   // X1+Y1
        it.copyToTop("jx", "_m_x1b");   // Y3+X1
        it.copyToTop("jy", "_m_y1a");   // X1+Y1
        it.copyToTop("jy", "_m_y1b");   // t4+Y1
        it.copyToTop("jz", "_m_z1a");   // X2*Z1
        it.copyToTop("jz", "_m_z1b");   // b3*Z1

        fieldMul(it, "jx", "_m_x2a", "_m_t0");            // t0 = X1*X2
        fieldMul(it, "jy", "_m_y2a", "_m_t1");            // t1 = Y1*Y2
        fieldAdd(it, "_m_x2b", "_m_y2b", "_m_s1");        // X2+Y2
        fieldAdd(it, "_m_x1a", "_m_y1a", "_m_s2");        // X1+Y1
        fieldMul(it, "_m_s1", "_m_s2", "_m_t3");          // t3 = (X2+Y2)(X1+Y1)

        it.copyToTop("_m_t0", "_m_t0a");
        it.copyToTop("_m_t1", "_m_t1a");
        fieldAdd(it, "_m_t0a", "_m_t1a", "_m_s3");        // t4 = t0+t1
        fieldSub(it, "_m_t3", "_m_s3", "_m_t3b");         // t3 = t3-t4

        fieldMul(it, "_m_y2c", "jz", "_m_t4");            // t4 = Y2*Z1
        fieldAdd(it, "_m_t4", "_m_y1b", "_m_t4b");        // t4 = t4+Y1
        fieldMul(it, "_m_x2c", "_m_z1a", "_m_Y3");        // Y3 = X2*Z1
        fieldAdd(it, "_m_Y3", "_m_x1b", "_m_Y3b");        // Y3 = Y3+X1

        fieldMulConst(it, "_m_t0", 3, "_m_t0b");          // t0 = 3*t0
        fieldMulConst(it, "_m_z1b", 21, "_m_t2");         // t2 = b3*Z1

        it.copyToTop("_m_t1", "_m_t1b");
        it.copyToTop("_m_t2", "_m_t2a");
        fieldAdd(it, "_m_t1b", "_m_t2a", "_m_Z3");        // Z3 = t1+t2
        fieldSub(it, "_m_t1", "_m_t2", "_m_t1c");         // t1 = t1-t2
        fieldMulConst(it, "_m_Y3b", 21, "_m_Y3c");        // Y3 = b3*Y3

        it.copyToTop("_m_Y3c", "_m_Y3ca");
        it.copyToTop("_m_t4b", "_m_t4ba");
        fieldMul(it, "_m_t4ba", "_m_Y3ca", "_m_X3");      // X3 = t4*Y3

        it.copyToTop("_m_t3b", "_m_t3ba");
        it.copyToTop("_m_t1c", "_m_t1ca");
        fieldMul(it, "_m_t3ba", "_m_t1ca", "_m_t2b");     // t2 = t3*t1
        fieldSub(it, "_m_t2b", "_m_X3", "_m_X3b");        // X3 = t2-X3

        it.copyToTop("_m_t0b", "_m_t0ba");
        fieldMul(it, "_m_Y3c", "_m_t0ba", "_m_Y3d");      // Y3 = Y3*t0

        it.copyToTop("_m_Z3", "_m_Z3a");
        fieldMul(it, "_m_t1c", "_m_Z3a", "_m_t1d");       // t1 = t1*Z3
        fieldAdd(it, "_m_t1d", "_m_Y3d", "_m_Y3e");       // Y3 = t1+Y3

        fieldMul(it, "_m_t0b", "_m_t3b", "_m_t0c");       // t0 = t0*t3
        fieldMul(it, "_m_Z3", "_m_t4b", "_m_Z3b");        // Z3 = Z3*t4
        fieldAdd(it, "_m_Z3b", "_m_t0c", "_m_Z3c");       // Z3 = Z3+t0

        it.toTop("_m_X3b"); it.rename("jx");
        it.toTop("_m_Y3e"); it.rename("jy");
        it.toTop("_m_Z3c"); it.rename("jz");
    }

    // ==================================================================
    // Public entry points
    // ==================================================================

    public static void emitEcAdd(Consumer<StackOp> emit) {
        ECTracker t = new ECTracker(List.of("_pa", "_pb"), emit);
        decomposePoint(t, "_pa", "px", "py");
        decomposePoint(t, "_pb", "qx", "qy");
        affineAdd(t);
        composePoint(t, "rx", "ry", "_result");
    }

    /**
     * ecMul: scalar multiplication P * k.
     *
     * <p>256-iteration MSB-first double-and-add over homogeneous projective
     * coordinates, using the RCB COMPLETE formulas. The accumulator starts at
     * the point at infinity, so every one of the 256 bits is handled uniformly.
     *
     * <p>The previous version ran 257 iterations over k+3n with an accumulator
     * seeded at P, to guarantee a set leading bit. That relied on the
     * INCOMPLETE Jacobian mixed-add never being handed two equal points —
     * which it was, for k = 2, on the final iteration, yielding an all-zero
     * point. No choice of offset avoids this: every candidate multiple of n
     * merely relocates the collision onto different small scalars.
     * Completeness is the only fix that holds for an operand the caller
     * chooses.
     */
    public static void emitEcMul(Consumer<StackOp> emit) {
        ECTracker t = new ECTracker(List.of("_pt", "_k"), emit);
        decomposePoint(t, "_pt", "ax", "ay");

        // Reduce the scalar into [0, n-1] so the 256-bit ladder covers the
        // whole domain: negative k and k >= n are now defined rather than
        // undefined.
        scalarModN(t, "_k", "_k");

        // Accumulator := point at infinity (0 : 1 : 0). Legal input to both
        // complete formulas, which is exactly why no special leading-bit
        // handling is needed.
        t.pushInt("jx", 0);
        t.pushInt("jy", 1);
        t.pushInt("jz", 0);

        // 256 iterations: bits 255 down to 0
        for (int bit = 255; bit >= 0; bit--) {
            // Double accumulator
            projectiveDouble(t);

            // Extract bit
            t.copyToTop("_k", "_k_copy");
            if (bit == 1) {
                t.rawBlock(List.of("_k_copy"), "_shifted",
                    e -> e.accept(new OpcodeOp("OP_2DIV")));
            } else if (bit > 1) {
                t.pushInt("_shift", bit);
                t.rawBlock(List.of("_k_copy", "_shift"), "_shifted",
                    e -> e.accept(new OpcodeOp("OP_RSHIFTNUM")));
            } else {
                t.rename("_shifted");
            }
            t.pushInt("_two", 2);
            t.rawBlock(List.of("_shifted", "_two"), "_bit",
                e -> e.accept(new OpcodeOp("OP_MOD")));

            // Move _bit to TOS and remove from tracker BEFORE generating add ops
            t.toTop("_bit");
            t.nm.remove(t.nm.size() - 1); // _bit consumed by IF
            List<StackOp> addOps = new ArrayList<>();
            buildProjectiveAddMixedInline(addOps::add, t);
            emit.accept(new IfOp(addOps, List.of()));
        }

        // Convert projective to affine
        projectiveToAffine(t, "_rx", "_ry");

        // Clean up base point and scalar
        t.toTop("ax"); t.drop();
        t.toTop("ay"); t.drop();
        t.toTop("_k"); t.drop();

        // Compose result
        composePoint(t, "_rx", "_ry", "_result");
    }

    public static void emitEcMulGen(Consumer<StackOp> emit) {
        byte[] gPoint = new byte[64];
        byte[] gx = bigintToBytes32(EC_GEN_X);
        byte[] gy = bigintToBytes32(EC_GEN_Y);
        System.arraycopy(gx, 0, gPoint, 0, 32);
        System.arraycopy(gy, 0, gPoint, 32, 32);
        emit.accept(new PushOp(PushValue.ofHex(hexOf(gPoint))));
        emit.accept(new SwapOp());
        emitEcMul(emit);
    }

    public static void emitEcNegate(Consumer<StackOp> emit) {
        ECTracker t = new ECTracker(List.of("_pt"), emit);
        decomposePoint(t, "_pt", "_nx", "_ny");
        pushFieldP(t, "_fp");
        fieldSub(t, "_fp", "_ny", "_neg_y");
        composePoint(t, "_nx", "_neg_y", "_result");
    }

    public static void emitEcOnCurve(Consumer<StackOp> emit) {
        ECTracker t = new ECTracker(List.of("_pt"), emit);
        decomposePoint(t, "_pt", "_x", "_y");

        // GAP-301: coordinate canonicity. decomposePoint BIN2NUMs each coordinate
        // as an unsigned value that may be >= p; the field arithmetic below would
        // silently reduce it mod p, so a non-canonical encoding of a valid point
        // would pass. Reject it: require x < p AND y < p (coordinates are unsigned,
        // so the 0 <= lower bound holds by construction). Combined with the curve
        // equation at the end via OP_BOOLAND so ecOnCurve still returns a boolean.
        t.copyToTop("_x", "_x_lt");
        pushFieldP(t, "_p_for_x");
        t.rawBlock(List.of("_x_lt", "_p_for_x"), "_x_canon",
            e -> e.accept(new OpcodeOp("OP_LESSTHAN")));
        t.copyToTop("_y", "_y_lt");
        pushFieldP(t, "_p_for_y");
        t.rawBlock(List.of("_y_lt", "_p_for_y"), "_y_canon",
            e -> e.accept(new OpcodeOp("OP_LESSTHAN")));
        t.toTop("_x_canon");
        t.toTop("_y_canon");
        t.rawBlock(List.of("_x_canon", "_y_canon"), "_canon",
            e -> e.accept(new OpcodeOp("OP_BOOLAND")));

        // lhs = y^2
        fieldSqr(t, "_y", "_y2");

        // rhs = x^3 + 7
        t.copyToTop("_x", "_x_copy");
        fieldSqr(t, "_x", "_x2");
        fieldMul(t, "_x2", "_x_copy", "_x3");
        t.pushInt("_seven", 7);
        fieldAdd(t, "_x3", "_seven", "_rhs");

        // Compare curve equation
        t.toTop("_y2");
        t.toTop("_rhs");
        t.rawBlock(List.of("_y2", "_rhs"), "_curve_eq",
            e -> e.accept(new OpcodeOp("OP_EQUAL")));

        // on-curve = canonical AND curve-equation
        t.toTop("_canon");
        t.toTop("_curve_eq");
        t.rawBlock(List.of("_canon", "_curve_eq"), "_result",
            e -> e.accept(new OpcodeOp("OP_BOOLAND")));
    }

    public static void emitEcModReduce(Consumer<StackOp> emit) {
        emit.accept(new OpcodeOp("OP_2DUP"));
        emit.accept(new OpcodeOp("OP_MOD"));
        emit.accept(new RotOp());
        emit.accept(new DropOp());
        emit.accept(new OverOp());
        emit.accept(new OpcodeOp("OP_ADD"));
        emit.accept(new SwapOp());
        emit.accept(new OpcodeOp("OP_MOD"));
    }

    public static void emitEcEncodeCompressed(Consumer<StackOp> emit) {
        // Split at 32: [x_bytes, y_bytes]
        emit.accept(new PushOp(PushValue.of(32)));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        // Get last byte of y for parity
        emit.accept(new OpcodeOp("OP_SIZE"));
        emit.accept(new PushOp(PushValue.of(1)));
        emit.accept(new OpcodeOp("OP_SUB"));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        // Stack: [x_bytes, y_prefix, last_byte]
        emit.accept(new OpcodeOp("OP_BIN2NUM"));
        emit.accept(new PushOp(PushValue.of(2)));
        emit.accept(new OpcodeOp("OP_MOD"));
        // Stack: [x_bytes, y_prefix, parity]
        emit.accept(new SwapOp());
        emit.accept(new DropOp());
        // Stack: [x_bytes, parity]
        emit.accept(new IfOp(
            List.of(new PushOp(PushValue.ofHex("03"))),
            List.of(new PushOp(PushValue.ofHex("02")))
        ));
        emit.accept(new SwapOp());
        emit.accept(new OpcodeOp("OP_CAT"));
    }

    public static void emitEcMakePoint(Consumer<StackOp> emit) {
        // y to 32-byte BE
        emit.accept(new PushOp(PushValue.of(33)));
        emit.accept(new OpcodeOp("OP_NUM2BIN"));
        emit.accept(new PushOp(PushValue.of(32)));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        emit.accept(new DropOp());
        emitReverse32(emit);
        // Stack: [x_num, y_be]
        emit.accept(new SwapOp());
        // x to 32-byte BE
        emit.accept(new PushOp(PushValue.of(33)));
        emit.accept(new OpcodeOp("OP_NUM2BIN"));
        emit.accept(new PushOp(PushValue.of(32)));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        emit.accept(new DropOp());
        emitReverse32(emit);
        // Stack: [y_be, x_be]
        emit.accept(new SwapOp());
        emit.accept(new OpcodeOp("OP_CAT"));
    }

    public static void emitEcPointX(Consumer<StackOp> emit) {
        emit.accept(new PushOp(PushValue.of(32)));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        emit.accept(new DropOp());
        emitReverse32(emit);
        emit.accept(new PushOp(PushValue.ofHex("00")));
        emit.accept(new OpcodeOp("OP_CAT"));
        emit.accept(new OpcodeOp("OP_BIN2NUM"));
    }

    public static void emitEcPointY(Consumer<StackOp> emit) {
        emit.accept(new PushOp(PushValue.of(32)));
        emit.accept(new OpcodeOp("OP_SPLIT"));
        emit.accept(new SwapOp());
        emit.accept(new DropOp());
        emitReverse32(emit);
        emit.accept(new PushOp(PushValue.ofHex("00")));
        emit.accept(new OpcodeOp("OP_CAT"));
        emit.accept(new OpcodeOp("OP_BIN2NUM"));
    }

    // ==================================================================
    // Dispatch
    // ==================================================================

    private static final java.util.Set<String> NAMES = java.util.Set.of(
        "ecAdd", "ecMul", "ecMulGen",
        "ecNegate", "ecOnCurve", "ecModReduce",
        "ecEncodeCompressed", "ecMakePoint",
        "ecPointX", "ecPointY"
    );

    public static boolean isEcBuiltin(String name) {
        return NAMES.contains(name);
    }

    public static void dispatch(String funcName, Consumer<StackOp> emit) {
        switch (funcName) {
            case "ecAdd" -> emitEcAdd(emit);
            case "ecMul" -> emitEcMul(emit);
            case "ecMulGen" -> emitEcMulGen(emit);
            case "ecNegate" -> emitEcNegate(emit);
            case "ecOnCurve" -> emitEcOnCurve(emit);
            case "ecModReduce" -> emitEcModReduce(emit);
            case "ecEncodeCompressed" -> emitEcEncodeCompressed(emit);
            case "ecMakePoint" -> emitEcMakePoint(emit);
            case "ecPointX" -> emitEcPointX(emit);
            case "ecPointY" -> emitEcPointY(emit);
            default -> throw new RuntimeException("unknown EC builtin: " + funcName);
        }
    }
}
