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
    // Jacobian point operations (for ecMul)
    // ==================================================================

    private static void jacobianDouble(ECTracker t) {
        // Save copies for later use
        t.copyToTop("jy", "_jy_save");
        t.copyToTop("jx", "_jx_save");
        t.copyToTop("jz", "_jz_save");

        // A = jy^2
        fieldSqr(t, "jy", "_A");

        // B = 4 * jx * A
        t.copyToTop("_A", "_A_save");
        fieldMul(t, "jx", "_A", "_xA");
        t.pushInt("_four", 4);
        fieldMul(t, "_xA", "_four", "_B");

        // C = 8 * A^2
        fieldSqr(t, "_A_save", "_A2");
        t.pushInt("_eight", 8);
        fieldMul(t, "_A2", "_eight", "_C");

        // D = 3 * X^2
        fieldSqr(t, "_jx_save", "_x2");
        t.pushInt("_three", 3);
        fieldMul(t, "_x2", "_three", "_D");

        // nx = D^2 - 2*B
        t.copyToTop("_D", "_D_save");
        t.copyToTop("_B", "_B_save");
        fieldSqr(t, "_D", "_D2");
        t.copyToTop("_B", "_B1");
        fieldMulConst(t, "_B1", 2, "_2B");
        fieldSub(t, "_D2", "_2B", "_nx");

        // ny = D*(B - nx) - C
        t.copyToTop("_nx", "_nx_copy");
        fieldSub(t, "_B_save", "_nx_copy", "_B_nx");
        fieldMul(t, "_D_save", "_B_nx", "_D_B_nx");
        fieldSub(t, "_D_B_nx", "_C", "_ny");

        // nz = 2 * Y * Z
        fieldMul(t, "_jy_save", "_jz_save", "_yz");
        fieldMulConst(t, "_yz", 2, "_nz");

        // Clean up leftovers: _B and old jz (only copied, never consumed)
        t.toTop("_B"); t.drop();
        t.toTop("jz"); t.drop();
        t.toTop("_nx"); t.rename("jx");
        t.toTop("_ny"); t.rename("jy");
        t.toTop("_nz"); t.rename("jz");
    }

    private static void jacobianToAffine(ECTracker t, String rxName, String ryName) {
        fieldInv(t, "jz", "_zinv");
        t.copyToTop("_zinv", "_zinv_keep");
        fieldSqr(t, "_zinv", "_zinv2");
        t.copyToTop("_zinv2", "_zinv2_keep");
        fieldMul(t, "_zinv_keep", "_zinv2", "_zinv3");
        fieldMul(t, "jx", "_zinv2_keep", rxName);
        fieldMul(t, "jy", "_zinv3", ryName);
    }

    // ==================================================================
    // Jacobian mixed addition (P_jacobian + Q_affine)
    // ==================================================================

    /**
     * Build Jacobian mixed-add ops for use inside OP_IF. Uses an inner
     * ECTracker to leverage field arithmetic helpers.
     *
     * Stack: [..., ax, ay, _k, jx, jy, jz]
     */
    private static void buildJacobianAddAffineInline(Consumer<StackOp> e, ECTracker t) {
        jacobianAddAffineBody(new ECTracker(t.nm, e), false);
    }

    /**
     * The mixed-add itself, emitting through an ECTracker the caller owns.
     *
     * <p>{@code keepHR} additionally leaves copies of H and R on the stack. They are the
     * exception detector: H = U2 - X1 and R = S2 - Y1 are both zero exactly when the
     * Jacobian accumulator is the same curve point as the affine operand, the one case
     * these formulas cannot compute (see buildJacobianAddOrDoubleInline).
     */
    private static void jacobianAddAffineBody(ECTracker it, boolean keepHR) {
        // Save copies of values consumed but needed later
        it.copyToTop("jz", "_jz_for_z1cu");
        it.copyToTop("jz", "_jz_for_z3");
        it.copyToTop("jy", "_jy_for_y3");
        it.copyToTop("jx", "_jx_for_u1h2");

        // Z1sq = jz^2
        fieldSqr(it, "jz", "_Z1sq");

        // Z1cu = _jz_for_z1cu * Z1sq
        it.copyToTop("_Z1sq", "_Z1sq_for_u2");
        fieldMul(it, "_jz_for_z1cu", "_Z1sq", "_Z1cu");

        // U2 = ax * Z1sq_for_u2
        it.copyToTop("ax", "_ax_c");
        fieldMul(it, "_ax_c", "_Z1sq_for_u2", "_U2");

        // S2 = ay * Z1cu
        it.copyToTop("ay", "_ay_c");
        fieldMul(it, "_ay_c", "_Z1cu", "_S2");

        // H = U2 - jx
        fieldSub(it, "_U2", "jx", "_H");

        // R = S2 - jy
        fieldSub(it, "_S2", "jy", "_R");

        if (keepHR) {
            it.copyToTop("_H", "_H_keep");
            it.copyToTop("_R", "_R_keep");
        }

        // Save copies of H
        it.copyToTop("_H", "_H_for_h3");
        it.copyToTop("_H", "_H_for_z3");

        // H2 = H^2
        fieldSqr(it, "_H", "_H2");

        // Save H2 for U1H2
        it.copyToTop("_H2", "_H2_for_u1h2");

        // H3 = H_for_h3 * H2
        fieldMul(it, "_H_for_h3", "_H2", "_H3");

        // U1H2 = _jx_for_u1h2 * H2_for_u1h2
        fieldMul(it, "_jx_for_u1h2", "_H2_for_u1h2", "_U1H2");

        // Save R, U1H2, H3 for Y3
        it.copyToTop("_R", "_R_for_y3");
        it.copyToTop("_U1H2", "_U1H2_for_y3");
        it.copyToTop("_H3", "_H3_for_y3");

        // X3 = R^2 - H3 - 2*U1H2
        fieldSqr(it, "_R", "_R2");
        fieldSub(it, "_R2", "_H3", "_x3_tmp");
        fieldMulConst(it, "_U1H2", 2, "_2U1H2");
        fieldSub(it, "_x3_tmp", "_2U1H2", "_X3");

        // Y3 = R_for_y3*(U1H2_for_y3 - X3) - jy_for_y3*H3_for_y3
        it.copyToTop("_X3", "_X3_c");
        fieldSub(it, "_U1H2_for_y3", "_X3_c", "_u_minus_x");
        fieldMul(it, "_R_for_y3", "_u_minus_x", "_r_tmp");
        fieldMul(it, "_jy_for_y3", "_H3_for_y3", "_jy_h3");
        fieldSub(it, "_r_tmp", "_jy_h3", "_Y3");

        // Z3 = _jz_for_z3 * _H_for_z3
        fieldMul(it, "_jz_for_z3", "_H_for_z3", "_Z3");

        // Rename results to jx/jy/jz
        it.toTop("_X3"); it.rename("jx");
        it.toTop("_Y3"); it.rename("jy");
        it.toTop("_Z3"); it.rename("jz");
    }

    /**
     * Branchless select of one Jacobian coordinate: {@code add + cond*(dbl - add)}.
     * Same shape as the numerator/denominator select in affineAdd, so both paths emit
     * the identical op sequence and the tracker's static stack model holds.
     * Consumes addName, dblName and condName.
     */
    private static void selectCoord(ECTracker t, String addName, String dblName,
                                    String condName, String resultName) {
        t.copyToTop(addName, "_sel_add_c");
        fieldSub(t, dblName, "_sel_add_c", "_sel_diff");
        fieldMul(t, "_sel_diff", condName, "_sel_scaled");
        fieldAdd(t, addName, "_sel_scaled", resultName);
    }

    /**
     * The ladder's LAST conditional step: mixed-add, but correct when the accumulator
     * already equals the point being added.
     *
     * <p>The Jacobian mixed-add cannot double. It computes H = U2 - X1, and when the two
     * operands are the same curve point H = 0, so Z3 = Z1*H = 0 — the point at infinity —
     * and since fieldInv is Fermat (inv(0) = 0), jacobianToAffine turns that into the
     * ALL-ZERO point instead of 2P. {@code ecMul(P, 2n)} and {@code ecMulGen(2n)}
     * returned 64 zero bytes.
     *
     * <p>WHY ONLY THE LAST STEP. After step i the accumulator holds c_i*P where
     * c_i = k' &gt;&gt; i and k' = k + 3n, so the conditional step adds P to (c_i - 1)*P.
     * secp256k1 has cofactor 1, so P has order n and the degenerate cases are exactly
     * c_i == 2 (mod n) — accumulator == P — and c_i == 0 or 1 (mod n) — accumulator == -P
     * or O. c_i ranges over a CONTIGUOUS interval determined only by i, so this is
     * decidable by interval arithmetic rather than by sampling, and over the whole domain
     * k in [0, n-1] only two steps qualify, both at i = 0:
     *
     * <pre>
     *   k = 2  -&gt;  c_0 = 3n+2 == 2, odd, so the add runs: accumulator == P.  &lt;- bug
     *   k = 0  -&gt;  c_0 = 3n   == 0, odd, so the add runs: accumulator == -P,
     *              true result the point at infinity, which affine coordinates
     *              cannot represent; it stays the all-zero point, as before.
     * </pre>
     *
     * <p>Handling H == 0 at every one of the 257 steps would cost ~70% more script bytes;
     * handling it here costs 0.26%. The operand P is caller-supplied but cannot move the
     * exception, because the condition depends only on c_i mod ord(P) and ord(P) = n for
     * every point on the curve. Points that are NOT on the curve carry no such guarantee —
     * gate untrusted input on {@code ecOnCurve} first.
     *
     * <p>Stack layout: [..., ax, ay, _k, jx, jy, jz] — same in and out.
     */
    private static void buildJacobianAddOrDoubleInline(Consumer<StackOp> e, ECTracker t) {
        ECTracker it = new ECTracker(t.nm, e);

        // Keep the pre-add accumulator: it is what must be DOUBLED in the
        // exceptional case, and the add below consumes jx/jy/jz.
        it.copyToTop("jx", "_sx");
        it.copyToTop("jy", "_sy");
        it.copyToTop("jz", "_sz");

        jacobianAddAffineBody(it, true);

        // cond = (H == 0) AND (R == 0). Requiring R == 0 too keeps the
        // accumulator == -P case (k = 0) on the add path, where Z3 = 0 correctly
        // signals the point at infinity.
        it.toTop("_H_keep");
        it.pushInt("_zero_h", 0);
        it.rawBlock(List.of("_H_keep", "_zero_h"), "_h_is0",
                e2 -> e2.accept(new OpcodeOp("OP_NUMEQUAL")));
        it.toTop("_R_keep");
        it.pushInt("_zero_r", 0);
        it.rawBlock(List.of("_R_keep", "_zero_r"), "_r_is0",
                e2 -> e2.accept(new OpcodeOp("OP_NUMEQUAL")));
        it.toTop("_h_is0");
        it.toTop("_r_is0");
        it.rawBlock(List.of("_h_is0", "_r_is0"), "_cond",
                e2 -> e2.accept(new OpcodeOp("OP_BOOLAND")));

        // Move the add result aside so jacobianDouble can work on jx/jy/jz again,
        // this time holding the saved accumulator.
        it.toTop("jx"); it.rename("_add_x");
        it.toTop("jy"); it.rename("_add_y");
        it.toTop("jz"); it.rename("_add_z");
        it.toTop("_sx"); it.rename("jx");
        it.toTop("_sy"); it.rename("jy");
        it.toTop("_sz"); it.rename("jz");
        jacobianDouble(it);
        it.toTop("jx"); it.rename("_dbl_x");
        it.toTop("jy"); it.rename("_dbl_y");
        it.toTop("jz"); it.rename("_dbl_z");

        it.copyToTop("_cond", "_cond_x");
        selectCoord(it, "_add_x", "_dbl_x", "_cond_x", "jx");
        it.copyToTop("_cond", "_cond_y");
        selectCoord(it, "_add_y", "_dbl_y", "_cond_y", "jy");
        it.toTop("_cond"); it.rename("_cond_z");
        selectCoord(it, "_add_z", "_dbl_z", "_cond_z", "jz");
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
     * Reduces a scalar to [0, n-1]: ((k mod n) + n) mod n.
     *
     * <p>OP_MOD takes the sign of the DIVIDEND, so {@code k mod n} alone lands in
     * (-n, n); the {@code + n, mod n} normalises the negative half. One push of n
     * covers both reductions — the same shape as {@code emitEcModReduce}.
     *
     * <p>Without it, {@link #emitEcMul}'s ladder is only correct while
     * 2^257 &lt;= k + 3n &lt; 2^258: a scalar &gt;= ~n sets bit 258, the
     * 257-iteration loop never sees it, and the ladder returns a DIFFERENT
     * multiple of P rather than failing. Scalars are contract input, so that is
     * attacker-chosen. Reducing costs 1 push + 8 opcodes (42 bytes) against a
     * ~429 KB script, and makes k &gt;= n, k &lt; 0 and k = 0 all well defined.
     */
    private static void emitScalarReduce(ECTracker t, String kName, String resultName) {
        t.pushBigInt("_n_red", EC_CURVE_N);
        t.rawBlock(List.of(kName, "_n_red"), resultName, e -> {
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

    public static void emitEcMul(Consumer<StackOp> emit) {
        ECTracker t = new ECTracker(List.of("_pt", "_k"), emit);
        decomposePoint(t, "_pt", "ax", "ay");

        // k' = k + 3n
        //
        // "k in [1, n-1]" is a PRECONDITION the caller cannot enforce — the scalar
        // is usually an unlock argument — so reduce it first.
        t.toTop("_k");
        emitScalarReduce(t, "_k", "_kr");
        t.pushBigInt("_n", EC_CURVE_N);
        t.rawBlock(List.of("_kr", "_n"), "_kn", e -> e.accept(new OpcodeOp("OP_ADD")));
        t.pushBigInt("_n2", EC_CURVE_N);
        t.rawBlock(List.of("_kn", "_n2"), "_kn2", e -> e.accept(new OpcodeOp("OP_ADD")));
        t.pushBigInt("_n3", EC_CURVE_N);
        t.rawBlock(List.of("_kn2", "_n3"), "_kn3", e -> e.accept(new OpcodeOp("OP_ADD")));
        t.rename("_k");

        // Init accumulator = P
        t.copyToTop("ax", "jx");
        t.copyToTop("ay", "jy");
        t.pushInt("jz", 1);

        // 257 iterations: bits 256 down to 0
        for (int bit = 256; bit >= 0; bit--) {
            // Double accumulator
            jacobianDouble(t);

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
            // Only the final step can be handed two equal operands — see
            // buildJacobianAddOrDoubleInline for why, and for what it costs not to.
            if (bit == 0) {
                buildJacobianAddOrDoubleInline(addOps::add, t);
            } else {
                buildJacobianAddAffineInline(addOps::add, t);
            }
            emit.accept(new IfOp(addOps, List.of()));
        }

        // Convert Jacobian to affine
        jacobianToAffine(t, "_rx", "_ry");

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
