// P-256 / P-384 codegen — NIST elliptic curve operations for Bitcoin Script.
//
// Follows the same pattern as ec.go (secp256k1). Uses ECTracker for
// named stack state tracking, but with different field primes, curve orders,
// and generator points.
//
// Point representation:
//
//	P-256: 64 bytes (x[32] || y[32], big-endian unsigned)
//	P-384: 96 bytes (x[48] || y[48], big-endian unsigned)
//
// Key difference from secp256k1: curve parameter a = -3 (not 0), which gives
// an optimized Jacobian doubling formula.
package codegen

import (
	"math/big"
)

// ===========================================================================
// P-256 constants (secp256r1 / NIST P-256)
// ===========================================================================

var (
	p256P       *big.Int
	p256PMinus2 *big.Int
	p256B       *big.Int
	p256N       *big.Int
	p256NMinus2 *big.Int
	p256GX      *big.Int
	p256GY      *big.Int
	p256SqrtExp *big.Int
)

// ===========================================================================
// P-384 constants (secp384r1 / NIST P-384)
// ===========================================================================

var (
	p384P       *big.Int
	p384PMinus2 *big.Int
	p384B       *big.Int
	p384N       *big.Int
	p384NMinus2 *big.Int
	p384GX      *big.Int
	p384GY      *big.Int
	p384SqrtExp *big.Int
)

func init() {
	p256P, _ = new(big.Int).SetString("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16)
	p256PMinus2 = new(big.Int).Sub(p256P, big.NewInt(2))
	p256B, _ = new(big.Int).SetString("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16)
	p256N, _ = new(big.Int).SetString("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16)
	p256NMinus2 = new(big.Int).Sub(p256N, big.NewInt(2))
	p256GX, _ = new(big.Int).SetString("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16)
	p256GY, _ = new(big.Int).SetString("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16)
	// sqrtExp = (p + 1) / 4
	p256SqrtExp = new(big.Int).Add(p256P, big.NewInt(1))
	p256SqrtExp.Rsh(p256SqrtExp, 2)

	p384P, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff", 16)
	p384PMinus2 = new(big.Int).Sub(p384P, big.NewInt(2))
	p384B, _ = new(big.Int).SetString("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef", 16)
	p384N, _ = new(big.Int).SetString("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973", 16)
	p384NMinus2 = new(big.Int).Sub(p384N, big.NewInt(2))
	p384GX, _ = new(big.Int).SetString("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7", 16)
	p384GY, _ = new(big.Int).SetString("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", 16)
	// sqrtExp = (p + 1) / 4
	p384SqrtExp = new(big.Int).Add(p384P, big.NewInt(1))
	p384SqrtExp.Rsh(p384SqrtExp, 2)
}

// ===========================================================================
// Curve parameter structs
// ===========================================================================

type nistCurveParams struct {
	fieldP       *big.Int
	fieldPMinus2 *big.Int
	// curveB is the curve b coefficient, needed by the RCB complete formulas
	// (a = -3).
	curveB       *big.Int
	coordBytes   int // 32 for P-256, 48 for P-384
	reverseBytes func(e func(StackOp))
}

type nistGroupParams struct {
	n       *big.Int
	nMinus2 *big.Int
}

var p256CurveParams = &nistCurveParams{
	fieldP:       nil, // set in init
	fieldPMinus2: nil,
	coordBytes:   32,
	reverseBytes: ecEmitReverse32, // reuse from ec.go
}

var p384CurveParams = &nistCurveParams{
	fieldP:       nil,
	fieldPMinus2: nil,
	coordBytes:   48,
	reverseBytes: emitReverse48,
}

var p256GroupParams = &nistGroupParams{n: nil, nMinus2: nil}
var p384GroupParams = &nistGroupParams{n: nil, nMinus2: nil}

func init() {
	p256CurveParams.fieldP = p256P
	p256CurveParams.fieldPMinus2 = p256PMinus2
	p256CurveParams.curveB = p256B
	p384CurveParams.fieldP = p384P
	p384CurveParams.fieldPMinus2 = p384PMinus2
	p384CurveParams.curveB = p384B
	p256GroupParams.n = p256N
	p256GroupParams.nMinus2 = p256NMinus2
	p384GroupParams.n = p384N
	p384GroupParams.nMinus2 = p384NMinus2
}

// ===========================================================================
// Byte reversal for 48 bytes (P-384)
// ===========================================================================

// emitReverse48 emits inline byte reversal for a 48-byte value on TOS.
func emitReverse48(e func(StackOp)) {
	e(StackOp{Op: "opcode", Code: "OP_0"})
	e(StackOp{Op: "swap"})
	for i := 0; i < 48; i++ {
		e(StackOp{Op: "push", Value: bigIntPush(1)})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
		e(StackOp{Op: "rot"})
		e(StackOp{Op: "rot"})
		e(StackOp{Op: "swap"})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "swap"})
	}
	e(StackOp{Op: "drop"})
}

// ===========================================================================
// bigintToNBytes converts a *big.Int to an N-byte big-endian byte slice.
// ===========================================================================

func bigintToNBytes(n *big.Int, size int) []byte {
	bytes := make([]byte, size)
	b := n.Bytes()
	copy(bytes[size-len(b):], b)
	return bytes
}

// ===========================================================================
// Helper: bit length of a big.Int
// ===========================================================================

func bigIntBitLen(n *big.Int) int {
	return n.BitLen()
}

// ===========================================================================
// Generic curve field arithmetic (parameterized by prime)
// ===========================================================================

func cPushFieldP(t *ECTracker, name string, c *nistCurveParams) {
	t.pushBigInt(name, c.fieldP)
}

func cFieldMod(t *ECTracker, aName, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	cPushFieldP(t, "_fmod_p", c)
	t.rawBlock([]string{aName, "_fmod_p"}, resultName, func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_2DUP"})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
		e(StackOp{Op: "rot"})
		e(StackOp{Op: "drop"})
		e(StackOp{Op: "over"})
		e(StackOp{Op: "opcode", Code: "OP_ADD"})
		e(StackOp{Op: "swap"})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
	})
}

func cFieldAdd(t *ECTracker, aName, bName, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	t.toTop(bName)
	t.rawBlock([]string{aName, bName}, "_fadd_sum", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_ADD"})
	})
	cFieldMod(t, "_fadd_sum", resultName, c)
}

func cFieldSub(t *ECTracker, aName, bName, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	t.toTop(bName)
	t.rawBlock([]string{aName, bName}, "_fsub_diff", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_SUB"})
	})
	cFieldMod(t, "_fsub_diff", resultName, c)
}

func cFieldMul(t *ECTracker, aName, bName, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	t.toTop(bName)
	t.rawBlock([]string{aName, bName}, "_fmul_prod", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_MUL"})
	})
	cFieldMod(t, "_fmul_prod", resultName, c)
}

func cFieldMulConst(t *ECTracker, aName string, cv int64, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	t.rawBlock([]string{aName}, "_fmc_prod", func(e func(StackOp)) {
		if cv == 2 {
			e(StackOp{Op: "opcode", Code: "OP_2MUL"})
		} else {
			e(StackOp{Op: "push", Value: bigIntPush(cv)})
			e(StackOp{Op: "opcode", Code: "OP_MUL"})
		}
	})
	cFieldMod(t, "_fmc_prod", resultName, c)
}

// cFieldMulBig computes (a * cv) mod p for a FULL-WIDTH constant such as the
// curve b coefficient, which does not fit the int64 taken by cFieldMulConst.
func cFieldMulBig(t *ECTracker, aName string, cv *big.Int, resultName string, c *nistCurveParams) {
	t.toTop(aName)
	t.rawBlock([]string{aName}, "_fmc_prod", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: PushValue{Kind: "bigint", BigInt: cv}})
		e(StackOp{Op: "opcode", Code: "OP_MUL"})
	})
	cFieldMod(t, "_fmc_prod", resultName, c)
}

func cFieldSqr(t *ECTracker, aName, resultName string, c *nistCurveParams) {
	t.copyToTop(aName, "_fsqr_copy")
	cFieldMul(t, aName, "_fsqr_copy", resultName, c)
}

// cFieldInv computes a^(p-2) mod p via generic square-and-multiply.
func cFieldInv(t *ECTracker, aName, resultName string, c *nistCurveParams) {
	exp := c.fieldPMinus2
	bits := bigIntBitLen(exp)

	// Start: result = a (highest bit of exp is 1)
	t.copyToTop(aName, "_inv_r")

	for i := bits - 2; i >= 0; i-- {
		cFieldSqr(t, "_inv_r", "_inv_r2", c)
		t.rename("_inv_r")
		if exp.Bit(i) == 1 {
			t.copyToTop(aName, "_inv_a")
			cFieldMul(t, "_inv_r", "_inv_a", "_inv_m", c)
			t.rename("_inv_r")
		}
	}

	t.toTop(aName)
	t.drop()
	t.toTop("_inv_r")
	t.rename(resultName)
}

// ===========================================================================
// Group-order arithmetic (for ECDSA: mod n operations)
// ===========================================================================

func cPushGroupN(t *ECTracker, name string, g *nistGroupParams) {
	t.pushBigInt(name, g.n)
}

func cGroupMod(t *ECTracker, aName, resultName string, g *nistGroupParams) {
	t.toTop(aName)
	cPushGroupN(t, "_gmod_n", g)
	t.rawBlock([]string{aName, "_gmod_n"}, resultName, func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_2DUP"})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
		e(StackOp{Op: "rot"})
		e(StackOp{Op: "drop"})
		e(StackOp{Op: "over"})
		e(StackOp{Op: "opcode", Code: "OP_ADD"})
		e(StackOp{Op: "swap"})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
	})
}

func cGroupMul(t *ECTracker, aName, bName, resultName string, g *nistGroupParams) {
	t.toTop(aName)
	t.toTop(bName)
	t.rawBlock([]string{aName, bName}, "_gmul_prod", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_MUL"})
	})
	cGroupMod(t, "_gmul_prod", resultName, g)
}

// cGroupInv computes a^(n-2) mod n via square-and-multiply.
func cGroupInv(t *ECTracker, aName, resultName string, g *nistGroupParams) {
	exp := g.nMinus2
	bits := bigIntBitLen(exp)

	t.copyToTop(aName, "_ginv_r")

	for i := bits - 2; i >= 0; i-- {
		// Square
		t.copyToTop("_ginv_r", "_ginv_sq_copy")
		cGroupMul(t, "_ginv_r", "_ginv_sq_copy", "_ginv_sq", g)
		t.rename("_ginv_r")
		if exp.Bit(i) == 1 {
			t.copyToTop(aName, "_ginv_a")
			cGroupMul(t, "_ginv_r", "_ginv_a", "_ginv_m", g)
			t.rename("_ginv_r")
		}
	}

	t.toTop(aName)
	t.drop()
	t.toTop("_ginv_r")
	t.rename(resultName)
}

// ===========================================================================
// Point decompose / compose (parameterized by coordinate byte size)
// ===========================================================================

func cDecomposePoint(t *ECTracker, pointName, xName, yName string, c *nistCurveParams) {
	t.toTop(pointName)
	t.rawBlock([]string{pointName}, "", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(int64(c.coordBytes))})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	})
	t.nm = append(t.nm, "_dp_xb")
	t.nm = append(t.nm, "_dp_yb")

	// Convert y_bytes (on top) to num
	t.rawBlock([]string{"_dp_yb"}, yName, func(e func(StackOp)) {
		c.reverseBytes(e)
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Convert x_bytes to num
	t.toTop("_dp_xb")
	t.rawBlock([]string{"_dp_xb"}, xName, func(e func(StackOp)) {
		c.reverseBytes(e)
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Swap to standard order [xName, yName]
	t.swap()
}

func cComposePoint(t *ECTracker, xName, yName, resultName string, c *nistCurveParams) {
	numBinSize := int64(c.coordBytes + 1)

	// Convert x to coordBytes big-endian
	t.toTop(xName)
	t.rawBlock([]string{xName}, "_cp_xb", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(numBinSize)})
		e(StackOp{Op: "opcode", Code: "OP_NUM2BIN"})
		e(StackOp{Op: "push", Value: bigIntPush(int64(c.coordBytes))})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
		e(StackOp{Op: "drop"})
		c.reverseBytes(e)
	})

	// Convert y to coordBytes big-endian
	t.toTop(yName)
	t.rawBlock([]string{yName}, "_cp_yb", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(numBinSize)})
		e(StackOp{Op: "opcode", Code: "OP_NUM2BIN"})
		e(StackOp{Op: "push", Value: bigIntPush(int64(c.coordBytes))})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
		e(StackOp{Op: "drop"})
		c.reverseBytes(e)
	})

	// Cat: x_be || y_be
	t.toTop("_cp_xb")
	t.toTop("_cp_yb")
	t.rawBlock([]string{"_cp_xb", "_cp_yb"}, resultName, func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
	})
}

// ===========================================================================
// Affine point addition
// ===========================================================================

func cAffineAdd(t *ECTracker, c *nistCurveParams) {
	// The chord slope (qy-py)/(qx-px) divides by zero when P == Q, so doubling
	// needs the tangent (3*px^2 + a)/(2*py) — and a = -3 on both NIST curves,
	// giving (3*px^2 - 3)/(2*py). Pick numerator and denominator BEFORE the one
	// cFieldInv:
	//   cond = (px == qx)                          1 when doubling, else 0
	//   num  = cond ? 3*px^2 - 3 : (qy - py)
	//   den  = cond ? 2*py       : (qx - px)
	//
	// selected as b + cond*(a - b) over the field, which needs no branch and so
	// keeps the emitted op sequence — and the tracker's static stack model —
	// identical on both paths. Mirrors the secp256k1 fix in ec.go.
	//
	// NOT handled: P == -Q, whose true result is the point at infinity, which
	// affine coordinates cannot represent.
	t.copyToTop("px", "_px_eq")
	t.copyToTop("qx", "_qx_eq")
	t.rawBlock([]string{"_px_eq", "_qx_eq"}, "_cond", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_NUMEQUAL"})
	})

	// chord numerator / denominator
	t.copyToTop("qy", "_qy1")
	t.copyToTop("py", "_py1")
	cFieldSub(t, "_qy1", "_py1", "_num_chord", c)
	t.copyToTop("qx", "_qx1")
	t.copyToTop("px", "_px1")
	cFieldSub(t, "_qx1", "_px1", "_den_chord", c)

	// tangent numerator / denominator: 3*px^2 - 3 and 2*py
	t.copyToTop("px", "_px_t")
	cFieldSqr(t, "_px_t", "_px_sq", c)
	cFieldMulConst(t, "_px_sq", 3, "_3x2", c)
	t.pushInt("_three", 3)
	cFieldSub(t, "_3x2", "_three", "_num_tan", c)
	t.copyToTop("py", "_py_t")
	cFieldMulConst(t, "_py_t", 2, "_den_tan", c)

	// num = num_chord + cond*(num_tan - num_chord)
	t.copyToTop("_num_chord", "_num_chord_c")
	cFieldSub(t, "_num_tan", "_num_chord_c", "_num_diff", c)
	t.copyToTop("_cond", "_cond_n")
	cFieldMul(t, "_num_diff", "_cond_n", "_num_sel", c)
	cFieldAdd(t, "_num_chord", "_num_sel", "_s_num", c)

	// den = den_chord + cond*(den_tan - den_chord)
	t.copyToTop("_den_chord", "_den_chord_c")
	cFieldSub(t, "_den_tan", "_den_chord_c", "_den_diff", c)
	t.toTop("_cond")
	t.rename("_cond_d")
	cFieldMul(t, "_den_diff", "_cond_d", "_den_sel", c)
	cFieldAdd(t, "_den_chord", "_den_sel", "_s_den", c)

	// s = s_num / s_den mod p
	cFieldInv(t, "_s_den", "_s_den_inv", c)
	cFieldMul(t, "_s_num", "_s_den_inv", "_s", c)

	// rx = s^2 - px - qx mod p
	t.copyToTop("_s", "_s_keep")
	cFieldSqr(t, "_s", "_s2", c)
	t.copyToTop("px", "_px2")
	cFieldSub(t, "_s2", "_px2", "_rx1", c)
	t.copyToTop("qx", "_qx2")
	cFieldSub(t, "_rx1", "_qx2", "rx", c)

	// ry = s * (px - rx) - py mod p
	t.copyToTop("px", "_px3")
	t.copyToTop("rx", "_rx2")
	cFieldSub(t, "_px3", "_rx2", "_px_rx", c)
	cFieldMul(t, "_s_keep", "_px_rx", "_s_px_rx", c)
	t.copyToTop("py", "_py2")
	cFieldSub(t, "_s_px_rx", "_py2", "ry", c)

	// Clean up original points
	t.toTop("px")
	t.drop()
	t.toTop("py")
	t.drop()
	t.toTop("qx")
	t.drop()
	t.toTop("qy")
	t.drop()
}

// ===========================================================================
// Jacobian point doubling with a=-3 optimization
// ===========================================================================

// cProjectiveDouble performs projective point doubling — RCB Algorithm 6
// (a = -3), 8M + 3S + 2 m_b. Expects jx, jy, jz on the tracker; replaces them
// with the doubled point.
//
// Complete: doubling the point at infinity (0 : 1 : 0) yields (0 : 1 : 0).
//
// P-256 and P-384 have a = -3, so these are the a = -3 algorithms (5 and 6),
// NOT the a = 0 pair used for secp256k1 in ec.go.
func cProjectiveDouble(t *ECTracker, c *nistCurveParams) {
	B := c.curveB

	t.copyToTop("jx", "_d_x_xy")
	t.copyToTop("jx", "_d_x_xz")
	t.copyToTop("jy", "_d_y_xy")
	t.copyToTop("jy", "_d_y_yz")
	t.copyToTop("jz", "_d_z_xz")
	t.copyToTop("jz", "_d_z_yz")

	cFieldSqr(t, "jx", "_d_t0", c) // t0 = X^2
	cFieldSqr(t, "jy", "_d_t1", c) // t1 = Y^2
	cFieldSqr(t, "jz", "_d_t2", c) // t2 = Z^2

	cFieldMul(t, "_d_x_xy", "_d_y_xy", "_d_xy", c)
	cFieldMulConst(t, "_d_xy", 2, "_d_t3", c) // t3 = 2*X*Y
	cFieldMul(t, "_d_x_xz", "_d_z_xz", "_d_xz", c)
	cFieldMulConst(t, "_d_xz", 2, "_d_Z3", c) // Z3 = 2*X*Z

	t.copyToTop("_d_t2", "_d_t2_b")
	cFieldMulBig(t, "_d_t2_b", B, "_d_bt2", c)
	t.copyToTop("_d_Z3", "_d_Z3_a")
	cFieldSub(t, "_d_bt2", "_d_Z3_a", "_d_Y3", c)
	cFieldMulConst(t, "_d_Y3", 3, "_d_Y3b", c)

	t.copyToTop("_d_t1", "_d_t1_a")
	t.copyToTop("_d_t1", "_d_t1_b")
	t.copyToTop("_d_Y3b", "_d_Y3b_a")
	cFieldSub(t, "_d_t1_a", "_d_Y3b_a", "_d_X3", c)
	cFieldAdd(t, "_d_t1", "_d_Y3b", "_d_Y3c", c)

	t.copyToTop("_d_X3", "_d_X3_a")
	cFieldMul(t, "_d_X3_a", "_d_Y3c", "_d_Y3d", c)
	cFieldMul(t, "_d_X3", "_d_t3", "_d_X3b", c)

	cFieldMulConst(t, "_d_t2", 3, "_d_t2c", c)

	cFieldMulBig(t, "_d_Z3", B, "_d_Z3b", c)
	t.copyToTop("_d_t2c", "_d_t2c_a")
	cFieldSub(t, "_d_Z3b", "_d_t2c_a", "_d_Z3c", c)
	t.copyToTop("_d_t0", "_d_t0_a")
	cFieldSub(t, "_d_Z3c", "_d_t0_a", "_d_Z3d", c)
	cFieldMulConst(t, "_d_Z3d", 3, "_d_Z3e", c)

	cFieldMulConst(t, "_d_t0", 3, "_d_t0b", c)
	cFieldSub(t, "_d_t0b", "_d_t2c", "_d_t0c", c)

	t.copyToTop("_d_Z3e", "_d_Z3e_a")
	cFieldMul(t, "_d_t0c", "_d_Z3e_a", "_d_t0d", c)
	cFieldAdd(t, "_d_Y3d", "_d_t0d", "_d_Y3e", c)

	cFieldMul(t, "_d_y_yz", "_d_z_yz", "_d_yz", c)
	cFieldMulConst(t, "_d_yz", 2, "_d_t0e", c)

	t.copyToTop("_d_t0e", "_d_t0e_a")
	cFieldMul(t, "_d_t0e_a", "_d_Z3e", "_d_Z3f", c)
	cFieldSub(t, "_d_X3b", "_d_Z3f", "_d_X3c", c)

	cFieldMul(t, "_d_t0e", "_d_t1_b", "_d_Z3g", c)
	cFieldMulConst(t, "_d_Z3g", 4, "_d_Z3h", c)

	t.toTop("_d_X3c")
	t.rename("jx")
	t.toTop("_d_Y3e")
	t.rename("jy")
	t.toTop("_d_Z3h")
	t.rename("jz")
}

// cProjectiveToAffine consumes jx, jy, jz; produces rxName, ryName.
//
// cFieldInv is Fermat exponentiation, so inv(0) = 0: the point at infinity
// (Z = 0) converts to (0, 0), the all-zero point blob.
func cProjectiveToAffine(t *ECTracker, rxName, ryName string, c *nistCurveParams) {
	cFieldInv(t, "jz", "_zinv", c)
	t.copyToTop("_zinv", "_zinv_b")
	cFieldMul(t, "jx", "_zinv", rxName, c)
	cFieldMul(t, "jy", "_zinv_b", ryName, c)
}

// cBuildProjectiveAddMixedInline builds complete mixed-add ops for use inside
// OP_IF — RCB Algorithm 5 (a = -3), 11M + 2 m_b.
//
// Complete: accumulator == Q doubles correctly (the case that returned the
// zero point for k = 2), accumulator == -Q yields infinity, and an infinity
// accumulator yields Q.
func cBuildProjectiveAddMixedInline(e func(StackOp), t *ECTracker, c *nistCurveParams) {
	initNm := make([]string, len(t.nm))
	copy(initNm, t.nm)
	it := NewECTracker(initNm, e)
	B := c.curveB

	it.copyToTop("ax", "_m_x2a")
	it.copyToTop("ax", "_m_x2b")
	it.copyToTop("ax", "_m_x2c")
	it.copyToTop("ay", "_m_y2a")
	it.copyToTop("ay", "_m_y2b")
	it.copyToTop("ay", "_m_y2c")
	it.copyToTop("jx", "_m_x1a")
	it.copyToTop("jx", "_m_x1b")
	it.copyToTop("jy", "_m_y1a")
	it.copyToTop("jy", "_m_y1b")
	it.copyToTop("jz", "_m_z1a")
	it.copyToTop("jz", "_m_z1b")
	it.copyToTop("jz", "_m_z1c")

	cFieldMul(it, "jx", "_m_x2a", "_m_t0", c)
	cFieldMul(it, "jy", "_m_y2a", "_m_t1", c)
	cFieldAdd(it, "_m_x2b", "_m_y2b", "_m_s1", c)
	cFieldAdd(it, "_m_x1a", "_m_y1a", "_m_s2", c)
	cFieldMul(it, "_m_s1", "_m_s2", "_m_t3", c)

	it.copyToTop("_m_t0", "_m_t0a")
	it.copyToTop("_m_t1", "_m_t1a")
	cFieldAdd(it, "_m_t0a", "_m_t1a", "_m_s3", c)
	cFieldSub(it, "_m_t3", "_m_s3", "_m_t3b", c)

	cFieldMul(it, "_m_y2c", "jz", "_m_t4", c)
	cFieldAdd(it, "_m_t4", "_m_y1b", "_m_t4b", c)
	cFieldMul(it, "_m_x2c", "_m_z1a", "_m_Y3", c)
	cFieldAdd(it, "_m_Y3", "_m_x1b", "_m_Y3b", c)

	cFieldMulBig(it, "_m_z1b", B, "_m_Z3", c)
	it.copyToTop("_m_Y3b", "_m_Y3b_a")
	cFieldSub(it, "_m_Y3b_a", "_m_Z3", "_m_X3", c)
	cFieldMulConst(it, "_m_X3", 3, "_m_X3b", c)

	it.copyToTop("_m_t1", "_m_t1b")
	it.copyToTop("_m_X3b", "_m_X3b_a")
	cFieldSub(it, "_m_t1b", "_m_X3b_a", "_m_Z3b", c)
	cFieldAdd(it, "_m_t1", "_m_X3b", "_m_X3c", c)

	cFieldMulBig(it, "_m_Y3b", B, "_m_Y3c", c)
	cFieldMulConst(it, "_m_z1c", 3, "_m_t2", c)

	it.copyToTop("_m_t2", "_m_t2a")
	cFieldSub(it, "_m_Y3c", "_m_t2a", "_m_Y3d", c)
	it.copyToTop("_m_t0", "_m_t0b")
	cFieldSub(it, "_m_Y3d", "_m_t0b", "_m_Y3e", c)
	cFieldMulConst(it, "_m_Y3e", 3, "_m_Y3f", c)

	cFieldMulConst(it, "_m_t0", 3, "_m_t0c", c)
	cFieldSub(it, "_m_t0c", "_m_t2", "_m_t0d", c)

	it.copyToTop("_m_t4b", "_m_t4b_a")
	it.copyToTop("_m_Y3f", "_m_Y3f_a")
	cFieldMul(it, "_m_t4b_a", "_m_Y3f_a", "_m_t1c", c)
	it.copyToTop("_m_t0d", "_m_t0d_a")
	cFieldMul(it, "_m_t0d_a", "_m_Y3f", "_m_t2b", c)

	it.copyToTop("_m_X3c", "_m_X3c_a")
	it.copyToTop("_m_Z3b", "_m_Z3b_a")
	cFieldMul(it, "_m_X3c_a", "_m_Z3b_a", "_m_Y3g", c)
	cFieldAdd(it, "_m_Y3g", "_m_t2b", "_m_Y3h", c)

	it.copyToTop("_m_t3b", "_m_t3b_a")
	cFieldMul(it, "_m_t3b_a", "_m_X3c", "_m_X3d", c)
	cFieldSub(it, "_m_X3d", "_m_t1c", "_m_X3e", c)

	cFieldMul(it, "_m_t4b", "_m_Z3b", "_m_Z3c", c)
	cFieldMul(it, "_m_t3b", "_m_t0d", "_m_t1d", c)
	cFieldAdd(it, "_m_Z3c", "_m_t1d", "_m_Z3d", c)

	it.toTop("_m_X3e")
	it.rename("jx")
	it.toTop("_m_Y3h")
	it.rename("jy")
	it.toTop("_m_Z3d")
	it.rename("jz")
}

func cEmitMul(emit func(StackOp), c *nistCurveParams, g *nistGroupParams) {
	t := NewECTracker([]string{"_pt", "_k"}, emit)
	cDecomposePoint(t, "_pt", "ax", "ay", c)

	// Reduce the scalar into [0, n-1] so the ladder covers the whole domain:
	// negative k and k >= n are now defined rather than undefined behaviour.
	cGroupMod(t, "_k", "_k", g)

	// Accumulator := point at infinity (0 : 1 : 0), a legal input to both
	// complete formulas — which is why no leading-bit special case is needed.
	t.pushInt("jx", 0)
	t.pushInt("jy", 1)
	t.pushInt("jz", 0)

	// One iteration per bit of n: 256 for P-256, 384 for P-384.
	startBit := g.n.BitLen() - 1

	for bit := startBit; bit >= 0; bit-- {
		cProjectiveDouble(t, c)

		// Extract bit: (k >> bit) & 1
		t.copyToTop("_k", "_k_copy")
		if bit == 1 {
			t.rawBlock([]string{"_k_copy"}, "_shifted", func(e func(StackOp)) {
				e(StackOp{Op: "opcode", Code: "OP_2DIV"})
			})
		} else if bit > 1 {
			t.pushInt("_shift", int64(bit))
			t.rawBlock([]string{"_k_copy", "_shift"}, "_shifted", func(e func(StackOp)) {
				e(StackOp{Op: "opcode", Code: "OP_RSHIFTNUM"})
			})
		} else {
			t.rename("_shifted")
		}
		t.pushInt("_two", 2)
		t.rawBlock([]string{"_shifted", "_two"}, "_bit", func(e func(StackOp)) {
			e(StackOp{Op: "opcode", Code: "OP_MOD"})
		})

		// Conditional add
		t.toTop("_bit")
		t.nm = t.nm[:len(t.nm)-1] // _bit consumed by IF
		var addOps []StackOp
		addEmit := func(op StackOp) { addOps = append(addOps, op) }
		cBuildProjectiveAddMixedInline(addEmit, t, c)
		emit(StackOp{Op: "if", Then: addOps, Else: []StackOp{}})
	}

	cProjectiveToAffine(t, "_rx", "_ry", c)

	// Clean up
	t.toTop("ax")
	t.drop()
	t.toTop("ay")
	t.drop()
	t.toTop("_k")
	t.drop()

	cComposePoint(t, "_rx", "_ry", "_result", c)
}

// ===========================================================================
// Square-and-multiply modular exponentiation (for sqrt)
// ===========================================================================

func cFieldPow(t *ECTracker, baseName string, exp *big.Int, resultName string, c *nistCurveParams) {
	bits := bigIntBitLen(exp)

	// Start: result = base (highest bit = 1)
	t.copyToTop(baseName, "_pow_r")

	for i := bits - 2; i >= 0; i-- {
		cFieldSqr(t, "_pow_r", "_pow_sq", c)
		t.rename("_pow_r")
		if exp.Bit(i) == 1 {
			t.copyToTop(baseName, "_pow_b")
			cFieldMul(t, "_pow_r", "_pow_b", "_pow_m", c)
			t.rename("_pow_r")
		}
	}

	t.toTop(baseName)
	t.drop()
	t.toTop("_pow_r")
	t.rename(resultName)
}

// ===========================================================================
// Pubkey decompression (prefix byte + x → (x, y))
// ===========================================================================

func cDecompressPubKey(
	t *ECTracker,
	pkName, qxName, qyName string,
	c *nistCurveParams,
	curveB, sqrtExp *big.Int,
) {
	t.toTop(pkName)

	// Split: [prefix_byte, x_bytes]
	t.rawBlock([]string{pkName}, "", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(1)})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	})
	t.nm = append(t.nm, "_dk_prefix")
	t.nm = append(t.nm, "_dk_xbytes")

	// Convert prefix to parity: 0x02 → 0, 0x03 → 1
	t.toTop("_dk_prefix")
	t.rawBlock([]string{"_dk_prefix"}, "_dk_parity", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
		e(StackOp{Op: "push", Value: bigIntPush(2)})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
	})

	// Stash parity on altstack
	t.toTop("_dk_parity")
	t.toAlt()

	// Convert x_bytes to number
	t.toTop("_dk_xbytes")
	t.rawBlock([]string{"_dk_xbytes"}, "_dk_x", func(e func(StackOp)) {
		c.reverseBytes(e)
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Save x for later
	t.copyToTop("_dk_x", "_dk_x_save")

	// Compute y^2 = x^3 - 3x + b mod p
	// x^2
	t.copyToTop("_dk_x", "_dk_x_c1")
	cFieldSqr(t, "_dk_x", "_dk_x2", c)
	// x^3 = x^2 * x
	cFieldMul(t, "_dk_x2", "_dk_x_c1", "_dk_x3", c)
	// 3 * x_save
	t.copyToTop("_dk_x_save", "_dk_x_for_3")
	cFieldMulConst(t, "_dk_x_for_3", 3, "_dk_3x", c)
	// x^3 - 3x
	cFieldSub(t, "_dk_x3", "_dk_3x", "_dk_x3m3x", c)
	// + b
	t.pushBigInt("_dk_b", curveB)
	cFieldAdd(t, "_dk_x3m3x", "_dk_b", "_dk_y2", c)

	// y = (y^2)^sqrtExp mod p
	cFieldPow(t, "_dk_y2", sqrtExp, "_dk_y_cand", c)

	// Check if candidate y has the right parity
	t.copyToTop("_dk_y_cand", "_dk_y_check")
	t.rawBlock([]string{"_dk_y_check"}, "_dk_y_par", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(2)})
		e(StackOp{Op: "opcode", Code: "OP_MOD"})
	})

	// Retrieve parity from altstack
	t.fromAlt("_dk_parity")

	// Compare
	t.toTop("_dk_y_par")
	t.toTop("_dk_parity")
	t.rawBlock([]string{"_dk_y_par", "_dk_parity"}, "_dk_match", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_EQUAL"})
	})

	// Compute p - y_cand
	t.copyToTop("_dk_y_cand", "_dk_y_for_neg")
	cPushFieldP(t, "_dk_pfn", c)
	t.toTop("_dk_y_for_neg")
	t.rawBlock([]string{"_dk_pfn", "_dk_y_for_neg"}, "_dk_neg_y", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_SUB"})
	})

	// Use OP_IF to select: if match, use y_cand (drop neg_y), else use neg_y (drop y_cand)
	t.toTop("_dk_match")
	t.nm = t.nm[:len(t.nm)-1] // condition consumed by IF

	thenOps := []StackOp{{Op: "drop"}} // remove neg_y, leaving y_cand
	elseOps := []StackOp{{Op: "nip"}}  // remove y_cand, leaving neg_y
	t.e(StackOp{Op: "if", Then: thenOps, Else: elseOps})

	// Remove one from tracker and rename the surviving item
	negIdx := -1
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_dk_neg_y" {
			negIdx = i
			break
		}
	}
	if negIdx >= 0 {
		t.nm = append(t.nm[:negIdx], t.nm[negIdx+1:]...)
	}

	ycIdx := -1
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_dk_y_cand" {
			ycIdx = i
			break
		}
	}
	if ycIdx >= 0 {
		t.nm[ycIdx] = qyName
	}

	xsIdx := -1
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_dk_x_save" {
			xsIdx = i
			break
		}
	}
	if xsIdx >= 0 {
		t.nm[xsIdx] = qxName
	}
}

// ===========================================================================
// ECDSA verification
// ===========================================================================

func cEmitVerifyECDSA(
	emit func(StackOp),
	c *nistCurveParams,
	g *nistGroupParams,
	curveB, sqrtExp, gx, gy *big.Int,
) {
	t := NewECTracker([]string{"_msg", "_sig", "_pk"}, emit)

	// Step 1: e = SHA-256(msg) as integer
	t.toTop("_msg")
	t.rawBlock([]string{"_msg"}, "_e", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_SHA256"})
		// SHA-256 produces 32 bytes BE. Convert to integer:
		ecEmitReverse32(e) // reuse 32-byte reversal from ec.go
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Step 2: Parse sig into (r, s)
	t.toTop("_sig")
	t.rawBlock([]string{"_sig"}, "", func(e func(StackOp)) {
		e(StackOp{Op: "push", Value: bigIntPush(int64(c.coordBytes))})
		e(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	})
	t.nm = append(t.nm, "_r_bytes")
	t.nm = append(t.nm, "_s_bytes")

	// Convert r_bytes to integer
	t.toTop("_r_bytes")
	t.rawBlock([]string{"_r_bytes"}, "_r", func(e func(StackOp)) {
		c.reverseBytes(e)
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Convert s_bytes to integer
	t.toTop("_s_bytes")
	t.rawBlock([]string{"_s_bytes"}, "_s", func(e func(StackOp)) {
		c.reverseBytes(e)
		e(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x00}}})
		e(StackOp{Op: "opcode", Code: "OP_CAT"})
		e(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	})

	// Step 3: Decompress pubkey
	cDecompressPubKey(t, "_pk", "_qx", "_qy", c, curveB, sqrtExp)

	// Step 4: w = s^{-1} mod n
	cGroupInv(t, "_s", "_w", g)

	// Step 5: u1 = e * w mod n
	t.copyToTop("_w", "_w_c1")
	cGroupMul(t, "_e", "_w_c1", "_u1", g)

	// Step 6: u2 = r * w mod n
	t.copyToTop("_r", "_r_save")
	cGroupMul(t, "_r", "_w", "_u2", g)

	// Step 7: R = u1*G + u2*Q
	pointBytes := c.coordBytes * 2
	gPointData := make([]byte, pointBytes)
	copy(gPointData[0:c.coordBytes], bigintToNBytes(gx, c.coordBytes))
	copy(gPointData[c.coordBytes:pointBytes], bigintToNBytes(gy, c.coordBytes))

	t.pushBytes("_G", gPointData)
	t.toTop("_u1")

	// Stash items on altstack
	t.toTop("_r_save")
	t.toAlt()
	t.toTop("_u2")
	t.toAlt()
	t.toTop("_qy")
	t.toAlt()
	t.toTop("_qx")
	t.toAlt()

	// Remove _G and _u1 from tracker before cEmitMul
	t.nm = t.nm[:len(t.nm)-1] // _u1
	t.nm = t.nm[:len(t.nm)-1] // _G

	cEmitMul(emit, c, g)

	// After mul, one result point is on the stack
	t.nm = append(t.nm, "_R1_point")

	// Pop qx/qy/u2 from altstack (LIFO order)
	t.fromAlt("_qx")
	t.fromAlt("_qy")
	t.fromAlt("_u2")

	// Stash R1 point
	t.toTop("_R1_point")
	t.toAlt()

	// Compose Q point
	cComposePoint(t, "_qx", "_qy", "_Q_point", c)

	t.toTop("_u2")

	// Remove from tracker, emit mul, push result
	t.nm = t.nm[:len(t.nm)-1] // _u2
	t.nm = t.nm[:len(t.nm)-1] // _Q_point
	cEmitMul(emit, c, g)
	t.nm = append(t.nm, "_R2_point")

	// Restore R1 point
	t.fromAlt("_R1_point")

	// Swap so R2 is on top
	t.swap()

	// Decompose both, add, compose
	cDecomposePoint(t, "_R1_point", "_rpx", "_rpy", c)
	cDecomposePoint(t, "_R2_point", "_rqx", "_rqy", c)

	// Rename to what cAffineAdd expects
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_rpx" {
			t.nm[i] = "px"
			break
		}
	}
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_rpy" {
			t.nm[i] = "py"
			break
		}
	}
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_rqx" {
			t.nm[i] = "qx"
			break
		}
	}
	for i := len(t.nm) - 1; i >= 0; i-- {
		if t.nm[i] == "_rqy" {
			t.nm[i] = "qy"
			break
		}
	}

	cAffineAdd(t, c)

	// Step 8: x_R mod n == r
	t.toTop("ry")
	t.drop()

	cGroupMod(t, "rx", "_rx_mod_n", g)

	// Restore r
	t.fromAlt("_r_save")

	// Compare
	t.toTop("_rx_mod_n")
	t.toTop("_r_save")
	t.rawBlock([]string{"_rx_mod_n", "_r_save"}, "_result", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_EQUAL"})
	})
}

// ===========================================================================
// P-256 public API
// ===========================================================================

// EmitP256Add adds two P-256 points.
func EmitP256Add(emit func(StackOp)) {
	t := NewECTracker([]string{"_pa", "_pb"}, emit)
	cDecomposePoint(t, "_pa", "px", "py", p256CurveParams)
	cDecomposePoint(t, "_pb", "qx", "qy", p256CurveParams)
	cAffineAdd(t, p256CurveParams)
	cComposePoint(t, "rx", "ry", "_result", p256CurveParams)
}

// EmitP256Mul performs P-256 scalar multiplication.
func EmitP256Mul(emit func(StackOp)) {
	cEmitMul(emit, p256CurveParams, p256GroupParams)
}

// EmitP256MulGen performs P-256 generator multiplication.
func EmitP256MulGen(emit func(StackOp)) {
	gPoint := make([]byte, 64)
	copy(gPoint[0:32], bigintToNBytes(p256GX, 32))
	copy(gPoint[32:64], bigintToNBytes(p256GY, 32))
	emit(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: gPoint}})
	emit(StackOp{Op: "swap"}) // [point, scalar]
	EmitP256Mul(emit)
}

// EmitP256Negate negates a P-256 point.
func EmitP256Negate(emit func(StackOp)) {
	t := NewECTracker([]string{"_pt"}, emit)
	cDecomposePoint(t, "_pt", "_nx", "_ny", p256CurveParams)
	cPushFieldP(t, "_fp", p256CurveParams)
	cFieldSub(t, "_fp", "_ny", "_neg_y", p256CurveParams)
	cComposePoint(t, "_nx", "_neg_y", "_result", p256CurveParams)
}

// EmitP256OnCurve checks if a P-256 point is on the curve (y^2 = x^3 - 3x + b mod p).
func EmitP256OnCurve(emit func(StackOp)) {
	t := NewECTracker([]string{"_pt"}, emit)
	cDecomposePoint(t, "_pt", "_x", "_y", p256CurveParams)

	// lhs = y^2
	cFieldSqr(t, "_y", "_y2", p256CurveParams)

	// rhs = x^3 - 3x + b
	t.copyToTop("_x", "_x_copy")
	t.copyToTop("_x", "_x_copy2")
	cFieldSqr(t, "_x", "_x2", p256CurveParams)
	cFieldMul(t, "_x2", "_x_copy", "_x3", p256CurveParams)
	cFieldMulConst(t, "_x_copy2", 3, "_3x", p256CurveParams)
	cFieldSub(t, "_x3", "_3x", "_x3m3x", p256CurveParams)
	t.pushBigInt("_b", p256B)
	cFieldAdd(t, "_x3m3x", "_b", "_rhs", p256CurveParams)

	// Compare
	t.toTop("_y2")
	t.toTop("_rhs")
	t.rawBlock([]string{"_y2", "_rhs"}, "_result", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_EQUAL"})
	})
}

// EmitP256EncodeCompressed encodes a P-256 point as 33-byte compressed pubkey.
func EmitP256EncodeCompressed(emit func(StackOp)) {
	// Split at 32: [x_bytes, y_bytes]
	emit(StackOp{Op: "push", Value: bigIntPush(32)})
	emit(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	// Get last byte of y for parity
	emit(StackOp{Op: "opcode", Code: "OP_SIZE"})
	emit(StackOp{Op: "push", Value: bigIntPush(1)})
	emit(StackOp{Op: "opcode", Code: "OP_SUB"})
	emit(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	// Stack: [x_bytes, y_prefix, last_byte]
	emit(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	emit(StackOp{Op: "push", Value: bigIntPush(2)})
	emit(StackOp{Op: "opcode", Code: "OP_MOD"})
	// Stack: [x_bytes, y_prefix, parity]
	emit(StackOp{Op: "swap"})
	emit(StackOp{Op: "drop"}) // drop y_prefix
	// Stack: [x_bytes, parity]
	emit(StackOp{Op: "if",
		Then: []StackOp{{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x03}}}},
		Else: []StackOp{{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x02}}}},
	})
	// Stack: [x_bytes, prefix_byte]
	emit(StackOp{Op: "swap"})
	emit(StackOp{Op: "opcode", Code: "OP_CAT"})
}

// EmitVerifyECDSA_P256 verifies an ECDSA signature on P-256.
func EmitVerifyECDSA_P256(emit func(StackOp)) {
	cEmitVerifyECDSA(emit, p256CurveParams, p256GroupParams, p256B, p256SqrtExp, p256GX, p256GY)
}

// ===========================================================================
// P-384 public API
// ===========================================================================

// EmitP384Add adds two P-384 points.
func EmitP384Add(emit func(StackOp)) {
	t := NewECTracker([]string{"_pa", "_pb"}, emit)
	cDecomposePoint(t, "_pa", "px", "py", p384CurveParams)
	cDecomposePoint(t, "_pb", "qx", "qy", p384CurveParams)
	cAffineAdd(t, p384CurveParams)
	cComposePoint(t, "rx", "ry", "_result", p384CurveParams)
}

// EmitP384Mul performs P-384 scalar multiplication.
func EmitP384Mul(emit func(StackOp)) {
	cEmitMul(emit, p384CurveParams, p384GroupParams)
}

// EmitP384MulGen performs P-384 generator multiplication.
func EmitP384MulGen(emit func(StackOp)) {
	gPoint := make([]byte, 96)
	copy(gPoint[0:48], bigintToNBytes(p384GX, 48))
	copy(gPoint[48:96], bigintToNBytes(p384GY, 48))
	emit(StackOp{Op: "push", Value: PushValue{Kind: "bytes", Bytes: gPoint}})
	emit(StackOp{Op: "swap"}) // [point, scalar]
	EmitP384Mul(emit)
}

// EmitP384Negate negates a P-384 point.
func EmitP384Negate(emit func(StackOp)) {
	t := NewECTracker([]string{"_pt"}, emit)
	cDecomposePoint(t, "_pt", "_nx", "_ny", p384CurveParams)
	cPushFieldP(t, "_fp", p384CurveParams)
	cFieldSub(t, "_fp", "_ny", "_neg_y", p384CurveParams)
	cComposePoint(t, "_nx", "_neg_y", "_result", p384CurveParams)
}

// EmitP384OnCurve checks if a P-384 point is on the curve.
func EmitP384OnCurve(emit func(StackOp)) {
	t := NewECTracker([]string{"_pt"}, emit)
	cDecomposePoint(t, "_pt", "_x", "_y", p384CurveParams)

	// lhs = y^2
	cFieldSqr(t, "_y", "_y2", p384CurveParams)

	// rhs = x^3 - 3x + b
	t.copyToTop("_x", "_x_copy")
	t.copyToTop("_x", "_x_copy2")
	cFieldSqr(t, "_x", "_x2", p384CurveParams)
	cFieldMul(t, "_x2", "_x_copy", "_x3", p384CurveParams)
	cFieldMulConst(t, "_x_copy2", 3, "_3x", p384CurveParams)
	cFieldSub(t, "_x3", "_3x", "_x3m3x", p384CurveParams)
	t.pushBigInt("_b", p384B)
	cFieldAdd(t, "_x3m3x", "_b", "_rhs", p384CurveParams)

	// Compare
	t.toTop("_y2")
	t.toTop("_rhs")
	t.rawBlock([]string{"_y2", "_rhs"}, "_result", func(e func(StackOp)) {
		e(StackOp{Op: "opcode", Code: "OP_EQUAL"})
	})
}

// EmitP384EncodeCompressed encodes a P-384 point as 49-byte compressed pubkey.
func EmitP384EncodeCompressed(emit func(StackOp)) {
	// Split at 48: [x_bytes, y_bytes]
	emit(StackOp{Op: "push", Value: bigIntPush(48)})
	emit(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	// Get last byte of y for parity
	emit(StackOp{Op: "opcode", Code: "OP_SIZE"})
	emit(StackOp{Op: "push", Value: bigIntPush(1)})
	emit(StackOp{Op: "opcode", Code: "OP_SUB"})
	emit(StackOp{Op: "opcode", Code: "OP_SPLIT"})
	// Stack: [x_bytes, y_prefix, last_byte]
	emit(StackOp{Op: "opcode", Code: "OP_BIN2NUM"})
	emit(StackOp{Op: "push", Value: bigIntPush(2)})
	emit(StackOp{Op: "opcode", Code: "OP_MOD"})
	// Stack: [x_bytes, y_prefix, parity]
	emit(StackOp{Op: "swap"})
	emit(StackOp{Op: "drop"}) // drop y_prefix
	// Stack: [x_bytes, parity]
	emit(StackOp{Op: "if",
		Then: []StackOp{{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x03}}}},
		Else: []StackOp{{Op: "push", Value: PushValue{Kind: "bytes", Bytes: []byte{0x02}}}},
	})
	// Stack: [x_bytes, prefix_byte]
	emit(StackOp{Op: "swap"})
	emit(StackOp{Op: "opcode", Code: "OP_CAT"})
}

// EmitVerifyECDSA_P384 verifies an ECDSA signature on P-384.
func EmitVerifyECDSA_P384(emit func(StackOp)) {
	cEmitVerifyECDSA(emit, p384CurveParams, p384GroupParams, p384B, p384SqrtExp, p384GX, p384GY)
}
