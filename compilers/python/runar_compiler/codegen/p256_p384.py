"""P-256 / P-384 codegen — NIST elliptic curve operations for Bitcoin Script.

Follows the same pattern as ec.py (secp256k1). Uses ECTracker for named
stack state tracking, but with different field primes, curve orders,
and generator points.

Point representation:
  P-256: 64 bytes (x[32] || y[32], big-endian unsigned)
  P-384: 96 bytes (x[48] || y[48], big-endian unsigned)

Key difference from secp256k1: curve parameter a = -3 (not 0), which gives
an optimised Jacobian doubling formula.

Direct port of ``compilers/go/codegen/p256_p384.go``.
"""

from __future__ import annotations

from typing import Callable, TYPE_CHECKING

if TYPE_CHECKING:
    from runar_compiler.codegen.stack import StackOp, PushValue

# Re-use ECTracker and the lazy-import helpers from ec.py
from runar_compiler.codegen.ec import (
    ECTracker,
    _make_stack_op,
    _make_push_value,
    _big_int_push,
)

# ===========================================================================
# P-256 constants (secp256r1 / NIST P-256)
# ===========================================================================

P256_P    = int("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16)
P256_B    = int("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16)
P256_N    = int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16)
P256_GX   = int("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16)
P256_GY   = int("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16)
# sqrt exp = (p + 1) / 4
P256_SQRT_EXP = (P256_P + 1) >> 2
P256_P_MINUS_2 = P256_P - 2
P256_N_MINUS_2 = P256_N - 2

# ===========================================================================
# P-384 constants (secp384r1 / NIST P-384)
# ===========================================================================

P384_P    = int("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff", 16)
P384_B    = int("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef", 16)
P384_N    = int("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973", 16)
P384_GX   = int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7", 16)
P384_GY   = int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", 16)
P384_SQRT_EXP = (P384_P + 1) >> 2
P384_P_MINUS_2 = P384_P - 2
P384_N_MINUS_2 = P384_N - 2


# ===========================================================================
# Utility helpers
# ===========================================================================

def _bigint_to_n_bytes(n: int, size: int) -> bytes:
    """Convert an int to a *size*-byte big-endian byte string."""
    return n.to_bytes(size, byteorder="big")


def _bigint_bit_len(n: int) -> int:
    return n.bit_length()


# ===========================================================================
# Byte reversal for 48 bytes (P-384)
# ===========================================================================

def _emit_reverse48(e: Callable) -> None:
    """Emit inline byte reversal for a 48-byte value on TOS."""
    e(_make_stack_op(op="opcode", code="OP_0"))
    e(_make_stack_op(op="swap"))
    for _ in range(48):
        e(_make_stack_op(op="push", value=_big_int_push(1)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))
        e(_make_stack_op(op="rot"))
        e(_make_stack_op(op="rot"))
        e(_make_stack_op(op="swap"))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="swap"))
    e(_make_stack_op(op="drop"))


# Re-use 32-byte reversal from ec.py
def _emit_reverse32(e: Callable) -> None:
    from runar_compiler.codegen.ec import _ec_emit_reverse32
    _ec_emit_reverse32(e)


# ===========================================================================
# Generic field arithmetic parameterised by prime
# ===========================================================================

def _c_push_field_p(t: ECTracker, name: str, field_p: int) -> None:
    t.push_big_int(name, field_p)


def _c_field_mod(t: ECTracker, a_name: str, result_name: str, field_p: int) -> None:
    t.to_top(a_name)
    _c_push_field_p(t, "_fmod_p", field_p)

    def _fn(e: Callable) -> None:
        e(_make_stack_op(op="opcode", code="OP_2DUP"))
        e(_make_stack_op(op="opcode", code="OP_MOD"))
        e(_make_stack_op(op="rot"))
        e(_make_stack_op(op="drop"))
        e(_make_stack_op(op="over"))
        e(_make_stack_op(op="opcode", code="OP_ADD"))
        e(_make_stack_op(op="swap"))
        e(_make_stack_op(op="opcode", code="OP_MOD"))

    t.raw_block([a_name, "_fmod_p"], result_name, _fn)


def _c_field_add(t: ECTracker, a_name: str, b_name: str, result_name: str, field_p: int) -> None:
    t.to_top(a_name)
    t.to_top(b_name)
    t.raw_block([a_name, b_name], "_fadd_sum", lambda e: e(_make_stack_op(op="opcode", code="OP_ADD")))
    _c_field_mod(t, "_fadd_sum", result_name, field_p)


def _c_field_sub(t: ECTracker, a_name: str, b_name: str, result_name: str, field_p: int) -> None:
    t.to_top(a_name)
    t.to_top(b_name)
    t.raw_block([a_name, b_name], "_fsub_diff", lambda e: e(_make_stack_op(op="opcode", code="OP_SUB")))
    _c_field_mod(t, "_fsub_diff", result_name, field_p)


def _c_field_mul(t: ECTracker, a_name: str, b_name: str, result_name: str, field_p: int) -> None:
    t.to_top(a_name)
    t.to_top(b_name)
    t.raw_block([a_name, b_name], "_fmul_prod", lambda e: e(_make_stack_op(op="opcode", code="OP_MUL")))
    _c_field_mod(t, "_fmul_prod", result_name, field_p)


def _c_field_mul_const(t: ECTracker, a_name: str, cv: int, result_name: str, field_p: int) -> None:
    t.to_top(a_name)

    def _fmc_body(e: Callable) -> None:
        if cv == 2:
            e(_make_stack_op(op="opcode", code="OP_2MUL"))
        else:
            e(_make_stack_op(op="push", value=_big_int_push(cv)))
            e(_make_stack_op(op="opcode", code="OP_MUL"))

    t.raw_block([a_name], "_fmc_prod", _fmc_body)
    _c_field_mod(t, "_fmc_prod", result_name, field_p)


def _c_field_sqr(t: ECTracker, a_name: str, result_name: str, field_p: int) -> None:
    t.copy_to_top(a_name, "_fsqr_copy")
    _c_field_mul(t, a_name, "_fsqr_copy", result_name, field_p)


def _c_field_inv(t: ECTracker, a_name: str, result_name: str, field_p: int, p_minus_2: int) -> None:
    """Compute a^(p-2) mod p via generic square-and-multiply."""
    exp = p_minus_2
    bits = _bigint_bit_len(exp)

    t.copy_to_top(a_name, "_inv_r")

    for i in range(bits - 2, -1, -1):
        _c_field_sqr(t, "_inv_r", "_inv_r2", field_p)
        t.rename("_inv_r")
        if (exp >> i) & 1 == 1:
            t.copy_to_top(a_name, "_inv_a")
            _c_field_mul(t, "_inv_r", "_inv_a", "_inv_m", field_p)
            t.rename("_inv_r")

    t.to_top(a_name)
    t.drop()
    t.to_top("_inv_r")
    t.rename(result_name)


# ===========================================================================
# Group-order arithmetic (for ECDSA: mod n operations)
# ===========================================================================

def _c_push_group_n(t: ECTracker, name: str, curve_n: int) -> None:
    t.push_big_int(name, curve_n)


def _c_group_mod(t: ECTracker, a_name: str, result_name: str, curve_n: int) -> None:
    t.to_top(a_name)
    _c_push_group_n(t, "_gmod_n", curve_n)

    def _fn(e: Callable) -> None:
        e(_make_stack_op(op="opcode", code="OP_2DUP"))
        e(_make_stack_op(op="opcode", code="OP_MOD"))
        e(_make_stack_op(op="rot"))
        e(_make_stack_op(op="drop"))
        e(_make_stack_op(op="over"))
        e(_make_stack_op(op="opcode", code="OP_ADD"))
        e(_make_stack_op(op="swap"))
        e(_make_stack_op(op="opcode", code="OP_MOD"))

    t.raw_block([a_name, "_gmod_n"], result_name, _fn)


def _c_group_mul(t: ECTracker, a_name: str, b_name: str, result_name: str, curve_n: int) -> None:
    t.to_top(a_name)
    t.to_top(b_name)
    t.raw_block([a_name, b_name], "_gmul_prod", lambda e: e(_make_stack_op(op="opcode", code="OP_MUL")))
    _c_group_mod(t, "_gmul_prod", result_name, curve_n)


def _c_group_inv(t: ECTracker, a_name: str, result_name: str, curve_n: int, n_minus_2: int) -> None:
    """Compute a^(n-2) mod n via square-and-multiply."""
    exp = n_minus_2
    bits = _bigint_bit_len(exp)

    t.copy_to_top(a_name, "_ginv_r")

    for i in range(bits - 2, -1, -1):
        t.copy_to_top("_ginv_r", "_ginv_sq_copy")
        _c_group_mul(t, "_ginv_r", "_ginv_sq_copy", "_ginv_sq", curve_n)
        t.rename("_ginv_r")
        if (exp >> i) & 1 == 1:
            t.copy_to_top(a_name, "_ginv_a")
            _c_group_mul(t, "_ginv_r", "_ginv_a", "_ginv_m", curve_n)
            t.rename("_ginv_r")

    t.to_top(a_name)
    t.drop()
    t.to_top("_ginv_r")
    t.rename(result_name)


# ===========================================================================
# Point decompose / compose (parameterised by coordinate byte size)
# ===========================================================================

def _c_decompose_point(
    t: ECTracker,
    point_name: str,
    x_name: str,
    y_name: str,
    coord_bytes: int,
    reverse_bytes_fn: Callable,
) -> None:
    t.to_top(point_name)

    def _split(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(coord_bytes)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))

    t.raw_block([point_name], "", _split)
    t.nm.append("_dp_xb")
    t.nm.append("_dp_yb")

    def _convert_y(e: Callable) -> None:
        reverse_bytes_fn(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_dp_yb"], y_name, _convert_y)

    t.to_top("_dp_xb")

    def _convert_x(e: Callable) -> None:
        reverse_bytes_fn(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_dp_xb"], x_name, _convert_x)

    # Swap to standard order [x_name, y_name]
    t.swap()


def _c_compose_point(
    t: ECTracker,
    x_name: str,
    y_name: str,
    result_name: str,
    coord_bytes: int,
    reverse_bytes_fn: Callable,
) -> None:
    num_bin_size = coord_bytes + 1

    t.to_top(x_name)

    def _convert_x(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(num_bin_size)))
        e(_make_stack_op(op="opcode", code="OP_NUM2BIN"))
        e(_make_stack_op(op="push", value=_big_int_push(coord_bytes)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))
        e(_make_stack_op(op="drop"))
        reverse_bytes_fn(e)

    t.raw_block([x_name], "_cp_xb", _convert_x)

    t.to_top(y_name)

    def _convert_y(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(num_bin_size)))
        e(_make_stack_op(op="opcode", code="OP_NUM2BIN"))
        e(_make_stack_op(op="push", value=_big_int_push(coord_bytes)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))
        e(_make_stack_op(op="drop"))
        reverse_bytes_fn(e)

    t.raw_block([y_name], "_cp_yb", _convert_y)

    t.to_top("_cp_xb")
    t.to_top("_cp_yb")
    t.raw_block(["_cp_xb", "_cp_yb"], result_name, lambda e: e(_make_stack_op(op="opcode", code="OP_CAT")))


# ===========================================================================
# Affine point addition (parameterised by curve)
# ===========================================================================

def _c_affine_add(t: ECTracker, field_p: int, p_minus_2: int) -> None:
    """Perform affine point addition.

    Expects px, py, qx, qy on tracker. Produces rx, ry. Consumes all four inputs.
    """
    # The chord slope (qy-py)/(qx-px) divides by zero when P == Q, so doubling
    # needs the tangent (3*px^2 + a)/(2*py) — and a = -3 on both NIST curves,
    # giving (3*px^2 - 3)/(2*py). Pick numerator and denominator BEFORE the one
    # _c_field_inv, selected as b + cond*(a - b) with cond = (px == qx), which
    # needs no branch and so keeps the emitted op sequence — and the tracker's
    # static stack model — identical on both paths. Mirrors the secp256k1 fix
    # in ec.py.
    #
    # NOT handled: P == -Q, whose true result is the point at infinity, which
    # affine coordinates cannot represent.
    t.copy_to_top("px", "_px_eq")
    t.copy_to_top("qx", "_qx_eq")
    t.raw_block(["_px_eq", "_qx_eq"], "_cond",
                lambda e: e(_make_stack_op(op="opcode", code="OP_NUMEQUAL")))

    # chord numerator / denominator
    t.copy_to_top("qy", "_qy1")
    t.copy_to_top("py", "_py1")
    _c_field_sub(t, "_qy1", "_py1", "_num_chord", field_p)
    t.copy_to_top("qx", "_qx1")
    t.copy_to_top("px", "_px1")
    _c_field_sub(t, "_qx1", "_px1", "_den_chord", field_p)

    # tangent numerator / denominator: 3*px^2 - 3 and 2*py
    t.copy_to_top("px", "_px_t")
    _c_field_sqr(t, "_px_t", "_px_sq", field_p)
    _c_field_mul_const(t, "_px_sq", 3, "_3x2", field_p)
    t.push_int("_three", 3)
    _c_field_sub(t, "_3x2", "_three", "_num_tan", field_p)
    t.copy_to_top("py", "_py_t")
    _c_field_mul_const(t, "_py_t", 2, "_den_tan", field_p)

    # num = num_chord + cond*(num_tan - num_chord)
    t.copy_to_top("_num_chord", "_num_chord_c")
    _c_field_sub(t, "_num_tan", "_num_chord_c", "_num_diff", field_p)
    t.copy_to_top("_cond", "_cond_n")
    _c_field_mul(t, "_num_diff", "_cond_n", "_num_sel", field_p)
    _c_field_add(t, "_num_chord", "_num_sel", "_s_num", field_p)

    # den = den_chord + cond*(den_tan - den_chord)
    t.copy_to_top("_den_chord", "_den_chord_c")
    _c_field_sub(t, "_den_tan", "_den_chord_c", "_den_diff", field_p)
    t.to_top("_cond")
    t.rename("_cond_d")
    _c_field_mul(t, "_den_diff", "_cond_d", "_den_sel", field_p)
    _c_field_add(t, "_den_chord", "_den_sel", "_s_den", field_p)

    _c_field_inv(t, "_s_den", "_s_den_inv", field_p, p_minus_2)
    _c_field_mul(t, "_s_num", "_s_den_inv", "_s", field_p)

    t.copy_to_top("_s", "_s_keep")
    _c_field_sqr(t, "_s", "_s2", field_p)
    t.copy_to_top("px", "_px2")
    _c_field_sub(t, "_s2", "_px2", "_rx1", field_p)
    t.copy_to_top("qx", "_qx2")
    _c_field_sub(t, "_rx1", "_qx2", "rx", field_p)

    t.copy_to_top("px", "_px3")
    t.copy_to_top("rx", "_rx2")
    _c_field_sub(t, "_px3", "_rx2", "_px_rx", field_p)
    _c_field_mul(t, "_s_keep", "_px_rx", "_s_px_rx", field_p)
    t.copy_to_top("py", "_py2")
    _c_field_sub(t, "_s_px_rx", "_py2", "ry", field_p)

    t.to_top("px")
    t.drop()
    t.to_top("py")
    t.drop()
    t.to_top("qx")
    t.drop()
    t.to_top("qy")
    t.drop()


# ===========================================================================
# Jacobian point doubling with a=-3 optimisation (P-256, P-384)
# ===========================================================================

def _c_projective_double(t: ECTracker, field_p: int, curve_b: int) -> None:
    """Projective point doubling — RCB Algorithm 6 (a = -3), 8M + 3S + 2 m_b.

    Expects jx, jy, jz on the tracker; replaces them with the doubled point.
    Complete: doubling the point at infinity (0 : 1 : 0) yields (0 : 1 : 0).

    P-256 and P-384 have a = -3, so these are the a = -3 algorithms (5 and 6),
    NOT the a = 0 pair used for secp256k1 in ec.py.
    """
    t.copy_to_top("jx", "_d_x_xy")
    t.copy_to_top("jx", "_d_x_xz")
    t.copy_to_top("jy", "_d_y_xy")
    t.copy_to_top("jy", "_d_y_yz")
    t.copy_to_top("jz", "_d_z_xz")
    t.copy_to_top("jz", "_d_z_yz")

    _c_field_sqr(t, "jx", "_d_t0", field_p)   # t0 = X^2
    _c_field_sqr(t, "jy", "_d_t1", field_p)   # t1 = Y^2
    _c_field_sqr(t, "jz", "_d_t2", field_p)   # t2 = Z^2

    _c_field_mul(t, "_d_x_xy", "_d_y_xy", "_d_xy", field_p)
    _c_field_mul_const(t, "_d_xy", 2, "_d_t3", field_p)      # t3 = 2*X*Y
    _c_field_mul(t, "_d_x_xz", "_d_z_xz", "_d_xz", field_p)
    _c_field_mul_const(t, "_d_xz", 2, "_d_Z3", field_p)      # Z3 = 2*X*Z

    t.copy_to_top("_d_t2", "_d_t2_b")
    _c_field_mul_const(t, "_d_t2_b", curve_b, "_d_bt2", field_p)
    t.copy_to_top("_d_Z3", "_d_Z3_a")
    _c_field_sub(t, "_d_bt2", "_d_Z3_a", "_d_Y3", field_p)
    _c_field_mul_const(t, "_d_Y3", 3, "_d_Y3b", field_p)

    t.copy_to_top("_d_t1", "_d_t1_a")
    t.copy_to_top("_d_t1", "_d_t1_b")
    t.copy_to_top("_d_Y3b", "_d_Y3b_a")
    _c_field_sub(t, "_d_t1_a", "_d_Y3b_a", "_d_X3", field_p)
    _c_field_add(t, "_d_t1", "_d_Y3b", "_d_Y3c", field_p)

    t.copy_to_top("_d_X3", "_d_X3_a")
    _c_field_mul(t, "_d_X3_a", "_d_Y3c", "_d_Y3d", field_p)
    _c_field_mul(t, "_d_X3", "_d_t3", "_d_X3b", field_p)

    _c_field_mul_const(t, "_d_t2", 3, "_d_t2c", field_p)

    _c_field_mul_const(t, "_d_Z3", curve_b, "_d_Z3b", field_p)
    t.copy_to_top("_d_t2c", "_d_t2c_a")
    _c_field_sub(t, "_d_Z3b", "_d_t2c_a", "_d_Z3c", field_p)
    t.copy_to_top("_d_t0", "_d_t0_a")
    _c_field_sub(t, "_d_Z3c", "_d_t0_a", "_d_Z3d", field_p)
    _c_field_mul_const(t, "_d_Z3d", 3, "_d_Z3e", field_p)

    _c_field_mul_const(t, "_d_t0", 3, "_d_t0b", field_p)
    _c_field_sub(t, "_d_t0b", "_d_t2c", "_d_t0c", field_p)

    t.copy_to_top("_d_Z3e", "_d_Z3e_a")
    _c_field_mul(t, "_d_t0c", "_d_Z3e_a", "_d_t0d", field_p)
    _c_field_add(t, "_d_Y3d", "_d_t0d", "_d_Y3e", field_p)

    _c_field_mul(t, "_d_y_yz", "_d_z_yz", "_d_yz", field_p)
    _c_field_mul_const(t, "_d_yz", 2, "_d_t0e", field_p)

    t.copy_to_top("_d_t0e", "_d_t0e_a")
    _c_field_mul(t, "_d_t0e_a", "_d_Z3e", "_d_Z3f", field_p)
    _c_field_sub(t, "_d_X3b", "_d_Z3f", "_d_X3c", field_p)

    _c_field_mul(t, "_d_t0e", "_d_t1_b", "_d_Z3g", field_p)
    _c_field_mul_const(t, "_d_Z3g", 4, "_d_Z3h", field_p)

    t.to_top("_d_X3c")
    t.rename("jx")
    t.to_top("_d_Y3e")
    t.rename("jy")
    t.to_top("_d_Z3h")
    t.rename("jz")


def _c_projective_to_affine(
    t: ECTracker, rx_name: str, ry_name: str, field_p: int, p_minus_2: int
) -> None:
    """Consume jx, jy, jz; produce rx_name, ry_name.

    _c_field_inv is Fermat exponentiation, so inv(0) = 0: the point at infinity
    (Z = 0) converts to (0, 0), the all-zero point blob.
    """
    _c_field_inv(t, "jz", "_zinv", field_p, p_minus_2)
    t.copy_to_top("_zinv", "_zinv_b")
    _c_field_mul(t, "jx", "_zinv", rx_name, field_p)
    _c_field_mul(t, "jy", "_zinv_b", ry_name, field_p)


def _c_build_projective_add_mixed_inline(
    e: Callable, t: ECTracker, field_p: int, curve_b: int
) -> None:
    """Complete mixed-add ops for use inside OP_IF — RCB Algorithm 5 (a = -3).

    Complete: accumulator == Q doubles correctly (the case that returned the
    zero point for k = 2), accumulator == -Q yields infinity, and an infinity
    accumulator yields Q.
    """
    it = ECTracker(list(t.nm), e)

    it.copy_to_top("ax", "_m_x2a")
    it.copy_to_top("ax", "_m_x2b")
    it.copy_to_top("ax", "_m_x2c")
    it.copy_to_top("ay", "_m_y2a")
    it.copy_to_top("ay", "_m_y2b")
    it.copy_to_top("ay", "_m_y2c")
    it.copy_to_top("jx", "_m_x1a")
    it.copy_to_top("jx", "_m_x1b")
    it.copy_to_top("jy", "_m_y1a")
    it.copy_to_top("jy", "_m_y1b")
    it.copy_to_top("jz", "_m_z1a")
    it.copy_to_top("jz", "_m_z1b")
    it.copy_to_top("jz", "_m_z1c")

    _c_field_mul(it, "jx", "_m_x2a", "_m_t0", field_p)
    _c_field_mul(it, "jy", "_m_y2a", "_m_t1", field_p)
    _c_field_add(it, "_m_x2b", "_m_y2b", "_m_s1", field_p)
    _c_field_add(it, "_m_x1a", "_m_y1a", "_m_s2", field_p)
    _c_field_mul(it, "_m_s1", "_m_s2", "_m_t3", field_p)

    it.copy_to_top("_m_t0", "_m_t0a")
    it.copy_to_top("_m_t1", "_m_t1a")
    _c_field_add(it, "_m_t0a", "_m_t1a", "_m_s3", field_p)
    _c_field_sub(it, "_m_t3", "_m_s3", "_m_t3b", field_p)

    _c_field_mul(it, "_m_y2c", "jz", "_m_t4", field_p)
    _c_field_add(it, "_m_t4", "_m_y1b", "_m_t4b", field_p)
    _c_field_mul(it, "_m_x2c", "_m_z1a", "_m_Y3", field_p)
    _c_field_add(it, "_m_Y3", "_m_x1b", "_m_Y3b", field_p)

    _c_field_mul_const(it, "_m_z1b", curve_b, "_m_Z3", field_p)
    it.copy_to_top("_m_Y3b", "_m_Y3b_a")
    _c_field_sub(it, "_m_Y3b_a", "_m_Z3", "_m_X3", field_p)
    _c_field_mul_const(it, "_m_X3", 3, "_m_X3b", field_p)

    it.copy_to_top("_m_t1", "_m_t1b")
    it.copy_to_top("_m_X3b", "_m_X3b_a")
    _c_field_sub(it, "_m_t1b", "_m_X3b_a", "_m_Z3b", field_p)
    _c_field_add(it, "_m_t1", "_m_X3b", "_m_X3c", field_p)

    _c_field_mul_const(it, "_m_Y3b", curve_b, "_m_Y3c", field_p)
    _c_field_mul_const(it, "_m_z1c", 3, "_m_t2", field_p)

    it.copy_to_top("_m_t2", "_m_t2a")
    _c_field_sub(it, "_m_Y3c", "_m_t2a", "_m_Y3d", field_p)
    it.copy_to_top("_m_t0", "_m_t0b")
    _c_field_sub(it, "_m_Y3d", "_m_t0b", "_m_Y3e", field_p)
    _c_field_mul_const(it, "_m_Y3e", 3, "_m_Y3f", field_p)

    _c_field_mul_const(it, "_m_t0", 3, "_m_t0c", field_p)
    _c_field_sub(it, "_m_t0c", "_m_t2", "_m_t0d", field_p)

    it.copy_to_top("_m_t4b", "_m_t4b_a")
    it.copy_to_top("_m_Y3f", "_m_Y3f_a")
    _c_field_mul(it, "_m_t4b_a", "_m_Y3f_a", "_m_t1c", field_p)
    it.copy_to_top("_m_t0d", "_m_t0d_a")
    _c_field_mul(it, "_m_t0d_a", "_m_Y3f", "_m_t2b", field_p)

    it.copy_to_top("_m_X3c", "_m_X3c_a")
    it.copy_to_top("_m_Z3b", "_m_Z3b_a")
    _c_field_mul(it, "_m_X3c_a", "_m_Z3b_a", "_m_Y3g", field_p)
    _c_field_add(it, "_m_Y3g", "_m_t2b", "_m_Y3h", field_p)

    it.copy_to_top("_m_t3b", "_m_t3b_a")
    _c_field_mul(it, "_m_t3b_a", "_m_X3c", "_m_X3d", field_p)
    _c_field_sub(it, "_m_X3d", "_m_t1c", "_m_X3e", field_p)

    _c_field_mul(it, "_m_t4b", "_m_Z3b", "_m_Z3c", field_p)
    _c_field_mul(it, "_m_t3b", "_m_t0d", "_m_t1d", field_p)
    _c_field_add(it, "_m_Z3c", "_m_t1d", "_m_Z3d", field_p)

    it.to_top("_m_X3e")
    it.rename("jx")
    it.to_top("_m_Y3h")
    it.rename("jy")
    it.to_top("_m_Z3d")
    it.rename("jz")


def _c_emit_mul(
    emit: Callable,
    coord_bytes: int,
    reverse_bytes_fn: Callable,
    field_p: int,
    p_minus_2: int,
    curve_n: int,
    n_minus_2: int,
    curve_b: int,
) -> None:
    """Generic scalar multiplication for NIST curves."""
    t = ECTracker(["_pt", "_k"], emit)
    _c_decompose_point(t, "_pt", "ax", "ay", coord_bytes, reverse_bytes_fn)

    # Reduce the scalar into [0, n-1] so the ladder covers the whole domain:
    # negative k and k >= n are now defined rather than undefined behaviour.
    _c_group_mod(t, "_k", "_k", curve_n)

    # Accumulator := point at infinity (0 : 1 : 0), a legal input to both
    # complete formulas — which is why no leading-bit special case is needed.
    t.push_int("jx", 0)
    t.push_int("jy", 1)
    t.push_int("jz", 0)

    # One iteration per bit of n: 256 for P-256, 384 for P-384.
    start_bit = curve_n.bit_length() - 1

    for bit in range(start_bit, -1, -1):
        _c_projective_double(t, field_p, curve_b)

        t.copy_to_top("_k", "_k_copy")
        if bit == 1:
            t.raw_block(["_k_copy"], "_shifted", lambda e: e(_make_stack_op(op="opcode", code="OP_2DIV")))
        elif bit > 1:
            t.push_int("_shift", bit)
            t.raw_block(["_k_copy", "_shift"], "_shifted", lambda e: e(_make_stack_op(op="opcode", code="OP_RSHIFTNUM")))
        else:
            t.rename("_shifted")
        t.push_int("_two", 2)
        t.raw_block(["_shifted", "_two"], "_bit", lambda e: e(_make_stack_op(op="opcode", code="OP_MOD")))

        t.to_top("_bit")
        t.nm.pop()  # _bit consumed by IF

        add_ops: list = []

        def _add_emit(op: object) -> None:
            add_ops.append(op)

        _c_build_projective_add_mixed_inline(_add_emit, t, field_p, curve_b)
        emit(_make_stack_op(op="if", then=add_ops, else_=[]))

    _c_projective_to_affine(t, "_rx", "_ry", field_p, p_minus_2)

    t.to_top("ax")
    t.drop()
    t.to_top("ay")
    t.drop()
    t.to_top("_k")
    t.drop()

    _c_compose_point(t, "_rx", "_ry", "_result", coord_bytes, reverse_bytes_fn)


# ===========================================================================
# Square-and-multiply modular exponentiation (for sqrt)
# ===========================================================================

def _c_field_pow(
    t: ECTracker, base_name: str, exp: int, result_name: str, field_p: int, p_minus_2: int
) -> None:
    bits = _bigint_bit_len(exp)
    t.copy_to_top(base_name, "_pow_r")

    for i in range(bits - 2, -1, -1):
        _c_field_sqr(t, "_pow_r", "_pow_sq", field_p)
        t.rename("_pow_r")
        if (exp >> i) & 1 == 1:
            t.copy_to_top(base_name, "_pow_b")
            _c_field_mul(t, "_pow_r", "_pow_b", "_pow_m", field_p)
            t.rename("_pow_r")

    t.to_top(base_name)
    t.drop()
    t.to_top("_pow_r")
    t.rename(result_name)


# ===========================================================================
# Pubkey decompression (prefix byte + x → (x, y))
# ===========================================================================

def _c_decompress_pub_key(
    t: ECTracker,
    pk_name: str,
    qx_name: str,
    qy_name: str,
    coord_bytes: int,
    reverse_bytes_fn: Callable,
    field_p: int,
    p_minus_2: int,
    curve_b: int,
    sqrt_exp: int,
) -> None:
    t.to_top(pk_name)

    def _split_prefix(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(1)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))

    t.raw_block([pk_name], "", _split_prefix)
    t.nm.append("_dk_prefix")
    t.nm.append("_dk_xbytes")

    t.to_top("_dk_prefix")

    def _prefix_to_parity(e: Callable) -> None:
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))
        e(_make_stack_op(op="push", value=_big_int_push(2)))
        e(_make_stack_op(op="opcode", code="OP_MOD"))

    t.raw_block(["_dk_prefix"], "_dk_parity", _prefix_to_parity)

    t.to_top("_dk_parity")
    t.to_alt()

    t.to_top("_dk_xbytes")

    def _xbytes_to_num(e: Callable) -> None:
        reverse_bytes_fn(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_dk_xbytes"], "_dk_x", _xbytes_to_num)

    t.copy_to_top("_dk_x", "_dk_x_save")

    # Compute y^2 = x^3 - 3x + b mod p
    t.copy_to_top("_dk_x", "_dk_x_c1")
    _c_field_sqr(t, "_dk_x", "_dk_x2", field_p)
    _c_field_mul(t, "_dk_x2", "_dk_x_c1", "_dk_x3", field_p)
    t.copy_to_top("_dk_x_save", "_dk_x_for_3")
    _c_field_mul_const(t, "_dk_x_for_3", 3, "_dk_3x", field_p)
    _c_field_sub(t, "_dk_x3", "_dk_3x", "_dk_x3m3x", field_p)
    t.push_big_int("_dk_b", curve_b)
    _c_field_add(t, "_dk_x3m3x", "_dk_b", "_dk_y2", field_p)

    # y = (y^2)^sqrtExp mod p
    _c_field_pow(t, "_dk_y2", sqrt_exp, "_dk_y_cand", field_p, p_minus_2)

    # Check parity
    t.copy_to_top("_dk_y_cand", "_dk_y_check")

    def _check_parity(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(2)))
        e(_make_stack_op(op="opcode", code="OP_MOD"))

    t.raw_block(["_dk_y_check"], "_dk_y_par", _check_parity)

    t.from_alt("_dk_parity")

    t.to_top("_dk_y_par")
    t.to_top("_dk_parity")
    t.raw_block(["_dk_y_par", "_dk_parity"], "_dk_match", lambda e: e(_make_stack_op(op="opcode", code="OP_EQUAL")))

    # Compute p - y_cand
    t.copy_to_top("_dk_y_cand", "_dk_y_for_neg")
    _c_push_field_p(t, "_dk_pfn", field_p)
    t.to_top("_dk_y_for_neg")
    t.raw_block(["_dk_pfn", "_dk_y_for_neg"], "_dk_neg_y", lambda e: e(_make_stack_op(op="opcode", code="OP_SUB")))

    t.to_top("_dk_match")
    t.nm.pop()  # condition consumed by IF

    then_ops = [_make_stack_op(op="drop")]   # remove neg_y, keep y_cand
    else_ops = [_make_stack_op(op="nip")]    # remove y_cand, keep neg_y
    t.e(_make_stack_op(op="if", then=then_ops, else_=else_ops))

    # Remove neg_y from tracker
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_dk_neg_y":
            del t.nm[i]
            break

    # Rename y_cand to qy_name
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_dk_y_cand":
            t.nm[i] = qy_name
            break

    # Rename x_save to qx_name
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_dk_x_save":
            t.nm[i] = qx_name
            break


# ===========================================================================
# ECDSA verification (generic)
# ===========================================================================

def _c_emit_verify_ecdsa(
    emit: Callable,
    coord_bytes: int,
    reverse_bytes_fn: Callable,
    field_p: int,
    p_minus_2: int,
    curve_n: int,
    n_minus_2: int,
    curve_b: int,
    sqrt_exp: int,
    gx: int,
    gy: int,
) -> None:
    t = ECTracker(["_msg", "_sig", "_pk"], emit)

    # Step 1: e = SHA-256(msg) as integer
    t.to_top("_msg")

    def _hash_msg(e: Callable) -> None:
        e(_make_stack_op(op="opcode", code="OP_SHA256"))
        _emit_reverse32(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_msg"], "_e", _hash_msg)

    # Step 2: Parse sig into (r, s)
    t.to_top("_sig")

    def _split_sig(e: Callable) -> None:
        e(_make_stack_op(op="push", value=_big_int_push(coord_bytes)))
        e(_make_stack_op(op="opcode", code="OP_SPLIT"))

    t.raw_block(["_sig"], "", _split_sig)
    t.nm.append("_r_bytes")
    t.nm.append("_s_bytes")

    t.to_top("_r_bytes")

    def _r_to_num(e: Callable) -> None:
        reverse_bytes_fn(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_r_bytes"], "_r", _r_to_num)

    t.to_top("_s_bytes")

    def _s_to_num(e: Callable) -> None:
        reverse_bytes_fn(e)
        e(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x00")))
        e(_make_stack_op(op="opcode", code="OP_CAT"))
        e(_make_stack_op(op="opcode", code="OP_BIN2NUM"))

    t.raw_block(["_s_bytes"], "_s", _s_to_num)

    # Step 3: Decompress pubkey
    _c_decompress_pub_key(
        t, "_pk", "_qx", "_qy",
        coord_bytes, reverse_bytes_fn,
        field_p, p_minus_2, curve_b, sqrt_exp,
    )

    # Step 4: w = s^{-1} mod n
    _c_group_inv(t, "_s", "_w", curve_n, n_minus_2)

    # Step 5: u1 = e * w mod n
    t.copy_to_top("_w", "_w_c1")
    _c_group_mul(t, "_e", "_w_c1", "_u1", curve_n)

    # Step 6: u2 = r * w mod n
    t.copy_to_top("_r", "_r_save")
    _c_group_mul(t, "_r", "_w", "_u2", curve_n)

    # Step 7: R = u1*G + u2*Q
    point_bytes = coord_bytes * 2
    g_point_data = _bigint_to_n_bytes(gx, coord_bytes) + _bigint_to_n_bytes(gy, coord_bytes)
    t.push_bytes("_G", g_point_data)
    t.to_top("_u1")

    # Stash items on altstack
    t.to_top("_r_save")
    t.to_alt()
    t.to_top("_u2")
    t.to_alt()
    t.to_top("_qy")
    t.to_alt()
    t.to_top("_qx")
    t.to_alt()

    # Remove _G and _u1 from tracker before cEmitMul
    t.nm.pop()  # _u1
    t.nm.pop()  # _G

    _c_emit_mul(emit, coord_bytes, reverse_bytes_fn, field_p, p_minus_2, curve_n, n_minus_2, curve_b)

    t.nm.append("_R1_point")

    t.from_alt("_qx")
    t.from_alt("_qy")
    t.from_alt("_u2")

    t.to_top("_R1_point")
    t.to_alt()

    _c_compose_point(t, "_qx", "_qy", "_Q_point", coord_bytes, reverse_bytes_fn)

    t.to_top("_u2")

    t.nm.pop()  # _u2
    t.nm.pop()  # _Q_point

    _c_emit_mul(emit, coord_bytes, reverse_bytes_fn, field_p, p_minus_2, curve_n, n_minus_2, curve_b)
    t.nm.append("_R2_point")

    t.from_alt("_R1_point")

    t.swap()

    _c_decompose_point(t, "_R1_point", "_rpx", "_rpy", coord_bytes, reverse_bytes_fn)
    _c_decompose_point(t, "_R2_point", "_rqx", "_rqy", coord_bytes, reverse_bytes_fn)

    # Rename to what _c_affine_add expects
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_rpx":
            t.nm[i] = "px"
            break
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_rpy":
            t.nm[i] = "py"
            break
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_rqx":
            t.nm[i] = "qx"
            break
    for i in range(len(t.nm) - 1, -1, -1):
        if t.nm[i] == "_rqy":
            t.nm[i] = "qy"
            break

    _c_affine_add(t, field_p, p_minus_2)

    # Step 8: x_R mod n == r
    t.to_top("ry")
    t.drop()

    _c_group_mod(t, "rx", "_rx_mod_n", curve_n)

    t.from_alt("_r_save")

    t.to_top("_rx_mod_n")
    t.to_top("_r_save")
    t.raw_block(
        ["_rx_mod_n", "_r_save"],
        "_result",
        lambda e: e(_make_stack_op(op="opcode", code="OP_EQUAL")),
    )


# ===========================================================================
# P-256 public API
# ===========================================================================

def emit_p256_add(emit: Callable) -> None:
    """Add two P-256 points. Stack in: [pa, pb], out: [result]."""
    t = ECTracker(["_pa", "_pb"], emit)
    _c_decompose_point(t, "_pa", "px", "py", 32, _emit_reverse32)
    _c_decompose_point(t, "_pb", "qx", "qy", 32, _emit_reverse32)
    _c_affine_add(t, P256_P, P256_P_MINUS_2)
    _c_compose_point(t, "rx", "ry", "_result", 32, _emit_reverse32)


def emit_p256_mul(emit: Callable) -> None:
    """P-256 scalar multiplication. Stack in: [point, scalar], out: [result]."""
    _c_emit_mul(emit, 32, _emit_reverse32, P256_P, P256_P_MINUS_2, P256_N, P256_N_MINUS_2, P256_B)


def emit_p256_mul_gen(emit: Callable) -> None:
    """P-256 generator multiplication. Stack in: [scalar], out: [result]."""
    g_point = _bigint_to_n_bytes(P256_GX, 32) + _bigint_to_n_bytes(P256_GY, 32)
    emit(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=g_point)))
    emit(_make_stack_op(op="swap"))  # [point, scalar]
    emit_p256_mul(emit)


def emit_p256_negate(emit: Callable) -> None:
    """Negate a P-256 point. Stack in: [point], out: [negated_point]."""
    t = ECTracker(["_pt"], emit)
    _c_decompose_point(t, "_pt", "_nx", "_ny", 32, _emit_reverse32)
    _c_push_field_p(t, "_fp", P256_P)
    _c_field_sub(t, "_fp", "_ny", "_neg_y", P256_P)
    _c_compose_point(t, "_nx", "_neg_y", "_result", 32, _emit_reverse32)


def emit_p256_on_curve(emit: Callable) -> None:
    """Check if a P-256 point is on the curve (y^2 = x^3 - 3x + b mod p)."""
    t = ECTracker(["_pt"], emit)
    _c_decompose_point(t, "_pt", "_x", "_y", 32, _emit_reverse32)

    _c_field_sqr(t, "_y", "_y2", P256_P)

    t.copy_to_top("_x", "_x_copy")
    t.copy_to_top("_x", "_x_copy2")
    _c_field_sqr(t, "_x", "_x2", P256_P)
    _c_field_mul(t, "_x2", "_x_copy", "_x3", P256_P)
    _c_field_mul_const(t, "_x_copy2", 3, "_3x", P256_P)
    _c_field_sub(t, "_x3", "_3x", "_x3m3x", P256_P)
    t.push_big_int("_b", P256_B)
    _c_field_add(t, "_x3m3x", "_b", "_rhs", P256_P)

    t.to_top("_y2")
    t.to_top("_rhs")
    t.raw_block(["_y2", "_rhs"], "_result", lambda e: e(_make_stack_op(op="opcode", code="OP_EQUAL")))


def emit_p256_encode_compressed(emit: Callable) -> None:
    """Encode a P-256 point as 33-byte compressed pubkey."""
    emit(_make_stack_op(op="push", value=_big_int_push(32)))
    emit(_make_stack_op(op="opcode", code="OP_SPLIT"))
    emit(_make_stack_op(op="opcode", code="OP_SIZE"))
    emit(_make_stack_op(op="push", value=_big_int_push(1)))
    emit(_make_stack_op(op="opcode", code="OP_SUB"))
    emit(_make_stack_op(op="opcode", code="OP_SPLIT"))
    emit(_make_stack_op(op="opcode", code="OP_BIN2NUM"))
    emit(_make_stack_op(op="push", value=_big_int_push(2)))
    emit(_make_stack_op(op="opcode", code="OP_MOD"))
    emit(_make_stack_op(op="swap"))
    emit(_make_stack_op(op="drop"))
    emit(_make_stack_op(
        op="if",
        then=[_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x03"))],
        else_=[_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x02"))],
    ))
    emit(_make_stack_op(op="swap"))
    emit(_make_stack_op(op="opcode", code="OP_CAT"))


def emit_verify_ecdsa_p256(emit: Callable) -> None:
    """Verify an ECDSA signature on P-256.

    Stack in: [msg, sig (64 bytes r||s), pk (33 bytes compressed)]
    Stack out: [boolean]
    """
    _c_emit_verify_ecdsa(
        emit,
        coord_bytes=32,
        reverse_bytes_fn=_emit_reverse32,
        field_p=P256_P,
        p_minus_2=P256_P_MINUS_2,
        curve_n=P256_N,
        n_minus_2=P256_N_MINUS_2,
        curve_b=P256_B,
        sqrt_exp=P256_SQRT_EXP,
        gx=P256_GX,
        gy=P256_GY,
    )


# ===========================================================================
# P-384 public API
# ===========================================================================

def emit_p384_add(emit: Callable) -> None:
    """Add two P-384 points. Stack in: [pa, pb], out: [result]."""
    t = ECTracker(["_pa", "_pb"], emit)
    _c_decompose_point(t, "_pa", "px", "py", 48, _emit_reverse48)
    _c_decompose_point(t, "_pb", "qx", "qy", 48, _emit_reverse48)
    _c_affine_add(t, P384_P, P384_P_MINUS_2)
    _c_compose_point(t, "rx", "ry", "_result", 48, _emit_reverse48)


def emit_p384_mul(emit: Callable) -> None:
    """P-384 scalar multiplication. Stack in: [point, scalar], out: [result]."""
    _c_emit_mul(emit, 48, _emit_reverse48, P384_P, P384_P_MINUS_2, P384_N, P384_N_MINUS_2, P384_B)


def emit_p384_mul_gen(emit: Callable) -> None:
    """P-384 generator multiplication. Stack in: [scalar], out: [result]."""
    g_point = _bigint_to_n_bytes(P384_GX, 48) + _bigint_to_n_bytes(P384_GY, 48)
    emit(_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=g_point)))
    emit(_make_stack_op(op="swap"))  # [point, scalar]
    emit_p384_mul(emit)


def emit_p384_negate(emit: Callable) -> None:
    """Negate a P-384 point. Stack in: [point], out: [negated_point]."""
    t = ECTracker(["_pt"], emit)
    _c_decompose_point(t, "_pt", "_nx", "_ny", 48, _emit_reverse48)
    _c_push_field_p(t, "_fp", P384_P)
    _c_field_sub(t, "_fp", "_ny", "_neg_y", P384_P)
    _c_compose_point(t, "_nx", "_neg_y", "_result", 48, _emit_reverse48)


def emit_p384_on_curve(emit: Callable) -> None:
    """Check if a P-384 point is on the curve (y^2 = x^3 - 3x + b mod p)."""
    t = ECTracker(["_pt"], emit)
    _c_decompose_point(t, "_pt", "_x", "_y", 48, _emit_reverse48)

    _c_field_sqr(t, "_y", "_y2", P384_P)

    t.copy_to_top("_x", "_x_copy")
    t.copy_to_top("_x", "_x_copy2")
    _c_field_sqr(t, "_x", "_x2", P384_P)
    _c_field_mul(t, "_x2", "_x_copy", "_x3", P384_P)
    _c_field_mul_const(t, "_x_copy2", 3, "_3x", P384_P)
    _c_field_sub(t, "_x3", "_3x", "_x3m3x", P384_P)
    t.push_big_int("_b", P384_B)
    _c_field_add(t, "_x3m3x", "_b", "_rhs", P384_P)

    t.to_top("_y2")
    t.to_top("_rhs")
    t.raw_block(["_y2", "_rhs"], "_result", lambda e: e(_make_stack_op(op="opcode", code="OP_EQUAL")))


def emit_p384_encode_compressed(emit: Callable) -> None:
    """Encode a P-384 point as 49-byte compressed pubkey."""
    emit(_make_stack_op(op="push", value=_big_int_push(48)))
    emit(_make_stack_op(op="opcode", code="OP_SPLIT"))
    emit(_make_stack_op(op="opcode", code="OP_SIZE"))
    emit(_make_stack_op(op="push", value=_big_int_push(1)))
    emit(_make_stack_op(op="opcode", code="OP_SUB"))
    emit(_make_stack_op(op="opcode", code="OP_SPLIT"))
    emit(_make_stack_op(op="opcode", code="OP_BIN2NUM"))
    emit(_make_stack_op(op="push", value=_big_int_push(2)))
    emit(_make_stack_op(op="opcode", code="OP_MOD"))
    emit(_make_stack_op(op="swap"))
    emit(_make_stack_op(op="drop"))
    emit(_make_stack_op(
        op="if",
        then=[_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x03"))],
        else_=[_make_stack_op(op="push", value=_make_push_value(kind="bytes", bytes_=b"\x02"))],
    ))
    emit(_make_stack_op(op="swap"))
    emit(_make_stack_op(op="opcode", code="OP_CAT"))


def emit_verify_ecdsa_p384(emit: Callable) -> None:
    """Verify an ECDSA signature on P-384.

    Stack in: [msg, sig (96 bytes r||s), pk (49 bytes compressed)]
    Stack out: [boolean]
    """
    _c_emit_verify_ecdsa(
        emit,
        coord_bytes=48,
        reverse_bytes_fn=_emit_reverse48,
        field_p=P384_P,
        p_minus_2=P384_P_MINUS_2,
        curve_n=P384_N,
        n_minus_2=P384_N_MINUS_2,
        curve_b=P384_B,
        sqrt_exp=P384_SQRT_EXP,
        gx=P384_GX,
        gy=P384_GY,
    )
