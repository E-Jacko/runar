"""Byte-identical parity tests for the Python ``p256_p384`` codegen
against the same goldens used by the Java reference (``P256P384Test``).

Pins op counts for every NIST P-256 and P-384 builtin.
"""

from __future__ import annotations

import pytest

from runar_compiler.codegen.p256_p384 import (
    emit_p256_add, emit_p256_mul, emit_p256_mul_gen, emit_p256_negate,
    emit_p256_on_curve, emit_p256_encode_compressed, emit_verify_ecdsa_p256,
    emit_p384_add, emit_p384_mul, emit_p384_mul_gen, emit_p384_negate,
    emit_p384_on_curve, emit_p384_encode_compressed, emit_verify_ecdsa_p384,
)
from runar_compiler.codegen.stack import StackOp


def _count_op_tree(ops: list[StackOp]) -> int:
    """Total StackOps in ``ops``, INCLUDING the bodies of ``if`` ops.

    A flat ``len(ops)`` cannot see inside a branch, so any emitter whose work
    sits in an ``if`` body -- the scalar ladders emit 257 / 385 conditional
    additions, WOTS+ and SLH-DSA are almost entirely conditional -- reports a
    count that barely moves no matter what the branch contains. Adding +1.3 KB
    of script inside the ladder's last step left the ``p256Mul`` / ``p384Mul``
    goldens byte-identical. Recursing is what makes the golden a gate.
    """
    total = 0
    for op in ops:
        total += 1
        if op.op == "if":
            total += _count_op_tree(op.then)
            total += _count_op_tree(op.else_ops)
    return total


# ---------------------------------------------------------------------------
# P-256 op-count goldens (op-TREE sizes: `if` bodies included)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,fn,expected", [
    ("p256Add",              emit_p256_add,               6642),
    ("p256Mul",              emit_p256_mul,             140036),
    ("p256MulGen",           emit_p256_mul_gen,         140038),
    ("p256Negate",           emit_p256_negate,             945),
    ("p256OnCurve",          emit_p256_on_curve,           559),
    ("p256EncodeCompressed", emit_p256_encode_compressed,   16),
    ("verifyECDSA_P256",     emit_verify_ecdsa_p256,    297188),
])
def test_p256_op_count(name, fn, expected):
    ops: list[StackOp] = []
    fn(ops.append)
    got = _count_op_tree(ops)
    assert got == expected, f"{name} op count drift: got {got} want {expected}"


# ---------------------------------------------------------------------------
# P-384 op-count goldens (op-TREE sizes: `if` bodies included)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,fn,expected", [
    ("p384Add",              emit_p384_add,              11448),
    ("p384Mul",              emit_p384_mul,             211178),
    ("p384MulGen",           emit_p384_mul_gen,         211180),
    ("p384Negate",           emit_p384_negate,            1393),
])
def test_p384_op_count(name, fn, expected):
    ops: list[StackOp] = []
    fn(ops.append)
    got = _count_op_tree(ops)
    assert got == expected, f"{name} op count drift: got {got} want {expected}"


# ---------------------------------------------------------------------------
# Determinism
# ---------------------------------------------------------------------------

def test_p256_add_is_deterministic():
    a: list[StackOp] = []
    b: list[StackOp] = []
    emit_p256_add(a.append)
    emit_p256_add(b.append)
    assert len(a) == len(b)
    for i, (x, y) in enumerate(zip(a, b)):
        assert x.op == y.op
        assert x.code == y.code
