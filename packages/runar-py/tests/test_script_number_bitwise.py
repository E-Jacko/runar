"""Byte-array semantics for bigint shift/bitwise ops in the ANF interpreter.

`& | ^ ~ << >>` compile to OP_AND/OP_OR/OP_XOR/OP_INVERT/OP_LSHIFT/OP_RSHIFT,
which operate on the operands' MINIMAL script-number BYTES, not their numeric
value. The interpreter must reproduce the deployed script byte-for-byte, so it
routes these ops through the _script_number_* helpers rather than native int.

Mirrors the TS reference test
packages/runar-testing/src/__tests__/script-number-bitwise.test.ts.
"""

from __future__ import annotations

import pytest

from runar.sdk.anf_interpreter import _eval_bin_op, _eval_unary_op


class TestShiftTruthTable:
    @pytest.mark.parametrize(
        "op,a,b,expected",
        [
            ("<<", 255, 1, 254),   # NOT 510 — byte length preserved, MSB masked off
            ("<<", 256, 1, 512),
            ("<<", 5, 3, 40),
            (">>", 32, 3, 4),
            (">>", 255, 1, -127),  # NOT 127 — high bit of last byte reads as sign
        ],
    )
    def test_shift(self, op, a, b, expected):
        assert _eval_bin_op(op, a, b) == expected

    def test_negative_shift_aborts(self):
        with pytest.raises(ValueError):
            _eval_bin_op("<<", 5, -1)
        with pytest.raises(ValueError):
            _eval_bin_op(">>", 5, -1)


class TestInvertTruthTable:
    @pytest.mark.parametrize(
        "a,expected",
        [
            (5, -122),      # NOT -6
            (255, -32512),
            (0, 0),
        ],
    )
    def test_invert(self, a, expected):
        assert _eval_unary_op("~", a) == expected


class TestBitwiseTruthTable:
    def test_and(self):
        assert _eval_bin_op("&", 5, 3) == 1
        assert _eval_bin_op("&", -1, 5) == 1  # NOT 5

    def test_length_mismatch_aborts(self):
        # 255 encodes to 2 bytes (ff 00), 1 encodes to 1 byte (01) -> abort.
        with pytest.raises(ValueError):
            _eval_bin_op("&", 255, 1)
        # 7 encodes to 1 byte, 0 encodes to the empty byte string -> abort.
        with pytest.raises(ValueError):
            _eval_bin_op("|", 7, 0)
