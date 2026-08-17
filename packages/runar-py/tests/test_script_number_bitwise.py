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

from runar.sdk.anf_interpreter import (
    _eval_bin_op,
    _eval_bindings,
    _eval_unary_op,
)


def _run_chain(bindings):
    """Evaluate a list of ANF bindings through the interpreter's binding walker
    (which threads the per-binding raw-stack-bytes side map) and return the
    populated env. A shift/bitwise RESULT is a fixed-length, possibly
    non-minimal byte array on-chain; feeding it to a length-sensitive
    ``& | ^``/shift/``~`` must see that real length. Building the chain through
    ``_eval_bindings`` (rather than calling ``_eval_bin_op`` directly) exercises
    that threading.
    """
    env = {}
    _eval_bindings(bindings, env, {}, [], [])
    return env


def _const(name, value):
    return {'name': name, 'value': {'kind': 'load_const', 'value': value}}


def _bin(name, op, left, right):
    return {'name': name, 'value': {'kind': 'bin_op', 'op': op, 'left': left, 'right': right}}


def _unary(name, op, operand):
    return {'name': name, 'value': {'kind': 'unary_op', 'op': op, 'operand': operand}}


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


class TestChainedByteThreading:
    """A shift/bitwise RESULT is a fixed-length, possibly NON-minimal byte
    array on-chain, and feeding it to a length-sensitive ``& | ^``/shift/``~``
    makes the result depend on that real length -- not on the re-minimised
    numeric value. The interpreter threads the raw result bytes through a
    per-binding side map so chained expressions match the deployed script.

    Without the fix these cases diverged (funds-relevant): ``(2<<8)|5``
    aborted on-chain agreement vs. the buggy re-minimised OP_OR length
    mismatch, and ``((1<<8)&0)`` returned 0 off-chain while the deployed
    script aborts.
    """

    def test_shift_then_or_matches_onchain(self):
        # 2<<8 -> raw stack bytes [0x00] (1 byte, non-minimal 0); OP_OR against
        # 5's minimal [0x05] agrees on length -> [0x05] -> 5. The buggy path
        # re-minimises 0 to empty, OP_OR length-mismatches and aborts.
        env = _run_chain([
            _const("a", 2),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _const("c", 5),
            _bin("result", "|", "shifted", "c"),
        ])
        assert env["result"] == 5

    def test_shift_then_and_zero_aborts(self):
        # 1<<8 -> raw [0x00] (1 byte); OP_AND against 0's empty encoding is a
        # length mismatch -> on-chain abort. The buggy path computes 0 & 0 = 0
        # (funds-loss: spends where the script aborts).
        with pytest.raises(ValueError, match="same length"):
            _run_chain([
                _const("a", 1),
                _const("b", 8),
                _bin("shifted", "<<", "a", "b"),
                _const("z", 0),
                _bin("result", "&", "shifted", "z"),
            ])

    def test_shift_then_invert_matches_onchain(self):
        # 2<<8 -> raw [0x00]; OP_INVERT flips length-preserving -> [0xff] ->
        # decodes to -127 (high bit = sign). Native ~0 would be -1.
        env = _run_chain([
            _const("a", 2),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _unary("result", "~", "shifted"),
        ])
        assert env["result"] == -127

    def test_shift_then_and_two_byte_matches_onchain(self):
        # 256<<8 -> raw [0x01,0x00] (2 bytes); OP_AND against 256's minimal
        # [0x00,0x01] agrees on length -> [0x00,0x00] -> 0.
        env = _run_chain([
            _const("a", 256),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _const("c", 256),
            _bin("result", "&", "shifted", "c"),
        ])
        assert env["result"] == 0


class TestNonMinimalNumericOperandAborts:
    """A shift PRESERVES its operand's byte length, so ``1 >> 1`` leaves the
    1-byte array ``[0x00]`` -- a NON-minimal zero (minimal zero is the empty
    array).

    Every NUMERIC consumer on-chain decodes with ``fRequireMinimal=True`` and
    ABORTS on a non-minimal encoding: OP_ADD/OP_SUB/OP_MUL/OP_DIV/OP_MOD,
    OP_NUMEQUAL/OP_NUMNOTEQUAL and the relational ops, and a shift's COUNT
    operand. The interpreter threaded the real stack bytes through the byte
    ops but the numeric path read only the decoded value, re-minimising
    ``[0x00]`` to ``0``. ``assert((n >> 1) == 0)`` with ``n = 1`` therefore
    reported a clean spend off-chain while the deployed script aborts --
    the UTXO becomes permanently unspendable.
    """

    # Prefix shared by every case: ``shifted`` = 1 >> 1 -> raw bytes [0x00].
    PREFIX = [
        _const("a", 1),
        _const("b", 1),
        _bin("shifted", ">>", "a", "b"),
        _const("zero", 0),
        _const("one", 1),
    ]

    @pytest.mark.parametrize(
        "op,left,right",
        [
            # The canonical funds-locking guard.
            ("===", "shifted", "zero"),
            # ...and with the non-minimal operand on the right.
            ("===", "zero", "shifted"),
            ("+", "shifted", "one"),
            ("-", "shifted", "one"),
            ("*", "shifted", "one"),
            ("/", "shifted", "one"),
            ("%", "shifted", "one"),
            ("!==", "shifted", "one"),
            ("<", "shifted", "one"),
            ("<=", "shifted", "one"),
            (">", "shifted", "one"),
            (">=", "shifted", "one"),
            # A shift's COUNT operand IS read as a number -> fRequireMinimal.
            ("<<", "one", "shifted"),
            (">>", "one", "shifted"),
        ],
    )
    def test_non_minimal_operand_aborts(self, op, left, right):
        with pytest.raises(ValueError, match="non-minimally encoded"):
            _run_chain(self.PREFIX + [_bin("result", op, left, right)])


class TestMinimalOperandsStillAccepted:
    """CONTROLS. None of these carry a non-minimal encoding into a numeric
    consumer, so all must keep evaluating exactly as before.
    """

    def test_minimal_shift_result_still_compares(self):
        # 2>>1 leaves [0x01] -- that IS the minimal encoding of 1, so the
        # numeric compare is legal on-chain.
        env = _run_chain([
            _const("a", 2),
            _const("b", 1),
            _bin("shifted", ">>", "a", "b"),
            _const("one", 1),
            _bin("result", "===", "shifted", "one"),
        ])
        assert env["result"] is True

    def test_or_on_non_minimal_equal_length_operands_still_works(self):
        # `& | ^` are NOT fRequireMinimal -- they take non-minimal bytes and
        # only require equal length. (2<<8) is the 1-byte [0x00]; OR with
        # [0x05] gives [0x05], which is minimal, so `=== 5` is legal too.
        # Pinned by conformance/fuzz-regressions/entries/
        # 2026-07-14-chained-shift-or-nonminimal -- rejecting this is WRONG.
        env = _run_chain([
            _const("a", 2),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _const("c", 5),
            _bin("ored", "|", "shifted", "c"),
            _bin("result", "===", "ored", "c"),
        ])
        assert env["ored"] == 5
        assert env["result"] is True

    def test_shift_value_operand_may_be_non_minimal(self):
        # A shift's VALUE operand is not fRequireMinimal either: (2<<8) is
        # [0x00], shifting it again is legal and stays 1 byte.
        env = _run_chain([
            _const("a", 2),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _const("one", 1),
            _bin("again", "<<", "shifted", "one"),
            _const("c", 5),
            _bin("ored", "|", "again", "c"),
        ])
        assert env["ored"] == 5

    def test_invert_of_non_minimal_still_works(self):
        # OP_INVERT is a byte op; ~(2<<8) = [0xff] = -127, itself minimal.
        env = _run_chain([
            _const("a", 2),
            _const("b", 8),
            _bin("shifted", "<<", "a", "b"),
            _unary("inv", "~", "shifted"),
            _const("m127", -127),
            _bin("result", "===", "inv", "m127"),
        ])
        assert env["result"] is True

    def test_plain_arithmetic_unaffected(self):
        env = _run_chain([
            _const("a", 1),
            _const("b", 1),
            _bin("sum", "+", "a", "b"),
            _const("two", 2),
            _bin("result", "===", "sum", "two"),
        ])
        assert env["result"] is True
