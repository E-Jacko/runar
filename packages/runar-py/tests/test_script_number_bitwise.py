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
