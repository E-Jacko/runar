"""C17 -- ``OP_NOT OP_NOT`` is boolean NORMALISATION, not numeric identity.

For a non-canonical operand (say 5) the pair yields 1, while deleting it
leaves 5.  Truthiness is preserved, the VALUE is not -- and a downstream
``OP_EQUAL`` / ``OP_NUMEQUAL`` / state serialisation consumes the value, so the
optimised and unoptimised programs disagree on accept/reject.

The unguarded 2-op ``not-not-elim`` rule is unsound in composition with the
sibling ``PUSH 0; OP_NUMEQUAL -> OP_NOT`` rule, which synthesises a fresh
``OP_NOT`` sitting on an ARBITRARY script number.  The stack lowerer emits
``!==`` as ``[OP_NUMEQUAL, OP_NOT]``, so::

    x !== 0n   ==>   <x> ; PUSH 0 ; OP_NUMEQUAL ; OP_NOT

became ``<x> ; OP_NOT ; OP_NOT``, which the unguarded rule then deleted
entirely -- ``x !== 0n`` compiled to ``x``.

The fix widens the rule to a 3-op window that includes the PRODUCER of the
negated value and only fires when that producer provably leaves a canonical
boolean (0 or 1) behind.
"""

from __future__ import annotations

from runar_compiler.codegen.optimizer import optimize_stack_ops
from runar_compiler.codegen.stack import StackOp, PushValue
from runar_compiler.compiler import compile_from_source_str_with_result


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def opc(code: str) -> StackOp:
    return StackOp(op="opcode", code=code)


def push_int(n: int) -> StackOp:
    return StackOp(op="push", value=PushValue(kind="bigint", big_int=n))


def push_bool(b: bool) -> StackOp:
    return StackOp(op="push", value=PushValue(kind="bool", bool_val=b))


def signature(ops: list[StackOp]) -> str:
    """Render a stack-op list as a compact, comparable string."""
    parts = []
    for op in ops:
        if op.op == "opcode":
            parts.append(op.code)
        elif op.op == "push":
            assert op.value is not None
            if op.value.kind == "bigint":
                parts.append(f"PUSH({op.value.big_int})")
            elif op.value.kind == "bool":
                parts.append(f"PUSH({op.value.bool_val})")
            else:
                parts.append(f"PUSH({(op.value.bytes_val or b'').hex()})")
        else:
            parts.append(op.op.upper())
    return " ".join(parts)


def check(ops: list[StackOp], want: str) -> None:
    got = signature(optimize_stack_ops(ops))
    assert got == want, f"input {signature(ops)!r} -> {got!r}, expected {want!r}"


# ---------------------------------------------------------------------------
# The guard: a non-canonical producer means the OP_NOT pair must SURVIVE
# ---------------------------------------------------------------------------

class TestC17NonCanonicalProducerSurvives:
    def test_x_not_equal_zero_keeps_the_pair(self):
        # `x !== 0n` where x comes off the witness stack via a pick.
        check(
            [StackOp(op="pick", depth=3), push_int(0), opc("OP_NUMEQUAL"), opc("OP_NOT")],
            "PICK OP_NOT OP_NOT",
        )

    def test_mirrored_composition_keeps_the_pair(self):
        # `(!b) === false` lowers to OP_NOT; PUSH 0; OP_NUMEQUAL.
        check(
            [StackOp(op="pick", depth=2), opc("OP_NOT"), push_int(0), opc("OP_NUMEQUAL")],
            "PICK OP_NOT OP_NOT",
        )

    def test_arbitrary_numeric_producers(self):
        check([opc("OP_ADD"), opc("OP_NOT"), opc("OP_NOT")], "OP_ADD OP_NOT OP_NOT")
        check([opc("OP_SIZE"), opc("OP_NOT"), opc("OP_NOT")], "OP_SIZE OP_NOT OP_NOT")
        check([push_int(5), opc("OP_NOT"), opc("OP_NOT")], "PUSH(5) OP_NOT OP_NOT")

    def test_stack_shuffles_are_deliberately_excluded(self):
        # dup / pick / roll forward a value whose provenance this local window
        # cannot see, so they are NOT canonical-bool producers.
        check([StackOp(op="dup"), opc("OP_NOT"), opc("OP_NOT")], "DUP OP_NOT OP_NOT")
        check([StackOp(op="roll", depth=4), opc("OP_NOT"), opc("OP_NOT")], "ROLL OP_NOT OP_NOT")

    def test_bare_pair_survives(self):
        # No producer in the window at all -- the operand could be anything.
        check([opc("OP_NOT"), opc("OP_NOT")], "OP_NOT OP_NOT")

    def test_raw_bytes_barrier_still_holds(self):
        check(
            [
                opc("OP_NUMEQUAL"),
                StackOp(op="raw_bytes", raw_bytes=b"\x51", in_arity=0, out_arity=1),
                opc("OP_NOT"),
                opc("OP_NOT"),
            ],
            "OP_NUMEQUAL RAW_BYTES OP_NOT OP_NOT",
        )


# ---------------------------------------------------------------------------
# NEGATIVE case: the guard must not make the rule dead
# ---------------------------------------------------------------------------

class TestC17CanonicalProducerStillElided:
    def test_canonical_opcode_producers(self):
        for code in [
            "OP_EQUAL",
            "OP_NUMEQUAL",
            "OP_NUMNOTEQUAL",
            "OP_LESSTHAN",
            "OP_GREATERTHAN",
            "OP_LESSTHANOREQUAL",
            "OP_GREATERTHANOREQUAL",
            "OP_BOOLAND",
            "OP_BOOLOR",
            "OP_WITHIN",
            "OP_0NOTEQUAL",
            "OP_CHECKSIG",
            "OP_CHECKMULTISIG",
        ]:
            check([opc(code), opc("OP_NOT"), opc("OP_NOT")], code)

    def test_op_not_is_itself_canonical(self):
        # Triple negation collapses to a single OP_NOT.
        check([opc("OP_NOT"), opc("OP_NOT"), opc("OP_NOT")], "OP_NOT")

    def test_literal_canonical_booleans(self):
        check([push_int(0), opc("OP_NOT"), opc("OP_NOT")], "PUSH(0)")
        check([push_int(1), opc("OP_NOT"), opc("OP_NOT")], "PUSH(1)")
        check([push_bool(True), opc("OP_NOT"), opc("OP_NOT")], "PUSH(True)")
        check([push_bool(False), opc("OP_NOT"), opc("OP_NOT")], "PUSH(False)")


# ---------------------------------------------------------------------------
# End-to-end: `x !== 0n` must not be optimised down to `x`
# ---------------------------------------------------------------------------

C17_SOURCE = """
import { SmartContract, assert } from 'runar-lang';

export class NotComposition extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint): void {
    const nonZero: boolean = x !== 0n;
    assert(nonZero === true);
  }
}
"""


class TestC17EndToEnd:
    def test_not_equal_zero_keeps_not_pair(self):
        """0x91 is OP_NOT; the surviving pair is the byte sequence ``9191``.

        Before the guard the whole comparison collapsed to ``OP_TRUE
        OP_NUMEQUAL`` (i.e. ``x == 1``), which REJECTS the valid witness x = 5.
        """
        result = compile_from_source_str_with_result(
            C17_SOURCE, "NotComposition.runar.ts", disable_constant_folding=True
        )
        assert result.success, f"compilation failed: {result.diagnostics}"
        assert "9191" in (result.script_hex or ""), (
            "`x !== 0n` lost its OP_NOT OP_NOT pair -- the comparison was "
            f"optimised away and the raw operand survives instead: "
            f"hex={result.script_hex} asm={result.script_asm}"
        )
