"""Stack lowering across unrolled for-loops -- outer-scope refs (method params,
pre-loop consts) must survive loop unrolling.

Mirrors packages/runar-compiler/src/__tests__/loop-outer-refs.test.ts.

Two related defects around unrolled for-loops:
 (a) a const defined before a loop and referenced inside it (including only
     inside a nested if-branch) was consumed by the first iteration, failing
     compilation with "Value 'X' not found on stack";
 (b) worse, a method PARAM referenced after an unrolled loop whose body also
     references it was silently lowered to an empty push (OP_0): compilation
     succeeded, the env-based interpreter passed, but the emitted Script would
     fail at runtime.

The fix: _lower_loop collects outer refs deeply (nested branches included) and
protects them in non-final iterations, and in the final iteration whenever the
enclosing scope still references them after the loop. The old silent OP_0
fallbacks in _lower_load_param / _lower_load_const are now hard errors.
"""

from __future__ import annotations

import json
import textwrap

import pytest

from runar_compiler.compiler import compile_from_ir_bytes, compile_from_source


# ---------------------------------------------------------------------------
# Sources (Python surface). snake_case identifiers map to camelCase in the AST.
# ---------------------------------------------------------------------------

# V003 repro: multi-input tx walk -- param `data` used inside AND after the loop.
LOOP_WALK_SOURCE = textwrap.dedent("""\
    from runar import SmartContract, ByteString, Bigint, public, assert_, substr, cat, bin2num

    class LoopWalk(SmartContract):
        pad00: ByteString = "00"

        def __init__(self):
            super().__init__()

        @public
        def walk(self, data: ByteString):
            off: Bigint = 5
            for i in range(3):
                if i < bin2num(cat(substr(data, 4, 1), self.pad00)):
                    sl: Bigint = bin2num(cat(substr(data, off + 36, 1), self.pad00))
                    assert_(sl < 253)
                    off = off + 36 + 1 + sl + 4
            tail: Bigint = bin2num(cat(substr(data, off, 1), self.pad00))
            assert_(tail == 7)
""")

# Symptom (a): const defined before the loop, referenced inside it.
CONST_BEFORE_LOOP_SOURCE = textwrap.dedent("""\
    from runar import SmartContract, ByteString, Bigint, public, assert_, substr, cat, bin2num

    class ConstLoop(SmartContract):
        pad00: ByteString = "00"

        def __init__(self):
            super().__init__()

        @public
        def probe(self, data: ByteString):
            base: Bigint = 5
            acc: Bigint = 0
            for i in range(3):
                b: Bigint = bin2num(cat(substr(data, base + i, 1), self.pad00))
                acc = acc + b
            assert_(acc == 6)
""")


def _compile(tmp_path, source: str, name: str):
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    return compile_from_source(str(path))


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestLoopOuterRefs:
    def test_param_after_loop_not_lowered_to_empty_push(self, tmp_path):
        # The post-loop code reads `data` via substr(data, off, 1). With the
        # bug, `data` was emitted as OP_0 right after the final OP_ENDIF; the
        # fix brings the real param up. Compilation must succeed and the
        # post-loop region must not carry a bare OP_0 placeholder.
        artifact = _compile(tmp_path, LOOP_WALK_SOURCE, "LoopWalk.runar.py")
        assert len(artifact.script) > 0
        asm = artifact.asm
        post_loop = asm[asm.rfind("OP_ENDIF"):]
        assert "OP_0" not in post_loop, (
            f"post-loop region carries an OP_0 placeholder: {post_loop!r}"
        )

    def test_const_before_loop_referenced_inside_compiles(self, tmp_path):
        # Previously: "Value 'base' not found on stack (...)" on iteration 2.
        artifact = _compile(tmp_path, CONST_BEFORE_LOOP_SOURCE, "ConstLoop.runar.py")
        assert len(artifact.script) > 0

    def test_load_param_that_cannot_be_satisfied_is_loud_error_not_op0(self):
        # Hand-written ANF referencing a parameter the method does not have --
        # the old code silently emitted OP_0 here.
        ir = json.dumps({
            "contractName": "Broken",
            "properties": [],
            "methods": [
                {
                    "name": "run",
                    "params": [{"name": "x", "type": "bigint"}],
                    "body": [
                        {"name": "t0", "value": {"kind": "load_param", "name": "ghost"}},
                        {"name": "t1", "value": {"kind": "assert", "value": "t0"}},
                    ],
                    "isPublic": True,
                }
            ],
        }).encode("utf-8")

        with pytest.raises(RuntimeError, match="Refusing to emit a silent OP_0"):
            compile_from_ir_bytes(ir)

    def test_load_const_ref_that_cannot_be_satisfied_is_loud_error_not_op0(self):
        # Hand-written ANF aliasing (@ref:) a binding that is not on the stack.
        ir = json.dumps({
            "contractName": "Broken",
            "properties": [],
            "methods": [
                {
                    "name": "run",
                    "params": [{"name": "x", "type": "bigint"}],
                    "body": [
                        {"name": "t0", "value": {"kind": "load_const", "value": "@ref:ghost"}},
                        {"name": "t1", "value": {"kind": "assert", "value": "t0"}},
                    ],
                    "isPublic": True,
                }
            ],
        }).encode("utf-8")

        with pytest.raises(RuntimeError, match="Refusing to emit a silent OP_0"):
            compile_from_ir_bytes(ir)
