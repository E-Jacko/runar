"""constructorArgs shape validation.

Mirrors packages/runar-compiler/src/__tests__/constructor-args-validation.test.ts.

``compile_from_source(constructor_args=...)`` must reject inputs that would
silently bake nothing and emit placeholder scripts that fail opaquely at
runtime:

 (a) positional arrays (natural guess, but keys match no property names);
 (b) keys that don't match any contract property (typos);
 (c) referenced readonly properties left unbaked after applying the args.

Python is dynamically typed, so unlike Go/Rust the positional-array reject (a)
is a real, reachable case and must be checked. snake_case source identifiers
map to camelCase property names in the ANF, so keys are camelCase.
"""

from __future__ import annotations

import textwrap

import pytest

from runar_compiler.compiler import CompilationError, compile_from_source


HASH_LOCK_SOURCE = textwrap.dedent("""\
    from runar import SmartContract, ByteString, Sha256, public, assert_, sha256

    class HashLock(SmartContract):
        hash_value: Sha256

        def __init__(self, hash_value: Sha256):
            super().__init__(hash_value)
            self.hash_value = hash_value

        @public
        def unlock(self, preimage: ByteString):
            assert_(sha256(preimage) == self.hash_value)
""")

TWO_PROP_SOURCE = textwrap.dedent("""\
    from runar import SmartContract, Bigint, public, assert_

    class TwoProp(SmartContract):
        target: Bigint
        unused: Bigint

        def __init__(self, target: Bigint, unused: Bigint):
            super().__init__(target, unused)
            self.target = target
            self.unused = unused

        @public
        def check(self, x: Bigint):
            assert_(x == self.target)
""")

HASH = "aa" * 32


def _compile(tmp_path, source: str, name: str, constructor_args=None):
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    return compile_from_source(str(path), constructor_args=constructor_args)


class TestConstructorArgsValidation:
    def test_rejects_positional_array(self, tmp_path):
        # Positional array -- the shape RunarContract/TestContract take, but NOT
        # what the compiler takes. Previously baked nothing silently.
        with pytest.raises(CompilationError, match="positional array"):
            _compile(tmp_path, HASH_LOCK_SOURCE, "HashLock.runar.py",
                     constructor_args=[HASH])

    def test_rejects_keys_matching_no_property(self, tmp_path):
        with pytest.raises(CompilationError) as exc:
            _compile(tmp_path, HASH_LOCK_SOURCE, "HashLock.runar.py",
                     constructor_args={"hashVal": HASH})  # typo: hashValue
        msg = str(exc.value)
        assert "'hashVal'" in msg
        assert "hashValue" in msg

    def test_rejects_referenced_readonly_left_unbaked(self, tmp_path):
        # 'target' is referenced by check() but not provided.
        with pytest.raises(CompilationError, match=r"'target'.*placeholder"):
            _compile(tmp_path, TWO_PROP_SOURCE, "TwoProp.runar.py",
                     constructor_args={"unused": 1})

    def test_accepts_unreferenced_readonly_left_unbaked(self, tmp_path):
        # 'unused' is never referenced by a method -- DCE eliminates it, so
        # leaving it unbaked is fine.
        artifact = _compile(tmp_path, TWO_PROP_SOURCE, "TwoProp.runar.py",
                            constructor_args={"target": 42})
        assert len(artifact.script) > 0

    def test_accepts_complete_named_record(self, tmp_path):
        artifact = _compile(tmp_path, HASH_LOCK_SOURCE, "HashLock.runar.py",
                            constructor_args={"hashValue": HASH})
        assert HASH in artifact.script
        # Fully baked -- no placeholder constructor slots.
        assert len(artifact.constructor_slots) == 0

    def test_still_compiles_placeholder_when_no_args(self, tmp_path):
        artifact = _compile(tmp_path, HASH_LOCK_SOURCE, "HashLock.runar.py")
        assert len(artifact.constructor_slots) >= 1
