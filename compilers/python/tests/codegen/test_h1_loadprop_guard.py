"""H1 (#119 tail): ``_lower_load_prop`` must NOT silently coerce an unknown
property onto a constructor slot.

A ``load_prop`` binding whose name is not a declared constructor-param property
used to fall through to the placeholder fallback: the ``param_index`` loop never
matched, leaving it at the count of non-initialized props, so the emitted
placeholder spliced an UNRELATED constructor argument's deploy-time bytes into
the locking script -- a silent-wrong-code path with no diagnostic.

The hardened behaviour is a HARD ERROR (``RuntimeError``) with a clear
diagnostic that names the offending property, states it has no deploy-time slot
/ is not a constructor parameter, and lists the known constructor-param
property names. A real constructor-param property (readonly, or a mutable state
field whose initial value is spliced at deploy) is found and is unaffected.
"""

from __future__ import annotations

import pytest

from runar_compiler.codegen.stack import lower_to_stack
from runar_compiler.ir.types import (
    ANFBinding,
    ANFMethod,
    ANFProgram,
    ANFProperty,
    ANFValue,
    SourceLocation,
)


def _program_with_unknown_load_prop() -> ANFProgram:
    """Minimal ANF program with a real readonly constructor-param property
    ``pk`` (constructor slot 0) plus a public method that loads a property
    ``ghost`` that is NOT declared on the contract. ``ghost`` therefore reaches
    the placeholder fallback with no matching constructor slot.
    """
    return ANFProgram(
        contract_name="Ghost",
        properties=[ANFProperty(name="pk", type="PubKey", readonly=True)],
        methods=[
            ANFMethod(
                name="spend",
                params=[],
                is_public=True,
                body=[
                    ANFBinding(
                        name="t0",
                        value=ANFValue(kind="load_prop", name="ghost"),
                        source_loc=SourceLocation(
                            file="Ghost.runar.py", line=7, column=4
                        ),
                    ),
                    ANFBinding(
                        name="t1",
                        value=ANFValue(kind="assert", value_ref="t0"),
                    ),
                ],
            )
        ],
    )


def test_raises_on_load_prop_with_no_constructor_slot() -> None:
    with pytest.raises(RuntimeError, match="ghost"):
        lower_to_stack(_program_with_unknown_load_prop())


def test_diagnostic_names_property_slot_and_source_location() -> None:
    with pytest.raises(RuntimeError) as excinfo:
        lower_to_stack(_program_with_unknown_load_prop())
    message = str(excinfo.value)
    # The offending property name.
    assert "ghost" in message
    # States it is not a constructor parameter / has no deploy-time slot.
    assert "constructor parameter" in message
    assert "deploy-time" in message
    # Lists the known constructor-param property names.
    assert "pk" in message
    # Includes the source location carried by the ANF binding.
    assert "Ghost.runar.py" in message
    assert "7" in message


def test_legit_ctor_param_prop_lowers_without_error() -> None:
    """A real readonly constructor-param property is found (param_index >= 0)
    and lowers to a placeholder without raising."""
    program = ANFProgram(
        contract_name="Ok",
        properties=[ANFProperty(name="pk", type="PubKey", readonly=True)],
        methods=[
            ANFMethod(
                name="spend",
                params=[],
                is_public=True,
                body=[
                    ANFBinding(name="t0", value=ANFValue(kind="load_prop", name="pk")),
                    ANFBinding(name="t1", value=ANFValue(kind="assert", value_ref="t0")),
                ],
            )
        ],
    )
    # Must not raise.
    lower_to_stack(program)
