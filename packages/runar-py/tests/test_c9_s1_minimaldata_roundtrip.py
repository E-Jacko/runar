"""C9 + S1 — single-byte MINIMALDATA push data must round-trip.

C9 (state): ``serialize_state`` routes a variable-length (ByteString) field
through ``encode_push_data``, which short-circuits single-byte payloads to
``OP_0`` / ``OP_1..OP_16`` / ``OP_1NEGATE``. ``decode_push_data`` only
understood direct pushes (``opcode <= 75``) and ``OP_PUSHDATA1/2/4``, so every
one of those minimal opcodes decoded as a zero-length push ('') — state
restored from chain came back empty instead of the real byte.

S1 (ctor): the same encoder backs ``_encode_arg`` (constructor-arg splicing +
unlocking-script args), and ``_interpret_script_element``'s default
(non-numeric) branch just forwarded ``data_hex``, which ``_read_script_element``
leaves empty for OP_N / OP_1NEGATE (they carry no separate data bytes — the
opcode IS the value). A 1-byte ByteString ctor arg restored as ''.

The ``0x00`` case is a distinct bug in the ENCODER: ``OP_0`` pushes the EMPTY
byte array, not a 1-byte ``0x00``. The minimal encoding of a 1-byte ``0x00``
payload is the direct push ``01 00`` — exactly what the compiler's
``encodePushBytesHex`` (packages/runar-compiler/src/passes/push-encoding.ts)
emits. Encoding it as ``OP_0`` changes the value.

Mirrors the TypeScript reference fix in packages/runar-sdk/src/{state,contract,
script-utils}.ts.
"""

import pytest

from runar.sdk.contract import RunarContract
from runar.sdk.script_utils import extract_constructor_args
from runar.sdk.state import serialize_state, deserialize_state
from runar.sdk.types import Abi, AbiParam, ConstructorSlot, RunarArtifact, StateField


# Payload set: the three MINIMALDATA short-circuit families (0x00 boundary,
# OP_1..OP_16 low/mid/high, OP_1NEGATE) plus a multi-byte and an empty control.
_PAYLOADS = [
    pytest.param('00', id='0x00-op0-boundary'),
    pytest.param('01', id='0x01-OP_1'),
    pytest.param('05', id='0x05-OP_5'),
    pytest.param('10', id='0x10-OP_16'),
    pytest.param('81', id='0x81-OP_1NEGATE'),
    pytest.param('aabbccdd', id='multi-byte'),
    pytest.param('', id='empty'),
]


# ---------------------------------------------------------------------------
# C9 — state serializer round-trip
# ---------------------------------------------------------------------------

@pytest.mark.parametrize('payload', _PAYLOADS)
def test_c9_bytestring_state_field_round_trips(payload):
    fields = [StateField(name='b', type='ByteString', index=0)]
    encoded = serialize_state(fields, {'b': payload})
    decoded = deserialize_state(fields, encoded)
    assert decoded['b'] == payload


# ---------------------------------------------------------------------------
# S1 — constructor-arg splice/restore round-trip
# ---------------------------------------------------------------------------

def _ctor_artifact() -> RunarArtifact:
    """Template: OP_DUP <ctor slot placeholder OP_0> OP_SWAP."""
    return RunarArtifact(
        version='runar-v0.1.0',
        contract_name='CtorByteString',
        abi=Abi(constructor_params=[AbiParam(name='b', type='ByteString')]),
        script='ab' + '00' + '7c',
        constructor_slots=[ConstructorSlot(param_index=0, byte_offset=1)],
    )


@pytest.mark.parametrize('payload', _PAYLOADS[:-1])  # empty is not a ctor case
def test_s1_bytestring_ctor_arg_round_trips(payload):
    artifact = _ctor_artifact()
    contract = RunarContract(artifact, [payload])
    locking_script = contract.get_locking_script()

    restored = extract_constructor_args(artifact, locking_script)
    assert restored['b'] == payload
