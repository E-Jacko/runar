"""A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
little-endian sign-magnitude word must be REFUSED, not silently truncated.

``num2bin-le8`` gives a bigint state field exactly 63 bits of magnitude (bytes
0..6 plus the low 7 bits of byte 7) and one sign bit (0x80 of byte 7).
``serialize_state`` wrote the low 8 bytes and dropped everything above, then
OR-ed the sign bit in on top of whatever landed there. Measured in the TS
reference before the guard::

    value       bytes written       reads back as
    2^63        0000000000000080    0    (negative zero)
    2^63 + 5    0500000000000080    -5   (SIGN FLIP)
    2^64        0000000000000000    0

Python ints are arbitrary-precision, so this tier has the identical defect: the
deploy succeeds and the UTXO is unspendable, because the covenant rebuilds the
continuation with the compiler's own OP_NUM2BIN 8, which cannot produce those
bytes from that number, so hash256(outputs) never matches.

Expected bytes below are derived BY HAND from the sign-magnitude rule, never
read off the serializer.
"""

import pytest
from runar.sdk.state import serialize_state, deserialize_state
from runar.sdk.types import StateField


COUNT = [StateField(name='count', type='bigint', index=0)]

#: 2^63 — one past the largest magnitude the 63 magnitude bits can hold.
TWO_63 = 9_223_372_036_854_775_808
#: 2^63 - 1 — the largest magnitude that DOES fit.
MAX_MAGNITUDE = TWO_63 - 1


class TestBigIntMagnitudeBound:
    def test_rejects_exactly_two_pow_63(self):
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': TWO_63})

    def test_rejects_exactly_negative_two_pow_63(self):
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': -TWO_63})

    def test_rejects_two_pow_63_plus_5(self):
        """The sign-flip case: used to write 0500000000000080, read back as -5."""
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': TWO_63 + 5})

    def test_rejects_two_pow_64(self):
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': 2 ** 64})

    def test_rejects_two_pow_70_both_signs(self):
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': 2 ** 70})
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': -(2 ** 70)})

    def test_rejects_out_of_range_bigint_string(self):
        """The unrevived-JSON path (``"...n"``) narrows to the same word."""
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(COUNT, {'count': f'{TWO_63}n'})

    def test_names_the_field_and_the_value_it_refused(self):
        with pytest.raises(ValueError) as excinfo:
            serialize_state(COUNT, {'count': TWO_63})
        message = str(excinfo.value)
        assert 'count' in message
        assert str(TWO_63) in message

    def test_rejects_out_of_range_fixed_array_element(self):
        fields = [
            StateField(
                name='slots',
                type='FixedArray<bigint, 2>',
                index=0,
                fixed_array={
                    'elementType': 'bigint',
                    'length': 2,
                    'syntheticNames': ['slots__0', 'slots__1'],
                },
            )
        ]
        with pytest.raises(ValueError, match='does not fit'):
            serialize_state(fields, {'slots': [1, TWO_63]})

    # -----------------------------------------------------------------
    # Accepting controls — byte-exact, and they must stay byte-exact
    # -----------------------------------------------------------------

    def test_accepts_max_magnitude_and_writes_ffffffffffffff7f(self):
        # magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (all seven magnitude
        # bits set, sign bit clear).
        assert serialize_state(COUNT, {'count': MAX_MAGNITUDE}) == 'ffffffffffffff7f'
        assert deserialize_state(COUNT, 'ffffffffffffff7f')['count'] == MAX_MAGNITUDE

    def test_accepts_negative_max_magnitude_and_writes_ffffffffffffffff(self):
        # same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
        assert serialize_state(COUNT, {'count': -MAX_MAGNITUDE}) == 'ffffffffffffffff'
        assert deserialize_state(COUNT, 'ffffffffffffffff')['count'] == -MAX_MAGNITUDE

    def test_accepts_max_magnitude_as_bigint_string(self):
        assert serialize_state(COUNT, {'count': f'{MAX_MAGNITUDE}n'}) == 'ffffffffffffff7f'
        assert serialize_state(COUNT, {'count': f'-{MAX_MAGNITUDE}n'}) == 'ffffffffffffffff'

    @pytest.mark.parametrize(
        'value,expected',
        [
            (0, '0000000000000000'),
            (1, '0100000000000000'),
            (-1, '0100000000000080'),
            (127, '7f00000000000000'),
            (-127, '7f00000000000080'),
            (128, '8000000000000000'),
            (-128, '8000000000000080'),
        ],
    )
    def test_accepts_the_small_values_every_shipped_contract_uses(self, value, expected):
        assert serialize_state(COUNT, {'count': value}) == expected
