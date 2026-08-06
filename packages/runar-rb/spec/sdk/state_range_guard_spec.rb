# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
# little-endian sign-magnitude word must be REFUSED, not silently truncated.
#
# +num2bin-le8+ gives a bigint state field exactly 63 bits of magnitude (bytes
# 0..6 plus the low 7 bits of byte 7) and one sign bit (0x80 of byte 7).
# +serialize_state+ wrote the low 8 bytes and dropped everything above, then
# OR-ed the sign bit in on top of whatever landed there. Measured in the TS
# reference before the guard:
#
#   value       bytes written       reads back as
#   2^63        0000000000000080    0    (negative zero)
#   2^63 + 5    0500000000000080    -5   (SIGN FLIP)
#   2^64        0000000000000000    0
#
# Ruby Integers are arbitrary-precision, so this tier has the identical defect:
# the deploy succeeds and the UTXO is unspendable, because the covenant
# rebuilds the continuation with the compiler's own OP_NUM2BIN 8, which cannot
# produce those bytes from that number, so hash256(outputs) never matches.
#
# Expected bytes below are derived BY HAND from the sign-magnitude rule, never
# read off the serializer.
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'Runar::SDK::State bigint magnitude bound' do
  # rubocop:enable RSpec/DescribeClass

  let(:mod) { Runar::SDK::State }

  # 2^63 — one past the largest magnitude the 63 magnitude bits can hold.
  two63 = 9_223_372_036_854_775_808
  # 2^63 - 1 — the largest magnitude that DOES fit.
  max_magnitude = two63 - 1

  let(:count_fields) do
    [Runar::SDK::StateField.new(name: 'count', type: 'bigint', index: 0)]
  end

  describe 'rejecting' do
    it 'rejects exactly 2^63' do
      expect { mod.serialize_state(count_fields, { 'count' => two63 }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'rejects exactly -(2^63)' do
      expect { mod.serialize_state(count_fields, { 'count' => -two63 }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'rejects 2^63 + 5 — the value that read back as -5' do
      expect { mod.serialize_state(count_fields, { 'count' => two63 + 5 }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'rejects 2^64' do
      expect { mod.serialize_state(count_fields, { 'count' => 2**64 }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'rejects a magnitude well above the word (2^70), both signs' do
      expect { mod.serialize_state(count_fields, { 'count' => 2**70 }) }
        .to raise_error(ArgumentError, /does not fit/)
      expect { mod.serialize_state(count_fields, { 'count' => -(2**70) }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'rejects an out-of-range BigInt string from unrevived JSON' do
      expect { mod.serialize_state(count_fields, { 'count' => "#{two63}n" }) }
        .to raise_error(ArgumentError, /does not fit/)
    end

    it 'names the field and the value it refused' do
      expect { mod.serialize_state(count_fields, { 'count' => two63 }) }
        .to raise_error(ArgumentError, /count/)
      expect { mod.serialize_state(count_fields, { 'count' => two63 }) }
        .to raise_error(ArgumentError, /#{two63}/)
    end

    it 'rejects an out-of-range element of a FixedArray field' do
      fa = { element_type: 'bigint', length: 2, synthetic_names: %w[slots__0 slots__1] }
      field = Runar::SDK::StateField.new(
        name: 'slots',
        type: 'FixedArray<bigint, 2>',
        index: 0,
        fixed_array: fa
      )
      expect { mod.serialize_state([field], { 'slots' => [1, two63] }) }
        .to raise_error(ArgumentError, /does not fit/)
    end
  end

  # ---------------------------------------------------------------------------
  # Accepting controls — byte-exact, and they must stay byte-exact
  # ---------------------------------------------------------------------------

  describe 'accepting' do
    it 'accepts 2^63 - 1 and writes ffffffffffffff7f' do
      # magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (all seven magnitude bits
      # set, sign bit clear).
      expect(mod.serialize_state(count_fields, { 'count' => max_magnitude }))
        .to eq('ffffffffffffff7f')
      expect(mod.deserialize_state(count_fields, 'ffffffffffffff7f')['count'])
        .to eq(max_magnitude)
    end

    it 'accepts -(2^63 - 1) and writes ffffffffffffffff' do
      # same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
      expect(mod.serialize_state(count_fields, { 'count' => -max_magnitude }))
        .to eq('ffffffffffffffff')
      expect(mod.deserialize_state(count_fields, 'ffffffffffffffff')['count'])
        .to eq(-max_magnitude)
    end

    it 'accepts the boundary as an unrevived BigInt string' do
      expect(mod.serialize_state(count_fields, { 'count' => "#{max_magnitude}n" }))
        .to eq('ffffffffffffff7f')
      expect(mod.serialize_state(count_fields, { 'count' => "-#{max_magnitude}n" }))
        .to eq('ffffffffffffffff')
    end

    {
      0 => '0000000000000000',
      1 => '0100000000000000',
      -1 => '0100000000000080',
      127 => '7f00000000000000',
      -127 => '7f00000000000080',
      128 => '8000000000000000',
      -128 => '8000000000000080'
    }.each do |value, expected|
      it "accepts #{value} and writes #{expected}" do
        expect(mod.serialize_state(count_fields, { 'count' => value })).to eq(expected)
      end
    end
  end
end
