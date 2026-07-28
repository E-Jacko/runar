# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# rubocop:disable RSpec/DescribeClass
RSpec.describe 'Runar::SDK::ScriptUtils.extract_constructor_args' do
  # rubocop:enable RSpec/DescribeClass

  # A param referenced N times in the contract body emits N constructor slots.
  # Every occurrence's encoded width shifts the offsets of everything after it,
  # so the extractor must account for ALL occurrences — not just the first per
  # param. Regression for a bug where slots were deduplicated by param_index
  # BEFORE the offset walk, mis-reading every later slot whenever an earlier
  # repeated value encoded wider than its 1-byte template placeholder.
  #
  # Template: ab <00> 7c <00> 7c <00> ac
  #   offset 1: alpha (param_index 0)
  #   offset 3: alpha again (param_index 0 — second reference)
  #   offset 5: beta  (param_index 1)
  # Resolved with alpha = 500 (scriptnum push `02f401`, 3 bytes) and
  # beta = 7 (OP_7, 1 byte):
  #   ab 02f401 7c 02f401 7c 57 ac
  def repeated_slot_artifact
    Runar::SDK::RunarArtifact.new(
      script: 'ab' + '00' + '7c' + '00' + '7c' + '00' + 'ac',
      constructor_slots: [
        Runar::SDK::ConstructorSlot.new(param_index: 0, byte_offset: 1),
        Runar::SDK::ConstructorSlot.new(param_index: 0, byte_offset: 3),
        Runar::SDK::ConstructorSlot.new(param_index: 1, byte_offset: 5)
      ],
      abi: Runar::SDK::ABI.new(
        constructor_params: [
          Runar::SDK::ABIParam.new(name: 'alpha', type: 'bigint'),
          Runar::SDK::ABIParam.new(name: 'beta', type: 'bigint')
        ]
      )
    )
  end

  it 'reads slots AFTER a repeated wide value at the correct offsets' do
    resolved = 'ab' + '02f401' + '7c' + '02f401' + '7c' + '57' + 'ac'
    args = Runar::SDK::ScriptUtils.extract_constructor_args(repeated_slot_artifact, resolved)

    expect(args['alpha']).to eq(500)
    # Before the fix, the second alpha occurrence's +2 byte shift was dropped,
    # so beta was read from inside the second alpha push and decoded as 124.
    expect(args['beta']).to eq(7)
  end

  it 'still extracts correctly when the repeated value fits its placeholder width' do
    # alpha = 5 → OP_5 (1 byte, same width as the placeholder: zero shift).
    resolved = 'ab' + '55' + '7c' + '55' + '7c' + '57' + 'ac'
    args = Runar::SDK::ScriptUtils.extract_constructor_args(repeated_slot_artifact, resolved)

    expect(args['alpha']).to eq(5)
    expect(args['beta']).to eq(7)
  end
end
