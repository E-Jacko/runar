# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# round-trip only — absolute pin: packages/runar-rb/spec/sdk/state_push_framing_spec.rb (C9, state half).
# The S1 (constructor-arg) half has no Ruby-local literal-byte KAT; its only
# absolute evidence is indirect, via the deploy-time splice path
# (conformance/sdk-vertical) -- see the "unlocking-encodeArg-minimaldata"
# residual note in conformance/wire-primitives.json.
#
# C9 + S1 — single-byte MINIMALDATA push data must round-trip.
#
# C9 (state): +serialize_state+ routes a variable-length (ByteString) field
# through +State.encode_push_data+, which short-circuits single-byte payloads
# to OP_0 / OP_1..OP_16 / OP_1NEGATE. +State.decode_push_data+ only understood
# direct pushes (+opcode <= 75+) and OP_PUSHDATA1/2/4, so every one of those
# minimal opcodes decoded as a zero-length push ('') — state restored from
# chain came back empty instead of the real byte.
#
# S1 (ctor): the same encoder backs +RunarContract#encode_arg+ (constructor-arg
# splicing + unlocking-script args), and +ScriptUtils.interpret_script_element+'s
# default (non-numeric) branch just forwarded +data_hex+, which
# +read_script_element+ leaves empty for OP_N / OP_1NEGATE (they carry no
# separate data bytes — the opcode IS the value). A 1-byte ByteString ctor arg
# restored as ''.
#
# The 0x00 case is a distinct bug in the ENCODER: OP_0 pushes the EMPTY byte
# array, not a 1-byte 0x00. The minimal encoding of a 1-byte 0x00 payload is
# the direct push "01 00" — exactly what the compiler's encodePushBytesHex
# (packages/runar-compiler/src/passes/push-encoding.ts) emits. Encoding it as
# OP_0 changes the value.
#
# Mirrors the TypeScript reference fix in
# packages/runar-sdk/src/{state,contract,script-utils}.ts.
#
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'C9 + S1 MINIMALDATA push-data round-trip' do
  # rubocop:enable RSpec/DescribeClass

  # Payload set: the three MINIMALDATA short-circuit families (0x00 boundary,
  # OP_1..OP_16 low/mid/high, OP_1NEGATE) plus a multi-byte and an empty control.
  minimaldata_payloads = %w[00 01 05 10 81]
  state_payloads       = minimaldata_payloads + ['aabbccdd', '']
  ctor_payloads        = minimaldata_payloads + ['aabbccdd']

  # ---------------------------------------------------------------------------
  # C9 — state serializer round-trip
  # ---------------------------------------------------------------------------

  describe 'C9: variable-length ByteString state field' do
    let(:fields) { [Runar::SDK::StateField.new(name: 'b', type: 'ByteString', index: 0)] }

    state_payloads.each do |payload|
      it "round-trips payload #{payload.empty? ? '(empty)' : payload}" do
        encoded = Runar::SDK::State.serialize_state(fields, { 'b' => payload })
        decoded = Runar::SDK::State.deserialize_state(fields, encoded)

        expect(decoded['b']).to eq(payload)
      end
    end
  end

  # ---------------------------------------------------------------------------
  # S1 — constructor-arg splice/restore round-trip
  # ---------------------------------------------------------------------------

  describe 'S1: ByteString constructor arg' do
    # Template: OP_DUP <1-byte ctor slot placeholder> OP_SWAP
    let(:artifact) do
      Runar::SDK::RunarArtifact.from_hash(
        'contractName' => 'CtorByteString',
        'abi' => {
          'constructor' => { 'params' => [{ 'name' => 'b', 'type' => 'ByteString' }] },
          'methods' => []
        },
        'script' => 'ab007c',
        'stateFields' => [],
        'constructorSlots' => [{ 'paramIndex' => 0, 'byteOffset' => 1 }]
      )
    end

    ctor_payloads.each do |payload|
      it "round-trips payload #{payload}" do
        contract        = Runar::SDK::RunarContract.new(artifact, [payload])
        locking_script  = contract.get_locking_script
        restored        = Runar::SDK::ScriptUtils.extract_constructor_args(artifact, locking_script)

        expect(restored['b']).to eq(payload)
      end
    end
  end
end
