# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# Deep-review finding G1 (P1) — spending a method that calls
# +add_raw_output(...)+ via the SDK must build a transaction whose outputs
# match the covenant's +hashOutputs+ continuation, or input 0's OP_VERIFY fails
# and the funds are stuck.
#
# The shipped example +RawOutputTest#send_to_script+ emits, in SOURCE order:
#
#     add_raw_output(1000, script_bytes)  # raw output FIRST
#     @count = @count + 1
#     add_output(0, @count)               # state continuation SECOND (0 sats)
#
# The compiler folds BOTH into the continuation +hashOutputs+ in that order, so
# the on-chain output layout the covenant reconstructs is
# +[raw(1000, script_bytes)] [stateContinuation(0)] [change]+. The SDK must
# emit exactly that ordering; emitting only the state continuation (the pre-fix
# behaviour) mismatches hashOutputs -> the auto-injected state-check OP_VERIFY
# rejects.
#
# Ruby ships no ScriptVM, so this test asserts the built call tx's outputs are
# in the required order + values (the strongest available verification per the
# G1 port spec) and that the SDK tracks the continuation at its real index.
#
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'G1 (P1) — add_raw_output spend builds a covenant-valid tx in source order' do
  # rubocop:enable RSpec/DescribeClass

  # The caller-supplied raw locking script: a plain P2PKH (76a914 <20> 88ac),
  # distinct from the change script so we can tell them apart by bytes.
  RAW_SCRIPT = "76a914#{'ab' * 20}88ac"

  CALLER_PKH     = ('00' * 20).freeze
  CALLER_ADDRESS = CALLER_PKH
  CALLER_PUB_KEY = ('02' + ('00' * 32)).freeze

  def load_artifact
    # Make the in-tree Ruby compiler frontend loadable so we exercise the REAL
    # artifact (ANF with add_raw_output before add_output), not a hand-written one.
    compiler_lib = File.expand_path('../../../../compilers/ruby/lib', __dir__)
    $LOAD_PATH.unshift(compiler_lib) unless $LOAD_PATH.include?(compiler_lib)
    require 'runar_compiler'
    repo_root = File.expand_path('../../../..', __dir__)
    path = File.join(repo_root, 'examples', 'ruby', 'add-raw-output', 'RawOutputTest.runar.rb')
    art  = RunarCompiler.compile_from_source(path)
    json = RunarCompiler.artifact_to_json(art)
    Runar::SDK::RunarArtifact.from_json(json)
  end

  # Minimal raw-tx output parser: returns [{ satoshis:, script: }] in tx order.
  def parse_outputs(tx_hex)
    pos = 8 # version (4 bytes)
    in_count, adv = Runar::SDK.read_varint_hex(tx_hex, pos)
    pos += adv
    in_count.times do
      pos += 72 # prev txid (32) + vout (4) = 72 hex chars
      slen, adv = Runar::SDK.read_varint_hex(tx_hex, pos)
      pos += adv + slen * 2 + 8 # scriptSig + sequence (4)
    end
    out_count, adv = Runar::SDK.read_varint_hex(tx_hex, pos)
    pos += adv
    Array.new(out_count) do
      sats = [tx_hex[pos, 16]].pack('H*').unpack1('Q<')
      pos += 16
      slen, adv = Runar::SDK.read_varint_hex(tx_hex, pos)
      pos += adv
      script = tx_hex[pos, slen * 2]
      pos += slen * 2
      { satoshis: sats, script: script }
    end
  end

  it 'builds call(send_to_script) outputs as [raw(1000)][state(0)][change] and tracks the continuation at index 1' do
    contract = Runar::SDK::RunarContract.new(load_artifact, [0])
    provider = Runar::SDK::MockProvider.new
    signer   = Runar::SDK::MockSigner.new(pub_key_hex: CALLER_PUB_KEY, address: CALLER_ADDRESS)
    contract.connect(provider, signer)

    # Fund the caller for deploy + call fees.
    provider.add_utxo(
      CALLER_ADDRESS,
      Runar::SDK::Utxo.new(txid: 'ee' * 32, output_index: 0, satoshis: 1_000_000,
                           script: "76a914#{CALLER_ADDRESS}88ac")
    )

    contract.deploy(provider, signer, Runar::SDK::DeployOptions.new(satoshis: 50_000))
    provider.add_utxo(
      CALLER_ADDRESS,
      Runar::SDK::Utxo.new(txid: 'ff' * 32, output_index: 0, satoshis: 1_000_000,
                           script: "76a914#{CALLER_ADDRESS}88ac")
    )

    # The parser camelCases method names (send_to_script -> sendToScript).
    contract.call('sendToScript', [RAW_SCRIPT])

    # State advanced 0 -> 1 (@count = @count + 1).
    expect(contract.get_state).to eq('count' => 1)

    call_tx_hex = provider.get_broadcasted_txs.last
    outputs     = parse_outputs(call_tx_hex)

    # --- Output ordering: [0] raw, [1] state continuation, [2] change. ---
    expect(outputs.length).to eq(3)

    # [0] raw output: 1000 sats, script === the caller-supplied bytes.
    expect(outputs[0][:satoshis]).to eq(1000)
    expect(outputs[0][:script]).to eq(RAW_SCRIPT)

    # [1] state continuation: 0 sats, codePart + OP_RETURN (6a) + serialized count.
    expect(outputs[1][:satoshis]).to eq(0)
    expect(outputs[1][:script]).not_to eq(RAW_SCRIPT)
    expect(outputs[1][:script]).to include('6a')

    # [2] change: a P2PKH output carrying the remainder.
    expect(outputs[2][:script]).to start_with('76a914')
    expect(outputs[2][:script]).to end_with('88ac')
    expect(outputs[2][:satoshis]).to be > 0

    # The SDK tracks the continuation as the next spendable UTXO at index 1
    # (no longer always 0 — the raw output precedes it) with its real 0-sat value.
    utxo = contract.get_utxo
    expect(utxo.output_index).to eq(1)
    expect(utxo.satoshis).to eq(0)
    expect(utxo.script).to eq(outputs[1][:script])
  end
end
