# frozen_string_literal: true

require 'spec_helper'
require 'tmpdir'
require 'runar/sdk'

# Deep-review follow-on (SDK funds bug, separate from the C20/C27 compiler
# cluster): the stateful CALL path must build the state-continuation output at
# the amount the contract's explicit +add_output(<sats>, ...)+ specifies — NOT
# default it to the spent input's value.
#
# The ANF interpreter already records the add_output satoshis (finding G1 reads
# it, but ONLY on the raw-output-present branch). A stateful method whose sole
# continuation is +add_output(1000, @count)+ therefore had its continuation
# built at the input value (e.g. 1 sat), so the covenant's hashOutputs binding
# rejects the spend — funds stranded. This generalizes G1 to the no-raw
# single-continuation path.
#
# Ruby ships no ScriptVM, so this test asserts the built call tx's continuation
# output (index 0) carries the add_output amount (the strongest available
# verification per the port spec).
#
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'SDK derives state-continuation satoshis from an explicit add_output(N)' do
  # rubocop:enable RSpec/DescribeClass
  let(:caller_address) { '00' * 20 }
  let(:caller_pub_key) { '02' + ('00' * 32) }

  # A stateful method whose ONLY output is +add_output(1000, @count)+ (mirrors
  # the TS reference SatCounter). Deployed at 1 sat, so the pre-fix behaviour
  # (continuation defaults to the input value) yields 1, and the fix yields 1000.
  SAT_COUNTER_SRC = <<~RUBY
    require 'runar'

    class SatCounter < Runar::StatefulSmartContract
      prop :count, Bigint

      def initialize(count)
        super(count)
        @count = count
      end

      runar_public
      def inc
        @count = @count + 1
        add_output(1000, @count)
      end
    end
  RUBY

  def load_artifact(dir)
    # Make the in-tree Ruby compiler frontend loadable so we exercise the REAL
    # artifact (ANF with a single add_output), not a hand-written one.
    compiler_lib = File.expand_path('../../../../compilers/ruby/lib', __dir__)
    $LOAD_PATH.unshift(compiler_lib) unless $LOAD_PATH.include?(compiler_lib)
    require 'runar_compiler'
    path = File.join(dir, 'SatCounter.runar.rb')
    File.write(path, SAT_COUNTER_SRC)
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

  it 'builds the continuation at 1000 sats (the add_output amount), not the 1-sat input value' do
    Dir.mktmpdir do |dir|
      contract = Runar::SDK::RunarContract.new(load_artifact(dir), [5])
      provider = Runar::SDK::MockProvider.new
      signer   = Runar::SDK::MockSigner.new(pub_key_hex: caller_pub_key, address: caller_address)
      contract.connect(provider, signer)

      # Fund the caller for deploy + call fees + the 999-sat continuation top-up.
      provider.add_utxo(
        caller_address,
        Runar::SDK::Utxo.new(txid: 'ee' * 32, output_index: 0, satoshis: 1_000_000,
                             script: "76a914#{caller_address}88ac")
      )

      # Deploy at 1 sat; the call's add_output(1000) must OVERRIDE the input value.
      contract.deploy(provider, signer, Runar::SDK::DeployOptions.new(satoshis: 1))
      provider.add_utxo(
        caller_address,
        Runar::SDK::Utxo.new(txid: 'ff' * 32, output_index: 0, satoshis: 1_000_000,
                             script: "76a914#{caller_address}88ac")
      )

      # NO satoshis option — the SDK must derive 1000 from the add_output.
      contract.call('inc', [])

      # State advanced 5 -> 6 (@count = @count + 1).
      expect(contract.get_state).to eq('count' => 6)

      call_tx_hex = provider.get_broadcasted_txs.last
      outputs     = parse_outputs(call_tx_hex)

      # Continuation is output index 0 (no raw output precedes it); change follows.
      expect(outputs.length).to eq(2)
      expect(outputs[0][:satoshis]).to eq(1000)
      expect(outputs[0][:script]).to include('6a') # codePart + OP_RETURN + state

      # The SDK tracks the continuation UTXO at its real 1000-sat value.
      utxo = contract.get_utxo
      expect(utxo.output_index).to eq(0)
      expect(utxo.satoshis).to eq(1000)
    end
  end
end
