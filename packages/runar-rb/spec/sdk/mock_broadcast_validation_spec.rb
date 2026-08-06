# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# Testing-gap remediation Phase A5 (Ruby tier).
#
# The Ruby tier ships NO Bitcoin Script VM — there is no canonical upstream BSV
# Ruby SDK to wrap, and project policy forbids hand-rolling an interpreter
# (root CLAUDE.md, "Off-chain Script VM"). So this spec does NOT claim
# script-level validation. It pins the checks that ARE genuinely available at
# the broadcast boundary and that a real node would also apply:
#
#   1. STRUCTURAL — the payload must actually parse as a Bitcoin transaction.
#   2. NON-VACUITY — at least one spent outpoint must be known to the provider,
#      so the gate can never pass by checking nothing.
#   3. VALUE CONSERVATION — when every input's outpoint is known, the outputs
#      must not exceed the inputs (no satoshis conjured from nowhere).
#   4. SCRIPT-SIZE BOUND — output scripts stay under MAX_SCRIPT_BYTES.
#
# Signature/covenant validity in this tier is proven VERTICALLY instead:
# absolute-hex pins against the other tiers' goldens, plus the on-chain
# integration spends in integration/ruby. See README, "How fund-path tests fail
# closed in the Ruby tier".
RSpec.describe 'Runar::SDK::MockProvider broadcast validation (Phase A5)' do
  ANYONE_CAN_SPEND = '51' # OP_TRUE

  def varint(n)
    if n < 0xFD then format('%02x', n)
    elsif n <= 0xFFFF then 'fd' + [n].pack('v').unpack1('H*')
    elsif n <= 0xFFFF_FFFF then 'fe' + [n].pack('V').unpack1('H*')
    else 'ff' + [n & 0xFFFFFFFF, n >> 32].pack('VV').unpack1('H*')
    end
  end

  # Serialize a minimal one-input transaction spending prev_txid:0.
  def build_tx(prev_txid_display, outputs, script_sig_hex: '')
    tx = +''
    tx << [1].pack('V').unpack1('H*')            # version
    tx << '01'                                   # 1 input
    tx << [prev_txid_display].pack('H*').bytes.reverse.pack('C*').unpack1('H*')
    tx << [0].pack('V').unpack1('H*')            # vout
    tx << varint(script_sig_hex.length / 2)
    tx << script_sig_hex
    tx << 'ffffffff'                             # sequence
    tx << varint(outputs.length)
    outputs.each do |(sats, script_hex)|
      tx << [sats & 0xFFFFFFFF, sats >> 32].pack('VV').unpack1('H*')
      tx << varint(script_hex.length / 2)
      tx << script_hex
    end
    tx << [0].pack('V').unpack1('H*')            # locktime
    tx
  end

  def seed(provider, txid, satoshis, script = ANYONE_CAN_SPEND)
    provider.add_utxo('addr', Runar::SDK::Utxo.new(
                                txid: txid, output_index: 0, satoshis: satoshis, script: script
                              ))
  end

  describe 'default (fail-closed) provider' do
    it 'accepts a well-formed, value-conserving spend of a known outpoint' do
      provider = Runar::SDK::MockProvider.new
      prev = 'aa' * 32
      seed(provider, prev, 10_000)
      txid = provider.broadcast(build_tx(prev, [[9_000, ANYONE_CAN_SPEND]]))

      expect(txid.length).to eq(64)
      expect(provider.last_validated_input_count).to eq(1)
      expect(provider.get_broadcasted_txs.length).to eq(1)
    end

    it 'REJECTS a payload that is not a parseable transaction' do
      provider = Runar::SDK::MockProvider.new
      expect { provider.broadcast('rawhexdata') }
        .to raise_error(Runar::SDK::BroadcastRejected, /not a parseable Bitcoin transaction/)
    end

    it 'REJECTS a transaction whose outputs exceed its known inputs' do
      provider = Runar::SDK::MockProvider.new
      prev = 'bb' * 32
      seed(provider, prev, 1_000)
      expect { provider.broadcast(build_tx(prev, [[5_000, ANYONE_CAN_SPEND]])) }
        .to raise_error(Runar::SDK::BroadcastRejected, /underfunded/)
    end

    it 'REJECTS a transaction none of whose inputs it knows (no vacuous pass)' do
      provider = Runar::SDK::MockProvider.new
      expect { provider.broadcast(build_tx('cc' * 32, [[1_000, ANYONE_CAN_SPEND]])) }
        .to raise_error(Runar::SDK::BroadcastRejected, /checked 0 of 1 input/)
    end

    it 'REJECTS an output script over MAX_SCRIPT_BYTES' do
      provider = Runar::SDK::MockProvider.new
      prev = 'dd' * 32
      seed(provider, prev, 10_000_000)
      huge = '00' * (Runar::SDK::MAX_SCRIPT_BYTES + 1)
      expect { provider.broadcast(build_tx(prev, [[1_000, huge]])) }
        .to raise_error(Runar::SDK::ScriptSizeExceededError)
    end

    it 'chains: a second spend of the first broadcast\'s own output is known' do
      provider = Runar::SDK::MockProvider.new
      prev = 'ee' * 32
      seed(provider, prev, 10_000)
      first = provider.broadcast(build_tx(prev, [[9_000, ANYONE_CAN_SPEND]]))
      second = provider.broadcast(build_tx(first, [[8_000, ANYONE_CAN_SPEND]]))

      expect(second.length).to eq(64)
      expect(provider.last_validated_input_count).to eq(1)
    end
  end

  describe 'the governed opt-out' do
    it 'always_ack skips every check' do
      provider = Runar::SDK::MockProvider.always_ack
      expect(provider.broadcast('rawhexdata').length).to eq(64)
    end

    it 'disable/enable_broadcast_validation toggles the gate' do
      provider = Runar::SDK::MockProvider.new
      expect { provider.broadcast('rawhexdata') }.to raise_error(Runar::SDK::BroadcastRejected)
      provider.disable_broadcast_validation
      expect(provider.broadcast('rawhexdata').length).to eq(64)
      provider.enable_broadcast_validation(true)
      expect { provider.broadcast('rawhexdata') }.to raise_error(Runar::SDK::BroadcastRejected)
    end
  end

  describe 'honest capability statement' do
    it 'does NOT claim script-level validation' do
      # The report deliberately carries no "scripts executed" field: this tier
      # cannot execute Bitcoin Script. If a Ruby ScriptVM ever lands, extend
      # the report rather than silently implying coverage that does not exist.
      provider = Runar::SDK::MockProvider.new
      prev = 'ff' * 32
      seed(provider, prev, 10_000)
      provider.broadcast(build_tx(prev, [[9_000, ANYONE_CAN_SPEND]]))
      report = provider.last_validation_report

      expect(report[:scripts_executed]).to eq(0)
      expect(report[:known_inputs]).to eq(1)
      expect(report[:total_inputs]).to eq(1)
      expect(report[:value_conserved]).to be(true)
    end
  end
end
