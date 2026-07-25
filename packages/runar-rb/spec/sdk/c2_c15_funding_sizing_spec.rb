# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# Findings C2 + C15 — call funding selection must size the fee against the
# contract/covenant INPUT's unlock bytes (C2) and against ALL outputs, not just
# the single continuation (C15). `estimate_deploy_fee` / `select_utxos` gained
# `extra_input_bytes:` (C2) and `extra_output_bytes:` (C15) keyword params (the
# serialized size of the non-P2PKH contract input(s) and the framing of the
# multi-output / raw / data outputs beyond the one already counted via
# `locking_script_byte_len`); `prepare_call` computes them so a contract call
# does not stop one UTXO short — which, after finding C3, would then be rejected
# as underfunded rather than silently stranding funds. Deploy and existing
# single-output callers pass nothing (defaults 0) and are byte-for-byte unchanged.
#
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'Runar::SDK funding fee sizing (C2 + C15)' do
  # rubocop:enable RSpec/DescribeClass

  GENESIS_PKH2   = '62e907b15cbf27d5425399ebf6f0fb50ebb88f18'.freeze
  GENESIS_SCRIPT2 = "76a914#{GENESIS_PKH2}88ac".freeze

  def make_utxo(txid, satoshis, index: 0)
    Runar::SDK::Utxo.new(
      txid: txid,
      output_index: index,
      satoshis: satoshis,
      script: GENESIS_SCRIPT2
    )
  end

  describe 'estimate_deploy_fee — extra byte params' do
    it 'adds extra_output_bytes to the fee (C15)' do
      base    = Runar::SDK.estimate_deploy_fee(1, 100, 1000) # 1000 sat/KB, no extra
      with_out = Runar::SDK.estimate_deploy_fee(1, 100, 1000, extra_output_bytes: 5000)
      expect(with_out).to be > base
      # 5000 extra bytes at 1000 sat/KB == 5000 sats more (exact: *1000/1000).
      expect(with_out - base).to eq(5000)
    end

    it 'adds extra_input_bytes to the fee (C2)' do
      base   = Runar::SDK.estimate_deploy_fee(1, 100, 1000)
      with_in = Runar::SDK.estimate_deploy_fee(1, 100, 1000, extra_input_bytes: 4000)
      expect(with_in).to be > base
      # 4000 extra bytes at 1000 sat/KB == 4000 sats more.
      expect(with_in - base).to eq(4000)
    end

    it 'leaves the fee unchanged when both extras are 0 (deploy path)' do
      base   = Runar::SDK.estimate_deploy_fee(1, 100, 1000)
      zeros  = Runar::SDK.estimate_deploy_fee(1, 100, 1000, extra_input_bytes: 0, extra_output_bytes: 0)
      expect(zeros).to eq(base)
    end
  end

  describe 'select_utxos — extra byte params tip coin selection' do
    it 'picks more coins when extra output bytes tip the fee over the single-coin edge (C15)' do
      utxos = [make_utxo('aa' * 32, 10_000), make_utxo('bb' * 32, 10_000)]
      # Target 9_000 at 1000 sat/KB. With no extra output bytes a single 10_000
      # coin covers 9_000 + a 226-sat fee -> 1 coin. Adding 2_000 output bytes
      # (2_000 sats of fee) pushes the requirement past 10_000 -> 2 coins needed.
      few  = Runar::SDK.select_utxos(utxos, 9_000, 25, fee_rate: 1000)
      more = Runar::SDK.select_utxos(utxos, 9_000, 25, fee_rate: 1000, extra_output_bytes: 2_000)
      expect(few.length).to eq(1)
      expect(more.length).to eq(2)
    end

    it 'picks more coins when extra input bytes tip the fee over the single-coin edge (C2)' do
      utxos = [make_utxo('cc' * 32, 10_000), make_utxo('dd' * 32, 10_000)]
      few  = Runar::SDK.select_utxos(utxos, 9_000, 25, fee_rate: 1000)
      more = Runar::SDK.select_utxos(utxos, 9_000, 25, fee_rate: 1000, extra_input_bytes: 2_000)
      expect(few.length).to eq(1)
      expect(more.length).to eq(2)
    end
  end
end
