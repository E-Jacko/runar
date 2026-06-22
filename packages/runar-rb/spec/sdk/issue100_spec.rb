# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'
require 'json'
require 'open3'
require 'tmpdir'

# Issue #100: a terminal method that reads variable-length (ByteString) state
# must receive _codePart in its unlocking script. Without it the on-chain
# var-length deserialization is skipped and the read returns the deploy-time
# initial value instead of the live state.
#
# codePart is ~472 bytes, so its push begins with PUSHDATA2 (0x4d); without the
# fix the unlock would begin with the ~72-byte opSig push (0x48).
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'Issue #100 — terminal var-len state read gets _codePart' do
  # rubocop:enable RSpec/DescribeClass
  SRC = <<~TS
    import { StatefulSmartContract, assert, substr } from 'runar-lang';
    import type { ByteString } from 'runar-lang';
    class StateRead extends StatefulSmartContract {
      s: ByteString;
      constructor(s: ByteString) { super(s); this.s = s; }
      public update(ns: ByteString): void { this.s = ns; }
      public termCheck(expected: ByteString): void { assert(substr(this.s, 8n, 20n) === expected); }
    }
  TS

  # Compile via the Ruby compiler CLI; skip cleanly if the repo layout/CLI is
  # unavailable (keeps the SDK gem's spec run self-contained).
  def compile_state_read
    repo_root = File.expand_path('../../../..', __dir__)
    cli = File.join(repo_root, 'compilers', 'ruby', 'bin', 'runar-compiler-ruby')
    return nil unless File.exist?(cli)

    src_path = File.join(Dir.tmpdir, 'StateRead.runar.ts')
    File.write(src_path, SRC)
    out, _err, status = Open3.capture3('ruby', cli, '--source', src_path)
    status.success? ? out : nil
  end

  # Parse input[0]'s unlocking-script hex out of a raw transaction hex.
  def input0_unlock(tx_hex)
    i = 8 # advance past the 4-byte version
    i += 2 # input count varint (single input)
    i += 64 + 8 # txid (32) + vout (4)
    slen = tx_hex[i, 2].to_i(16)
    i += 2
    if slen == 0xfd
      slen = (tx_hex[i + 2, 2].to_i(16) * 256) + tx_hex[i, 2].to_i(16)
      i += 4
    end
    tx_hex[i, slen * 2]
  end

  it 'marks the ABI method usesCodePart and prefixes the unlock with codePart' do
    compiled = compile_state_read
    skip 'Ruby compiler CLI unavailable' if compiled.nil?

    artifact = Runar::SDK::RunarArtifact.from_json(compiled)
    term = artifact.abi.methods.find { |m| m.name == 'termCheck' }
    expect(term.uses_code_part).to be(true)

    signer   = Runar::SDK::LocalSigner.new(('00' * 31) + '03')
    provider = Runar::SDK::MockProvider.new
    provider.add_utxo(
      signer.get_address,
      Runar::SDK::Utxo.new(
        txid: 'aa' * 32, output_index: 0, satoshis: 500_000,
        script: '76a914' + ('00' * 20) + '88ac'
      )
    )

    init = ('00' * 8) + ('cc' * 20)
    live = ('11' * 8) + ('dd' * 20)
    contract = Runar::SDK::RunarContract.new(artifact, [init])
    contract.connect(provider, signer)
    contract.deploy
    contract.call('update', [live])
    contract.call('termCheck', ['dd' * 20])

    unlock = input0_unlock(provider.get_broadcasted_txs.last)
    # PUSHDATA2 (0x4d) prefix => codePart push leads the unlock (issue #100).
    expect(unlock[0, 2]).to eq('4d')
  end
end
