# frozen_string_literal: true

# PrivateHelperOutputs integration test -- 2026-04-30 audit regression
# (F1 + F3).
#
# The contract delegates state mutation, addDataOutput, and addOutput to
# private helpers. Before the F1 fix the auto-injection was a shallow
# scan of the public method body, so these methods were silently
# classified as terminal and the deploy + call cycle would fail.
#
# Mirrors the TS / Go / Rust / Python integration tests for the same
# contract.

require 'spec_helper'

# Compile an inline TypeScript source string to a RunarArtifact via the
# reference TS compiler (Node.js). Mirrors data_outputs_spec.rb.
def compile_source_inline(source, file_name)
  script = <<~JS
    (async () => {
      const { compile } = await import('#{PROJECT_ROOT}/packages/runar-compiler/dist/index.js');
      const result = compile(#{source.inspect}, { fileName: #{file_name.inspect} });
      if (!result.success) { console.error(JSON.stringify(result.diagnostics)); process.exit(1); }
      const json = JSON.stringify(result.artifact, (k, v) => typeof v === 'bigint' ? v.toString() + 'n' : v);
      process.stdout.write(json);
    })();
  JS

  node_bin = ENV['NODE_BIN'] || `which node 2>/dev/null`.strip
  node_bin = 'node' if node_bin.empty?
  output = `#{node_bin} -e #{Shellwords.escape(script)} 2>&1`
  status = Process.last_status
  raise "Compilation failed for #{file_name}:\n#{output}" unless status&.success?

  Runar::SDK::RunarArtifact.from_json(output)
end

# Inline private-helper variant whose `record()` helper emits a 1-satoshi
# (not 0) data output. The CI regtest node runs with acceptnonstdtxn=0
# (oracle hardening, PR #49) and rejects 0-satoshi OP_RETURN outputs as
# "dust" at sendrawtransaction. The shared conformance contract
# (examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts) is
# deliberately left at 0n so its cross-tier hex goldens stay frozen; this
# inline source preserves the exact "data output routed through a private
# helper, broadcast to a live node" assertion without that golden churn.
PRIVATE_HELPER_LOG_SOURCE = <<~TS.freeze
  import { StatefulSmartContract, ByteString, assert } from 'runar-lang';

  export class PrivateHelperLog extends StatefulSmartContract {
      counter: bigint;

      constructor(counter: bigint) {
          super(counter);
          this.counter = counter;
      }

      private record(payload: ByteString): void {
          this.addDataOutput(1n, payload);
      }

      public log(payload: ByteString): void {
          this.record(payload);
          assert(true);
      }
  }
TS

RSpec.describe 'PrivateHelperOutputs' do # rubocop:disable RSpec/DescribeClass
  let(:source_path) { 'examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts' }

  it 'chains three commit() calls — each spends the previous continuation UTXO' do
    # Failure here means the runtime hashOutputs hash didn't match the
    # compiled continuation, which is exactly what F1's shallow-scan
    # miss would produce for state-mutation routed through a private
    # helper.
    artifact = compile_contract(source_path)
    contract = Runar::SDK::RunarContract.new(artifact, [0])

    provider = create_provider
    wallet   = create_funded_wallet(provider)

    contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: 5000))

    3.times do |i|
      txid, _state = contract.call(
        'commit', [], provider, wallet[:signer],
        Runar::SDK::CallOptions.new(new_state: { 'counter' => i + 1 })
      )
      expect(txid).to be_truthy, "commit ##{i + 1}: empty txid"
    end
  end

  it 'log() routes a data output through a private helper' do
    artifact = compile_source_inline(PRIVATE_HELPER_LOG_SOURCE, 'PrivateHelperLog.runar.ts')
    contract = Runar::SDK::RunarContract.new(artifact, [0])

    provider = create_provider
    wallet   = create_funded_wallet(provider)

    contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: 5000))

    # OP_RETURN-style payload (0x6a + 7-byte ASCII "hello!").
    payload = '6a0768656c6c6f21'
    txid, _state = contract.call(
      'log', [payload], provider, wallet[:signer],
    )
    expect(txid).to be_truthy
  end
end
