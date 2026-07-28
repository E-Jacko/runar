# frozen_string_literal: true

require 'spec_helper'
require 'runar/sdk'

# G6 — a nil arg for a ByteString param is only meaningful for the
# auto-computed +allPrevouts+ slot. For any other ByteString param it is a
# caller mistake, and silently substituting the 36*n zero-byte prevouts stub
# hands the contract outpoint bytes where it expected its own value: the tx
# broadcasts and then fails at script execution with an opaque error.
#
# nil for a Sig param (auto-sign) must keep working untouched.
#
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'G6 — nil ByteString call arg is rejected unless it is allPrevouts' do
  # rubocop:enable RSpec/DescribeClass
  let(:caller_address) { '00' * 20 }

  def artifact(byte_string_param_name)
    Runar::SDK::RunarArtifact.from_hash(
      'version' => 'runar-v0.1.0',
      'contractName' => 'NullByteStringArgTest',
      'script' => '51',
      'stateFields' => [{ 'name' => 'count', 'type' => 'bigint', 'index' => 0 }],
      'codeSeparatorIndex' => 0,
      'abi' => {
        'constructor' => { 'params' => [{ 'name' => 'count', 'type' => 'bigint' }] },
        'methods' => [{
          'name' => 'move',
          'isPublic' => true,
          'params' => [
            { 'name' => 'sig', 'type' => 'Sig' },
            { 'name' => byte_string_param_name, 'type' => 'ByteString' },
            { 'name' => '_changePKH', 'type' => 'Ripemd160' },
            { 'name' => '_changeAmount', 'type' => 'bigint' },
            { 'name' => 'txPreimage', 'type' => 'SigHashPreimage' }
          ]
        }]
      }
    )
  end

  def deploy(art)
    contract = Runar::SDK::RunarContract.new(art, [0])
    signer   = Runar::SDK::MockSigner.new(address: caller_address)
    provider = Runar::SDK::MockProvider.new(network: 'testnet')
    provider.add_utxo(signer.get_address, Runar::SDK::Utxo.new(
                                            txid: 'aa' * 32, output_index: 0, satoshis: 100_000,
                                            script: "76a914#{'00' * 20}88ac"
                                          ))
    contract.deploy(provider, signer, Runar::SDK::DeployOptions.new(satoshis: 50_000))
    provider.add_utxo(signer.get_address, Runar::SDK::Utxo.new(
                                            txid: 'bb' * 32, output_index: 1, satoshis: 100_000,
                                            script: "76a914#{'00' * 20}88ac"
                                          ))
    [contract, provider, signer]
  end

  it 'rejects a nil ByteString arg for an ordinary user param, naming it' do
    contract, provider, signer = deploy(artifact('memo'))
    expect { contract.prepare_call('move', [nil, nil], provider, signer) }
      .to raise_error(ArgumentError, /memo/)
  end

  it 'still auto-resolves a nil allPrevouts arg' do
    contract, provider, signer = deploy(artifact('allPrevouts'))
    expect { contract.prepare_call('move', [nil, nil], provider, signer) }.not_to raise_error
  end

  it 'still auto-signs a nil Sig arg' do
    contract, provider, signer = deploy(artifact('memo'))
    expect { contract.prepare_call('move', [nil, 'deadbeef'], provider, signer) }.not_to raise_error
  end
end
