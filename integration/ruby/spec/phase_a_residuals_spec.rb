# frozen_string_literal: true

# Phase A residual contracts — deploy+spend (Ruby SDK).

require 'spec_helper'

RSpec.describe 'Phase A residuals' do # rubocop:disable RSpec/DescribeClass
  def deploy_call(path, ctor, method, args, sats: 50_000)
    artifact = compile_contract(path)
    contract = Runar::SDK::RunarContract.new(artifact, ctor)
    provider = create_provider
    wallet = create_funded_wallet(provider)
    txid, = contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: sats))
    expect(txid.length).to eq(64)
    call_txid, = contract.call(method, args, provider, wallet[:signer])
    expect(call_txid.length).to eq(64)
    [contract, call_txid]
  end

  it 'BranchMergedLocals' do
    deploy_call(
      'integration/contracts/constructs/BranchMergedLocals.runar.ts',
      [10, 20], 'bid', [99, 1]
    )
  end

  it 'CondWriteMultiField' do
    deploy_call(
      'integration/contracts/constructs/CondWriteMultiField.runar.ts',
      [1, 2], 'bump', [1]
    )
  end

  it 'ConditionalDataOutput' do
    payload = '6a09' + '6273766d2d74657374'
    deploy_call(
      'integration/contracts/constructs/ConditionalDataOutput.runar.ts',
      [0], 'pay', [true, payload], sats: 20_000
    )
  end

  it 'StateByteString1B' do
    deploy_call(
      'integration/contracts/constructs/StateByteString1B.runar.ts',
      ['05'], 'setTag', ['ab'], sats: 10_000
    )
  end

  it 'RawOutput' do
    artifact = compile_contract('integration/contracts/outputs/RawOutput.runar.ts')
    provider = create_provider
    wallet = create_funded_wallet(provider)
    contract = Runar::SDK::RunarContract.new(artifact, [0])
    p2pkh = "76a914#{wallet[:pub_key_hash]}88ac"
    contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: 50_000))
    txid, = contract.call('sendToScript', [p2pkh], provider, wallet[:signer])
    expect(txid.length).to eq(64)
  end

  it 'MultiSig2of3 same-key SDK call' do
    artifact = compile_contract('integration/contracts/crypto/MultiSig2of3.runar.ts')
    provider = create_provider
    wallet = create_funded_wallet(provider)
    other = create_wallet
    contract = Runar::SDK::RunarContract.new(
      artifact,
      [wallet[:pub_key_hex], wallet[:pub_key_hex], other[:pub_key_hex]]
    )
    contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: 5000))
    txid, = contract.call('unlock', [nil, nil], provider, wallet[:signer])
    expect(txid.length).to eq(64)
  end
end
