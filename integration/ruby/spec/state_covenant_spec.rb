# frozen_string_literal: true

# StateCovenant integration test -- stateful covenant combining Baby Bear field
# arithmetic, Merkle proof verification, and hash256 batch data binding.
#
# Deploys and advances the covenant on a real regtest node. Tests both valid
# state transitions and on-chain rejection of invalid inputs.

require 'spec_helper'

BB_PRIME = 2_013_265_921

def bb_mul_field(a, b)
  (a * b) % BB_PRIME
end

def hex_sha256(hex_data)
  data = [hex_data].pack('H*')
  Digest::SHA256.hexdigest(data)
end

def hex_hash256(hex_data)
  hex_sha256(hex_sha256(hex_data))
end

def hex_state_root(n)
  hex_sha256(format('%02x', n))
end

def hex_zeros32
  '00' * 32
end

def build_hex_merkle_tree(leaves)
  level = leaves.dup
  layers = [level.dup]

  while level.length > 1
    next_level = []
    (0...level.length).step(2) do |i|
      next_level << hex_sha256(level[i] + level[i + 1])
    end
    level = next_level
    layers << level.dup
  end

  { root: level[0], layers: layers, leaves: leaves }
end

def merkle_get_proof(tree, index)
  siblings = []
  idx = index
  (0...tree[:layers].length - 1).each do |d|
    siblings << tree[:layers][d][idx ^ 1]
    idx >>= 1
  end
  proof = siblings.join
  [tree[:leaves][index], proof]
end

SC_LEAF_IDX = 3

def sc_test_tree
  @sc_test_tree ||= begin
    leaves = (0...16).map { |i| hex_sha256(format('%02x', i)) }
    build_hex_merkle_tree(leaves)
  end
end

def build_call_args(pre_state_root, new_block_number)
  tree = sc_test_tree
  new_state_root = hex_state_root(new_block_number)
  batch_data_hash = hex_hash256(pre_state_root + new_state_root)
  proof_a = 1_000_000
  proof_b = 2_000_000
  proof_c = bb_mul_field(proof_a, proof_b)
  leaf, proof = merkle_get_proof(tree, SC_LEAF_IDX)

  [
    new_state_root,      # newStateRoot
    new_block_number,    # newBlockNumber
    batch_data_hash,     # batchDataHash
    pre_state_root,      # preStateRoot
    proof_a,             # proofFieldA
    proof_b,             # proofFieldB
    proof_c,             # proofFieldC
    leaf,                # merkleLeaf
    proof,               # merkleProof
    SC_LEAF_IDX          # merkleIndex
  ]
end

def deploy_state_covenant
  tree = sc_test_tree
  artifact = compile_contract('examples/ts/state-covenant/StateCovenant.runar.ts')
  contract = Runar::SDK::RunarContract.new(artifact, [hex_zeros32, 0, tree[:root]])

  provider = create_provider
  wallet = create_funded_wallet(provider)

  txid, _tx = contract.deploy(provider, wallet[:signer], Runar::SDK::DeployOptions.new(satoshis: 10_000))
  expect(txid).to be_truthy
  expect(txid.length).to eq(64)

  [contract, wallet]
end

RSpec.describe 'StateCovenant' do # rubocop:disable RSpec/DescribeClass
  it 'deploys with initial state' do
    deploy_state_covenant
  end

  it 'advances state with valid inputs' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    args = build_call_args(hex_zeros32, 1)
    txid, _tx = contract.call('advanceState', args, provider, wallet[:signer])
    expect(txid).to be_truthy
  end

  it 'chains multiple state advances: 0 -> 1 -> 2 -> 3' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    pre = hex_zeros32
    (1..3).each do |block|
      args = build_call_args(pre, block)
      txid, _tx = contract.call('advanceState', args, provider, wallet[:signer])
      expect(txid).to be_truthy
      pre = hex_state_root(block)
    end
  end

  it 'rejects wrong pre-state root' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    args = build_call_args(hex_zeros32, 1)
    # Replace preStateRoot (index 3) with a wrong value
    args[3] = 'ff' + hex_zeros32[2..]

    expect do
      contract.call('advanceState', args, provider, wallet[:signer])
    end.to raise_error(RuntimeError)
  end

  it 'rejects non-increasing block number' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    # First advance to block 1
    args1 = build_call_args(hex_zeros32, 1)
    contract.call('advanceState', args1, provider, wallet[:signer])

    # Try to advance to block 0 (not increasing)
    pre = hex_state_root(1)
    args2 = build_call_args(pre, 0)
    args2[1] = 0 # force block number 0

    expect do
      contract.call('advanceState', args2, provider, wallet[:signer])
    end.to raise_error(RuntimeError)
  end

  it 'rejects invalid Baby Bear proof' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    args = build_call_args(hex_zeros32, 1)
    args[6] = 99_999 # wrong proofFieldC

    expect do
      contract.call('advanceState', args, provider, wallet[:signer])
    end.to raise_error(RuntimeError)
  end

  it 'rejects invalid Merkle proof' do
    contract, wallet = deploy_state_covenant
    provider = create_provider

    args = build_call_args(hex_zeros32, 1)
    # wrong merkleLeaf
    args[7] = 'aa' + hex_zeros32[2..]

    expect do
      contract.call('advanceState', args, provider, wallet[:signer])
    end.to raise_error(RuntimeError)
  end
end
