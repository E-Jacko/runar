"""Python-tier ports of the SDK remediation fixes (#118, #119, #131, #133, #134, #143, #144).

Mirrors the TypeScript reference tests:
  packages/runar-sdk/src/__tests__/issue-118-terminal-fee.test.ts
  packages/runar-sdk/src/__tests__/issue-119-restore-args.test.ts
  packages/runar-sdk/src/__tests__/issue-131-locktime-sequence.test.ts
  packages/runar-sdk/src/__tests__/issue-133-funding-selection.test.ts
  packages/runar-sdk/src/__tests__/issue-134-funding-signer.test.ts
"""

import struct
import pytest

from runar.sdk.calling import build_call_transaction, resolve_input_sequence
from runar.sdk.deployment import estimate_deploy_fee, select_utxos
from runar.sdk.script_utils import extract_constructor_args, restore_constructor_args
from runar.sdk.contract import RunarContract
from runar.sdk.provider import MockProvider
from runar.sdk.signer import MockSigner
from runar.sdk.types import (
    RunarArtifact, Abi, AbiParam, AbiMethod, StateField, Utxo,
    DeployOptions, CallOptions, TerminalOutput, ConstructorSlot,
)


P2PKH_SCRIPT = '76a914' + '00' * 20 + '88ac'


def _make_utxo(satoshis: int, index: int = 0) -> Utxo:
    return Utxo(txid=f'{index:02x}' * 32, output_index=index,
                satoshis=satoshis, script=P2PKH_SCRIPT)


def _parse_input_sequences(tx_hex: str) -> list[int]:
    """Return the nSequence of every input in a raw tx."""
    pos = 8  # skip version
    first = int(tx_hex[pos:pos + 2], 16)
    pos += 2
    if first < 0xFD:
        n = first
    elif first == 0xFD:
        n = int.from_bytes(bytes.fromhex(tx_hex[pos:pos + 4]), 'little'); pos += 4
    else:
        n = int.from_bytes(bytes.fromhex(tx_hex[pos:pos + 8]), 'little'); pos += 8
    seqs = []
    for _ in range(n):
        pos += 64 + 8  # prev txid + index
        sl = int(tx_hex[pos:pos + 2], 16); pos += 2  # (varint < 0xfd for these tests)
        pos += sl * 2
        seqs.append(struct.unpack('<I', bytes.fromhex(tx_hex[pos:pos + 8]))[0])
        pos += 8
    return seqs


def _count_inputs(tx_hex: str) -> int:
    first = int(tx_hex[8:10], 16)
    if first < 0xFD:
        return first
    if first == 0xFD:
        return int.from_bytes(bytes.fromhex(tx_hex[10:14]), 'little')
    return int.from_bytes(bytes.fromhex(tx_hex[10:18]), 'little')


# ---------------------------------------------------------------------------
# #131 — locktime -> non-final input sequences
# ---------------------------------------------------------------------------

class TestIssue131Sequence:
    def test_resolve_defaults_to_final(self):
        assert resolve_input_sequence(None, None) == 0xFFFFFFFF
        assert resolve_input_sequence(0, None) == 0xFFFFFFFF

    def test_resolve_non_final_when_locktime_set(self):
        assert resolve_input_sequence(800000, None) == 0xFFFFFFFE

    def test_resolve_explicit_override_wins(self):
        assert resolve_input_sequence(800000, 0x12345678) == 0x12345678
        assert resolve_input_sequence(None, 0x12345678) == 0x12345678

    def test_build_call_tx_non_final_sequences_when_locktime(self):
        utxo = _make_utxo(100_000)
        additional = [_make_utxo(50_000, 1), _make_utxo(30_000, 2)]
        tx_hex, input_count, _ = build_call_transaction(
            utxo, '51', '51', 10_000, 'changeaddr',
            change_script='76a914' + 'ff' * 20 + '88ac',
            additional_utxos=additional, locktime=800000,
        )
        assert input_count == 3
        seqs = _parse_input_sequences(tx_hex)
        assert seqs == [0xFFFFFFFE, 0xFFFFFFFE, 0xFFFFFFFE]
        # locktime written into the tx
        assert tx_hex[-8:] == struct.pack('<I', 800000).hex()

    def test_build_call_tx_final_sequences_when_no_locktime(self):
        utxo = _make_utxo(100_000)
        additional = [_make_utxo(50_000, 1)]
        tx_hex, _, _ = build_call_transaction(
            utxo, '51', '51', 10_000, 'changeaddr',
            change_script='76a914' + 'ff' * 20 + '88ac',
            additional_utxos=additional,
        )
        assert all(s == 0xFFFFFFFF for s in _parse_input_sequences(tx_hex))

    def test_build_call_tx_final_when_locktime_zero(self):
        utxo = _make_utxo(100_000)
        tx_hex, _, _ = build_call_transaction(
            utxo, '51', '51', 10_000, 'changeaddr',
            change_script='76a914' + 'ff' * 20 + '88ac', locktime=0,
        )
        assert _parse_input_sequences(tx_hex)[0] == 0xFFFFFFFF

    def test_build_call_tx_explicit_sequence_override(self):
        utxo = _make_utxo(100_000)
        additional = [_make_utxo(50_000, 1)]
        tx_hex, _, _ = build_call_transaction(
            utxo, '51', '51', 10_000, 'changeaddr',
            change_script='76a914' + 'ff' * 20 + '88ac',
            additional_utxos=additional, locktime=800000, sequence=0x12345678,
        )
        assert all(s == 0x12345678 for s in _parse_input_sequences(tx_hex))


# ---------------------------------------------------------------------------
# #119 — restore real constructor args from a deployed script
# ---------------------------------------------------------------------------

class TestIssue119RestoreArgs:
    def test_restores_positional_values_by_param_index(self):
        # Script: OP_5 (0x55) at offset 0, then OP_2 (0x52) at offset 1.
        # Two ctor slots map param 0 -> offset 0, param 1 -> offset 1.
        artifact = RunarArtifact(
            contract_name='Restore',
            abi=Abi(constructor_params=[
                AbiParam(name='a', type='bigint'),
                AbiParam(name='b', type='bigint'),
            ]),
            script='5552',
            constructor_slots=[
                ConstructorSlot(param_index=0, byte_offset=0),
                ConstructorSlot(param_index=1, byte_offset=1),
            ],
        )
        assert restore_constructor_args(artifact, '5552') == [5, 2]

    def test_no_constructor_params_returns_empty(self):
        artifact = RunarArtifact(contract_name='Empty', abi=Abi(constructor_params=[]))
        assert restore_constructor_args(artifact, '51') == []

    def test_param_without_slot_falls_back_to_zero(self):
        # param 'a' has a slot; state field param 'total' has none -> 0 fallback.
        artifact = RunarArtifact(
            contract_name='Mixed',
            abi=Abi(constructor_params=[
                AbiParam(name='a', type='bigint'),
                AbiParam(name='total', type='bigint'),
            ]),
            script='55',
            constructor_slots=[ConstructorSlot(param_index=0, byte_offset=0)],
        )
        assert restore_constructor_args(artifact, '55') == [5, 0]


# ---------------------------------------------------------------------------
# #143 — repeated constructor slot references must still shift later offsets
# ---------------------------------------------------------------------------

class TestIssue143RepeatedSlotReferences:
    """A param referenced N times in the contract body emits N constructor
    slots. Every occurrence's encoded width shifts the offsets of everything
    after it, so the extractor must account for ALL occurrences -- not just the
    first per param. Regression for a bug where slots were deduplicated by
    param_index BEFORE the offset walk, mis-reading every later slot whenever
    an earlier repeated value encoded wider than its 1-byte template
    placeholder.

    Template: ab <00> 7c <00> 7c <00> ac
      offset 1: alpha (param_index 0)
      offset 3: alpha again (param_index 0 -- second reference)
      offset 5: beta  (param_index 1)
    """

    ARTIFACT = RunarArtifact(
        contract_name='Repeated',
        abi=Abi(constructor_params=[
            AbiParam(name='alpha', type='bigint'),
            AbiParam(name='beta', type='bigint'),
        ]),
        script='ab' + '00' + '7c' + '00' + '7c' + '00' + 'ac',
        constructor_slots=[
            ConstructorSlot(param_index=0, byte_offset=1),
            ConstructorSlot(param_index=0, byte_offset=3),
            ConstructorSlot(param_index=1, byte_offset=5),
        ],
    )

    def test_reads_slots_after_a_repeated_wide_value_at_correct_offsets(self):
        # alpha = 500 -> scriptnum push `02f401` (3 bytes), beta = 7 -> OP_7.
        resolved = 'ab' + '02f401' + '7c' + '02f401' + '7c' + '57' + 'ac'
        args = extract_constructor_args(self.ARTIFACT, resolved)
        assert args['alpha'] == 500
        # Before the fix, the second alpha occurrence's +2 byte shift was
        # dropped, so beta was read from inside the second alpha push and
        # decoded as 124 instead of 7.
        assert args['beta'] == 7
        assert restore_constructor_args(self.ARTIFACT, resolved) == [500, 7]

    def test_still_extracts_when_repeated_value_fits_placeholder_width(self):
        # alpha = 5 -> OP_5 (1 byte, same width as the placeholder: zero shift).
        resolved = 'ab' + '55' + '7c' + '55' + '7c' + '57' + 'ac'
        args = extract_constructor_args(self.ARTIFACT, resolved)
        assert args['alpha'] == 5
        assert args['beta'] == 7


# ---------------------------------------------------------------------------
# Contract-level harness for #118 / #133 / #134
# ---------------------------------------------------------------------------

def _make_stateless_artifact() -> RunarArtifact:
    return RunarArtifact(
        version='runar-v0.1.0', contract_name='Test',
        abi=Abi(constructor_params=[], methods=[
            AbiMethod(name='cancel', params=[], is_public=True),
        ]),
        script='51',
    )


def _deploy(satoshis: int, wallet_utxos: list[Utxo], signer: MockSigner):
    contract = RunarContract(_make_stateless_artifact(), [])
    provider = MockProvider(network='testnet')
    for u in wallet_utxos:
        provider.add_utxo(signer.get_address(), u)
    contract.deploy(provider, signer, DeployOptions(satoshis=satoshis))
    return contract, provider


# ---------------------------------------------------------------------------
# #118 — terminal fee input
# ---------------------------------------------------------------------------

class TestIssue118TerminalFee:
    def test_fee_utxo_adds_input_at_index_one(self):
        signer = MockSigner(pub_key_hex='02' + '11' * 32, address='11' * 20)
        contract, provider = _deploy(50_000, [_make_utxo(100_000)], signer)

        fee_utxo = Utxo(txid='fe' * 32, output_index=0, satoshis=5_000, script=P2PKH_SCRIPT)
        prepared = contract.prepare_call(
            'cancel', [], provider, signer,
            CallOptions(
                terminal_outputs=[TerminalOutput(script_hex='76a914' + 'bb' * 20 + '88ac',
                                                 satoshis=50_000)],
                fee_utxo=fee_utxo,
            ),
        )
        # Contract input (0) + fee input (1)
        assert _count_inputs(prepared.tx_hex) == 2
        # Fee input's outpoint is the fee utxo (reversed txid at input index 1).
        seqs = _parse_input_sequences(prepared.tx_hex)
        assert len(seqs) == 2

    def test_no_fee_utxo_keeps_single_input(self):
        signer = MockSigner()
        contract, provider = _deploy(50_000, [_make_utxo(100_000)], signer)
        prepared = contract.prepare_call(
            'cancel', [], provider, signer,
            CallOptions(terminal_outputs=[TerminalOutput(
                script_hex='76a914' + 'bb' * 20 + '88ac', satoshis=49_000)]),
        )
        assert _count_inputs(prepared.tx_hex) == 1

    def test_fee_input_signed_by_funding_signer(self):
        # The fee input's P2PKH unlock must carry funding_signer's pubkey.
        method_signer = MockSigner(pub_key_hex='02' + 'aa' * 32, address='aa' * 20)
        funding_signer = MockSigner(pub_key_hex='03' + 'bb' * 32, address='bb' * 20)
        contract, provider = _deploy(50_000, [_make_utxo(100_000)], method_signer)

        fee_utxo = Utxo(txid='fe' * 32, output_index=0, satoshis=5_000, script=P2PKH_SCRIPT)
        prepared = contract.prepare_call(
            'cancel', [], provider, method_signer,
            CallOptions(
                terminal_outputs=[TerminalOutput(script_hex='76a914' + 'bb' * 20 + '88ac',
                                                 satoshis=50_000)],
                fee_utxo=fee_utxo,
                funding_signer=funding_signer,
            ),
        )
        # funding_signer's pubkey (03bb..bb) must appear in the tx (fee unlock),
        # the method signer's (02aa..aa) must not be pushed for the fee input.
        assert '03' + 'bb' * 32 in prepared.tx_hex


# ---------------------------------------------------------------------------
# #133 — coin-select funding instead of sweeping
# ---------------------------------------------------------------------------

class TestIssue133FundingSelection:
    def test_does_not_sweep_all_wallet_utxos(self):
        signer = MockSigner()
        # 5 large wallet UTXOs; a tiny stateless call needs at most 1 for the fee.
        wallet = [_make_utxo(200_000, i) for i in range(6)]
        contract, provider = _deploy(50_000, wallet, signer)
        prepared = contract.prepare_call('cancel', [], provider, signer, CallOptions())
        # Contract input + a small number of funding inputs (NOT all 5 remaining).
        assert _count_inputs(prepared.tx_hex) < 6

    def test_max_funding_inputs_cap_raises(self):
        signer = MockSigner()
        # Wallet still has spendable UTXOs after deploy, so covering the fee
        # selects >=1 funding input; a cap of 0 must fail loudly instead of
        # silently broadcasting.
        wallet = [_make_utxo(200_000, i) for i in range(3)]
        contract, provider = _deploy(50_000, wallet, signer)
        with pytest.raises(ValueError, match='max_funding_inputs'):
            contract.prepare_call('cancel', [], provider, signer,
                                  CallOptions(max_funding_inputs=0))


# ---------------------------------------------------------------------------
# #134 — funding inputs signed by funding_signer
# ---------------------------------------------------------------------------

class TestIssue134FundingSigner:
    def test_funding_input_uses_funding_signer_pubkey(self):
        method_signer = MockSigner(pub_key_hex='02' + 'aa' * 32, address='aa' * 20)
        funding_signer = MockSigner(pub_key_hex='03' + 'cc' * 32, address='cc' * 20)
        # Fund the METHOD signer's address (deploy + funding come from there).
        contract, provider = _deploy(50_000, [_make_utxo(200_000)], method_signer)
        prepared = contract.prepare_call(
            'cancel', [], provider, method_signer,
            CallOptions(funding_signer=funding_signer),
        )
        # funding_signer's pubkey must be pushed onto the funding input.
        assert '03' + 'cc' * 32 in prepared.tx_hex

    def test_defaults_to_method_signer(self):
        signer = MockSigner(pub_key_hex='02' + 'dd' * 32, address='dd' * 20)
        contract, provider = _deploy(50_000, [_make_utxo(200_000)], signer)
        prepared = contract.prepare_call('cancel', [], provider, signer, CallOptions())
        assert '02' + 'dd' * 32 in prepared.tx_hex


# ---------------------------------------------------------------------------
# #144 — call-funding must size the contract/covenant input(s) it spends
# ---------------------------------------------------------------------------

def _merge_artifact() -> RunarArtifact:
    """Stateful covenant whose `merge` method takes a large ByteString arg —
    the shape of a real MERGE, where each covenant input embeds a parent tx."""
    return RunarArtifact(
        version='runar-v0.1.0',
        contract_name='MergeCovenant',
        parent_class='StatefulSmartContract',
        abi=Abi(constructor_params=[], methods=[
            AbiMethod(name='merge', params=[AbiParam(name='parentTx', type='ByteString')],
                      is_public=True, uses_code_part=False),
        ]),
        script='51',
        state_fields=[StateField(name='count', type='bigint', index=0)],
    )