"""G6 — ``None`` for a ByteString call arg is only meaningful for ``allPrevouts``.

For any other ByteString parameter it is a caller mistake, and silently
substituting the ``36 * n`` zero-byte prevouts stub hands the contract outpoint
bytes where it expected its own value: the transaction broadcasts and then
fails at script execution with an opaque error. Fail at build time instead,
naming the parameter.

``None`` for a ``Sig`` param (auto-sign) must keep working untouched.
"""

import pytest

from runar.sdk.contract import RunarContract
from runar.sdk.provider import MockProvider
from runar.sdk.signer import MockSigner
from runar.sdk.types import (
    Abi, AbiMethod, AbiParam, CallOptions, DeployOptions, RunarArtifact, StateField, Utxo,
)


def _artifact(byte_string_param_name: str) -> RunarArtifact:
    return RunarArtifact(
        version='runar-v0.1.0',
        contract_name='NullByteStringArgTest',
        abi=Abi(
            constructor_params=[AbiParam(name='count', type='bigint')],
            methods=[AbiMethod(name='move', is_public=True, params=[
                AbiParam(name='sig', type='Sig'),
                AbiParam(name=byte_string_param_name, type='ByteString'),
                AbiParam(name='_changePKH', type='Ripemd160'),
                AbiParam(name='_changeAmount', type='bigint'),
                AbiParam(name='txPreimage', type='SigHashPreimage'),
            ])],
        ),
        script='51',
        state_fields=[StateField(name='count', type='bigint', index=0)],
        code_separator_index=0,
    )


def _deploy(artifact: RunarArtifact):
    contract = RunarContract(artifact, [0])
    signer = MockSigner(address='00' * 20)
    provider = MockProvider('testnet')
    provider.add_utxo(signer.get_address(), Utxo(
        txid='aa' * 32, output_index=0, satoshis=100_000,
        script='76a914' + '00' * 20 + '88ac',
    ))
    contract.deploy(provider, signer, DeployOptions(satoshis=50_000))
    provider.add_utxo(signer.get_address(), Utxo(
        txid='bb' * 32, output_index=1, satoshis=100_000,
        script='76a914' + '00' * 20 + '88ac',
    ))
    return contract, provider, signer


def test_none_bytestring_arg_rejected_for_non_prevouts_param():
    contract, provider, signer = _deploy(_artifact('memo'))
    with pytest.raises(ValueError, match='memo'):
        contract.prepare_call('move', [None, None], provider, signer)


def test_none_bytestring_arg_all_prevouts_still_auto_resolves():
    contract, provider, signer = _deploy(_artifact('allPrevouts'))
    contract.prepare_call('move', [None, None], provider, signer)


def test_none_sig_arg_still_auto_signs():
    contract, provider, signer = _deploy(_artifact('memo'))
    contract.prepare_call('move', [None, 'deadbeef'], provider, signer)


def test_none_bytestring_arg_rejected_for_additional_contract_input_args():
    contract, provider, signer = _deploy(_artifact('memo'))
    extra = Utxo(
        txid='cc' * 32, output_index=0, satoshis=5_000,
        script=contract.get_utxo().script,
    )
    opts = CallOptions(
        additional_contract_inputs=[extra],
        additional_contract_input_args=[[None, None]],
    )
    with pytest.raises(ValueError, match='memo'):
        contract.prepare_call('move', [None, 'deadbeef'], provider, signer, opts)
