"""Phase A residual contracts — deploy+spend on regtest (Python SDK)."""

from __future__ import annotations

from conftest import compile_contract, create_provider, create_funded_wallet, create_wallet
from runar.sdk import RunarContract, DeployOptions


def _deploy_call(path, ctor, method, args, sats=50000):
    artifact = compile_contract(path)
    contract = RunarContract(artifact, ctor)
    provider = create_provider()
    wallet = create_funded_wallet(provider)
    txid, _ = contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=sats))
    assert len(txid) == 64
    call_txid, _ = contract.call(method, args, provider, wallet["signer"])
    assert call_txid and len(call_txid) == 64
    return contract, call_txid, artifact


class TestPhaseAResiduals:
    def test_branch_merged_locals(self):
        _deploy_call(
            "integration/contracts/constructs/BranchMergedLocals.runar.ts",
            [10, 20],
            "bid",
            [99, 1],
        )

    def test_cond_write_multi_field(self):
        _deploy_call(
            "integration/contracts/constructs/CondWriteMultiField.runar.ts",
            [1, 2],
            "bump",
            [1],
        )

    def test_conditional_data_output(self):
        payload = "6a09" + "6273766d2d74657374"
        _deploy_call(
            "integration/contracts/constructs/ConditionalDataOutput.runar.ts",
            [0],
            "pay",
            [True, payload],
            sats=20000,
        )

    def test_state_bytestring_1b(self):
        _deploy_call(
            "integration/contracts/constructs/StateByteString1B.runar.ts",
            ["05"],
            "setTag",
            ["ab"],
            sats=10000,
        )

    def test_raw_output(self):
        provider = create_provider()
        w = create_funded_wallet(provider)
        artifact = compile_contract("integration/contracts/outputs/RawOutput.runar.ts")
        contract = RunarContract(artifact, [0])
        p2pkh = "76a914" + w["pubKeyHash"] + "88ac"
        contract.deploy(provider, w["signer"], DeployOptions(satoshis=50000))
        txid, _ = contract.call("sendToScript", [p2pkh], provider, w["signer"])
        assert len(txid) == 64

    def test_multisig_same_key_sdk_call(self):
        """SDK Call with pk1=pk2=signer (distinct pk3). Multi-key PrepareCall is TS/Go."""
        artifact = compile_contract("integration/contracts/crypto/MultiSig2of3.runar.ts")
        provider = create_provider()
        w = create_funded_wallet(provider)
        other = create_wallet()
        contract = RunarContract(
            artifact, [w["pubKeyHex"], w["pubKeyHex"], other["pubKeyHex"]]
        )
        contract.deploy(provider, w["signer"], DeployOptions(satoshis=5000))
        txid, _ = contract.call("unlock", [None, None], provider, w["signer"])
        assert len(txid) == 64
