"""
Counter integration test -- stateful contract (SDK Deploy/Call path).

Counter is a StatefulSmartContract with a single mutable property `count`.
Methods: increment(), decrement().
"""

import pytest
from conftest import (
    compile_contract, create_provider, create_funded_wallet,
)
from runar.sdk import RunarContract, CallOptions, DeployOptions


class TestCounter:

    def test_increment(self):
        """Deploy with count=0, call increment, verify count=1."""
        artifact = compile_contract("examples/ts/stateful-counter/Counter.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        txid, _ = contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=5000))
        assert txid
        assert len(txid) == 64

        call_txid, _ = contract.call(
            "increment", [], provider, wallet["signer"],
        )
        assert call_txid

    def test_chain_increments(self):
        """Chain increments: 0 -> 1 -> 2."""
        artifact = compile_contract("examples/ts/stateful-counter/Counter.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=5000))

        contract.call(
            "increment", [], provider, wallet["signer"],
        )

        contract.call(
            "increment", [], provider, wallet["signer"],
        )

    def test_increment_then_decrement(self):
        """Increment then decrement: 0 -> 1 -> 0."""
        artifact = compile_contract("examples/ts/stateful-counter/Counter.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=5000))

        contract.call(
            "increment", [], provider, wallet["signer"],
        )

        contract.call(
            "decrement", [], provider, wallet["signer"],
        )

    def test_reject_wrong_state(self):
        """Claiming count=99 instead of 1 after increment should fail."""
        artifact = compile_contract("examples/ts/stateful-counter/Counter.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=5000))

        # A negative test must prove the NODE rejected this spend.
        # pytest.raises(Exception) catches anything at all, including the
        # SDK declining to build the transaction, so record the broadcast
        # count and assert the failing call actually reached consensus.
        broadcasts_before_0 = provider.broadcast_attempts
        with pytest.raises(Exception):
            contract.call(
                "increment", [], provider, wallet["signer"],
                CallOptions(new_state={"count": 99}),
            )
        assert provider.broadcast_attempts > broadcasts_before_0, (
            "the rejected call must have been broadcast to the node, "
            "not refused by the SDK before a transaction was built"
        )

    def test_reject_decrement_from_zero(self):
        """Decrement from 0 should fail (assert(count > 0))."""
        artifact = compile_contract("examples/ts/stateful-counter/Counter.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(provider, wallet["signer"], DeployOptions(satoshis=5000))

        # A negative test must prove the NODE rejected this spend.
        # pytest.raises(Exception) catches anything at all, including the
        # SDK declining to build the transaction, so record the broadcast
        # count and assert the failing call actually reached consensus.
        broadcasts_before_1 = provider.broadcast_attempts
        with pytest.raises(Exception):
            contract.call(
                "decrement", [], provider, wallet["signer"],
                CallOptions(new_state={"count": -1}),
            )

        assert provider.broadcast_attempts > broadcasts_before_1, (
            "the rejected call must have been broadcast to the node, "
            "not refused by the SDK before a transaction was built"
        )