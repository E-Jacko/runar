"""Deep-review SDK follow-on (funds-safety, separate from the C20/C27 compiler
cluster): the stateful CALL path must build the state continuation at the amount
an explicit ``self.add_output(<sats>, ...)`` specifies, NOT default it to the
spent input's value.

The ANF interpreter already records the add_output satoshis (finding G1 reads
it, but ONLY on the raw-output-present branch). A stateful method whose single
continuation is ``add_output(1000, self.count)`` therefore had its continuation
built at the input value (e.g. 1 sat), so the covenant's hashOutputs binding
rejected the spend -- funds stranded. This test pins the no-raw
single-continuation generalization: with NO raw output and NO explicit
``options.satoshis``, the continuation amount comes from the single ANF
``state`` entry (1000), not the input value.
"""

from __future__ import annotations

import json

import pytest

from runar.sdk.contract import RunarContract
from runar.sdk.provider import MockProvider
from runar.sdk.deployment import build_p2pkh_script
from runar.sdk.local_signer import LocalSigner
from runar.sdk.types import RunarArtifact, DeployOptions, Utxo
from runar.sdk.oppushtx import _parse_raw_tx

compiler = pytest.importorskip("runar_compiler.compiler")

DEPLOYER_KEY = "00" * 31 + "05"
CALLER_KEY = "00" * 31 + "06"

# A stateful method whose ONLY output is `self.add_output(1000, self.count)`
# (a single state continuation, no raw output).
SRC = '''from runar import StatefulSmartContract, Bigint, public


class SatCounter(StatefulSmartContract):
    count: Bigint

    def __init__(self, count: Bigint):
        super().__init__(count)
        self.count = count

    @public
    def inc(self):
        self.count = self.count + 1
        self.add_output(1000, self.count)
'''


def _artifact() -> RunarArtifact:
    result = compiler.compile_from_source_str_with_result(SRC, "SatCounter.runar.py")
    errs = [d.message for d in result.diagnostics if d.severity == "error"]
    assert result.artifact is not None, errs
    d = json.loads(compiler.artifact_to_json(result.artifact))
    return RunarArtifact.from_dict(d)


def _funded_signer(provider: MockProvider, key_hex: str, satoshis: int) -> LocalSigner:
    signer = LocalSigner(key_hex)
    # A REAL P2PKH script for this signer. The old fixture
    # ("76a914" + "00"*20 + "88ac") is not spendable by ANY key, so the funding
    # input it produced would be rejected by a node — visible only once
    # MockProvider stopped always-acking (testing-gap remediation Phase A5).
    provider.add_utxo(signer.get_address(), Utxo(
        txid=key_hex[:64],
        output_index=0,
        satoshis=satoshis,
        script=build_p2pkh_script(signer.get_public_key()),
    ))
    return signer


def test_call_derives_continuation_satoshis_from_add_output():
    """Deploy SatCounter at 1 sat, call inc() with NO satoshis option, and assert
    the built call tx's continuation output (index 0) carries the add_output
    amount (1000), not the spent input value (1)."""
    artifact = _artifact()
    provider = MockProvider("testnet")
    deployer = _funded_signer(provider, DEPLOYER_KEY, 500_000)
    caller = _funded_signer(provider, CALLER_KEY, 500_000)

    contract = RunarContract(artifact, [5])
    # Deploy at the minimum (1 sat); the call's add_output(1000) must OVERRIDE it.
    contract.deploy(provider, deployer, DeployOptions(satoshis=1))
    # NO options.satoshis -- the SDK must derive 1000 from the add_output.
    contract.call("inc", [], provider, caller)

    txs = provider.get_broadcasted_txs()
    call_tx = _parse_raw_tx(bytes.fromhex(txs[1]))
    outs = call_tx["outputs"]

    # State advanced 5 -> 6.
    assert contract.get_state()["count"] == 6

    # Continuation output (index 0) must carry the add_output amount (1000),
    # NOT the spent input value (1). This is the RED->GREEN assertion.
    assert outs[0]["satoshis"] == 1000

    # And the SDK tracks the continuation UTXO at that real index + amount.
    assert contract._current_utxo is not None
    assert contract._current_utxo.output_index == 0
    assert contract._current_utxo.satoshis == 1000
