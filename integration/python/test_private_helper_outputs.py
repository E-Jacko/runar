"""PrivateHelperOutputs integration test — 2026-04-30 audit regression
(F1 + F3).

The contract delegates state mutation, addDataOutput, and addOutput to
private helpers. Before the F1 fix the auto-injection was a shallow
scan of the public method body, so these methods were silently
classified as terminal and the deploy + call cycle would fail.

Mirrors the TS / Go integration tests for the same contract.
"""

import json
import os
import tempfile

from conftest import (
    compile_contract, create_provider, create_funded_wallet,
)
from runar_compiler.compiler import compile_from_source, artifact_to_json
from runar.sdk import RunarArtifact, RunarContract, DeployOptions


# Inline private-helper variant whose `record()` helper emits a 1-satoshi
# (not 0) data output. The CI regtest node runs with acceptnonstdtxn=0
# (oracle hardening, PR #49) and rejects 0-satoshi OP_RETURN outputs as
# "dust" at sendrawtransaction. The shared conformance contract
# (examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts) is
# deliberately left at 0n so its cross-tier hex goldens stay frozen; this
# inline source preserves the exact "data output routed through a private
# helper, broadcast to a live node" assertion without that golden churn.
LOG_SOURCE = """\
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
"""


def _compile_source(source: str, file_name: str) -> RunarArtifact:
    """Compile inline source to an SDK artifact via a temp file."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=file_name, delete=False, dir=tempfile.gettempdir()
    ) as f:
        f.write(source)
        tmp_path = f.name
    try:
        compiler_artifact = compile_from_source(tmp_path)
        artifact_dict = json.loads(artifact_to_json(compiler_artifact))
        return RunarArtifact.from_dict(artifact_dict)
    finally:
        os.unlink(tmp_path)


class TestPrivateHelperOutputs:

    def test_commit_chain(self):
        """Three sequential commits — each spends the previous
        continuation UTXO. Failure here means the runtime
        hashOutputs hash didn't match the compiled continuation,
        which is exactly what F1's shallow-scan miss would produce
        for state-mutation routed through a private helper."""
        artifact = compile_contract(
            "examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts"
        )
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(
            provider, wallet["signer"], DeployOptions(satoshis=5000)
        )

        for i in range(3):
            txid, _ = contract.call(
                "commit", [], provider, wallet["signer"],
            )
            assert txid, f"commit #{i + 1}: empty txid"

    def test_log_emits_data_output(self):
        """log routes a data output through a private helper —
        verifies the F1 fix's recursive scan picks up
        addDataOutput inside a private method."""
        artifact = _compile_source(LOG_SOURCE, "PrivateHelperLog.runar.ts")
        contract = RunarContract(artifact, [0])

        provider = create_provider()
        wallet = create_funded_wallet(provider)

        contract.deploy(
            provider, wallet["signer"], DeployOptions(satoshis=5000)
        )

        # OP_RETURN-style payload (0x6a + 7-byte ASCII "hello!").
        payload = "6a0768656c6c6f21"
        txid, _ = contract.call(
            "log", [payload], provider, wallet["signer"],
        )
        assert txid
