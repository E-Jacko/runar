"""Issue #106 — EMPTY_SIG marker for OR-CHECKSIG branched authorization
(Python port of the TypeScript reference issue-106-empty-sig.test.ts).

An OR-CHECKSIG method — ``checkSig(sigA, pkA) || checkSig(sigB, pkB)`` — runs
BOTH ``OP_CHECKSIG`` branches (Rúnar lowers ``||`` to the non-lazy
``OP_BOOLOR``). Only the matching branch supplies a real signature; the failing
branch MUST push an empty signature (OP_0) or BIP146 NULLFAIL rejects the spend.

The Python SDK ships no Spend interpreter, so — like the TS RED baseline — these
assertions are at the wire level: the failing branch's push is OP_0 (empty)
under ``[None, EMPTY_SIG]`` and non-empty under ``[None, None]``.
"""

from __future__ import annotations

import json
import warnings

import pytest

from runar.sdk.contract import RunarContract, EMPTY_SIG, is_empty_sig, _encode_arg
from runar.sdk import EMPTY_SIG as EMPTY_SIG_PUBLIC, is_empty_sig as is_empty_sig_public
from runar.sdk.types import RunarArtifact, DeployOptions
from runar.sdk.provider import MockProvider
from runar.sdk.signer import MockSigner

compiler = pytest.importorskip("runar_compiler.compiler")


SRC = """
class OrChecksig extends SmartContract {
  readonly pkA: PubKey;
  readonly pkB: PubKey;
  constructor(pkA: PubKey, pkB: PubKey) { super(pkA, pkB); this.pkA = pkA; this.pkB = pkB; }
  public execute(sigA: Sig, sigB: Sig): void {
    assert(checkSig(sigA, this.pkA) || checkSig(sigB, this.pkB));
  }
}
"""


def _artifact(src: str, file_name: str) -> RunarArtifact:
    result = compiler.compile_from_source_str_with_result(src, file_name)
    errs = [d.message for d in result.diagnostics if d.severity == "error"]
    assert result.artifact is not None, errs
    return RunarArtifact.from_dict(json.loads(compiler.artifact_to_json(result.artifact)))


def _funded_provider(address: str, satoshis: int = 500_000) -> MockProvider:
    from runar.sdk.types import Utxo
    provider = MockProvider("testnet")
    provider.add_utxo(address, Utxo(
        txid="00" * 32, output_index=0, satoshis=satoshis,
        script="76a914" + "00" * 20 + "88ac",
    ))
    return provider


def _parse_pushes(script_hex: str) -> list[str]:
    """Parse the data elements pushed by a scriptSig hex. OP_0 yields ''."""
    pushes: list[str] = []
    raw = bytes.fromhex(script_hex)
    p = 0
    n = len(raw)
    while p < n:
        op = raw[p]
        p += 1
        if op == 0x00:
            pushes.append("")           # OP_0 -> empty push
        elif 0x01 <= op <= 0x4B:
            pushes.append(raw[p:p + op].hex())
            p += op
        elif op == 0x4C:
            ln = raw[p]
            p += 1
            pushes.append(raw[p:p + ln].hex())
            p += ln
        else:
            pushes.append("")           # bare opcode (not expected here)
    return pushes


def _input0_script_hex(tx_hex: str) -> str:
    raw = bytes.fromhex(tx_hex)
    off = 4  # version
    # input count varint (assume < 0xfd for these small txs)
    in_count = raw[off]
    off += 1
    assert in_count >= 1
    off += 32 + 4  # outpoint of input 0
    script_len = raw[off]
    off += 1
    # handle 0xfd/0xfe just in case
    if script_len == 0xFD:
        script_len = int.from_bytes(raw[off:off + 2], "little")
        off += 2
    return raw[off:off + script_len].hex()


def _deploy_or_checksig():
    art = _artifact(SRC, "OrChecksig.runar.ts")
    alice = MockSigner()
    provider = _funded_provider(alice.get_address())
    pk_a = alice.get_public_key()
    # A distinct, valid compressed pubkey for branch B (secp256k1 generator G).
    # The wire-level assertions never validate a signature against it.
    pk_b = "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
    contract = RunarContract(art, [pk_a, pk_b])
    contract.deploy(provider, alice, DeployOptions(satoshis=10_000))
    return contract, provider, alice


class TestEmptySig:
    def test_marker_identity(self):
        assert is_empty_sig(EMPTY_SIG)
        assert not is_empty_sig(None)
        assert not is_empty_sig("00")
        # Public re-export is the same singleton.
        assert EMPTY_SIG_PUBLIC is EMPTY_SIG
        assert is_empty_sig_public(EMPTY_SIG)

    def test_encodes_as_op_0(self):
        assert _encode_arg(EMPTY_SIG) == "00"

    def test_empty_sig_branch_is_op_0(self):
        # [None, EMPTY_SIG]: Alice signs branch A (auto); branch B is empty.
        contract, provider, alice = _deploy_or_checksig()
        contract.call("execute", [None, EMPTY_SIG], provider, alice)
        call_tx = provider.get_broadcasted_txs()[1]
        pushes = _parse_pushes(_input0_script_hex(call_tx))
        assert len(pushes) == 2
        assert len(pushes[0]) > 0          # branch A: real signature
        assert pushes[1] == ""             # branch B: OP_0 — satisfies NULLFAIL

    def test_double_auto_duplicates_sig_and_warns(self):
        # [None, None]: both slots auto -> both filled with Alice's sig (the
        # non-empty failing-branch push a NULLFAIL node rejects). Also emits the
        # >=2-auto-slots soft warning.
        contract, provider, alice = _deploy_or_checksig()
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            contract.call("execute", [None, None], provider, alice)
        assert any("EMPTY_SIG" in str(w.message) and "issue #106" in str(w.message)
                   for w in caught)
        call_tx = provider.get_broadcasted_txs()[1]
        pushes = _parse_pushes(_input0_script_hex(call_tx))
        assert len(pushes) == 2
        assert len(pushes[0]) > 0          # branch A: real signature
        assert len(pushes[1]) > 0          # branch B: non-empty -> trips NULLFAIL
        assert pushes[1] == pushes[0]      # same single-signer signature in both

    def test_empty_sig_does_not_warn(self):
        # A single auto slot + EMPTY_SIG must NOT trip the >=2 heuristic.
        contract, provider, alice = _deploy_or_checksig()
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            contract.call("execute", [None, EMPTY_SIG], provider, alice)
        assert not any("issue #106" in str(w.message) for w in caught)
