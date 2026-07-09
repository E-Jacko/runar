"""Independent OFFICIAL crypto known-answer tests.

Unlike ``test_runtime_vectors.py`` (cross-SDK goldens the tiers agree on),
the vectors here are copied verbatim from external authorities — the BLAKE3
team's own reference test file and RFC 6979 — and are NOT re-derived from any
Runar tier. They guard the BUG-101 failure mode, where a primitive was
"validated" only against self-produced goldens that were themselves wrong.

Sources are recorded in the ``_source`` field of each vendored JSON:
  conformance/runtime-vectors/blake3-official-kat.json  (BLAKE3-team/BLAKE3)
  conformance/runtime-vectors/ecdsa-rfc6979.json        (RFC 6979 A.2.5/A.2.6)
"""

import json
from pathlib import Path

import pytest

from runar.builtins import blake3_hash, verify_ecdsa_p256, verify_ecdsa_p384


def _vectors_dir() -> Path:
    here = Path(__file__).resolve()
    for ancestor in (here, *here.parents):
        candidate = ancestor / "conformance" / "runtime-vectors"
        if candidate.is_dir():
            return candidate
    raise RuntimeError(
        f"could not locate conformance/runtime-vectors walking up from {here}"
    )


def _load(name: str) -> dict:
    return json.loads((_vectors_dir() / name).read_text())


BLAKE3_KAT = _load("blake3-official-kat.json")
ECDSA_KAT = _load("ecdsa-rfc6979.json")


# ---------------------------------------------------------------------------
# BLAKE3 — official reference vectors (BLAKE3-team/BLAKE3 test_vectors.json)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "case",
    BLAKE3_KAT["blake3_hash_official"],
    ids=lambda v: f"len{v['input_len']}",
)
def test_official_blake3_hash(case: dict) -> None:
    inp = bytes.fromhex(case["input"])
    assert len(inp) == case["input_len"], "vendored input_len/hex disagree"
    got = blake3_hash(inp).hex()
    assert got == case["expected"], (
        f"blake3_hash(len={case['input_len']}) disagrees with official BLAKE3 KAT"
    )


# ---------------------------------------------------------------------------
# ECDSA P-256 / P-384 — RFC 6979 deterministic-ECDSA vectors
# ---------------------------------------------------------------------------


def _compressed_pubkey(qx_hex: str, qy_hex: str) -> bytes:
    """SEC1 compressed public key: 0x02/0x03 (y parity) || Qx."""
    qx = bytes.fromhex(qx_hex)
    qy = bytes.fromhex(qy_hex)
    prefix = 0x02 if (qy[-1] & 1) == 0 else 0x03
    return bytes([prefix]) + qx


def _raw_sig(r_hex: str, s_hex: str, width: int) -> bytes:
    r = bytes.fromhex(r_hex).rjust(width, b"\x00")
    s = bytes.fromhex(s_hex).rjust(width, b"\x00")
    return r + s


@pytest.mark.parametrize(
    "case",
    ECDSA_KAT["ecdsa_rfc6979"],
    ids=lambda v: v["name"],
)
def test_official_ecdsa_rfc6979(case: dict) -> None:
    if case["curve"] == "P-256":
        width, verify = 32, verify_ecdsa_p256
    elif case["curve"] == "P-384":
        width, verify = 48, verify_ecdsa_p384
    else:
        pytest.fail(f"unknown curve {case['curve']!r}")

    pubkey = _compressed_pubkey(case["qx"], case["qy"])
    sig = _raw_sig(case["r"], case["s"], width)
    msg = case["message_ascii"].encode()

    # The published (r,s) MUST verify.
    assert verify(msg, sig, pubkey), (
        f"{case['name']}: native verify rejected the OFFICIAL signature "
        f"({case['source']}) — impl disagrees with RFC 6979"
    )

    # A 1-bit-flipped signature MUST be rejected.
    tampered = bytearray(sig)
    tampered[-1] ^= 0x01
    assert not verify(msg, bytes(tampered), pubkey), (
        f"{case['name']}: accepted a 1-bit-tampered signature — must reject"
    )

    # A different message MUST be rejected.
    assert not verify(b"wrong message", sig, pubkey), (
        f"{case['name']}: accepted signature against the wrong message — must reject"
    )
