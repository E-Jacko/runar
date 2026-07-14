"""BIP-62 low-S enforcement test for the Python ECDSA signer."""

from runar.ecdsa import ecdsa_sign, _parse_der_signature
from runar.ec import EC_N

HALF_N = EC_N // 2


def test_ecdsa_sign_produces_low_s():
    """Every signature produced by ecdsa_sign must have S <= N/2 (BIP-62)."""
    priv_key = 1  # well-known test key: private key = 1

    for i in range(20):
        # Produce a distinct 32-byte message hash for each iteration
        msg_hash = bytes([i] + [0] * 31)
        der = ecdsa_sign(priv_key, msg_hash)

        result = _parse_der_signature(der)
        assert result is not None, f"iteration {i}: could not parse DER signature"
        _r, s = result
        assert s <= HALF_N, (
            f"iteration {i}: S value 0x{s:x} exceeds N/2 (BIP-62 low-S violation)"
        )
