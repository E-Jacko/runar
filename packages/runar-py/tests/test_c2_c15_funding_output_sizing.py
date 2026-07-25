"""Findings C2 + C15 — call funding selection must size the fee against the
contract/covenant INPUT's unlock bytes (C2) AND every output, not just the
single continuation (C15).

`estimate_deploy_fee` / `select_utxos` gained trailing `extra_input_bytes`
(C2) and `extra_output_bytes` (C15) params. `prepare_call` computes both so a
MERGE (whose covenant input embeds tens of KB of parent-tx bytes) or a
multi-output / large-dataOutput call does not stop one UTXO short — which,
after finding C3, would then be rejected as underfunded rather than silently
stranding funds. Deploy and single-output callers pass 0 and are unchanged.

Mirrors the TS reference `c15-funding-output-sizing.test.ts`.
"""

from runar.sdk.deployment import estimate_deploy_fee, select_utxos
from runar.sdk.types import Utxo


class TestC15FundingOutputSizing:
    def test_estimate_adds_extra_output_bytes_to_fee(self):
        """extra_output_bytes raises the fee by exactly bytes * rate / 1000."""
        base = estimate_deploy_fee(1, 100, 1000)  # 1000 sat/KB, no extra
        with_out = estimate_deploy_fee(1, 100, 1000, 0, 5000)  # +5000 output bytes
        assert with_out > base
        # 5000 extra bytes at 1000 sat/KB == 5000 sats more.
        assert with_out - base == 5000

    def test_estimate_adds_extra_input_bytes_to_fee(self):
        """extra_input_bytes (C2) raises the fee by exactly bytes * rate / 1000."""
        base = estimate_deploy_fee(1, 100, 1000)
        with_in = estimate_deploy_fee(1, 100, 1000, 5000, 0)  # +5000 input bytes
        assert with_in > base
        assert with_in - base == 5000

    def test_select_picks_more_coins_when_extra_output_bytes_tip_the_edge(self):
        """extra_output_bytes that push the fee past a single-coin edge force a
        second coin to be selected."""
        utxos = [
            Utxo(txid='aa' * 32, output_index=0, satoshis=10_000, script=''),
            Utxo(txid='bb' * 32, output_index=0, satoshis=10_000, script=''),
        ]
        # Target 9_000 at 1000 sat/KB. With no extra output bytes a single
        # 10_000 coin covers 9_000 + a ~226-sat fee -> 1 coin. Adding 2_000
        # output bytes (2_000 sats of fee) pushes the requirement past 10_000
        # -> 2 coins needed.
        few = select_utxos(utxos, 9_000, 25, 1000, 0, 0)
        more = select_utxos(utxos, 9_000, 25, 1000, 0, 2_000)
        assert len(few) == 1
        assert len(more) == 2

    def test_select_picks_more_coins_when_extra_input_bytes_tip_the_edge(self):
        """extra_input_bytes (C2 — the covenant input's unlock) that push the
        fee past a single-coin edge force a second coin to be selected."""
        utxos = [
            Utxo(txid='cc' * 32, output_index=0, satoshis=10_000, script=''),
            Utxo(txid='dd' * 32, output_index=0, satoshis=10_000, script=''),
        ]
        few = select_utxos(utxos, 9_000, 25, 1000, 0, 0)
        more = select_utxos(utxos, 9_000, 25, 1000, 2_000, 0)
        assert len(few) == 1
        assert len(more) == 2
