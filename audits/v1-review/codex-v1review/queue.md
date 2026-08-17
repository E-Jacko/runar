# Rúnar v1 Codex Audit Queue

- `CONFIRMED` — Audit target is isolated on branch `audit/codex/v1-review` at `e7221a7b914d765d57cae613a54bcac968d1608f`; evidence: `git -C ../runar-codex status --short --branch && git -C ../runar-codex rev-parse HEAD`.
- `CONFIRMED` — Required audit output directories created under `audits/v1-review/codex/`; evidence: `find audits/v1-review/codex -maxdepth 1 -type d -print`.
- `CLEARED` — Dependency installation completed from the pinned lockfile; evidence: `pnpm install` (`172` packages, all reused).
- `CLEARED` — Target sources build without shared-cache substitution; evidence: `pnpm exec turbo run build --force` (`7` successful, `0` cached).
- `CONFIRMED` — Provenance allowlist contains exactly 58 entries: 3 `official-KAT`, 8 `differential-oracle`, 47 `intentional-spec-change`; evidence: `jq -r '.entries | group_by(."verified-against")[] | [.[0]."verified-against", length] | @tsv' conformance/golden-provenance-allowlist.json`.
- `CONFIRMED` — CX-001: the gate accepts re-authorized bytes with a stale unrelated reason. Commit `ed2ca565` changed the two `intent-output-p2pkh` hashes but retained the `#116` reason; evidence: `git show ed2ca565 -- conformance/golden-provenance-allowlist.json` and `node conformance/scripts/check-golden-provenance.mjs --files conformance/tests/intent-output-p2pkh/expected-ir.json --json`.
- `CLEARED` — Provenance entry 1 BLAKE3 official-KAT: all 11 vendored cases' input pattern and first 32 hash bytes exactly match the upstream BLAKE3-team vector file; evidence command recorded in `provenance-entry-verdicts.md`.
- `CLEARED` — Provenance entry 2 RFC 6979 official-KAT: all 16 qx/qy/r/s values match RFC 6979 A.2.5/A.2.6 after whitespace/case normalization; evidence command recorded in `provenance-entry-verdicts.md`.
- `CLEARED` — Provenance entry 3 NIST SLH-DSA official-KAT: prompt fields for tgId 31/tcId 422 match byte-for-byte modulo hex case and NIST's expected result is `testPassed: true`; evidence command recorded in `provenance-entry-verdicts.md`.
- `CONFIRMED` — CX-002: `ecMulGen(2)` returns the all-zero point instead of secp256k1 `2G`, making `ec-unit` unspendable; repro: `node audits/v1-review/codex/repro/ecmul-k2.mjs`.
- `CLEARED` — Provenance entries 14–15: exact fold-off/fold-on script hashes match the allowlist and six targeted real `@bsv/sdk` Spend cases pass; evidence: commands in `provenance-entry-verdicts.md`.
- `CONFIRMED` — Provenance entry 16: the cited execution oracle does not consume the authorized selector IR JSON; exact IR has only self-compile/parity support.
- `CONFIRMED` — Provenance entries 4–13, 17–52, 58: all 47 `intentional-spec-change` records fail independent-spec review; individual origins, hashes, diffs and verdicts are in `provenance-entry-verdicts.md`.
- `CONFIRMED` — Provenance entries 53–57: the cited EC test executes a synthetic primitive script, not any exact authorized fixture; entry 56 is independently reproduced unspendable.
- `CLEARED` — All 58 provenance entries now have exactly one terminal verdict in `provenance-entry-verdicts.md` (5 cleared, 53 confirmed).
- `CONFIRMED` — Skip inventory contains 65 physical Markdown rows but the auditor reports 64 because the Java analyzer `@EnabledIf` row has no parseable `file:line`; repro: `python3 scripts/audit-test-skips.py` plus `rg -n '@EnabledIf\\(' packages/runar-java/src/test/java`.
- `CLEARED` — All 64 machine-counted skip rows plus the manually excluded Java row have individual classifications in `skip-classification.md`.
- `CONFIRMED` — Two skip rows are deferred defects, not environmental: higher-arity/per-query FRI coverage and the decompiler's seven-example SLH-DSA pathological set.
