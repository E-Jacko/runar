# Skip inventory classification

`python3 scripts/audit-test-skips.py` reports 132 sites and 64 parsed rows. The Markdown inventory physically contains 65 rows: `analyzerMatchesGolden` has no parseable `file:line`, so the auditor excludes it (`scripts/audit-test-skips.py:305`, `docs/test-skips.md:92`). I classified all 64 machine-counted rows plus that manually tracked row.

Classes:

- **Environmental**: an external service/toolchain/cost flag controls execution, and the mandatory CI path is strict or executes it.
- **Deliberate scope**: a defensive extracted-package/missing-repo-layout guard or an intentionally impossible branch for the pinned fixture; not a current correctness deferral.
- **Deferred defect**: supported behavior is excluded because the implementation/test machinery is incomplete or pathological. The missing defect is named in the verdict.

| # | Inventory row (`docs/test-skips.md:line`) | Classification | Evidence/verdict | State |
|---:|---|---|---|---|
| 1 | WOTS script execution (`:45`) | Environmental | `testing.Short`; CI runs conformance without `-short` (`.github/workflows/ci.yml:1079`) | CLEARED |
| 2 | Stateful WOTS gate (`:46`) | Environmental | Same cost gate and mandatory non-short conformance job | CLEARED |
| 3 | SLH-DSA 128s execution (`:47`) | Environmental | Same; CI timeout is 1200s, no `-short` | CLEARED |
| 4 | SLH-DSA 128f execution (`:48`) | Environmental | Same | CLEARED |
| 5 | SLH-DSA 192s execution (`:49`) | Environmental | Same | CLEARED |
| 6 | SLH-DSA 192f execution (`:50`) | Environmental | Same | CLEARED |
| 7 | SLH-DSA 256s execution (`:51`) | Environmental | Same | CLEARED |
| 8 | SLH-DSA 256f execution (`:52`) | Environmental | Same | CLEARED |
| 9 | WOTS regtest spends (`:53`) | Environmental | Regtest plus `testing.Short`; CI integration runs non-short (`.github/workflows/ci.yml:1191`) | CLEARED |
| 10 | SLH-DSA regtest spends (`:54`) | Environmental | Same | CLEARED |
| 11 | Groth16-WA regtest SP1 (`:55`) | Environmental | Same | CLEARED |
| 12 | Groth16-WA SDK regtest (`:56`) | Environmental | Same | CLEARED |
| 13 | Schnorr proof regtest (`:57`) | Environmental | Same | CLEARED |
| 14 | Go Groth16-WA CLI (`:58`) | Environmental | Short-mode performance guard; compiler CI is non-short (`.github/workflows/ci.yml:349`) | CLEARED |
| 15 | Groth16-WA SP1 script (`:59`) | Environmental | Short-mode minutes-long interpreter guard; SDK CI is non-short (`.github/workflows/ci.yml:488`) | CLEARED |
| 16 | EVM-guest SP1 FRI fixture (`:60`) | Deliberate scope | Missing-file guard for extracted/partial trees; target checkout tracks the 319 KiB fixture (`tests/vectors/sp1/fri/evm-guest/proof.postcard:1`) | CLEARED |
| 17 | SP1 FRI FoldRow arity guards (`:61`) | Deferred defect | Defect: higher-arity/per-query input-MMCS folding has no stable end-to-end test; source says it is “scheduled for the next dispatch” (`compilers/go/codegen/sp1_fri_test.go:1263`) | CONFIRMED |
| 18 | Go source-compile fixture guards (`:62`) | Deliberate scope | Extracted-module guard; all fixtures exist in normal checkout | CLEARED |
| 19 | Go multiformat fixture guards (`:63`) | Deliberate scope | Same | CLEARED |
| 20 | Go integration fixture guards (`:64`) | Deliberate scope | Same plus integration build tag | CLEARED |
| 21 | Go live wallet client (`:65`) | Environmental | Requires external BRC-100 endpoint | CLEARED |
| 22 | TS live wallet client (`:66`) | Environmental | Same | CLEARED |
| 23 | Zig live wallet client (`:67`) | Environmental | Same | CLEARED |
| 24 | Java live wallet client (`:68`) | Environmental | Same | CLEARED |
| 25 | Python live wallet client (`:69`) | Environmental | Same | CLEARED |
| 26 | Rust live wallet client (`:70`) | Environmental | Same, explicit ignored-test invocation | CLEARED |
| 27 | Ruby live wallet client (`:71`) | Environmental | Same, including optional auth | CLEARED |
| 28 | TS cross-compiler suites (`:72`) | Environmental | Local toolchain skips become hard failures under `RUNAR_REQUIRE_ALL_COMPILERS=1` in CI | CLEARED |
| 29 | Multi-contract regtest (`:73`) | Environmental | Requires live node; always-on in-process Spend suite covers core path | CLEARED |
| 30 | TS wallet skipped sentinel (`:74`) | Environmental | Deliberate visible sentinel when endpoint is absent | CLEARED |
| 31 | Zig live HTTP (`:75`) | Environmental | Requires opt-in external httpbin network call | CLEARED |
| 32 | Zig E2E missing examples (`:76`) | Deliberate scope | Extracted-module guard | CLEARED |
| 33 | Zig script integration missing TS dist (`:77`) | Environmental | Build artifact precondition, satisfied by required build | CLEARED |
| 34 | Python-hosted Ruby compiler parity (`:78`) | Deliberate scope | Missing-source guard; all target fixtures list Ruby | CLEARED |
| 35 | Python compile-check missing example (`:79`) | Deliberate scope | Extracted-package guard | CLEARED |
| 36 | Java `IntegrationBase.ensureNode` (`:80`) | Environmental | Explicit integration property plus live regtest | CLEARED |
| 37 | Java `@RequiresIntegration` (`:81`) | Environmental | Same declarative gate | CLEARED |
| 38 | Lenient ANF driver parity (`:82`) | Environmental | Missing local drivers hard-fail in CI strict mode | CLEARED |
| 39 | Java integration in `run-all.sh` (`:83`) | Environmental | Missing Gradle hard-fails with `RUNAR_INTEGRATION_STRICT=1`; CI invokes Gradle directly | CLEARED |
| 40 | Python SPHINCSWallet (`:84`) | Environmental | Optional `slh-dsa`; CI installs it and implementation fails closed if absent | CLEARED |
| 41 | Python insecure SLH example (`:85`) | Environmental | Same | CLEARED |
| 42 | Go SLH self-consistency (`:86`) | Environmental | Short-mode cost only; SDK CI runs non-short | CLEARED |
| 43 | Strict ANF driver parity (`:87`) | Environmental | Missing local drivers hard-fail in CI strict mode | CLEARED |
| 44 | Real-crypto ANF driver parity (`:88`) | Environmental | Same | CLEARED |
| 45 | Go parse-only CLI (`:89`) | Environmental | Short-mode build/subprocess cost; compiler CI non-short | CLEARED |
| 46 | Decompiler missing conformance directory (`:90`) | Deliberate scope | Extracted-package guard; directory present in checkout | CLEARED |
| 47 | Decompiler pathological examples (`:91`) | Deferred defect | Defect: symbolic lifter has super-linear blow-up on seven supported SLH-DSA examples, removing them from byte-match regression coverage (`packages/decompiler/__tests__/roundtrip.test.ts:92`, `:109`) | CONFIRMED |
| 48 | Java analyzer `@EnabledIf` (`:92`) | Deliberate scope | Repo-layout guard; runs in monorepo. Separately, the skip auditor cannot see this generic annotation (`scripts/audit-test-skips.py:80`) | CLEARED |
| 49 | Go debug CLI (`:93`) | Environmental | Short-mode build/subprocess cost; compiler CI non-short | CLEARED |
| 50 | Move insecure SLH example (`:94`) | Environmental | Slow gate runs automatically when `CI=true` | CLEARED |
| 51 | Move SPHINCSWallet (`:95`) | Environmental | Same | CLEARED |
| 52 | Solidity insecure SLH example (`:96`) | Environmental | Same | CLEARED |
| 53 | Solidity SPHINCSWallet (`:97`) | Environmental | Same | CLEARED |
| 54 | TS insecure SLH example (`:98`) | Environmental | Same | CLEARED |
| 55 | TS SPHINCSWallet (`:99`) | Environmental | Same | CLEARED |
| 56 | SLH dual oracle (`:100`) | Environmental | Same | CLEARED |
| 57 | SLH reference implementation (`:101`) | Environmental | Same | CLEARED |
| 58 | Ruby compile-check missing example (`:102`) | Deliberate scope | Extracted-gem guard | CLEARED |
| 59 | Rabin tiny-signature mutation (`:103`) | Deliberate scope | Guard is unreachable for the fixed hundreds-of-bits test key; other mutations remain unconditional | CLEARED |
| 60 | Python analyzer missing goldens (`:104`) | Deliberate scope | Extracted-package guard | CLEARED |
| 61 | Ruby analyzer missing goldens (`:105`) | Deliberate scope | Extracted-package guard | CLEARED |
| 62 | SLH adversarial bounds (`:106`) | Environmental | Slow gate runs automatically when `CI=true` | CLEARED |
| 63 | Ruby issue #100 compiler unavailable (`:107`) | Deliberate scope | Extracted-gem guard; CLI exists in monorepo | CLEARED |
| 64 | Ruby issue #106 compiler unavailable (`:108`) | Deliberate scope | Same | CLEARED |
| 65 | Ruby issue #123 compiler unavailable (`:109`) | Deliberate scope | Same | CLEARED |

Totals over the 65 physical rows: 47 environmental, 16 deliberate scope, 2 deferred defects. The script's advertised 64-row total excludes row 48 because that row deliberately lacks a parseable `file:line`.
