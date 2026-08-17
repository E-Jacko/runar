# Skip inventory audit

Source: [docs/test-skips.md](../../docs/test-skips.md). The repository currently has 67 rows (the prompt said 64). Each row is individually classified; “CLEARED” means the documented condition is environmental or deliberate scope, not that the test ran in this checkout. S-067 is the deferred defect and has a separate repro.

| ID | Test | skip site | declared | audit class | state |
|---|---|---|---|---|---|
| S-001 | `TestWOTS_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:1093,1123,1154` | Environmental | Environmental | CLEARED |
| S-002 | `TestStatefulWOTSGate_ScriptExecution` (+ `_TamperedSig`) | `conformance/script_execution_test.go:1218,1326` | Environmental | Environmental | CLEARED |
| S-003 | `TestSLHDSA_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:1432,1483,1521` | Environmental | Environmental | CLEARED |
| S-004 | `TestSLHDSA128f_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:2249,2263,2281` | Environmental | Environmental | CLEARED |
| S-005 | `TestSLHDSA192s_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:2313,2327,2345` | Environmental | Environmental | CLEARED |
| S-006 | `TestSLHDSA192f_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:2363,2377,2395` | Environmental | Environmental | CLEARED |
| S-007 | `TestSLHDSA256s_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:2413,2427,2445` | Environmental | Environmental | CLEARED |
| S-008 | `TestSLHDSA256f_ScriptExecution` (+ `_TamperedSig`, `_WrongMessage`) | `conformance/script_execution_test.go:2463,2477,2495` | Environmental | Environmental | CLEARED |
| S-009 | `TestWOTS_ValidSpend` (+ `_TamperedSig`, `_WrongMessage`) | `integration/go/wots_test.go:168,219,268` | Environmental | Environmental | CLEARED |
| S-010 | `TestSLHDSA_*` regtest tests | `integration/go/slhdsa_test.go:173,219,263` | Environmental | Environmental | CLEARED |
| S-011 | `TestGroth16WA_Regtest_Deploy_SP1` (+ `_Spend`, `_Tamper`, `_Tamper2`) | `integration/go/groth16_wa_test.go:418,437,459,506` | Environmental | Environmental | CLEARED |
| S-012 | `TestGroth16WA_SDK_*` | `integration/go/groth16_wa_sdk_test.go:113,178` | Environmental | Environmental | CLEARED |
| S-013 | `TestSchnorr_ValidProof` / `TestSchnorr_TamperedProof` | `integration/go/schnorr_zkp_test.go:289,343` | Environmental | Environmental | CLEARED |
| S-014 | `TestCLI_Groth16WA_SP1` | `compilers/go/groth16_wa_cli_test.go:21` | Environmental | Environmental | CLEARED |
| S-015 | `TestGroth16WA_EndToEnd_SP1Proof_Script` | `packages/runar-go/bn254witness/sp1_script_test.go:207` | Environmental | Environmental | CLEARED |
| S-016 | `TestVerifyEvmGuest` / `TestSp1FriEvmGuest_*` | `packages/runar-go/sp1fri/verify_test.go:71`, `compilers/go/codegen/sp1_fri_test.go:2114,2118` | Environmental | Environmental | CLEARED |
| S-017 | `TestSp1Fri_FoldRow` arity-skip branches | `compilers/go/codegen/sp1_fri_test.go:1274,1600` | Environmental | Deliberate scope | CLEARED |
| S-018 | `TestSourceCompile_*` (P2PKH / Arithmetic / BooleanLogic / IfElse / BoundedLoop / MultiMethod / Stateful / IRvsSourceMatch / AllConformanceFromSource / TestCompilerParity_AllConformance) | `compilers/go/compiler/compiler_test.go:899,926,947,964,978,992,1006,1051,1117,1186` | Environmental | Environmental | CLEARED |
| S-019 | `TestSource_LoadsRunarSource` (multiformat) | `compilers/go/compiler/compiler_multiformat_test.go:47,57,216,327,362,406` | Environmental | Environmental | CLEARED |
| S-020 | `TestIntegrationCompiler` (per-fixture loader) | `compilers/go/compiler/integration_test.go:48,95` | Environmental | Environmental | CLEARED |
| S-021 | `TestWalletClient_LiveEndpoint_RoundTrip` | `packages/runar-go/sdk_wallet_client_integration_test.go:130` | Environmental | Environmental | CLEARED |
| S-022 | `BRC-100 WalletClient live endpoint` | `packages/runar-sdk/src/__tests__/wallet-client.spec.ts:47` | Environmental | Environmental | CLEARED |
| S-023 | `BRC-100 WalletClient live endpoint round-trip` | `packages/runar-zig/src/sdk_wallet_client_integration_test.zig:96,97` | Environmental | Environmental | CLEARED |
| S-024 | `walletClientLiveRoundTrip` | `packages/runar-java/src/test/java/runar/lang/sdk/WalletClientIntegrationTest.java:44` | Environmental | Environmental | CLEARED |
| S-025 | `test_wallet_client_live_round_trip` | `packages/runar-py/tests/test_wallet_client_integration.py:61` | Environmental | Environmental | CLEARED |
| S-026 | `wallet_client_live_round_trip` | `packages/runar-rs/tests/wallet_client_integration.rs:46` | Environmental | Environmental | CLEARED |
| S-027 | `BRC-100 WalletClient live endpoint round-trip` | `integration/ruby/spec/wallet_client_spec.rb:107,142` | Environmental | Environmental | CLEARED |
| S-028 | `Cross-compiler: TS IR -> Go Script` (+ Rust / Python / Zig / Ruby / Java suites, 11 `describe.skipIf(...)` blocks) | `packages/runar-compiler/src/__tests__/cross-compiler.test.ts:610,687,821,940,994,1038,1088,1133,1176,1217,1259` | Environmental | Environmental | CLEARED |
| S-029 | `assembleMultiContractCall — regtest integration` | `packages/runar-sdk/src/__tests__/multi-contract-call.regtest.test.ts:237` | Environmental | Environmental | CLEARED |
| S-030 | `BRC-100 WalletClient live endpoint (skipped)` sentinel | `packages/runar-sdk/src/__tests__/wallet-client.spec.ts:76,77` | Environmental | Environmental | CLEARED |
| S-031 | `CurlHttpTransport live GET hits httpbin` / `StdHttpTransport live GET hits httpbin` | `packages/runar-zig/src/sdk_http_client.zig:331,341` | Environmental | Environmental | CLEARED |
| S-032 | `e2e FixedArray: TicTacToe v2 ...` / `e2e MultiSig2of3 ...` | `compilers/zig/src/tests/e2e.zig:657,663,738` | Environmental | Environmental | CLEARED |
| S-033 | Zig `script_integration_test` (compileRunarScriptHex) | `packages/runar-zig/src/script_integration_test.zig:79,145` | Environmental | Environmental | CLEARED |
| S-034 | `TestRubyCompilerParity::test_ruby_compiler_parity_all` | `compilers/python/tests/test_source_compile.py:169` | Environmental | Environmental | CLEARED |
| S-035 | `test_compile_check_accepts_valid_p2pkh` | `packages/runar-py/tests/test_compile_check.py:16` | Environmental | Environmental | CLEARED |
| S-036 | `IntegrationBase.ensureNode` (Java) | `integration/java/src/test/java/runar/integration/helpers/IntegrationBase.java:43` | Environmental | Environmental | CLEARED |
| S-037 | `@RequiresIntegration` meta-annotation (Java) | `integration/java/src/test/java/runar/integration/helpers/RequiresIntegration.java:27` | Environmental | Environmental | CLEARED |
| S-038 | `ANF interpreter parity (<sdk> SDK)` (per-SDK suite) | `conformance/anf-interpreter/cross-interpreter.test.ts:253` | Environmental | Environmental | CLEARED |
| S-039 | Java integration suite (run-all.sh) | `integration/run-all.sh:129` | Environmental | Environmental | CLEARED |
| S-040 | `test_spend` / `test_tampered_slhdsa_sig` / `test_slhdsa_signed_wrong_message` / `test_spend_multiple_messages` (SPHINCSWallet) | `examples/python/sphincs-wallet/test_sphincs_wallet.py:22` | Environmental | Environmental | CLEARED |
| S-041 | `test_arbitrary_message_passes_anyone_can_spend` | `examples/python/post-quantum-slhdsa-naive-INSECURE/test_post_quantum_slhdsa_naive_insecure.py:20` | Environmental | Environmental | CLEARED |
| S-042 | `TestSLHDSA_SelfConsistency` (-short) | `packages/runar-go/crypto_kat_test.go:313` | Environmental | Environmental | CLEARED |
| S-043 | ANF strict-mode parity (per-SDK suite) | `conformance/anf-interpreter/cross-interpreter-strict.test.ts:257` | Environmental | Environmental | CLEARED |
| S-044 | ANF real-crypto parity (per-SDK suite) | `conformance/anf-interpreter/cross-interpreter-real-crypto.test.ts:273` | Environmental | Environmental | CLEARED |
| S-045 | `TestCLI_ParseOnly_ValidSource` / `_InvalidSource` / `_RequiresSourceFlag` | `compilers/go/cli_parse_only_test.go:27,75,112` | Environmental | Environmental | CLEARED |
| S-046 | `Tier 2: conformance fixtures` directory-missing guard | `packages/decompiler/__tests__/roundtrip.test.ts:125` | Environmental | Environmental | CLEARED |
| S-047 | `Tier 1: examples coverage matrix` — pathological-decompile skip set | `packages/decompiler/__tests__/roundtrip.test.ts:109` | Environmental | Deliberate scope | CLEARED |
| S-048 | `analyzerMatchesGolden` (Java analyzer ↔ golden) | `packages/runar-java/src/test/java/runar/lang/analyzer/FixtureConformanceTest.java` | Environmental | Environmental | CLEARED |
| S-049 | `TestCLI_Debug_TrivialScript` / `_RequiresInput` / `_FailingScript` / `_Artifact` | `compilers/go/cli_debug_test.go:21,56,77,110` | Environmental | Environmental | CLEARED |
| S-050 | `PostQuantumSLHDSANaiveInsecure (Move)` | `examples/move/post-quantum-slhdsa-naive-INSECURE/PostQuantumSLHDSANaiveInsecure.test.ts:16` | Environmental | Environmental | CLEARED |
| S-051 | `SPHINCSWallet (Move)` | `examples/move/sphincs-wallet/SPHINCSWallet.test.ts:41` | Environmental | Environmental | CLEARED |
| S-052 | `PostQuantumSLHDSANaiveInsecure (Solidity)` | `examples/sol/post-quantum-slhdsa-naive-INSECURE/PostQuantumSLHDSANaiveInsecure.test.ts:16` | Environmental | Environmental | CLEARED |
| S-053 | `SPHINCSWallet (Solidity, Hybrid ECDSA + SLH-DSA-SHA2-128s)` | `examples/sol/sphincs-wallet/SPHINCSWallet.test.ts:41` | Environmental | Environmental | CLEARED |
| S-054 | `PostQuantumSLHDSANaiveInsecure` | `examples/ts/post-quantum-slhdsa-naive-INSECURE/PostQuantumSLHDSANaiveInsecure.test.ts:19` | Environmental | Environmental | CLEARED |
| S-055 | `SPHINCSWallet (Hybrid ECDSA + SLH-DSA-SHA2-128s)` | `examples/ts/sphincs-wallet/SPHINCSWallet.test.ts:40` | Environmental | Environmental | CLEARED |
| S-056 | `SLH-DSA-SHA2-128s dual-oracle` | `packages/runar-testing/src/__tests__/post-quantum-slh-dual-oracle.test.ts:36` | Environmental | Environmental | CLEARED |
| S-057 | `SLH-DSA reference implementation` | `packages/runar-testing/src/crypto/__tests__/slh-dsa.test.ts:9` | Environmental | Environmental | CLEARED |
| S-058 | `Runar.compile_check accepts a path to a valid .runar.rb contract` | `packages/runar-rb/spec/sdk/compile_check_spec.rb:22` | Environmental | Environmental | CLEARED |
| S-059 | `TestEmitVerifyRabinSig_RejectsMalleatedSignature/FlipHighBitOfSig` | `compilers/go/codegen/rabin_adversarial_test.go:381` | Environmental | Environmental | CLEARED |
| S-060 | `test_fixture_byte_identical` (Python analyzer conformance) | `packages/runar-py/tests/analyzer/test_conformance.py:42,44` | Environmental | Environmental | CLEARED |
| S-061 | `produces byte-identical JSON for <fixture>` (Ruby analyzer conformance) | `packages/runar-rb/spec/analyzer/conformance_spec.rb:25,26` | Environmental | Environmental | CLEARED |
| S-062 | `SLH-DSA adversarial bound-violation tests (all 6 parameter sets)` | `packages/runar-testing/src/__tests__/post-quantum-bounds.test.ts:193` | Environmental | Environmental | CLEARED |
| S-063 | `Issue #100 — terminal var-len state read gets _codePart` | `packages/runar-rb/spec/sdk/issue100_spec.rb:59` | Environmental | Environmental | CLEARED |
| S-064 | `Issue #106 — EMPTY_SIG marker for OR-CHECKSIG branched auth` | `packages/runar-rb/spec/sdk/issue106_empty_sig_spec.rb:120,131,144` | Environmental | Environmental | CLEARED |
| S-065 | `Issue #123 — per-method SIGHASH mode threaded through preimage/signing` | `packages/runar-rb/spec/sdk/issue123_sighash_spec.rb:124` | Environmental | Environmental | CLEARED |
| S-066 | `needs_script_vm` marker (MockProvider script-execution layer) | `packages/runar-py/tests/test_mock_broadcast_validation.py:49` | Environmental | Environmental | CLEARED |
| S-067 | `OPEN: nested declared-results if rotates its enclosing arm` | `packages/runar-testing/src/__tests__/nested-declared-results-arm-layout-vm.test.ts:112` | Gap | Deferred defect | CONFIRMED |
