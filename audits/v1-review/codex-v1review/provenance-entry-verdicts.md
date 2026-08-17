# Golden provenance: all 58 entry verdicts

Audit target: `e7221a7b914d765d57cae613a54bcac968d1608f`.

Verdict meanings: `CLEARED` means the claimed independent authority was reproduced for the exact authorized value; `CONFIRMED` means the entry demonstrates a provenance weakness or failed its claimed authority. No entry is left pending.

## Mechanical evidence

- Current hashes: `for p in $(jq -r '.entries[].path' conformance/golden-provenance-allowlist.json); do want=$(jq -r --arg p "$p" '.entries[]|select(.path==$p)|.sha256' conformance/golden-provenance-allowlist.json); got=$(shasum -a 256 "$p"|cut -d' ' -f1); test "$want" = "$got" || echo "$p $want $got"; done`. Entry 58 is the sole mismatch.
- Origin/diff: `git log -1 -- <path>`, `git diff --numstat <origin>^ <origin> -- <path>`, and SHA-256 of `<origin>^:<path>` versus the target file.
- Spec history: `git log --all --format='%H %s' --grep='#116\|#121'` identifies the implementation/golden changes, while `git log --all --format='%H %s' -- spec` contains no #116 or #121 spec change. The state specification describes a continuation but not `_changeAmount` gating (`spec/semantics.md:413`, `spec/type-system.md:313`). The loop specification still expressly defines the pre-#121 count-only/zero-start behavior (`spec/semantics.md:266`, `spec/semantics.md:268`, `spec/semantics.md:286`, `spec/ir-format.md:276`, `spec/ir-format.md:291`).
- BLAKE3 upstream check: downloaded the official [BLAKE3 test vectors](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/master/test_vectors/test_vectors.json), then compared every vendored input pattern and first 32 output bytes with `node -e 'const fs=require("fs");const u=JSON.parse(fs.readFileSync("/tmp/runar-codex-blake3-upstream.json"));const l=JSON.parse(fs.readFileSync("conformance/runtime-vectors/blake3-official-kat.json"));const m=new Map(u.cases.map(x=>[x.input_len,x.hash.slice(0,64)]));for(const x of l.blake3_hash_official){const input=Buffer.from(Array.from({length:x.input_len},(_,i)=>i%251)).toString("hex");if(x.input!==input||x.expected!==m.get(x.input_len))throw Error("mismatch "+x.input_len)};console.log("verified")'`.
- ECDSA upstream check: downloaded [RFC 6979](https://www.rfc-editor.org/rfc/rfc6979.txt), removed whitespace, normalized case, and found every qx/qy/r/s field from all four vendored A.2.5/A.2.6 cases.
- SLH-DSA upstream check: downloaded NIST ACVP's [prompt](https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json) and [expected results](https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json); tgId 31/tcId 422's parameter set, interface, test type, key, message and signature match modulo hex case, and the result is `testPassed: true`.
- Branch/selector exact script check: fold-off and fold-on CLI compiles both hashed exactly to the authorized script hashes; `pnpm exec vitest run conformance/witnesses/real-crypto-execution.test.ts --testNamePattern 'branched-readonly-len|selector'` ran six exact-script spends (four accepts, two rejects) successfully. The oracle never reads `selector/expected-ir.json` (`conformance/witnesses/real-crypto-execution.test.ts:186`).
- EC check: `pnpm --filter runar-testing test -- ec-add-doubling.test.ts` passes four primitive-emitter tests, but the test synthesizes a new `emitMethod` script (`packages/runar-testing/src/__tests__/ec-add-doubling.test.ts:35`, `packages/runar-testing/src/__tests__/ec-add-doubling.test.ts:42`); it does not load or execute any of entries 53–57. Entry 56's exact fixture is expressly recorded as unspendable (`conformance/witnesses/coverage-ledger.json:179`) and reproduced by `node audits/v1-review/codex/repro/ecmul-k2.mjs`.

## Individual entries

| # | Entry (`file:line`) | Origin and golden diff | Spec/oracle verdict | State |
|---:|---|---|---|---|
| 1 | `conformance/runtime-vectors/blake3-official-kat.json:1` (`allowlist:29`) | Added by `2aa1beda`; 11 cases | Exact inputs and hashes match BLAKE3-team upstream | CLEARED |
| 2 | `conformance/runtime-vectors/ecdsa-rfc6979.json:1` (`allowlist:37`) | Added by `2aa1beda`; 4 cases | All 16 coordinate/signature fields match RFC 6979 A.2.5/A.2.6 | CLEARED |
| 3 | `conformance/runtime-vectors/slh-dsa-acvp-kat.json:1` (`allowlist:45`) | Added by `2aa1beda`; 1 case | Exact NIST ACVP tgId 31/tcId 422 prompt; official result passes | CLEARED |
| 4 | `conformance/analyzer/auction/expected-analyzer-report.json:1` (`allowlist:53`) | `4b63d22b`, `a09c9ace76d6→fadd1e3225be`, +275/−35 | #116 re-stamp; no spec change; parity is not independent | CONFIRMED |
| 5 | `conformance/analyzer/stateful-counter/expected-analyzer-report.json:1` (`allowlist:61`) | `4b63d22b`, `24b5a4e79526→954359a11ad5`, +2844/−279 | #116 re-stamp; no spec change; parity is not independent | CONFIRMED |
| 6 | `conformance/tests/add-data-output/expected-ir.json:1` (`allowlist:69`) | `3400d66d`, `6a9a0cecdc89→9bc964c3258d`, +61/−27 | #116 re-stamp; no spec change | CONFIRMED |
| 7 | `conformance/tests/add-data-output/expected-script.hex:1` (`allowlist:77`) | `3400d66d`, `bf637ebe6d27→ab2f450d65fe`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 8 | `conformance/tests/add-raw-output/expected-ir.json:1` (`allowlist:85`) | `3400d66d`, `a96831e06258→fa35039e2a25`, +53/−19 | #116 re-stamp; no spec change | CONFIRMED |
| 9 | `conformance/tests/add-raw-output/expected-script.hex:1` (`allowlist:93`) | `3400d66d`, `b57fa380dfcb→e748f15c03d8`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 10 | `conformance/tests/auction/expected-ir.json:1` (`allowlist:101`) | `3400d66d`, `b2796bdbfe7b→f81892f2a617`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 11 | `conformance/tests/auction/expected-script.hex:1` (`allowlist:109`) | `3400d66d`, `41be8b4b8a33→fbaa5b5e8eea`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 12 | `conformance/tests/bounded-loop/expected-ir.json:1` (`allowlist:117`) | `3400d66d`, `47743f866512→35b23e46b5fb`, +3/−1 | #121 added `start`/`step`, but written specs still mandate count-only/zero-start (`spec/semantics.md:268`, `spec/ir-format.md:282`) | CONFIRMED |
| 13 | `conformance/tests/branched-readonly-len/expected-ir.json:1` (`allowlist:125`) | `3400d66d`, `0ba34e920adc→d93505136c3d`, +51/−17 | #116 re-stamp; no spec change | CONFIRMED |
| 14 | `conformance/tests/branched-readonly-len/expected-script.hex:1` (`allowlist:133`) | `f029d33e`, `36ee6eb0fce5→0554576be0ab`, 1/1 | Exact fold-off/fold-on script ran both branches and tamper reject through `@bsv/sdk` Spend | CLEARED |
| 15 | `conformance/tests/selector/expected-script.hex:1` (`allowlist:141`) | `f029d33e`, new `1f7280b9baf0`, +1 | Exact fold-off/fold-on script ran two in-range accepts and unmatched-selector reject | CLEARED |
| 16 | `conformance/tests/selector/expected-ir.json:1` (`allowlist:149`) | `f029d33e`, new `219ac1e28f82`, +501 | Cited execution oracle consumes emitted script, not this IR JSON; exact IR value has only self-compile/parity support | CONFIRMED |
| 17 | `conformance/tests/cond-write-multi-field/expected-ir.json:1` (`allowlist:157`) | `3400d66d`, `b2d160b62552→87963449a3bd`, +51/−17 | #116 re-stamp; no spec change | CONFIRMED |
| 18 | `conformance/tests/cond-write-multi-field/expected-script.hex:1` (`allowlist:165`) | `3400d66d`, `6873252207ea→3083a6f37cec`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 19 | `conformance/tests/conditional-data-output-stateful/expected-ir.json:1` (`allowlist:173`) | `3400d66d`, `1c68603ea258→d768c0c03734`, +61/−27 | #116 re-stamp; no spec change | CONFIRMED |
| 20 | `conformance/tests/conditional-data-output-stateful/expected-script.hex:1` (`allowlist:181`) | `3400d66d`, `3b5fd3479e20→7e384cf1fd9b`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 21 | `conformance/tests/function-patterns/expected-ir.json:1` (`allowlist:189`) | `3400d66d`, `a6f41cd1ff1d→2e0280b1eb03`, +236/−100 | #116 re-stamp; no spec change | CONFIRMED |
| 22 | `conformance/tests/function-patterns/expected-script.hex:1` (`allowlist:197`) | `3400d66d`, `790185c9df54→f92c2f065c32`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 23 | `conformance/tests/intent-current-block-height/expected-ir.json:1` (`allowlist:205`) | `3400d66d`, `e12ad6b3107c→abda8c9661f6`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 24 | `conformance/tests/intent-current-block-height/expected-script.hex:1` (`allowlist:213`) | `3400d66d`, `626c8018f4b5→62a879bc0626`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 25 | `conformance/tests/intent-output-p2pkh/expected-ir.json:1` (`allowlist:221`) | `ed2ca565`, `adf9912cd5df→8c831a058cce`, −190 lines | Hash re-authorized for audit #3 while reason remained unrelated #116 text | CONFIRMED |
| 26 | `conformance/tests/intent-output-p2pkh/expected-script.hex:1` (`allowlist:229`) | `ed2ca565`, `508435c06b35→aa85919fee39`, 1/1 | Hash re-authorized for audit #3 while reason remained unrelated #116 text | CONFIRMED |
| 27 | `conformance/tests/intent-prev-output-script/expected-ir.json:1` (`allowlist:237`) | `3400d66d`, `daf3a6105bc9→bb49c5355c4c`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 28 | `conformance/tests/intent-prev-output-script/expected-script.hex:1` (`allowlist:245`) | `3400d66d`, `40612d3791d6→74476bd75e4b`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 29 | `conformance/tests/math-demo/expected-ir.json:1` (`allowlist:253`) | `3400d66d`, `d8cabe08a2b4→55f9420638a6`, +830/−354 | #116 re-stamp; no spec change | CONFIRMED |
| 30 | `conformance/tests/math-demo/expected-script.hex:1` (`allowlist:261`) | `3400d66d`, `00166301222f→472ed9b25f2d`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 31 | `conformance/tests/private-helper-outputs/expected-ir.json:1` (`allowlist:269`) | `3400d66d`, `cf2d0f9301c9→756508127727`, +171/−69 | #116 re-stamp; no spec change | CONFIRMED |
| 32 | `conformance/tests/private-helper-outputs/expected-script.hex:1` (`allowlist:277`) | `3400d66d`, `1fa44f23fe15→a0e51f89ef25`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 33 | `conformance/tests/property-initializers/expected-ir.json:1` (`allowlist:285`) | `3400d66d`, `5f9b01ae6d7e→53aaba675147`, +118/−50 | #116 re-stamp; no spec change | CONFIRMED |
| 34 | `conformance/tests/property-initializers/expected-script.hex:1` (`allowlist:293`) | `3400d66d`, `fc54c28adc6b→062fff744da1`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 35 | `conformance/tests/state-covenant/expected-ir.json:1` (`allowlist:301`) | `3400d66d`, `1a4171eaf592→df54379f5892`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 36 | `conformance/tests/state-covenant/expected-script.hex:1` (`allowlist:309`) | `3400d66d`, `322d0b20906a→c1a68af86947`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 37 | `conformance/tests/state-ripemd160/expected-ir.json:1` (`allowlist:317`) | `3400d66d`, `60a6e772efe8→9950c2e8274c`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 38 | `conformance/tests/state-ripemd160/expected-script.hex:1` (`allowlist:325`) | `3400d66d`, `247ce56975a4→0dedcc913bac`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 39 | `conformance/tests/stateful-bytestring/expected-ir.json:1` (`allowlist:333`) | `3400d66d`, `73189bcb99d8→91acdabef761`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 40 | `conformance/tests/stateful-bytestring/expected-script.hex:1` (`allowlist:341`) | `3400d66d`, `50a6154634a2→713b04e9809b`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 41 | `conformance/tests/stateful-counter/expected-ir.json:1` (`allowlist:349`) | `3400d66d`, `f51e2af34869→a6348eea2df7`, +118/−50 | #116 re-stamp; no spec change | CONFIRMED |
| 42 | `conformance/tests/stateful-counter/expected-script.hex:1` (`allowlist:357`) | `3400d66d`, `4ab3fb309c1f→17e415409a94`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 43 | `conformance/tests/stateful-wots-gate/expected-ir.json:1` (`allowlist:365`) | `3400d66d`, `ccdbac383b3f→8da4550dbc52`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 44 | `conformance/tests/stateful-wots-gate/expected-script.hex:1` (`allowlist:373`) | `3400d66d`, `e38a1d4738a1→267f83776c63`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 45 | `conformance/tests/stateful/expected-ir.json:1` (`allowlist:381`) | `3400d66d`, `9600f1d6ae66→ed82a9cd6d38`, +118/−50 | #116 re-stamp; no spec change | CONFIRMED |
| 46 | `conformance/tests/stateful/expected-script.hex:1` (`allowlist:389`) | `3400d66d`, `095aa710d27b→422d9671e881`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 47 | `conformance/tests/terminal-varlen-read/expected-ir.json:1` (`allowlist:397`) | `3400d66d`, `925a4115e2e8→374d81d93e4f`, +59/−25 | #116 re-stamp; no spec change | CONFIRMED |
| 48 | `conformance/tests/terminal-varlen-read/expected-script.hex:1` (`allowlist:405`) | `3400d66d`, `e00ce5b2a0a9→737f68ffd2ee`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 49 | `conformance/tests/token-ft/expected-ir.json:1` (`allowlist:413`) | `3400d66d`, `25d2ab0c3941→694f4e553103`, +155/−53 | #116 re-stamp; no spec change | CONFIRMED |
| 50 | `conformance/tests/token-ft/expected-script.hex:1` (`allowlist:421`) | `3400d66d`, `98719d60d740→3a54d69f2ea9`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 51 | `conformance/tests/token-nft/expected-ir.json:1` (`allowlist:429`) | `3400d66d`, `c6722c6c0922→8e3c44743d26`, +51/−17 | #116 re-stamp; no spec change | CONFIRMED |
| 52 | `conformance/tests/token-nft/expected-script.hex:1` (`allowlist:437`) | `3400d66d`, `e936f7786f38→1b17b847a1e8`, 1/1 | #116 re-stamp; no independent execution cited | CONFIRMED |
| 53 | `conformance/tests/convergence-proof/expected-script.hex:1` (`allowlist:445`) | `8a6494b4`, `c91f0d0de8fe→ccc59a1ea703`, 1/1 | Cited test executes a synthetic primitive script, not this exact fixture value | CONFIRMED |
| 54 | `conformance/tests/ec-demo/expected-script.hex:1` (`allowlist:452`) | `8a6494b4`, `63bdea797606→cf7dac2c75d6`, 1/1 | Cited test executes a synthetic primitive script, not this exact fixture value | CONFIRMED |
| 55 | `conformance/tests/ec-primitives/expected-script.hex:1` (`allowlist:459`) | `8a6494b4`, `6c22de1794ed→84f7c121db70`, 1/1 | Cited test executes a synthetic primitive script, not this exact fixture value | CONFIRMED |
| 56 | `conformance/tests/ec-unit/expected-script.hex:1` (`allowlist:466`) | `8a6494b4`, `0ada607d68c8→d543af1444b1`, 1/1 | Exact fixture is known and reproduced unspendable due `ecMul(2)` (`coverage-ledger.json:179`) | CONFIRMED |
| 57 | `conformance/tests/schnorr-zkp/expected-script.hex:1` (`allowlist:473`) | `8a6494b4`, `c8967ed9bc28→7c7501b30f34`, 1/1 | Cited test executes a synthetic primitive script, not this exact fixture value | CONFIRMED |
| 58 | `conformance/script-size-baseline.json:1` (`allowlist:480`) | Current origin `23ef2d2b`, `d0ba1a09307b→bde6dd61df90`, +1 | Allowlist still pins pre-merge hash; gate fails when explicitly asked to verify this file; no spec change | CONFIRMED |

## Totals

- `CLEARED`: 5/58 (3 official KATs, 2 exact executed scripts).
- `CONFIRMED`: 53/58. All 47 `intentional-spec-change` entries are self-attesting in this target: 43 remain #116 output re-stamps with no spec delta, bounded-loop contradicts the written spec, two were later re-authorized with stale reasons, and the size baseline entry is stale. Six of eight `differential-oracle` entries do not run the exact authorized value (one of those exact scripts is demonstrably unspendable).
