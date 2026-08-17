# Invalid-program rejection matrix

The required malformed-input fuzz was not completed because the conformance
runner and direct tsx entry points fail before loading test code with
node:net listen EPERM on the sandbox temporary IPC pipe; Java's runner also
cannot start because Gradle's native-platform arm64 library is unavailable.
Therefore these are deliberately conservative verdicts, not claims of parity.
The unknown-ANF tests exist in
packages/runar-compiler/src/__tests__/unknown-anf-kind.test.ts and the
corresponding non-TS suites, but they do not constitute the requested fixed
duration, all-frontend fuzz.

unverifiable means no clean reject/diagnostic result was established for that
cell in this checkout. The source-level loader evidence is cited where it is
available.

| invalid class | ts | go | rust | python | zig | ruby | java |
|---|---|---|---|---|---|---|---|
| non-Rúnar call | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable |
| type error | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable |
| readonly mutation | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable |
| malformed or truncated source | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable | unverifiable |
| malformed or invalid --ir JSON | tested by loader unit, full category parity unverifiable | tested by loader unit, full category parity unverifiable | unverifiable | unverifiable | loader has explicit unknown-kind path at compilers/zig/src/ir/json.zig:279-287 | unverifiable | loader dispatch at compilers/java/src/main/java/runar/compiler/passes/AnfLoader.java:133-200 |
| unknown ANF kind | tested by packages/runar-compiler/src/__tests__/unknown-anf-kind.test.ts | tested by compilers/go/ir/unknown_anf_kind_error.go:7-25 | unverifiable | tested by compilers/python/tests/test_unknown_anf_kind.py:71-118 | loader has explicit unknown-kind path at compilers/zig/src/ir/json.zig:279-287 | unverifiable | unverifiable |

