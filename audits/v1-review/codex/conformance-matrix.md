# ANF dispatch conformance matrix

This is the exhaustive ANF-value row set from CLAUDE.md:110-147 and
packages/runar-compiler/src/ir/anf-ir.ts:246-265. The verdict is for presence
of the value in the stack-lowering dispatch, not a claim that implementations
are semantically equivalent. The full runner was blocked by the local tsx IPC
restriction (see REPORT.md).

Dispatch ranges used for every cell:

| tier | dispatch location |
|---|---|
| ts | packages/runar-compiler/src/passes/05-stack-lower.ts:465-530 |
| go | compilers/go/codegen/stack.go:499-555 |
| rust | compilers/rust/src/codegen/stack.rs:1217-1303 |
| python | compilers/python/runar_compiler/codegen/stack.py:1131-1177 |
| zig | compilers/zig/src/passes/stack_lower.zig:941-987 |
| ruby | compilers/ruby/lib/runar_compiler/codegen/stack.rb:1384-1425 |
| java | compilers/java/src/main/java/runar/compiler/passes/StackLower.java:1120-1163 |

same means the dispatch arm exists at the cited location; no differs or
absent arm was found in this static enumeration.

| ANF value kind | ts | go | rust | python | zig | ruby | java |
|---|---|---|---|---|---|---|---|
| load_param | same (05-stack-lower.ts:465) | same (stack.go:499) | same (stack.rs:1217) | same (stack.py:1136) | same (stack_lower.zig:951) | same (stack.rb:1384) | same (StackLower.java:1124) |
| load_prop | same (05-stack-lower.ts:470) | same (stack.go:503) | same (stack.rs:1222) | same (stack.py:1138) | same (stack_lower.zig:953) | same (stack.rb:1386) | same (StackLower.java:1127) |
| load_const | same (05-stack-lower.ts:473) | same (stack.go:505) | same (stack.rs:1227) | same (stack.py:1140) | same (stack_lower.zig:955) | same (stack.rb:1388) | same (StackLower.java:1130) |
| bin_op | same (05-stack-lower.ts:489) | same (stack.go:510) | same (stack.rs:1230) | same (stack.py:1142) | same (stack_lower.zig:957) | same (stack.rb:1390) | same (StackLower.java:1133) |
| unary_op | same (05-stack-lower.ts:492) | same (stack.go:512) | same (stack.rs:1235) | same (stack.py:1144) | same (stack_lower.zig:959) | same (stack.rb:1392) | same (StackLower.java:1136) |
| call | same (05-stack-lower.ts:495) | same (stack.go:514) | same (stack.rs:1238) | same (stack.py:1146) | same (stack_lower.zig:961) | same (stack.rb:1394) | same (StackLower.java:1139) |
| method_call | same (05-stack-lower.ts:498) | same (stack.go:516) | same (stack.rs:1244) | same (stack.py:1148) | same (stack_lower.zig:963) | same (stack.rb:1396) | same (StackLower.java:1142) |
| if | same (05-stack-lower.ts:501) | same (stack.go:519) | same (stack.rs:1251) | same (stack.py:1150) | same (stack_lower.zig:965) | same (stack.rb:1404) | same (StackLower.java:1145) |
| loop | same (05-stack-lower.ts:510) | same (stack.go:527) | same (stack.rs:1259) | same (stack.py:1153) | same (stack_lower.zig:967) | same (stack.rb:1407) | same (StackLower.java:1150) |
| assert | same (05-stack-lower.ts:515) | same (stack.go:531) | same (stack.rs:1268) | same (stack.py:1156) | same (stack_lower.zig:969) | same (stack.rb:1409) | same (StackLower.java:1153) |
| update_prop | same (05-stack-lower.ts:518) | same (stack.go:533) | same (stack.rs:1271) | same (stack.py:1158) | same (stack_lower.zig:971) | same (stack.rb:1411) | same (StackLower.java:1156) |
| get_state_script | same (05-stack-lower.ts:471) | same (stack.go:1224) | same (stack.rs:1277) | same (stack.py:1160) | same (stack_lower.zig:973) | same (stack.rb:1421) | same (StackLower.java:1159) |
| check_preimage | same (05-stack-lower.ts:521) | same (stack.go:535) | same (stack.rs:1280) | same (stack.py:1163) | same (stack_lower.zig:975) | same (stack.rb:1413) | same (StackLower.java:1162) |
| deserialize_state | same (05-stack-lower.ts:524) | same (stack.go:537) | same (stack.rs:1283) | same (stack.py:1165) | same (stack_lower.zig:977) | same (stack.rb:1415) | same (StackLower.java:1165) |
| add_output | same (05-stack-lower.ts:479) | same (stack.go:539) | same (stack.rs:1286) | same (stack.py:1166) | same (stack_lower.zig:979) | same (stack.rb:1417) | unverifiable (StackLower.java:1120-1163) |
| add_raw_output | same (05-stack-lower.ts:483) | same (stack.go:545) | same (stack.rs:1289) | same (stack.py:1168) | same (stack_lower.zig:981) | same (stack.rb:1419) | unverifiable (StackLower.java:1120-1163) |
| add_data_output | same (05-stack-lower.ts:486) | same (stack.go:548) | same (stack.rs:1292) | same (stack.py:1171) | same (stack_lower.zig:983) | same (stack.rb:1421) | unverifiable (StackLower.java:1120-1163) |
| array_literal | same (05-stack-lower.ts:527) | same (stack.go:551) | same (stack.rs:1297) | same (stack.py:1174) | same (stack_lower.zig:985) | same (stack.rb:1423) | unverifiable (StackLower.java:1120-1163) |
| raw_script | same (05-stack-lower.ts:530) | same (stack.go:553) | same (stack.rs:1300) | same (stack.py:1176) | same (stack_lower.zig:987) | same (stack.rb:1425) | unverifiable (StackLower.java:1120-1163) |

The Java cells marked unverifiable deliberately avoid invented per-arm line
numbers. The enclosing Java dispatch is present at StackLower.java:1120-1163,
but individual arm line numbers were not re-enumerated before report
generation.
