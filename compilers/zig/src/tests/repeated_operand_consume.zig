//! Repeated-operand consume bug (hand-written ANF via compile-ir).
//!
//! Mirrors packages/runar-compiler/src/__tests__/repeated-operand-consume.test.ts.
//!
//! A binding whose ANF value reads the SAME ref at more than one operand
//! position used to make an independent last-use consume decision per load;
//! a consume-mode bringToTop of a ref already on top of the stack is a
//! no-op, so `t := x + x` left a single stack slot for OP_ADD (underflow at
//! runtime), or paired the opcode with the wrong slot when the ref was
//! buried. Canonical rule: an operand load may consume (ROLL) its ref only
//! when this binding is the ref's last use AND the ref occurs exactly once
//! in the value's FULL operand list. Repeated refs copy (PICK / DUP) at
//! every position. Unreachable from the frontend (every operand gets a
//! fresh temp); reachable via hand-written IR.

const std = @import("std");
const json_parser = @import("../ir/json.zig");
const types = @import("../ir/types.zig");
const stack_lower = @import("../passes/stack_lower.zig");
const peephole = @import("../passes/peephole.zig");
const emit = @import("../codegen/emit.zig");

/// Mirror main.zig's compileFromIR --hex pipeline:
/// parse ANF JSON -> stack lower -> peephole -> emitArtifact -> "script" hex.
fn compileIrToHex(allocator: std.mem.Allocator, json: []const u8) ![]const u8 {
    const program = try json_parser.parseANFProgram(allocator, json);
    const stack_program = try stack_lower.lower(allocator, program);
    const optimized_methods = try peephole.optimize(allocator, stack_program.methods);
    const optimized_stack_program = types.StackProgram{
        .methods = optimized_methods,
        .contract_name = stack_program.contract_name,
        .properties = stack_program.properties,
        .constructor_params = stack_program.constructor_params,
    };
    const artifact = try emit.emitArtifact(allocator, optimized_stack_program, program);
    const marker = "\"script\":\"";
    const idx = std.mem.indexOf(u8, artifact, marker) orelse return error.MissingHex;
    const after = idx + marker.len;
    const end = std.mem.indexOfPos(u8, artifact, after, "\"") orelse return error.MissingHex;
    return artifact[after..end];
}

test "bin_op with the same ref twice: t := x + x" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // unlock(x) { assert(x + x === target) }
    const json =
        \\{
        \\  "contractName": "Repeat",
        \\  "properties": [{"name": "target", "type": "bigint", "readonly": true}],
        \\  "methods": [{
        \\    "name": "unlock",
        \\    "params": [{"name": "x", "type": "bigint"}],
        \\    "body": [
        \\      {"name": "t0", "value": {"kind": "bin_op", "op": "+", "left": "x", "right": "x"}},
        \\      {"name": "t1", "value": {"kind": "load_prop", "name": "target"}},
        \\      {"name": "t2", "value": {"kind": "bin_op", "op": "===", "left": "t0", "right": "t1"}},
        \\      {"name": "t3", "value": {"kind": "assert", "value": "t2"}}
        \\    ],
        \\    "isPublic": true
        \\  }]
        \\}
    ;
    const hex = try compileIrToHex(a, json);
    // Both loads of x must COPY: DUP DUP ADD <placeholder OP_0> NUMEQUAL NIP.
    // Cross-tier canonical hex, byte-identical with the TS tier.
    try std.testing.expectEqualStrings("767693009c77", hex);
}

test "call with the same ref in two argument positions: min(x, x)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // unlock(x) { assert(min(x, x) === target) }
    const json =
        \\{
        \\  "contractName": "Repeat",
        \\  "properties": [{"name": "target", "type": "bigint", "readonly": true}],
        \\  "methods": [{
        \\    "name": "unlock",
        \\    "params": [{"name": "x", "type": "bigint"}],
        \\    "body": [
        \\      {"name": "t0", "value": {"kind": "call", "func": "min", "args": ["x", "x"]}},
        \\      {"name": "t1", "value": {"kind": "load_prop", "name": "target"}},
        \\      {"name": "t2", "value": {"kind": "bin_op", "op": "===", "left": "t0", "right": "t1"}},
        \\      {"name": "t3", "value": {"kind": "assert", "value": "t2"}}
        \\    ],
        \\    "isPublic": true
        \\  }]
        \\}
    ;
    const hex = try compileIrToHex(a, json);
    // DUP DUP MIN <placeholder OP_0> NUMEQUAL NIP
    try std.testing.expectEqualStrings("7676a3009c77", hex);
}

test "repeated ref buried below another live slot" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // unlock(x, y) { assert(x + x + y === target) } — at t0 the stack is
    // [x, y]: x sits at depth 1, so a naive rule pairs OP_ADD with the
    // wrong slot instead of copying x twice.
    const json =
        \\{
        \\  "contractName": "Repeat",
        \\  "properties": [{"name": "target", "type": "bigint", "readonly": true}],
        \\  "methods": [{
        \\    "name": "unlock",
        \\    "params": [{"name": "x", "type": "bigint"}, {"name": "y", "type": "bigint"}],
        \\    "body": [
        \\      {"name": "t0", "value": {"kind": "bin_op", "op": "+", "left": "x", "right": "x"}},
        \\      {"name": "t1", "value": {"kind": "bin_op", "op": "+", "left": "t0", "right": "y"}},
        \\      {"name": "t2", "value": {"kind": "load_prop", "name": "target"}},
        \\      {"name": "t3", "value": {"kind": "bin_op", "op": "===", "left": "t1", "right": "t2"}},
        \\      {"name": "t4", "value": {"kind": "assert", "value": "t3"}}
        \\    ],
        \\    "isPublic": true
        \\  }]
        \\}
    ;
    const hex = try compileIrToHex(a, json);
    // OVER DUP ADD SWAP ADD OP_0 NUMEQUAL NIP — byte-identical with TS.
    try std.testing.expectEqualStrings("7876937c93009c77", hex);
}

test "bin_op with distinct refs is unchanged (frontend canonical shape)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // Frontend-shaped ANF (fresh temp per operand) must not shift bytes.
    const json =
        \\{
        \\  "contractName": "Repeat",
        \\  "properties": [{"name": "target", "type": "bigint", "readonly": true}],
        \\  "methods": [{
        \\    "name": "unlock",
        \\    "params": [{"name": "x", "type": "bigint"}],
        \\    "body": [
        \\      {"name": "t0", "value": {"kind": "load_param", "name": "x"}},
        \\      {"name": "t1", "value": {"kind": "load_param", "name": "x"}},
        \\      {"name": "t2", "value": {"kind": "bin_op", "op": "+", "left": "t0", "right": "t1"}},
        \\      {"name": "t3", "value": {"kind": "load_prop", "name": "target"}},
        \\      {"name": "t4", "value": {"kind": "bin_op", "op": "===", "left": "t2", "right": "t3"}},
        \\      {"name": "t5", "value": {"kind": "assert", "value": "t4"}}
        \\    ],
        \\    "isPublic": true
        \\  }]
        \\}
    ;
    const hex = try compileIrToHex(a, json);
    // DUP SWAP ADD <placeholder OP_0> NUMEQUAL — canonical frontend Dbl shape.
    try std.testing.expectEqualStrings("767c93009c", hex);
}
