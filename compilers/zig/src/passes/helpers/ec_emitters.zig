const std = @import("std");
const registry = @import("crypto_builtins.zig");

const Allocator = std.mem.Allocator;

pub const PushValue = union(enum) {
    bytes: []const u8,
    integer: i64,
    boolean: bool,
};

pub const StackIf = struct {
    then: []StackOp,
    @"else": ?[]StackOp = null,
};

pub const StackOp = union(enum) {
    push: PushValue,
    dup: void,
    swap: void,
    drop: void,
    nip: void,
    over: void,
    rot: void,
    tuck: void,
    roll: u32,
    pick: u32,
    opcode: []const u8,
    @"if": StackIf,
};

const FIELD_P_MINUS_2_LOW_BITS: u32 = 0xfffffc2d;

const field_p_be = [_]u8{
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xfc, 0x2f,
};

const curve_n_be = [_]u8{
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
    0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b,
    0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41,
};

// secp256k1 curve ORDER n as a script number (little-endian sign-magnitude).
// The MSB has bit 7 set, so a 0x00 sign byte keeps it positive.
const curve_n_script_num_le = [_]u8{
    0x41, 0x41, 0x36, 0xd0, 0x8c, 0x5e, 0xd2, 0xbf,
    0x3b, 0xa0, 0x48, 0xaf, 0xe6, 0xdc, 0xae, 0xba,
    0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0x00,
};

const gen_x_be = [_]u8{
    0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac,
    0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07,
    0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9,
    0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98,
};

const gen_y_be = [_]u8{
    0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65,
    0x5d, 0xa4, 0xfb, 0xfc, 0x0e, 0x11, 0x08, 0xa8,
    0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19,
    0x9c, 0x47, 0xd0, 0x8f, 0xfb, 0x10, 0xd4, 0xb8,
};

pub const EcEmitterError = anyerror;

pub const EcOpBundle = struct {
    allocator: Allocator,
    ops: []StackOp,
    owned_bytes: [][]u8,

    pub fn deinit(self: *EcOpBundle) void {
        deinitOpsRecursive(self.allocator, self.ops);
        self.allocator.free(self.ops);
        for (self.owned_bytes) |bytes| self.allocator.free(bytes);
        self.allocator.free(self.owned_bytes);
        self.* = undefined;
    }
};

pub fn buildBuiltinOps(allocator: Allocator, builtin: registry.CryptoBuiltin) EcEmitterError!EcOpBundle {
    var tracker = try ECTracker.init(allocator, initialNames(builtin));
    errdefer tracker.deinit();

    switch (builtin) {
        .ec_add => try emitEcAdd(&tracker),
        .ec_mul => try emitEcMul(&tracker, "_pt", "_k"),
        .ec_mul_gen => try emitEcMulGen(&tracker),
        .ec_negate => try emitEcNegate(&tracker),
        .ec_on_curve => try emitEcOnCurve(&tracker),
        else => return error.UnsupportedBuiltin,
    }

    return tracker.takeBundle();
}

pub fn appendBuiltinOps(
    list: *std.ArrayListUnmanaged(StackOp),
    allocator: Allocator,
    builtin: registry.CryptoBuiltin,
) EcEmitterError!EcOpBundle {
    var bundle = try buildBuiltinOps(allocator, builtin);
    errdefer bundle.deinit();
    try list.appendSlice(allocator, bundle.ops);
    return bundle;
}

pub fn deinitOpsRecursive(allocator: Allocator, ops: []StackOp) void {
    for (ops) |*op| {
        switch (op.*) {
            .@"if" => |stack_if| {
                deinitOpsRecursive(allocator, stack_if.then);
                allocator.free(stack_if.then);
                if (stack_if.@"else") |else_ops| {
                    deinitOpsRecursive(allocator, else_ops);
                    allocator.free(else_ops);
                }
            },
            else => {},
        }
    }
}

const ECTracker = struct {
    allocator: Allocator,
    names: std.ArrayListUnmanaged(?[]const u8),
    ops: std.ArrayListUnmanaged(StackOp),
    owned_bytes: std.ArrayListUnmanaged([]u8),

    fn init(allocator: Allocator, initial_names: []const ?[]const u8) !ECTracker {
        var names: std.ArrayListUnmanaged(?[]const u8) = .empty;
        errdefer names.deinit(allocator);
        try names.appendSlice(allocator, initial_names);
        return .{
            .allocator = allocator,
            .names = names,
            .ops = .empty,
            .owned_bytes = .empty,
        };
    }

    fn deinit(self: *ECTracker) void {
        deinitOpsRecursive(self.allocator, self.ops.items);
        self.ops.deinit(self.allocator);
        self.names.deinit(self.allocator);
        for (self.owned_bytes.items) |bytes| self.allocator.free(bytes);
        self.owned_bytes.deinit(self.allocator);
    }

    fn takeBundle(self: *ECTracker) !EcOpBundle {
        const ops = try self.ops.toOwnedSlice(self.allocator);
        errdefer self.allocator.free(ops);
        const owned_bytes = try self.owned_bytes.toOwnedSlice(self.allocator);
        self.names.deinit(self.allocator);
        self.names = .empty;
        self.ops = .empty;
        self.owned_bytes = .empty;
        return .{
            .allocator = self.allocator,
            .ops = ops,
            .owned_bytes = owned_bytes,
        };
    }

    fn depth(self: *const ECTracker) usize {
        return self.names.items.len;
    }

    fn findDepth(self: *const ECTracker, name: []const u8) !usize {
        var i = self.names.items.len;
        while (i > 0) {
            i -= 1;
            const slot = self.names.items[i] orelse continue;
            if (std.mem.eql(u8, slot, name)) {
                return self.names.items.len - 1 - i;
            }
        }
        return error.UnsupportedBuiltin;
    }

    fn emitRaw(self: *ECTracker, op: StackOp) !void {
        try self.ops.append(self.allocator, op);
    }

    fn emitOpcode(self: *ECTracker, code: []const u8) !void {
        try self.emitRaw(.{ .opcode = code });
    }

    fn emitPushIntRaw(self: *ECTracker, value: i64) !void {
        try self.emitRaw(.{ .push = .{ .integer = value } });
    }

    fn emitPushBytesRaw(self: *ECTracker, value: []const u8) !void {
        try self.emitRaw(.{ .push = .{ .bytes = value } });
    }

    fn pushInt(self: *ECTracker, name: ?[]const u8, value: i64) !void {
        try self.emitPushIntRaw(value);
        try self.names.append(self.allocator, name);
    }

    fn pushOwnedBytes(self: *ECTracker, name: ?[]const u8, value: []u8) !void {
        try self.owned_bytes.append(self.allocator, value);
        try self.emitPushBytesRaw(value);
        try self.names.append(self.allocator, name);
    }

    fn pushStaticBytes(self: *ECTracker, name: ?[]const u8, value: []const u8) !void {
        try self.emitPushBytesRaw(value);
        try self.names.append(self.allocator, name);
    }

    fn dup(self: *ECTracker, name: ?[]const u8) !void {
        try self.emitRaw(.{ .dup = {} });
        try self.names.append(self.allocator, name);
    }

    fn drop(self: *ECTracker) !void {
        try self.emitRaw(.{ .drop = {} });
        _ = self.names.pop();
    }

    fn swap(self: *ECTracker) !void {
        try self.emitRaw(.{ .swap = {} });
        const len = self.names.items.len;
        if (len >= 2) {
            const tmp = self.names.items[len - 1];
            self.names.items[len - 1] = self.names.items[len - 2];
            self.names.items[len - 2] = tmp;
        }
    }

    fn rot(self: *ECTracker) !void {
        try self.emitRaw(.{ .rot = {} });
        const len = self.names.items.len;
        if (len >= 3) {
            const rolled = self.names.orderedRemove(len - 3);
            try self.names.append(self.allocator, rolled);
        }
    }

    fn over(self: *ECTracker, name: ?[]const u8) !void {
        try self.emitRaw(.{ .over = {} });
        try self.names.append(self.allocator, name);
    }

    fn roll(self: *ECTracker, depth_from_top: usize) !void {
        if (depth_from_top == 0) return;
        if (depth_from_top == 1) return self.swap();
        if (depth_from_top == 2) return self.rot();
        try self.emitRaw(.{ .roll = @intCast(depth_from_top) });
        const idx = self.names.items.len - 1 - depth_from_top;
        const rolled = self.names.orderedRemove(idx);
        try self.names.append(self.allocator, rolled);
    }

    fn pick(self: *ECTracker, depth_from_top: usize, name: ?[]const u8) !void {
        if (depth_from_top == 0) return self.dup(name);
        if (depth_from_top == 1) return self.over(name);
        try self.emitRaw(.{ .pick = @intCast(depth_from_top) });
        try self.names.append(self.allocator, name);
    }

    fn toTop(self: *ECTracker, name: []const u8) !void {
        try self.roll(try self.findDepth(name));
    }

    fn copyToTop(self: *ECTracker, name: []const u8, copy_name: ?[]const u8) !void {
        try self.pick(try self.findDepth(name), copy_name);
    }

    fn renameTop(self: *ECTracker, name: ?[]const u8) void {
        if (self.names.items.len > 0) {
            self.names.items[self.names.items.len - 1] = name;
        }
    }

    fn popNames(self: *ECTracker, count: usize) void {
        var i: usize = 0;
        while (i < count and self.names.items.len > 0) : (i += 1) {
            _ = self.names.pop();
        }
    }

    fn rawBlock(
        self: *ECTracker,
        consume_count: usize,
        produce_name: ?[]const u8,
        body: *const fn (*ECTracker) anyerror!void,
    ) !void {
        self.popNames(consume_count);
        try body(self);
        if (produce_name) |name| {
            try self.names.append(self.allocator, name);
        }
    }
};

fn initialNames(builtin: registry.CryptoBuiltin) []const ?[]const u8 {
    return switch (builtin) {
        .ec_add => &.{ "_pa", "_pb" },
        .ec_mul => &.{ "_pt", "_k" },
        .ec_mul_gen => &.{ "_k" },
        .ec_negate => &.{ "_pt" },
        .ec_on_curve => &.{ "_pt" },
        else => &.{},
    };
}

fn emitNumEqualOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_NUMEQUAL");
}

fn emitAddOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_ADD");
}

fn emitSubOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_SUB");
}

fn emitMulOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_MUL");
}

fn emitCatOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_CAT");
}

fn emitEqualOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_EQUAL");
}

fn emitDivOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_DIV");
}

fn emit2DivOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_2DIV");
}

fn emitRshiftnumOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_RSHIFTNUM");
}

fn emitModOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_MOD");
}

fn emitLessThanOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_LESSTHAN");
}

fn emitBoolAndOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_BOOLAND");
}

fn emitFieldModSequence(t: *ECTracker) !void {
    try t.emitOpcode("OP_2DUP");
    try t.emitOpcode("OP_MOD");
    try t.emitRaw(.{ .rot = {} });
    try t.emitRaw(.{ .drop = {} });
    try t.emitRaw(.{ .over = {} });
    try t.emitOpcode("OP_ADD");
    try t.emitRaw(.{ .swap = {} });
    try t.emitOpcode("OP_MOD");
}

fn emitSplit32Sequence(t: *ECTracker) !void {
    try t.emitPushIntRaw(32);
    try t.emitOpcode("OP_SPLIT");
}

fn emitBytesToUnsignedNumSequence(t: *ECTracker) !void {
    try emitReverse32Raw(t);
    try t.emitPushBytesRaw(&.{0x00});
    try t.emitOpcode("OP_CAT");
    try t.emitOpcode("OP_BIN2NUM");
}

fn emitUnsignedNumToBigEndianBytes32Sequence(t: *ECTracker) !void {
    try t.emitPushIntRaw(33);
    try t.emitOpcode("OP_NUM2BIN");
    try t.emitPushIntRaw(32);
    try t.emitOpcode("OP_SPLIT");
    try t.emitRaw(.{ .drop = {} });
    try emitReverse32Raw(t);
}

fn emitReverse32Raw(t: *ECTracker) !void {
    try t.emitOpcode("OP_0");
    try t.emitRaw(.{ .swap = {} });
    for (0..32) |_| {
        try t.emitPushIntRaw(1);
        try t.emitOpcode("OP_SPLIT");
        try t.emitRaw(.{ .rot = {} });
        try t.emitRaw(.{ .rot = {} });
        try t.emitRaw(.{ .swap = {} });
        try t.emitOpcode("OP_CAT");
        try t.emitRaw(.{ .swap = {} });
    }
    try t.emitRaw(.{ .drop = {} });
}

fn beToUnsignedScriptNumAlloc(allocator: Allocator, be: []const u8) ![]u8 {
    var first: usize = 0;
    while (first < be.len and be[first] == 0) : (first += 1) {}
    if (first == be.len) {
        return allocator.dupe(u8, &.{});
    }

    const trimmed = be[first..];
    const needs_sign_byte = (trimmed[0] & 0x80) != 0;
    const out_len = trimmed.len + @as(usize, if (needs_sign_byte) 1 else 0);
    const out = try allocator.alloc(u8, out_len);
    for (trimmed, 0..) |_, idx| {
        out[idx] = trimmed[trimmed.len - 1 - idx];
    }
    if (needs_sign_byte) out[out_len - 1] = 0;
    return out;
}

fn pow2ScriptNumAlloc(allocator: Allocator, bit: usize) ![]u8 {
    const byte_index = bit / 8;
    const byte_mask: u8 = @as(u8, 1) << @intCast(bit % 8);
    const needs_sign_byte = byte_mask == 0x80;
    const out_len = byte_index + 1 + @as(usize, if (needs_sign_byte) 1 else 0);
    const out = try allocator.alloc(u8, out_len);
    @memset(out, 0);
    out[byte_index] = byte_mask;
    return out;
}

fn pushFieldPNum(t: *ECTracker, name: []const u8) !void {
    const encoded = try beToUnsignedScriptNumAlloc(t.allocator, field_p_be[0..]);
    try t.pushOwnedBytes(name, encoded);
}

fn pushCurveNNum(t: *ECTracker, name: []const u8) !void {
    const encoded = try beToUnsignedScriptNumAlloc(t.allocator, curve_n_be[0..]);
    try t.pushOwnedBytes(name, encoded);
}

fn pushPow2Divisor(t: *ECTracker, name: []const u8, bit: usize) !void {
    if (bit <= 4) {
        const value: i64 = @as(i64, 1) << @intCast(bit);
        try t.pushInt(name, value);
        return;
    }
    const encoded = try pow2ScriptNumAlloc(t.allocator, bit);
    try t.pushOwnedBytes(name, encoded);
}

fn generatorPointAlloc(allocator: Allocator) ![]u8 {
    const point = try allocator.alloc(u8, 64);
    @memcpy(point[0..32], gen_x_be[0..]);
    @memcpy(point[32..64], gen_y_be[0..]);
    return point;
}

fn fieldMod(t: *ECTracker, a_name: []const u8, result_name: []const u8) !void {
    try t.toTop(a_name);
    try pushFieldPNum(t, "_fmod_p");
    try t.rawBlock(2, result_name, emitFieldModSequence);
}

fn fieldAdd(t: *ECTracker, a_name: []const u8, b_name: []const u8, result_name: []const u8) !void {
    try t.toTop(a_name);
    try t.toTop(b_name);
    try t.rawBlock(2, "_fadd_sum", emitAddOpcode);
    try fieldMod(t, "_fadd_sum", result_name);
}

fn fieldSub(t: *ECTracker, a_name: []const u8, b_name: []const u8, result_name: []const u8) !void {
    try t.toTop(a_name);
    try t.toTop(b_name);
    try t.rawBlock(2, "_fsub_diff", emitSubOpcode);
    try fieldMod(t, "_fsub_diff", result_name);
}

fn fieldMul(t: *ECTracker, a_name: []const u8, b_name: []const u8, result_name: []const u8) !void {
    try t.toTop(a_name);
    try t.toTop(b_name);
    try t.rawBlock(2, "_fmul_prod", emitMulOpcode);
    try fieldMod(t, "_fmul_prod", result_name);
}

fn emit2MulOpcode(t: *ECTracker) !void {
    try t.emitOpcode("OP_2MUL");
}

fn fieldMulConst(t: *ECTracker, a_name: []const u8, c: i64, result_name: []const u8) !void {
    try t.toTop(a_name);
    if (c == 2) {
        // Use OP_2MUL (single opcode, no push needed)
        try t.rawBlock(1, "_fmc_prod", emit2MulOpcode);
    } else {
        try t.pushInt("_fmc_c", c);
        try t.rawBlock(2, "_fmc_prod", emitMulOpcode);
    }
    try fieldMod(t, "_fmc_prod", result_name);
}

fn fieldSqr(t: *ECTracker, a_name: []const u8, result_name: []const u8) !void {
    try t.copyToTop(a_name, "_fsqr_copy");
    try fieldMul(t, a_name, "_fsqr_copy", result_name);
}

fn fieldInv(t: *ECTracker, a_name: []const u8, result_name: []const u8) !void {
    try t.copyToTop(a_name, "_inv_r");

    var i: usize = 0;
    while (i < 222) : (i += 1) {
        try fieldSqr(t, "_inv_r", "_inv_r2");
        t.renameTop("_inv_r");
        try t.copyToTop(a_name, "_inv_a");
        try fieldMul(t, "_inv_r", "_inv_a", "_inv_m");
        t.renameTop("_inv_r");
    }

    try fieldSqr(t, "_inv_r", "_inv_r2");
    t.renameTop("_inv_r");

    var bit: i32 = 31;
    while (bit >= 0) : (bit -= 1) {
        try fieldSqr(t, "_inv_r", "_inv_r2");
        t.renameTop("_inv_r");
        if (((FIELD_P_MINUS_2_LOW_BITS >> @intCast(bit)) & 1) != 0) {
            try t.copyToTop(a_name, "_inv_a");
            try fieldMul(t, "_inv_r", "_inv_a", "_inv_m");
            t.renameTop("_inv_r");
        }
    }

    try t.toTop(a_name);
    try t.drop();
    try t.toTop("_inv_r");
    t.renameTop(result_name);
}

fn decomposePoint(t: *ECTracker, point_name: []const u8, x_name: []const u8, y_name: []const u8) !void {
    try t.toTop(point_name);
    t.popNames(1);
    try emitSplit32Sequence(t);
    try t.names.append(t.allocator, "_dp_xb");
    try t.names.append(t.allocator, "_dp_yb");

    try t.toTop("_dp_yb");
    try t.rawBlock(1, y_name, emitBytesToUnsignedNumSequence);

    try t.toTop("_dp_xb");
    try t.rawBlock(1, x_name, emitBytesToUnsignedNumSequence);
    try t.swap();
}

fn composePoint(t: *ECTracker, x_name: []const u8, y_name: []const u8, result_name: []const u8) !void {
    try t.toTop(x_name);
    try t.rawBlock(1, "_cp_xb", emitUnsignedNumToBigEndianBytes32Sequence);

    try t.toTop(y_name);
    try t.rawBlock(1, "_cp_yb", emitUnsignedNumToBigEndianBytes32Sequence);

    try t.toTop("_cp_xb");
    try t.toTop("_cp_yb");
    try t.rawBlock(2, result_name, emitCatOpcode);
}

fn affineAdd(t: *ECTracker) !void {
    // The chord slope s = (qy - py) / (qx - px) is undefined when P == Q: the
    // denominator is zero and the correct slope is the TANGENT, 3px^2 / (2py).
    // Without this, ecAdd(P, P) silently produced a wrong point, so every
    // contract that doubled deployed an unspendable script.
    //
    // Both cases are `s = num / den`, so only the NUMERATOR and DENOMINATOR are
    // selected and the single expensive fieldInv still runs exactly once.
    // rx and ry below are already correct for doubling.
    //
    //   cond = (px == qx)
    //   num  = cond ? 3*px^2 : (qy - py)
    //   den  = cond ? 2*py   : (qx - px)
    //
    // selected as `b + cond*(a - b)`, which needs no branch and keeps the
    // emitted op sequence identical on both paths.
    //
    // NOT handled: P == -Q, whose true result is the point at infinity, which
    // affine coordinates cannot represent.
    try t.copyToTop("px", "_px_eq");
    try t.copyToTop("qx", "_qx_eq");
    try t.rawBlock(2, "_cond", emitNumEqualOpcode);

    try t.copyToTop("qy", "_qy1");
    try t.copyToTop("py", "_py1");
    try fieldSub(t, "_qy1", "_py1", "_num_chord");

    try t.copyToTop("qx", "_qx1");
    try t.copyToTop("px", "_px1");
    try fieldSub(t, "_qx1", "_px1", "_den_chord");

    try t.copyToTop("px", "_px_t");
    try fieldSqr(t, "_px_t", "_px_sq");
    try fieldMulConst(t, "_px_sq", 3, "_num_tan");
    try t.copyToTop("py", "_py_t");
    try fieldMulConst(t, "_py_t", 2, "_den_tan");

    try t.copyToTop("_num_chord", "_num_chord_c");
    try fieldSub(t, "_num_tan", "_num_chord_c", "_num_diff");
    try t.copyToTop("_cond", "_cond_n");
    try fieldMul(t, "_num_diff", "_cond_n", "_num_sel");
    try fieldAdd(t, "_num_chord", "_num_sel", "_s_num");

    try t.copyToTop("_den_chord", "_den_chord_c");
    try fieldSub(t, "_den_tan", "_den_chord_c", "_den_diff");
    try t.toTop("_cond");
    t.renameTop("_cond_d");
    try fieldMul(t, "_den_diff", "_cond_d", "_den_sel");
    try fieldAdd(t, "_den_chord", "_den_sel", "_s_den");

    try fieldInv(t, "_s_den", "_s_den_inv");
    try fieldMul(t, "_s_num", "_s_den_inv", "_s");

    try t.copyToTop("_s", "_s_keep");
    try fieldSqr(t, "_s", "_s2");
    try t.copyToTop("px", "_px2");
    try fieldSub(t, "_s2", "_px2", "_rx1");
    try t.copyToTop("qx", "_qx2");
    try fieldSub(t, "_rx1", "_qx2", "rx");

    try t.copyToTop("px", "_px3");
    try t.copyToTop("rx", "_rx2");
    try fieldSub(t, "_px3", "_rx2", "_px_rx");
    try fieldMul(t, "_s_keep", "_px_rx", "_s_px_rx");
    try t.copyToTop("py", "_py2");
    try fieldSub(t, "_s_px_rx", "_py2", "ry");

    try t.toTop("px");
    try t.drop();
    try t.toTop("py");
    try t.drop();
    try t.toTop("qx");
    try t.drop();
    try t.toTop("qy");
    try t.drop();
}

// scalarModN reduces TOS mod n (the curve ORDER, not the field prime), result
// non-negative. Same op sequence as fieldMod, different modulus.
//
// This defines the scalar domain of ecMul over the whole of script-number
// space: negative scalars and scalars >= n both reduce into [0, n-1], and
// k = 0 / k = n give the point at infinity. Under the old ladder anything
// outside [1, n-1] was undefined behaviour.
fn scalarModN(t: *ECTracker, a_name: []const u8, result_name: []const u8) !void {
    try t.toTop(a_name);
    try t.pushStaticBytes("_smod_n", curve_n_script_num_le[0..]);
    try t.rawBlock(2, result_name, emitFieldModSequence);
}

// Projective point doubling — RCB Algorithm 9 (a = 0), 6M + 2S + 1 m_3b.
// Expects jx, jy, jz on the tracker; replaces them with the doubled point.
//
// Complete: doubling the point at infinity (0 : 1 : 0) yields (0 : 1 : 0).
//
// Deviations from the paper, both exact mod p and strictly cheaper here
// (a multiply by a small constant costs one push + OP_MUL, an addition costs
// a full reduce): line 2-4's Z3 = 8*t0 is one mulConst rather than three
// doublings, and line 11-12's t2 = 3*t2 is one mulConst rather than two adds.
fn projectiveDouble(t: *ECTracker) !void {
    // Copies of the inputs that outlive their first consumer.
    try t.copyToTop("jy", "_d_yz"); // t1 = Y*Z
    try t.copyToTop("jy", "_d_xy"); // t1 = X*Y  (line 16)
    try t.copyToTop("jz", "_d_zz_src"); // t2 = Z*Z

    try fieldSqr(t, "jy", "_d_t0"); // t0 = Y^2
    try t.copyToTop("_d_t0", "_d_t0a");
    try fieldMulConst(t, "_d_t0a", 8, "_d_Z3"); // Z3 = 8*t0
    try fieldMul(t, "_d_yz", "jz", "_d_t1"); // t1 = Y*Z
    try fieldSqr(t, "_d_zz_src", "_d_zz"); // Z^2
    try fieldMulConst(t, "_d_zz", 21, "_d_t2"); // t2 = b3*Z^2  (b3 = 3*7)

    try t.copyToTop("_d_t2", "_d_t2a");
    try t.copyToTop("_d_Z3", "_d_Z3a");
    try fieldMul(t, "_d_t2a", "_d_Z3a", "_d_X3"); // X3 = t2*Z3

    try t.copyToTop("_d_t0", "_d_t0b");
    try t.copyToTop("_d_t2", "_d_t2b");
    try fieldAdd(t, "_d_t0b", "_d_t2b", "_d_Y3"); // Y3 = t0+t2

    try fieldMul(t, "_d_t1", "_d_Z3", "_d_Z3n"); // Z3 = t1*Z3
    try fieldMulConst(t, "_d_t2", 3, "_d_t2c"); // t2 = 3*t2
    try fieldSub(t, "_d_t0", "_d_t2c", "_d_t0n"); // t0 = t0-t2

    try t.copyToTop("_d_t0n", "_d_t0na");
    try fieldMul(t, "_d_t0na", "_d_Y3", "_d_Y3b"); // Y3 = t0*Y3
    try fieldAdd(t, "_d_X3", "_d_Y3b", "_d_Y3c"); // Y3 = X3+Y3

    try fieldMul(t, "jx", "_d_xy", "_d_xyv"); // t1 = X*Y
    try fieldMul(t, "_d_t0n", "_d_xyv", "_d_X3b"); // X3 = t0*t1
    try fieldMulConst(t, "_d_X3b", 2, "_d_X3c"); // X3 = X3+X3

    try t.toTop("_d_X3c");
    t.renameTop("jx");
    try t.toTop("_d_Y3c");
    t.renameTop("jy");
    try t.toTop("_d_Z3n");
    t.renameTop("jz");
}

// Projective -> affine. Consumes jx, jy, jz; produces rx_name, ry_name.
//
// fieldInv is Fermat exponentiation, so inv(0) = 0: the point at infinity
// (Z = 0) converts to (0, 0), which is the all-zero Point blob. That is the
// agreed encoding for infinity — it is not a curve point, so it cannot be
// confused with a real result.
fn projectiveToAffine(t: *ECTracker, rx_name: []const u8, ry_name: []const u8) !void {
    try fieldInv(t, "jz", "_zinv");
    try t.copyToTop("_zinv", "_zinv_b");
    try fieldMul(t, "jx", "_zinv", rx_name);
    try fieldMul(t, "jy", "_zinv_b", ry_name);
}

// Build complete mixed-add ops for use inside OP_IF — RCB Algorithm 8 (a = 0),
// 11M + 2 m_3b. Adds the affine base point (ax, ay) into the accumulator.
//
// Complete: no exceptional cases. In particular
//   - accumulator == Q        -> correctly doubles (this is the case that broke
//     ecMul(P, 2n): the old Jacobian mixed-add computed H = R = 0 and returned
//     the zero point, which then absorbed every remaining iteration)
//   - accumulator == -Q       -> correctly yields the point at infinity
//   - accumulator == infinity -> correctly yields Q
//
// Uses an inner ECTracker cloned from the outer one, because the ops run under
// OP_IF: the outer tracker's model must describe the stack for BOTH branches,
// so this block has to be stack-shape neutral — same names, same depths, with
// jx/jy/jz replaced in place.
//
// Stack layout: [..., ax, ay, _k, jx, jy, jz]
// After:        [..., ax, ay, _k, jx', jy', jz']
fn buildProjectiveAddMixedInline(allocator: Allocator, base_names: []const ?[]const u8) !EcOpBundle {
    var inner = try ECTracker.init(allocator, base_names);
    errdefer inner.deinit();

    // The affine base survives every iteration, so only ever consume copies.
    try inner.copyToTop("ax", "_m_x2a"); // t0 = X1*X2
    try inner.copyToTop("ax", "_m_x2b"); // X2+Y2
    try inner.copyToTop("ax", "_m_x2c"); // X2*Z1
    try inner.copyToTop("ay", "_m_y2a"); // t1 = Y1*Y2
    try inner.copyToTop("ay", "_m_y2b"); // X2+Y2
    try inner.copyToTop("ay", "_m_y2c"); // Y2*Z1
    try inner.copyToTop("jx", "_m_x1a"); // X1+Y1
    try inner.copyToTop("jx", "_m_x1b"); // Y3+X1
    try inner.copyToTop("jy", "_m_y1a"); // X1+Y1
    try inner.copyToTop("jy", "_m_y1b"); // t4+Y1
    try inner.copyToTop("jz", "_m_z1a"); // X2*Z1
    try inner.copyToTop("jz", "_m_z1b"); // b3*Z1

    try fieldMul(&inner, "jx", "_m_x2a", "_m_t0"); // t0 = X1*X2
    try fieldMul(&inner, "jy", "_m_y2a", "_m_t1"); // t1 = Y1*Y2
    try fieldAdd(&inner, "_m_x2b", "_m_y2b", "_m_s1"); // X2+Y2
    try fieldAdd(&inner, "_m_x1a", "_m_y1a", "_m_s2"); // X1+Y1
    try fieldMul(&inner, "_m_s1", "_m_s2", "_m_t3"); // t3 = (X2+Y2)(X1+Y1)

    try inner.copyToTop("_m_t0", "_m_t0a");
    try inner.copyToTop("_m_t1", "_m_t1a");
    try fieldAdd(&inner, "_m_t0a", "_m_t1a", "_m_s3"); // t4 = t0+t1
    try fieldSub(&inner, "_m_t3", "_m_s3", "_m_t3b"); // t3 = t3-t4

    try fieldMul(&inner, "_m_y2c", "jz", "_m_t4"); // t4 = Y2*Z1
    try fieldAdd(&inner, "_m_t4", "_m_y1b", "_m_t4b"); // t4 = t4+Y1
    try fieldMul(&inner, "_m_x2c", "_m_z1a", "_m_Y3"); // Y3 = X2*Z1
    try fieldAdd(&inner, "_m_Y3", "_m_x1b", "_m_Y3b"); // Y3 = Y3+X1

    try fieldMulConst(&inner, "_m_t0", 3, "_m_t0b"); // t0 = 3*t0
    try fieldMulConst(&inner, "_m_z1b", 21, "_m_t2"); // t2 = b3*Z1

    try inner.copyToTop("_m_t1", "_m_t1b");
    try inner.copyToTop("_m_t2", "_m_t2a");
    try fieldAdd(&inner, "_m_t1b", "_m_t2a", "_m_Z3"); // Z3 = t1+t2
    try fieldSub(&inner, "_m_t1", "_m_t2", "_m_t1c"); // t1 = t1-t2
    try fieldMulConst(&inner, "_m_Y3b", 21, "_m_Y3c"); // Y3 = b3*Y3

    try inner.copyToTop("_m_Y3c", "_m_Y3ca");
    try inner.copyToTop("_m_t4b", "_m_t4ba");
    try fieldMul(&inner, "_m_t4ba", "_m_Y3ca", "_m_X3"); // X3 = t4*Y3

    try inner.copyToTop("_m_t3b", "_m_t3ba");
    try inner.copyToTop("_m_t1c", "_m_t1ca");
    try fieldMul(&inner, "_m_t3ba", "_m_t1ca", "_m_t2b"); // t2 = t3*t1
    try fieldSub(&inner, "_m_t2b", "_m_X3", "_m_X3b"); // X3 = t2-X3

    try inner.copyToTop("_m_t0b", "_m_t0ba");
    try fieldMul(&inner, "_m_Y3c", "_m_t0ba", "_m_Y3d"); // Y3 = Y3*t0

    try inner.copyToTop("_m_Z3", "_m_Z3a");
    try fieldMul(&inner, "_m_t1c", "_m_Z3a", "_m_t1d"); // t1 = t1*Z3
    try fieldAdd(&inner, "_m_t1d", "_m_Y3d", "_m_Y3e"); // Y3 = t1+Y3

    try fieldMul(&inner, "_m_t0b", "_m_t3b", "_m_t0c"); // t0 = t0*t3
    try fieldMul(&inner, "_m_Z3", "_m_t4b", "_m_Z3b"); // Z3 = Z3*t4
    try fieldAdd(&inner, "_m_Z3b", "_m_t0c", "_m_Z3c"); // Z3 = Z3+t0

    try inner.toTop("_m_X3b");
    inner.renameTop("jx");
    try inner.toTop("_m_Y3e");
    inner.renameTop("jy");
    try inner.toTop("_m_Z3c");
    inner.renameTop("jz");

    return inner.takeBundle();
}

fn emitEcAdd(t: *ECTracker) !void {
    try decomposePoint(t, "_pa", "px", "py");
    try decomposePoint(t, "_pb", "qx", "qy");
    try affineAdd(t);
    try composePoint(t, "rx", "ry", "_result");
}

// 256-iteration MSB-first double-and-add over homogeneous projective
// coordinates, using the RCB COMPLETE formulas. The accumulator starts at the
// point at infinity, so every one of the 256 bits is handled uniformly.
//
// The previous version ran 257 iterations over k+3n with an accumulator seeded
// at P, to guarantee a set leading bit. That relied on the INCOMPLETE Jacobian
// mixed-add never being handed two equal points — which it was, for k = 2, on
// the final iteration, yielding an all-zero point. No choice of offset avoids
// this: every candidate multiple of n merely relocates the collision onto
// different small scalars. Completeness is the only fix that holds for an
// operand the caller chooses.
fn emitEcMul(t: *ECTracker, point_name: []const u8, scalar_name: []const u8) !void {
    try decomposePoint(t, point_name, "ax", "ay");

    // Reduce the scalar into [0, n-1] so the 256-bit ladder covers the whole
    // domain: negative k and k >= n are now defined rather than undefined.
    try scalarModN(t, scalar_name, "_k");

    // Accumulator := point at infinity (0 : 1 : 0). Legal input to both complete
    // formulas, which is exactly why no special leading-bit handling is needed.
    try t.pushInt("jx", 0);
    try t.pushInt("jy", 1);
    try t.pushInt("jz", 0);

    var bit: i32 = 255;
    while (bit >= 0) : (bit -= 1) {
        try projectiveDouble(t);

        try t.copyToTop("_k", "_k_copy");
        if (bit == 1) {
            // Single-bit shift: OP_2DIV (no push needed)
            try t.rawBlock(1, "_shifted", emit2DivOpcode);
        } else if (bit > 1) {
            // Multi-bit shift: push shift amount, OP_RSHIFTNUM
            try t.pushInt("_shift", @as(i64, bit));
            try t.rawBlock(2, "_shifted", emitRshiftnumOpcode);
        } else {
            t.renameTop("_shifted");
        }
        try t.pushInt("_two", 2);
        try t.rawBlock(2, "_bit", emitModOpcode);

        try t.toTop("_bit");
        t.popNames(1);

        var add_bundle = try buildProjectiveAddMixedInline(t.allocator, t.names.items);
        errdefer add_bundle.deinit();

        try t.owned_bytes.appendSlice(t.allocator, add_bundle.owned_bytes);
        t.allocator.free(add_bundle.owned_bytes);
        add_bundle.owned_bytes = &.{};

        try t.emitRaw(.{ .@"if" = .{ .then = add_bundle.ops, .@"else" = null } });
        add_bundle.ops = &.{};
    }

    try projectiveToAffine(t, "_rx", "_ry");

    try t.toTop("ax");
    try t.drop();
    try t.toTop("ay");
    try t.drop();
    try t.toTop("_k");
    try t.drop();

    try composePoint(t, "_rx", "_ry", "_result");
}

fn emitEcMulGen(t: *ECTracker) !void {
    const point = try generatorPointAlloc(t.allocator);
    try t.pushOwnedBytes("_pt", point);
    try t.swap();
    try emitEcMul(t, "_pt", "_k");
}

fn emitEcNegate(t: *ECTracker) !void {
    try decomposePoint(t, "_pt", "_nx", "_ny");
    try pushFieldPNum(t, "_fp");
    try fieldSub(t, "_fp", "_ny", "_neg_y");
    try composePoint(t, "_nx", "_neg_y", "_result");
}

fn emitEcOnCurve(t: *ECTracker) !void {
    try decomposePoint(t, "_pt", "_x", "_y");

    // GAP-301: coordinate canonicity. `decomposePoint` BIN2NUMs each coordinate
    // as an unsigned value that may be >= p; the field arithmetic below would
    // silently reduce it mod p, so a non-canonical encoding of a valid point
    // would pass. Reject it: require x < p AND y < p (coordinates are unsigned,
    // so the 0 <= lower bound holds by construction). Combined with the curve
    // equation at the end via OP_BOOLAND so ecOnCurve still returns a boolean.
    try t.copyToTop("_x", "_x_lt");
    try pushFieldPNum(t, "_p_for_x");
    try t.rawBlock(2, "_x_canon", emitLessThanOpcode);
    try t.copyToTop("_y", "_y_lt");
    try pushFieldPNum(t, "_p_for_y");
    try t.rawBlock(2, "_y_canon", emitLessThanOpcode);
    try t.toTop("_x_canon");
    try t.toTop("_y_canon");
    try t.rawBlock(2, "_canon", emitBoolAndOpcode);

    try fieldSqr(t, "_y", "_y2");

    try t.copyToTop("_x", "_x_copy");
    try fieldSqr(t, "_x", "_x2");
    try fieldMul(t, "_x2", "_x_copy", "_x3");
    try t.pushInt("_seven", 7);
    try fieldAdd(t, "_x3", "_seven", "_rhs");

    try t.toTop("_y2");
    try t.toTop("_rhs");
    try t.rawBlock(2, "_curve_eq", emitEqualOpcode);

    try t.toTop("_canon");
    try t.toTop("_curve_eq");
    try t.rawBlock(2, "_result", emitBoolAndOpcode);
}

fn containsOpcode(ops: []const StackOp, opcode: []const u8) bool {
    for (ops) |op| {
        switch (op) {
            .opcode => |value| if (std.mem.eql(u8, value, opcode)) return true,
            .@"if" => |stack_if| {
                if (containsOpcode(stack_if.then, opcode)) return true;
                if (stack_if.@"else") |else_ops| {
                    if (containsOpcode(else_ops, opcode)) return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn firstPushBytesLen(ops: []const StackOp) ?usize {
    for (ops) |op| {
        switch (op) {
            .push => |value| switch (value) {
                .bytes => |bytes| return bytes.len,
                else => {},
            },
            else => {},
        }
    }
    return null;
}

test "ec add helper emits affine split and compose flow" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_add);
    defer bundle.deinit();

    try std.testing.expect(bundle.ops.len > 0);
    try std.testing.expect(containsOpcode(bundle.ops, "OP_SPLIT"));
    try std.testing.expect(containsOpcode(bundle.ops, "OP_CAT"));
    try std.testing.expectEqualStrings("OP_CAT", bundle.ops[bundle.ops.len - 1].opcode);
}

// ---------------------------------------------------------------------------
// T-11: Op-count goldens for the Zig EC helper bundles.
//
// The structural tests above check load-bearing opcodes (OP_SPLIT, OP_CAT,
// 257 OP_IF branches in ec_mul, ...) but not the total op-count. These
// goldens pin the Zig helper's pre-stack-lowering bundle size so a
// regression in `buildBuiltinOps` surfaces here as a localized failure
// rather than only as a cross-tier hex mismatch from the golden harness.
//
// The counts diverge from the Python/Java peers because the Zig tier
// represents control flow at the helper level as a single `.@"if"` op
// (containing nested `.then` / `.else` slices), whereas Python/Java
// flatten if-bodies into separate ops. Final compiled hex is byte-
// identical (enforced by the conformance harness).
// ---------------------------------------------------------------------------

test "ec helper op-count goldens" {
    const cases = .{
        .{ registry.CryptoBuiltin.ec_add, "ecAdd", @as(usize, 8183) },
        .{ registry.CryptoBuiltin.ec_mul, "ecMul", @as(usize, 57181) },
        .{ registry.CryptoBuiltin.ec_mul_gen, "ecMulGen", @as(usize, 57183) },
        .{ registry.CryptoBuiltin.ec_negate, "ecNegate", @as(usize, 945) },
        .{ registry.CryptoBuiltin.ec_on_curve, "ecOnCurve", @as(usize, 530) },
    };
    inline for (cases) |c| {
        var bundle = try buildBuiltinOps(std.testing.allocator, c[0]);
        defer bundle.deinit();
        if (bundle.ops.len != c[2]) {
            std.debug.print(
                "{s}: op-count drift — got {d}, want {d}\n",
                .{ c[1], bundle.ops.len, c[2] },
            );
        }
        try std.testing.expectEqual(c[2], bundle.ops.len);
    }
}

test "ec mul helper emits 256 conditional additions" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_mul);
    defer bundle.deinit();

    var if_count: usize = 0;
    for (bundle.ops) |op| switch (op) {
        .@"if" => if_count += 1,
        else => {},
    };

    try std.testing.expectEqual(@as(usize, 256), if_count);
}

test "ec mul gen helper seeds the generator point" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_mul_gen);
    defer bundle.deinit();

    try std.testing.expect(bundle.ops.len > 2);
    try std.testing.expectEqual(@as(?usize, 64), firstPushBytesLen(bundle.ops));
    try std.testing.expect(containsOpcode(bundle.ops, "OP_SPLIT"));
}

test "ec on curve helper ends in canonicity-anded equality" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_on_curve);
    defer bundle.deinit();

    // GAP-301: ecOnCurve now returns (x < p) AND (y < p) AND curve-equation,
    // so the final op is the OP_BOOLAND that folds canonicity into the result.
    try std.testing.expect(bundle.ops.len > 0);
    try std.testing.expectEqualStrings("OP_BOOLAND", bundle.ops[bundle.ops.len - 1].opcode);
    try std.testing.expect(containsOpcode(bundle.ops, "OP_LESSTHAN"));
}

test "ec negate helper uses field-prime script number bytes" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_negate);
    defer bundle.deinit();

    var found = false;
    for (bundle.ops) |op| {
        switch (op) {
            .push => |value| switch (value) {
                .bytes => |bytes| {
                    if (bytes.len != 33) continue;
                    if (bytes[0] != 0x2f or bytes[1] != 0xfc or bytes[2] != 0xff or bytes[3] != 0xff or bytes[4] != 0xfe) continue;
                    if (bytes[32] != 0x00) continue;
                    found = true;
                    break;
                },
                else => {},
            },
            else => {},
        }
    }

    try std.testing.expect(found);
}

test "ec mul helper reduces the scalar mod the curve order" {
    var bundle = try buildBuiltinOps(std.testing.allocator, .ec_mul);
    defer bundle.deinit();

    var found = false;
    for (bundle.ops) |op| {
        switch (op) {
            .push => |value| switch (value) {
                .bytes => |bytes| {
                    if (std.mem.eql(u8, bytes, curve_n_script_num_le[0..])) {
                        found = true;
                        break;
                    }
                },
                else => {},
            },
            else => {},
        }
    }

    try std.testing.expect(found);
}

test "field prime encoding uses initialized script number bytes" {
    const encoded = try beToUnsignedScriptNumAlloc(std.testing.allocator, field_p_be[0..]);
    defer std.testing.allocator.free(encoded);

    try std.testing.expectEqual(@as(usize, 33), encoded.len);
    try std.testing.expectEqual(@as(u8, 0x2f), encoded[0]);
    try std.testing.expectEqual(@as(u8, 0xfc), encoded[1]);
    try std.testing.expectEqual(@as(u8, 0xff), encoded[2]);
    try std.testing.expectEqual(@as(u8, 0xff), encoded[3]);
    try std.testing.expectEqual(@as(u8, 0xfe), encoded[4]);
    try std.testing.expectEqual(@as(u8, 0x00), encoded[32]);
}

test "small power-of-two divisors use small-int pushes" {
    var tracker = try ECTracker.init(std.testing.allocator, &.{});
    defer tracker.deinit();

    try pushPow2Divisor(&tracker, "_pow2", 4);

    try std.testing.expectEqual(@as(usize, 1), tracker.ops.items.len);
    try std.testing.expectEqualDeep(StackOp{ .push = .{ .integer = 16 } }, tracker.ops.items[0]);
}
