const runar = @import("runar");

pub const TerminalVarlenRead = struct {
    pub const Contract = runar.StatefulSmartContract;

    message: runar.ByteString = "",

    pub fn init(message: runar.ByteString) TerminalVarlenRead {
        return .{ .message = message };
    }

    pub fn post(self: *TerminalVarlenRead, newMessage: runar.ByteString) void {
        self.message = newMessage;
    }

    pub fn reveal(self: *const TerminalVarlenRead, minLen: i64) void {
        runar.assert(runar.len(self.message) > minLen);
    }
};
