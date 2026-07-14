const runar = @import("runar");

// StatefulWOTSGate — stateful + post-quantum interaction fixture (GAP-407).
pub const StatefulWOTSGate = struct {
    pub const Contract = runar.StatefulSmartContract;
    count: i64 = 0,

    pub fn init(count: i64) StatefulWOTSGate {
        return .{ .count = count };
    }

    pub fn advance(self: *StatefulWOTSGate, msg: runar.ByteString, sig: runar.ByteString, wotsPubKey: runar.ByteString) void {
        runar.assert(runar.verifyWOTS(msg, sig, wotsPubKey));
        self.count = self.count + 1;
    }
};
