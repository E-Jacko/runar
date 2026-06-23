use runar::prelude::*;

// StatefulWOTSGate - stateful + post-quantum interaction fixture (GAP-407).
#[runar::contract]
struct StatefulWOTSGate {
    count: Int,
}

impl StatefulWOTSGate {
    pub fn advance(&mut self, msg: &ByteString, sig: &ByteString, wots_pub_key: &ByteString) {
        assert!(verify_wots(msg, sig, wots_pub_key));
        self.count = self.count + 1;
    }
}
