module StatefulWOTSGate {
    use runar::types::{ByteString};
    use runar::crypto::{verifyWOTS};
    use runar::StatefulSmartContract;

    // StatefulWOTSGate — stateful + post-quantum interaction fixture (GAP-407).
    resource struct StatefulWOTSGate {
        count: &mut Int,
    }

    public fun advance(contract: &mut StatefulWOTSGate, msg: ByteString, sig: ByteString, wotsPubKey: ByteString) {
        assert!(verifyWOTS(msg, sig, wotsPubKey), 0);
        contract.count = contract.count + 1;
    }
}
