pragma runar ^0.1.0;

// StatefulWOTSGate — stateful + post-quantum interaction fixture (GAP-407).
contract StatefulWOTSGate is StatefulSmartContract {
    bigint count;

    constructor(bigint _count) {
        count = _count;
    }

    function advance(ByteString msg, ByteString sig, ByteString wotsPubKey) public {
        require(verifyWOTS(msg, sig, wotsPubKey));
        this.count = this.count + 1;
    }
}
