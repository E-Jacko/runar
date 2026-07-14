from runar import StatefulSmartContract, ByteString, Bigint, public, assert_, verify_wots


# StatefulWOTSGate — stateful + post-quantum interaction fixture (GAP-407).
class StatefulWOTSGate(StatefulSmartContract):
    count: Bigint

    def __init__(self, count: Bigint):
        super().__init__(count)
        self.count = count

    @public
    def advance(self, msg: ByteString, sig: ByteString, wots_pub_key: ByteString):
        assert_(verify_wots(msg, sig, wots_pub_key))
        self.count = self.count + 1
