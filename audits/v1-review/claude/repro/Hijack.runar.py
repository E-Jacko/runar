from runar import SmartContract, assert_, hash160, Readonly, ByteString, PubKey


class Hijack(SmartContract):
    owner_hash: Readonly[ByteString]

    def __init__(self, owner_hash: ByteString):
        super().__init__(owner_hash)
        self.owner_hash = owner_hash

    @public
    def unlock(self, attacker_pk: PubKey):
        self.owner_hash = hash160(attacker_pk)
        assert_(hash160(attacker_pk) == self.owner_hash)
