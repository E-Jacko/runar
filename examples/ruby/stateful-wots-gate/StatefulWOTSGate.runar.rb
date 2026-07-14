require 'runar'

# StatefulWOTSGate — stateful + post-quantum interaction fixture (GAP-407).
class StatefulWOTSGate < Runar::StatefulSmartContract
  prop :count, Bigint

  def initialize(count)
    super(count)
    @count = count
  end

  runar_public msg: ByteString, sig: ByteString, wots_pub_key: ByteString
  def advance(msg, sig, wots_pub_key)
    assert verify_wots(msg, sig, wots_pub_key)
    @count = @count + 1
  end
end
