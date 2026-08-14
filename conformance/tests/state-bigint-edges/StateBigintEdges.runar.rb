require 'runar'

# StateBigintEdges -- bigint state values at the SIGN boundary. A bigint state
# field is a fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN
# semantics): the sign lives in bit 0x80 of byte 7, so -1 is
# `0100000000000080` and NOT the two's-complement `ffffffffffffffff`. `shift`
# moves the two fields in opposite directions so one spend crosses the
# boundary in both senses.
class StateBigintEdges < Runar::StatefulSmartContract
  prop :lo, Bigint
  prop :hi, Bigint

  def initialize(lo, hi)
    super(lo, hi)
    @lo = lo
    @hi = hi
  end

  runar_public delta: Bigint
  def shift(delta)
    @lo = @lo - delta
    @hi = @hi + delta
    add_output(1000, @lo, @hi)
  end
end
