require 'runar'

# Selector -- regression fixture for deep-review finding C20: a dispatch method
# whose branches each end in a single state update and whose terminal else is
# `assert false`. The abort must survive ANF lowering so an out-of-range
# selector fails the script instead of producing a spendable no-op.
class Selector < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint

  def initialize(a, b)
    super(a, b)
    @a = a
    @b = b
  end

  runar_public i: Bigint, v: Bigint
  def set(i, v)
    if i == 0
      @a = v
    elsif i == 1
      @b = v
    else
      assert false
    end
  end
end
