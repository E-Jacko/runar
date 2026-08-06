require 'runar'

# MergeLocalsPropUpdates -- the branch-merge shape crossed with property
# mutation: one method that BOTH merges two locals across an `if` AND writes
# contract properties from the merged results. No contract in the repo did
# both before this one.
class MergeLocalsPropUpdates < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint
  prop :total, Bigint

  def initialize(a, b, total)
    super(a, b, total)
    @a = a
    @b = b
    @total = total
  end

  runar_public amount: Bigint, to_first: Bigint
  def settle(amount, to_first)
    na = @a
    nb = @b
    if to_first > 0
      na = na + amount
    else
      nb = nb + amount
    end
    @a = na
    @b = nb
    @total = na + nb
    add_output(1000, @a, @b, @total)
  end
end
