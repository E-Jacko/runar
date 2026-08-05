require 'runar'

# BranchMergedLocals -- regression fixture for the branch-merged-local
# miscompilation reported privately on 2026-08-03: two locals initialised from
# state, the arms of an `if` reassigning DIFFERENT ones, both feeding the
# continuation. Post-branch references used to resolve to the dead pre-branch
# binding.
class BranchMergedLocals < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint

  def initialize(a, b)
    super(a, b)
    @a = a
    @b = b
  end

  runar_public amount: Bigint, to_first: Bigint
  def bid(amount, to_first)
    na = @a
    nb = @b
    if to_first > 0
      na = amount
    else
      nb = amount
    end
    add_output(1000, na, nb)
  end
end
