require 'runar'

# LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
# the enclosing scope, which is what an `if` inside a loop body always makes
# them. Companion to `merge-locals-shapes` (merged locals LIVE after the `if`)
# and `bounded-loop` (a loop with no branch in it) -- neither covers their
# intersection, which is where the merge block's premise fails.
class LoopIfMergedLocals < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint
  prop :c, Bigint

  def initialize(a, b, c)
    super(a, b, c)
    @a = a
    @b = b
    @c = c
  end

  runar_public x: Bigint, limit: Bigint
  def guarded(x, limit)
    na = 0
    nb = 0
    for i in 0...2
      if i < limit
        na = na + x
        nb = nb + na
      end
    end
    add_output(1000, na, nb, @c)
  end

  runar_public x: Bigint, limit: Bigint
  def after_if(x, limit)
    na = 0
    nb = 0
    for i in 0...2
      if i < limit
        na = na + x
      end
      nb = nb + na
    end
    add_output(1000, na, nb, @c)
  end
end
