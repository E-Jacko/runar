require 'runar'

# AssertFalseGuard -- the `assert false`-else guard, in the two positions the
# multi-result branch node originally missed. `bump` is a single property
# written under a guard whose else is the dead abort -- recognised as a
# ONE-branch chain, so excluded from declaring its result, and not rewritten
# either because the lift only rewrites chains of two or more. `dispatch` is
# `Selector`'s exact chain one loop deeper, where the lift never walks.
class AssertFalseGuard < Runar::StatefulSmartContract
  prop :count, Bigint
  prop :a, Bigint
  prop :b, Bigint

  def initialize(count, a, b)
    super(count, a, b)
    @count = count
    @a = a
    @b = b
  end

  runar_public n: Bigint
  def bump(n)
    if n > 0
      @count = @count + n
    else
      assert false
    end
  end

  runar_public sel: Bigint, v: Bigint
  def dispatch(sel, v)
    for i in 0...2
      if sel == 0
        @a = v
      elsif sel == 1
        @b = v
      else
        assert false
      end
    end
  end
end
