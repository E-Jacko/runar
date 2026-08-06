require 'runar'

# MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
# evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
# `if` whose merge lands at the outer level. Companion to
# `branch-merged-locals`, which pins the asymmetric k=2 case.
class MergeLocalsShapes < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint
  prop :c, Bigint

  def initialize(a, b, c)
    super(a, b, c)
    @a = a
    @b = b
    @c = c
  end

  runar_public x: Bigint, flag: Bigint
  def both_arms(x, flag)
    na = @a
    nb = @b
    if flag > 0
      na = x + 1
      nb = x + 2
    else
      na = x + 3
      nb = x + 4
    end
    add_output(1000, na, nb, @c)
  end

  runar_public x: Bigint, flag: Bigint
  def three(x, flag)
    na = @a
    nb = @b
    nc = @c
    if flag > 0
      na = x + 1
      nb = x + 2
      nc = x + 3
    else
      na = x + 4
      nb = x + 5
      nc = x + 6
    end
    add_output(1000, na, nb, nc)
  end

  runar_public x: Bigint, outer: Bigint, inner: Bigint
  def nested(x, outer, inner)
    na = @a
    nb = @b
    if outer > 0
      if inner > 0
        na = x + 1
      else
        nb = x + 2
      end
    end
    add_output(1000, na, nb, @c)
  end
end
