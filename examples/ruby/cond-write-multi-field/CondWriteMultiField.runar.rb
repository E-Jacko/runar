require 'runar'

# CondWriteMultiField -- regression fixture for GitHub issue #99: a
# conditional write of two mutable state fields in an `if` without an `else`.
class CondWriteMultiField < Runar::StatefulSmartContract
  prop :a, Bigint
  prop :b, Bigint

  def initialize(a, b)
    super(a, b)
    @a = a
    @b = b
  end

  runar_public flag: Bigint
  def bump(flag)
    if flag > 0
      @a = @a + 1
      @b = @b + 2
    end
    add_output(1000, @a, @b)
  end
end
