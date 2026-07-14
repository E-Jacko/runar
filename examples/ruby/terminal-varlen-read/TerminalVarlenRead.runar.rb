require 'runar'

# TerminalVarlenRead -- regression fixture for GitHub issue #100: a terminal
# method that reads the mutable variable-length (ByteString) state field.
class TerminalVarlenRead < Runar::StatefulSmartContract
  prop :message, ByteString

  def initialize(message)
    super(message)
    @message = message
  end

  runar_public new_message: ByteString
  def post(new_message)
    @message = new_message
  end

  runar_public min_len: Bigint
  def reveal(min_len)
    assert len(@message) > min_len
  end
end
