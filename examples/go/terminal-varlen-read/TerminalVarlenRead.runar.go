package x

import runar "github.com/icellan/runar/packages/runar-go"

// TerminalVarlenRead -- regression fixture for GitHub issue #100: a terminal
// method that reads the mutable variable-length (ByteString) state field.
type TerminalVarlenRead struct {
	runar.StatefulSmartContract

	Message runar.ByteString
}

func (c *TerminalVarlenRead) Post(newMessage runar.ByteString) {
	c.Message = newMessage
}

func (c *TerminalVarlenRead) Reveal(minLen runar.Bigint) {
	runar.Assert(runar.Len(c.Message) > minLen)
}
