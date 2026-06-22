package x

import runar "github.com/icellan/runar/packages/runar-go"

// CondWriteMultiField -- regression fixture for GitHub issue #99: a
// conditional write of two mutable state fields in an `if` without an `else`.
type CondWriteMultiField struct {
	runar.StatefulSmartContract

	A runar.Bigint
	B runar.Bigint
}

func (c *CondWriteMultiField) Bump(flag runar.Bigint) {
	if flag > 0 {
		c.A = c.A + 1
		c.B = c.B + 2
	}
	c.AddOutput(1000, c.A, c.B)
}
