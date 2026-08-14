//go:build ignore

package x

import runar "github.com/icellan/runar/packages/runar-go"

// StateBigintEdges -- bigint state values at the SIGN boundary. A bigint state
// field is a fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN
// semantics): the sign lives in bit 0x80 of byte 7, so -1 is
// `0100000000000080` and NOT the two's-complement `ffffffffffffffff`. `shift`
// moves the two fields in opposite directions so one spend crosses the
// boundary in both senses.
type StateBigintEdges struct {
	runar.StatefulSmartContract

	Lo runar.Bigint
	Hi runar.Bigint
}

func (c *StateBigintEdges) Shift(delta runar.Bigint) {
	c.Lo = c.Lo - delta
	c.Hi = c.Hi + delta
	c.AddOutput(1000, c.Lo, c.Hi)
}
