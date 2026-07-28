package x

import runar "github.com/icellan/runar/packages/runar-go"

// Selector -- regression fixture for deep-review finding C20: a dispatch method
// whose branches each end in a single state update and whose terminal else is
// runar.Assert(false). The abort must survive ANF lowering so an out-of-range
// selector fails the script instead of producing a spendable no-op.
type Selector struct {
	runar.StatefulSmartContract

	A runar.Bigint
	B runar.Bigint
}

func (c *Selector) Set(i runar.Bigint, v runar.Bigint) {
	if i == 0 {
		c.A = v
	} else if i == 1 {
		c.B = v
	} else {
		runar.Assert(false)
	}
}
