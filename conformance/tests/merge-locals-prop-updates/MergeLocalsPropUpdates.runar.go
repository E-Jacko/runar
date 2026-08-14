//go:build ignore

package x

import runar "github.com/icellan/runar/packages/runar-go"

// MergeLocalsPropUpdates -- the branch-merge shape crossed with property
// mutation: one method that BOTH merges two locals across an `if` AND writes
// contract properties from the merged results. No contract in the repo did
// both before this one.
type MergeLocalsPropUpdates struct {
	runar.StatefulSmartContract

	A     runar.Bigint
	B     runar.Bigint
	Total runar.Bigint
}

func (c *MergeLocalsPropUpdates) Settle(amount runar.Bigint, toFirst runar.Bigint) {
	na := c.A
	nb := c.B
	if toFirst > 0 {
		na = na + amount
	} else {
		nb = nb + amount
	}
	c.A = na
	c.B = nb
	c.Total = na + nb
	c.AddOutput(1000, c.A, c.B, c.Total)
}
