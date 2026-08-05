package x

import runar "github.com/icellan/runar/packages/runar-go"

// BranchMergedLocals -- regression fixture for the branch-merged-local
// miscompilation reported privately on 2026-08-03: two locals initialised from
// state, the arms of an `if` reassigning DIFFERENT ones, both feeding the
// continuation. Post-branch references used to resolve to the dead pre-branch
// binding.
type BranchMergedLocals struct {
	runar.StatefulSmartContract

	A runar.Bigint
	B runar.Bigint
}

func (c *BranchMergedLocals) Bid(amount runar.Bigint, toFirst runar.Bigint) {
	na := c.A
	nb := c.B
	if toFirst > 0 {
		na = amount
	} else {
		nb = amount
	}
	c.AddOutput(1000, na, nb)
}
