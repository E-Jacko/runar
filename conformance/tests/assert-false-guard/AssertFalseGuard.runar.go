package x

import runar "github.com/icellan/runar/packages/runar-go"

// AssertFalseGuard -- the runar.Assert(false)-else guard, in the two positions
// the multi-result branch node originally missed. Bump is a single property
// written under a guard whose else is the dead abort -- recognised as a
// ONE-branch chain, so excluded from declaring its result, and not rewritten
// either because the lift only rewrites chains of two or more. Dispatch is
// Selector's exact chain one loop deeper, where the lift never walks.
type AssertFalseGuard struct {
	runar.StatefulSmartContract

	Count runar.Bigint
	A     runar.Bigint
	B     runar.Bigint
}

func (c *AssertFalseGuard) Bump(n runar.Bigint) {
	if n > 0 {
		c.Count = c.Count + n
	} else {
		runar.Assert(false)
	}
}

func (c *AssertFalseGuard) Dispatch(sel runar.Bigint, v runar.Bigint) {
	for i := runar.Bigint(0); i < 2; i++ {
		if sel == 0 {
			c.A = v
		} else if sel == 1 {
			c.B = v
		} else {
			runar.Assert(false)
		}
	}
}
