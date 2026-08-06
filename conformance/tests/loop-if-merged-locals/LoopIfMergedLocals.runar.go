//go:build ignore

package x

import runar "github.com/icellan/runar/packages/runar-go"

// LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
// the enclosing scope, which is what an `if` inside a loop body always makes
// them. Companion to `merge-locals-shapes` (merged locals LIVE after the `if`)
// and `bounded-loop` (a loop with no branch in it) -- neither covers their
// intersection, which is where the merge block's premise fails.
type LoopIfMergedLocals struct {
	runar.StatefulSmartContract

	A runar.Bigint
	B runar.Bigint
	C runar.Bigint
}

func (c *LoopIfMergedLocals) Guarded(x runar.Bigint, limit runar.Bigint) {
	na := runar.Bigint(0)
	nb := runar.Bigint(0)
	for i := runar.Bigint(0); i < 2; i++ {
		if i < limit {
			na = na + x
			nb = nb + na
		}
	}
	c.AddOutput(1000, na, nb, c.C)
}

func (c *LoopIfMergedLocals) AfterIf(x runar.Bigint, limit runar.Bigint) {
	na := runar.Bigint(0)
	nb := runar.Bigint(0)
	for i := runar.Bigint(0); i < 2; i++ {
		if i < limit {
			na = na + x
		}
		nb = nb + na
	}
	c.AddOutput(1000, na, nb, c.C)
}
