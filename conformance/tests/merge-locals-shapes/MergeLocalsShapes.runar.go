//go:build ignore

package x

import runar "github.com/icellan/runar/packages/runar-go"

// MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
// evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
// `if` whose merge lands at the outer level. Companion to
// `branch-merged-locals`, which pins the asymmetric k=2 case.
type MergeLocalsShapes struct {
	runar.StatefulSmartContract

	A runar.Bigint
	B runar.Bigint
	C runar.Bigint
}

func (c *MergeLocalsShapes) BothArms(x runar.Bigint, flag runar.Bigint) {
	na := c.A
	nb := c.B
	if flag > 0 {
		na = x + 1
		nb = x + 2
	} else {
		na = x + 3
		nb = x + 4
	}
	c.AddOutput(1000, na, nb, c.C)
}

func (c *MergeLocalsShapes) Three(x runar.Bigint, flag runar.Bigint) {
	na := c.A
	nb := c.B
	nc := c.C
	if flag > 0 {
		na = x + 1
		nb = x + 2
		nc = x + 3
	} else {
		na = x + 4
		nb = x + 5
		nc = x + 6
	}
	c.AddOutput(1000, na, nb, nc)
}

func (c *MergeLocalsShapes) Nested(x runar.Bigint, outer runar.Bigint, inner runar.Bigint) {
	na := c.A
	nb := c.B
	if outer > 0 {
		if inner > 0 {
			na = x + 1
		} else {
			nb = x + 2
		}
	}
	c.AddOutput(1000, na, nb, c.C)
}
