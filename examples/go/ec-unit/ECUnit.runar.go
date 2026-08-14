package contract

import runar "github.com/icellan/runar/packages/runar-go"

// ECUnit -- Unit-style exercises for the secp256k1 EC built-ins.
type ECUnit struct {
	runar.SmartContract
	PubKey runar.ByteString `runar:"readonly"`
}

// TestOps exercises ecMulGen, ecOnCurve, ecNegate, ecMul, ecAdd, ecPointX,
// ecPointY, ecMakePoint, and ecEncodeCompressed.
func (c *ECUnit) TestOps() {
	g := runar.EcMulGen(1)
	runar.Assert(runar.EcOnCurve(g))
	neg := runar.EcNegate(g)
	runar.Assert(runar.EcOnCurve(neg))
	doubled := runar.EcMul(g, 2)
	runar.Assert(runar.EcOnCurve(doubled))
	sum := runar.EcAdd(g, g)
	runar.Assert(runar.EcOnCurve(sum))
	// P + (-P) is the point at infinity: EcAdd returns the all-zero blob from
	// a SUCCESSFUL script, and EcOnCurve must reject it.
	infPt := runar.EcAdd(g, neg)
	runar.Assert(!runar.EcOnCurve(infPt))
	x := runar.EcPointX(g)
	y := runar.EcPointY(g)
	rebuilt := runar.EcMakePoint(x, y)
	runar.Assert(runar.EcOnCurve(rebuilt))
	compressed := runar.EcEncodeCompressed(g)
	runar.Assert(runar.Len(compressed) == 33)
	runar.Assert(true)
}
