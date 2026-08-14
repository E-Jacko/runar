import {
  SmartContract, assert, len,
  ecAdd, ecMul, ecMulGen, ecNegate, ecOnCurve,
  ecEncodeCompressed, ecMakePoint, ecPointX, ecPointY,
} from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ECUnit extends SmartContract {
    readonly pubKey: ByteString;
    constructor(pubKey: ByteString) {
        super(pubKey);
        this.pubKey = pubKey;
    }

    public testOps() {
        const g = ecMulGen(1n);
        assert(ecOnCurve(g));
        const neg = ecNegate(g);
        assert(ecOnCurve(neg));
        const doubled = ecMul(g, 2n);
        assert(ecOnCurve(doubled));
        const sum = ecAdd(g, g);
        assert(ecOnCurve(sum));
        // P + (-P) is the point at infinity, which affine x||y cannot encode:
        // ecAdd returns the all-zero blob from a SUCCESSFUL script (as does
        // ecMul for any k = 0 mod n). ecOnCurve is the only way to notice,
        // so it must reject it. Selecting the tangent on px == qx alone
        // returned 2G here instead: on-curve, plausible, and accepted.
        const infPt = ecAdd(g, neg);
        assert(!ecOnCurve(infPt));
        const x = ecPointX(g);
        const y = ecPointY(g);
        const rebuilt = ecMakePoint(x, y);
        assert(ecOnCurve(rebuilt));
        const compressed = ecEncodeCompressed(g);
        assert(len(compressed) == 33n);
        assert(true);
    }
}
