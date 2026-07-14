package runar.compiler.ir.anf;

import java.math.BigInteger;
import java.util.List;

/**
 * Bounded, compile-time-unrolled loop.
 *
 * <p>The loop is unrolled {@code count} times; on iteration {@code i}
 * (0-based) the iterator variable holds {@code start + i * step}
 * (issue #121). Zero-start counting-up loops carry {@code start = 0}
 * and {@code step = 1}, which reproduces the historical
 * {@code i = 0..count-1} lowering byte-for-byte. Countdown loops carry
 * {@code step = -1}.
 */
public record Loop(int count, List<AnfBinding> body, String iterVar, BigInteger start, int step)
    implements AnfValue {
    @Override
    public String kind() {
        return "loop";
    }
}
