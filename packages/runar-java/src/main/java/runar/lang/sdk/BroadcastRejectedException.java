package runar.lang.sdk;

/**
 * Thrown when {@link MockProvider} refuses to acknowledge a broadcast
 * (testing-gap remediation Phase A5).
 *
 * <p>Distinct typed exception so a test can assert the fund-safety gate fired,
 * rather than matching on a generic {@link RuntimeException}.
 */
public class BroadcastRejectedException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public BroadcastRejectedException(String message) {
        super(message);
    }
}
