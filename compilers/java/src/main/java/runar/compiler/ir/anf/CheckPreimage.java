package runar.compiler.ir.anf;

public record CheckPreimage(String preimage, Integer sighashFlag) implements AnfValue {
    /** Backwards-compatible constructor: default sighash (ALL|FORKID, 0x41). */
    public CheckPreimage(String preimage) {
        this(preimage, null);
    }

    @Override
    public String kind() {
        return "check_preimage";
    }
}
