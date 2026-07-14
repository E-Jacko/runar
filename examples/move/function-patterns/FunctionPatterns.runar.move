module FunctionPatterns {
    use runar::StatefulSmartContract;
    use runar::types::{PubKey, Sig, Int};
    use runar::crypto::{check_sig};
    use runar::math::{percent_of, mul_div, clamp, safemod};

    resource struct FunctionPatterns {
        owner: PubKey,
        balance: &mut Int,
    }

    public fun deposit(contract: &mut FunctionPatterns, sig: Sig, amount: Int) {
        self.require_owner(sig);
        assert!(amount > 0, 0);
        contract.balance = contract.balance + amount;
    }

    public fun withdraw(contract: &mut FunctionPatterns, sig: Sig, amount: Int, fee_bps: Int) {
        self.require_owner(sig);
        assert!(amount > 0, 0);
        let fee: Int = self.compute_fee(amount, fee_bps);
        let total: Int = amount + fee;
        assert!(total <= contract.balance, 0);
        contract.balance = contract.balance - total;
    }

    public fun scale(contract: &mut FunctionPatterns, sig: Sig, numerator: Int, denominator: Int) {
        self.require_owner(sig);
        contract.balance = self.scale_value(contract.balance, numerator, denominator);
    }

    public fun normalize(contract: &mut FunctionPatterns, sig: Sig, lo: Int, hi: Int, step: Int) {
        self.require_owner(sig);
        let clamped: Int = self.clamp_value(contract.balance, lo, hi);
        contract.balance = self.round_down(clamped, step);
    }

    fun require_owner(sig: Sig) {
        assert!(check_sig(sig, self.owner), 0);
    }

    fun compute_fee(amount: Int, fee_bps: Int): Int {
        return percent_of(amount, fee_bps);
    }

    fun scale_value(value: Int, numerator: Int, denominator: Int): Int {
        return mul_div(value, numerator, denominator);
    }

    fun clamp_value(value: Int, lo: Int, hi: Int): Int {
        return clamp(value, lo, hi);
    }

    fun round_down(value: Int, step: Int): Int {
        let remainder: Int = safemod(value, step);
        return value - remainder;
    }
}
