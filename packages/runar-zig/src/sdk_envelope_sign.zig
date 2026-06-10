//! GAP-064: canonical RFC 6979 deterministic ECDSA over secp256k1 (nonce HMAC
//! uses PLAIN SHA-256) — the wire-protocol signing path for the signed-envelope
//! cross-tier interop matrix.
//!
//! Why this exists separately from `sdk_signer.zig`, and why it does NOT use
//! Zig's stdlib ECDSA signer:
//!
//!   * `sdk_signer.LocalSigner` signs BIP-143 sighashes via
//!     `bsvz.crypto.PrivateKey.signDigest256`, which routes through bsvz's
//!     `EcdsaSha256d` (double-SHA256). Its RFC 6979 nonce hashes the message
//!     with SHA-256d, so for an arbitrary 32-byte digest it derives a DIFFERENT
//!     deterministic `k` than the other six Rúnar tiers (all plain-SHA-256
//!     nonce). bsvz is a gitignored fetch cache and cannot be patched here.
//!
//!   * Zig's stdlib `EcdsaSecp256k1Sha256` derives its nonce from the
//!     "Deterministic ECDSA with Additional Randomness" draft, NOT canonical
//!     RFC 6979: it folds a `noise` block (32 zero bytes when null) into the
//!     HMAC-DRBG seed and uses the raw digest rather than `bits2octets(h)`.
//!     That yields a different `k` than @bsv/sdk / go-sdk / k256 / the
//!     Python+Ruby implementations, so it also diverges.
//!
//! This module therefore implements canonical RFC 6979 §3.2 directly on top of
//! Zig's secp256k1 scalar/point primitives (HMAC-SHA256 DRBG, no noise,
//! `bits2octets` reduction), then applies BIP-62 low-S normalization and DER
//! encoding. The output is byte-identical to @bsv/sdk `primitives/ECDSA` sign
//! and the five other tiers.

const std = @import("std");

const Secp256k1 = std.crypto.ecc.Secp256k1;
const Scalar = Secp256k1.scalar.Scalar;
const HmacSha256 = std.crypto.auth.hmac.sha2.HmacSha256;

/// N/2 (big-endian, 32 bytes). s is "high" (must be flipped) iff s > N/2.
const HALF_N_BE: [32]u8 = .{
    0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d,
    0xdf, 0xe9, 0x2f, 0x46, 0x68, 0x1b, 0x20, 0xa0,
};

pub const SignError = error{ InvalidPrivateKey, SigningFailed };

/// `bits2octets(h)` per RFC 6979 §2.3.4 for a 256-bit hash on a 256-bit curve:
/// reduce the hash modulo N and return the 32-byte big-endian encoding. With
/// qlen == hlen == 256 the bits2int step is the identity, so this is `h mod N`.
fn bits2octets(digest: [32]u8) [32]u8 {
    // Scalar.fromBytes64 reduces a wide input mod N; we left-pad the 32-byte
    // digest into a 64-byte buffer to get an unconditional reduction.
    var wide: [64]u8 = [_]u8{0} ** 64;
    @memcpy(wide[32..], &digest);
    return Scalar.fromBytes64(wide, .big).toBytes(.big);
}

fn hmac(key: []const u8, msgs: []const []const u8) [32]u8 {
    var mac = HmacSha256.init(key);
    for (msgs) |m| mac.update(m);
    var out: [32]u8 = undefined;
    mac.final(&out);
    return out;
}

/// RFC 6979 §3.2 HMAC-DRBG nonce generator. Stateful so that a caller which
/// rejects a candidate's *signature* (r == 0 or s == 0, §3.2 final paragraph)
/// draws a NEW `k` on the next call instead of re-deriving the same one.
const Rfc6979Drbg = struct {
    k: [32]u8,
    v: [32]u8,

    /// Steps b–g: `x_oct` = int2octets(privkey), `h1_oct` = bits2octets(digest).
    fn init(x_oct: [32]u8, h1_oct: [32]u8) Rfc6979Drbg {
        var st: Rfc6979Drbg = .{ .v = [_]u8{0x01} ** 32, .k = [_]u8{0x00} ** 32 };
        // K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1)); V = HMAC_K(V)
        st.k = hmac(&st.k, &.{ &st.v, &[_]u8{0x00}, &x_oct, &h1_oct });
        st.v = hmac(&st.k, &.{&st.v});
        // K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1)); V = HMAC_K(V)
        st.k = hmac(&st.k, &.{ &st.v, &[_]u8{0x01}, &x_oct, &h1_oct });
        st.v = hmac(&st.k, &.{&st.v});
        return st;
    }

    /// Step h: next candidate `k` in [1, N-1]. The retry update
    /// (K = HMAC_K(V || 0x00); V = HMAC_K(V)) is applied eagerly after every
    /// emitted candidate — the update is deterministic in (K, V), so this
    /// yields the exact same candidate sequence as the lazy on-reject update
    /// the RFC describes, while leaving the state ready for a re-draw.
    fn next(self: *Rfc6979Drbg) Scalar {
        while (true) {
            // T = V (single block, since hlen == qlen == 256).
            self.v = hmac(&self.k, &.{&self.v});
            const t = self.v;
            // K = HMAC_K(V || 0x00); V = HMAC_K(V).
            self.k = hmac(&self.k, &.{ &self.v, &[_]u8{0x00} });
            self.v = hmac(&self.k, &.{&self.v});
            if (Scalar.fromBytes(t, .big)) |s| {
                if (!s.isZero()) return s;
            } else |_| {}
        }
    }
};

/// Sign `digest` (a 32-byte hash, e.g. sha256(payload)) with `priv_key_be`
/// (32-byte big-endian secp256k1 scalar) using canonical RFC 6979 deterministic
/// ECDSA (plain-SHA-256 nonce). Writes the low-S DER signature into `der_buf`
/// and returns the populated slice. The digest is the message representative —
/// it is signed directly and never re-hashed.
pub fn signDigestLowSDer(
    priv_key_be: [32]u8,
    digest: [32]u8,
    der_buf: *[72]u8,
) SignError![]u8 {
    const x = Scalar.fromBytes(priv_key_be, .big) catch return error.InvalidPrivateKey;
    if (x.isZero()) return error.InvalidPrivateKey;

    const z = bits2octets(digest); // message representative, reduced mod N
    const z_scalar = Scalar.fromBytes(z, .big) catch return error.SigningFailed;

    var drbg = Rfc6979Drbg.init(priv_key_be, z);
    while_k: while (true) {
        const k = drbg.next();

        // R = k*G; r = R.x mod N.
        const rp = Secp256k1.basePoint.mul(k.toBytes(.big), .big) catch continue :while_k;
        const rx = rp.affineCoordinates().x.toBytes(.big);
        const r = Scalar.fromBytes64(blk: {
            var wide: [64]u8 = [_]u8{0} ** 64;
            @memcpy(wide[32..], &rx);
            break :blk wide;
        }, .big);
        if (r.isZero()) continue :while_k;

        // s = k^-1 * (z + r*x) mod N.
        const s = k.invert().mul(z_scalar.add(r.mul(x)));
        if (s.isZero()) continue :while_k;

        // BIP-62 low-S normalization.
        var s_bytes = s.toBytes(.big);
        if (std.mem.order(u8, &s_bytes, &HALF_N_BE) == .gt) {
            s_bytes = s.neg().toBytes(.big); // N - s
        }

        return encodeDer(r.toBytes(.big), s_bytes, der_buf);
    }
}

/// DER-encode (r, s) as 0x30 len 0x02 rlen r 0x02 slen s, with minimal
/// big-endian integers (strip leading zeros; prepend 0x00 if high bit set).
fn encodeDer(r_be: [32]u8, s_be: [32]u8, der_buf: *[72]u8) []u8 {
    var r_int: [33]u8 = undefined;
    const r_slice = minimalInt(&r_be, &r_int);
    var s_int: [33]u8 = undefined;
    const s_slice = minimalInt(&s_be, &s_int);

    var i: usize = 0;
    der_buf[i] = 0x30;
    i += 1;
    der_buf[i] = @intCast(2 + r_slice.len + 2 + s_slice.len);
    i += 1;
    der_buf[i] = 0x02;
    i += 1;
    der_buf[i] = @intCast(r_slice.len);
    i += 1;
    @memcpy(der_buf[i .. i + r_slice.len], r_slice);
    i += r_slice.len;
    der_buf[i] = 0x02;
    i += 1;
    der_buf[i] = @intCast(s_slice.len);
    i += 1;
    @memcpy(der_buf[i .. i + s_slice.len], s_slice);
    i += s_slice.len;
    return der_buf[0..i];
}

/// Render a 32-byte big-endian integer as a minimal DER INTEGER body: strip
/// leading zero bytes, then prepend a single 0x00 if the high bit is set (so
/// the value stays non-negative). Writes into `out` (>= 33 bytes) and returns
/// the populated slice.
fn minimalInt(be: []const u8, out: *[33]u8) []u8 {
    var start: usize = 0;
    while (start < be.len - 1 and be[start] == 0x00) start += 1;
    const body = be[start..];
    if (body[0] & 0x80 != 0) {
        out[0] = 0x00;
        @memcpy(out[1 .. 1 + body.len], body);
        return out[0 .. 1 + body.len];
    }
    @memcpy(out[0..body.len], body);
    return out[0..body.len];
}

// ---------------------------------------------------------------------------
// Tests — canonical public RFC 6979 secp256k1 vector.
// ---------------------------------------------------------------------------

test "RFC 6979 canonical vector: priv=1, msg=\"Satoshi Nakamoto\" — nonce k and low-S DER signature" {
    // The widely published secp256k1 RFC 6979 (plain-SHA-256 nonce) vector:
    //   priv = 0x...01, h1 = sha256("Satoshi Nakamoto")
    //   k = 8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15
    //   r = 934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d8
    //   s = 2442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5 (low-S)
    var priv: [32]u8 = [_]u8{0} ** 32;
    priv[31] = 0x01;

    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash("Satoshi Nakamoto", &digest, .{});

    // Nonce check (private path: k must match the published vector exactly).
    var drbg = Rfc6979Drbg.init(priv, bits2octets(digest));
    const k = drbg.next();
    var expected_k: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&expected_k, "8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15");
    try std.testing.expectEqualSlices(u8, &expected_k, &k.toBytes(.big));

    // Full signature check (r and s in minimal low-S DER). r's high bit is
    // set (0x93...), so DER prefixes its INTEGER body with 0x00 (33 bytes).
    var der_buf: [72]u8 = undefined;
    const der = try signDigestLowSDer(priv, digest, &der_buf);
    var expected_der: [71]u8 = undefined;
    _ = try std.fmt.hexToBytes(&expected_der, "3045022100934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d802202442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5");
    try std.testing.expectEqualSlices(u8, &expected_der, der);
}
