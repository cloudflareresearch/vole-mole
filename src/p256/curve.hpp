// The NIST P-256 curve y^2 = x^3 - 3 x + b over F_p, and ECDSA-P256-SHA256 (FIPS 186-5).
//
// This is reference code for building and checking proofs: point arithmetic in Jacobian
// coordinates, and signing and verification. Scalar multiplication is NOT constant time.

#ifndef VOLE_MOLE_P256_CURVE_HPP
#define VOLE_MOLE_P256_CURVE_HPP

#include "p256/field.hpp"
#include "sha256/sha256.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::p256 {

inline constexpr Fp CURVE_B = Fp::from_canonical(
    detail::limbs_from_hex("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"));

struct Affine {
    Fp x, y;
    bool inf = false;

    bool operator==(const Affine& o) const {
        return inf == o.inf && (inf || (x == o.x && y == o.y));
    }
    bool on_curve() const {
        return inf || y.square() == (x.square() - Fp::from_u64(3)) * x + CURVE_B;
    }
    Affine neg() const { return {x, -y, inf}; }
};

inline constexpr Affine GENERATOR = {
    Fp::from_canonical(
        detail::limbs_from_hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296")),
    Fp::from_canonical(
        detail::limbs_from_hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5")),
    false};

struct Jacobian {
    Fp x, y, z; // (x / z^2, y / z^3); z = 0 is the point at infinity

    static Jacobian infinity() { return {Fp::one(), Fp::one(), Fp::zero()}; }
    static Jacobian from(const Affine& p) {
        return p.inf ? infinity() : Jacobian{p.x, p.y, Fp::one()};
    }
    bool is_inf() const { return z.is_zero(); }

    // dbl-2001-b, for a = -3.
    Jacobian dbl() const {
        if (is_inf() || y.is_zero()) {
            return infinity();
        }
        const Fp delta = z.square();
        const Fp gamma = y.square();
        const Fp beta = x * gamma;
        const Fp t = (x - delta) * (x + delta);
        const Fp alpha = t + t + t;
        const Fp beta4 = beta + beta + beta + beta;
        const Fp x3 = alpha.square() - beta4 - beta4;
        const Fp z3 = (y + z).square() - gamma - delta;
        const Fp g2 = gamma.square();
        const Fp g8 = g2 + g2 + g2 + g2 + g2 + g2 + g2 + g2;
        const Fp y3 = alpha * (beta4 - x3) - g8;
        return {x3, y3, z3};
    }

    // add-2007-bl.
    Jacobian add(const Jacobian& o) const {
        if (is_inf()) {
            return o;
        }
        if (o.is_inf()) {
            return *this;
        }
        const Fp z1z1 = z.square();
        const Fp z2z2 = o.z.square();
        const Fp u1 = x * z2z2;
        const Fp u2 = o.x * z1z1;
        const Fp s1 = y * o.z * z2z2;
        const Fp s2 = o.y * z * z1z1;
        const Fp h = u2 - u1;
        const Fp rr = s2 - s1;
        if (h.is_zero()) {
            return rr.is_zero() ? dbl() : infinity();
        }
        const Fp i = (h + h).square();
        const Fp j = h * i;
        const Fp r = rr + rr;
        const Fp v = u1 * i;
        const Fp x3 = r.square() - j - v - v;
        const Fp s1j = s1 * j;
        const Fp y3 = r * (v - x3) - s1j - s1j;
        const Fp z3 = ((z + o.z).square() - z1z1 - z2z2) * h;
        return {x3, y3, z3};
    }

    Affine to_affine() const {
        if (is_inf()) {
            return {Fp::zero(), Fp::zero(), true};
        }
        const Fp zi = z.inv();
        const Fp zi2 = zi.square();
        return {x * zi2, y * zi2 * zi, false};
    }
};

// Convert many points to affine coordinates with one inversion.
inline std::vector<Affine> batch_to_affine(std::span<const Jacobian> pts) {
    std::vector<Fp> prefix(pts.size());
    Fp acc = Fp::one();
    for (size_t i = 0; i < pts.size(); ++i) {
        prefix[i] = acc;
        if (!pts[i].is_inf()) {
            acc *= pts[i].z;
        }
    }
    Fp inv = acc.inv();
    std::vector<Affine> out(pts.size());
    for (size_t i = pts.size(); i-- > 0;) {
        if (pts[i].is_inf()) {
            out[i] = {Fp::zero(), Fp::zero(), true};
            continue;
        }
        const Fp zi = inv * prefix[i];
        inv *= pts[i].z;
        const Fp zi2 = zi.square();
        out[i] = {pts[i].x * zi2, pts[i].y * zi2 * zi, false};
    }
    return out;
}

// k P for a 256-bit integer k (not reduced). Not constant time.
inline Jacobian scalar_mul(const Affine& p, const Limbs& k) {
    const Jacobian base = Jacobian::from(p);
    Jacobian acc = Jacobian::infinity();
    for (size_t i = 256; i-- > 0;) {
        acc = acc.dbl();
        if ((k[i / 64] >> (i % 64)) & 1) {
            acc = acc.add(base);
        }
    }
    return acc;
}

// A point whose discrete logarithm nobody knows: try-and-increment on x = SHA-256(label || ctr),
// choosing the even y.
inline Affine hash_to_point(std::span<const uint8_t> label) {
    // (p + 1) / 4
    Limbs e{};
    detail::limbs_add(e, Fp::M, Limbs{1, 0, 0, 0});
    for (size_t i = 0; i < 4; ++i) {
        e[i] = (e[i] >> 2) | (i < 3 ? e[i + 1] << 62 : 0);
    }
    for (uint32_t ctr = 0;; ++ctr) {
        std::vector<uint8_t> in(label.begin(), label.end());
        for (size_t b = 0; b < 4; ++b) {
            in.push_back(static_cast<uint8_t>(ctr >> (8 * b)));
        }
        const auto h = sha256::hash(in);
        const Fp x = Fp::reduce_32(h);
        const Fp rhs = (x.square() - Fp::from_u64(3)) * x + CURVE_B;
        Fp y = rhs.pow(e);
        if (y.square() == rhs) {
            if (y.bit(0)) {
                y = -y;
            }
            return {x, y, false};
        }
    }
}

// SEC 1 uncompressed encoding: 0x04 || x || y.
constexpr size_t PUBLIC_KEY_BYTES = 65;
using PublicKeyBytes = std::array<uint8_t, PUBLIC_KEY_BYTES>;

inline PublicKeyBytes encode_point(const Affine& p) {
    PublicKeyBytes out;
    out[0] = 0x04;
    const auto xb = p.x.to_bytes();
    const auto yb = p.y.to_bytes();
    std::copy(xb.begin(), xb.end(), out.begin() + 1);
    std::copy(yb.begin(), yb.end(), out.begin() + 33);
    return out;
}

// Decode and validate a public key: a point on the curve other than the identity. (Every such
// point has order n, since the cofactor is 1.)
inline std::optional<Affine> decode_point(std::span<const uint8_t, PUBLIC_KEY_BYTES> b) {
    if (b[0] != 0x04) {
        return std::nullopt;
    }
    const auto x = Fp::from_bytes(b.subspan<1, 32>());
    const auto y = Fp::from_bytes(b.subspan<33, 32>());
    if (!x || !y) {
        return std::nullopt;
    }
    Affine p{*x, *y, false};
    if (!p.on_curve()) {
        return std::nullopt;
    }
    return p;
}

// ECDSA signature (r, s), each 32 big-endian bytes.
struct Signature {
    Bytes32 r, s;
};

// e = SHA-256(msg) as an integer (the hash is as long as n, so it isn't truncated).
inline Limbs ecdsa_e(std::span<const uint8_t> msg) {
    const auto h = sha256::hash(msg);
    return Fp::limbs_from_be(h);
}

// Sign with secret key d and nonce k (both nonzero and less than n). For tests; not constant time.
inline std::optional<Signature> ecdsa_sign_with_nonce(const Fn& d, const Fn& k,
                                                       std::span<const uint8_t> msg) {
    const Affine rp = scalar_mul(GENERATOR, k.canonical()).to_affine();
    const Fn r = Fn::reduce_32(rp.x.to_bytes());
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    const Fn s = k.inv() * (e + r * d);
    if (r.is_zero() || s.is_zero()) {
        return std::nullopt;
    }
    return Signature{r.to_bytes(), s.to_bytes()};
}

inline bool ecdsa_verify(const Affine& q, std::span<const uint8_t> msg, const Signature& sig) {
    const auto r = Fn::from_bytes(sig.r);
    const auto s = Fn::from_bytes(sig.s);
    if (!r || !s || r->is_zero() || s->is_zero()) {
        return false;
    }
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    const Fn w = s->inv();
    const Fn u1 = e * w;
    const Fn u2 = *r * w;
    const Jacobian rp =
        scalar_mul(GENERATOR, u1.canonical()).add(scalar_mul(q, u2.canonical()));
    if (rp.is_inf()) {
        return false;
    }
    return Fn::reduce_32(rp.to_affine().x.to_bytes()) == *r;
}

} // namespace vole_mole::p256

#endif
