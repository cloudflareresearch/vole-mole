// Arithmetic in the prime field F_q, q = 3329 (the ML-KEM modulus), and in its extension F_{q^16}.
//
// F_{q^16} is represented as F_q[X] / (X^16 - 3). This polynomial is irreducible: X^(2^k) - c is
// irreducible over F_q if and only if c is a quadratic non-residue and q = 1 (mod 4) (Lidl and
// Niederreiter, Theorem 3.75). Indeed q = 3329 = 13 * 2^8 + 1, and 3 is a non-residue modulo q.
//
// Elements of F_q are always kept in canonical form [0, q). The operations below avoid
// secret-dependent branches and table lookups.

#ifndef VOLE_MOLE_VOLEITH_FQ_FIELD_HPP
#define VOLE_MOLE_VOLEITH_FQ_FIELD_HPP

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::voleith_fq::detail {

constexpr uint32_t Q = 3329;

// An element of F_q in [0, q).
using Fq = uint16_t;

// x mod q for any 32-bit x. (Division by a constant compiles to a multiplication and shift.)
constexpr Fq fq_reduce(uint32_t x) { return static_cast<Fq>(x % Q); }

constexpr Fq fq_add(Fq a, Fq b) {
    // a + b - q, plus q if that's negative.
    const int32_t t = int32_t{a} + int32_t{b} - int32_t{Q};
    return static_cast<Fq>(t + (int32_t{Q} & (t >> 31)));
}

constexpr Fq fq_sub(Fq a, Fq b) {
    const int32_t t = int32_t{a} - int32_t{b};
    return static_cast<Fq>(t + (int32_t{Q} & (t >> 31)));
}

constexpr Fq fq_neg(Fq a) { return fq_sub(0, a); }

constexpr Fq fq_mul(Fq a, Fq b) { return fq_reduce(uint32_t{a} * uint32_t{b}); }

// x mod q for a signed x with |x| < 2^31 - q.
constexpr Fq fq_from_int(int32_t x) {
    const int32_t r = x % int32_t{Q}; // in (-q, q)
    return static_cast<Fq>(r + (int32_t{Q} & (r >> 31)));
}

// The representative of a in (-q/2, q/2].
constexpr int32_t fq_centered(Fq a) {
    const int32_t t = int32_t{a};
    // Subtract q if a > q/2.
    return t - (int32_t{Q} & ((int32_t{Q / 2} - t) >> 31));
}

constexpr Fq fq_pow(Fq a, uint32_t e) {
    Fq out = 1;
    while (e) {
        if (e & 1) {
            out = fq_mul(out, a);
        }
        a = fq_mul(a, a);
        e >>= 1;
    }
    return out;
}

constexpr size_t packed12_bytes(size_t n) { return 3 * n / 2; }

// Pack an even number of elements of F_q, 12 bits each, as in ML-KEM's ByteEncode_12: each pair
// (a, b) is encoded as the 3 bytes of a + 2^12 b in little-endian order.
inline void pack12(std::span<const Fq> in, std::span<uint8_t> out) {
    assert(in.size() % 2 == 0 && out.size() == packed12_bytes(in.size()));
    for (size_t i = 0; i < in.size() / 2; ++i) {
        const uint32_t a = in[2 * i], b = in[2 * i + 1];
        out[3 * i] = static_cast<uint8_t>(a);
        out[3 * i + 1] = static_cast<uint8_t>((a >> 8) | (b << 4));
        out[3 * i + 2] = static_cast<uint8_t>(b >> 4);
    }
}

// The inverse of pack12. Returns false if any element is not in canonical form, i.e., >= q. The
// output is then unspecified.
inline bool unpack12(std::span<const uint8_t> in, std::span<Fq> out) {
    assert(out.size() % 2 == 0 && in.size() == packed12_bytes(out.size()));
    uint32_t bad = 0;
    for (size_t i = 0; i < out.size() / 2; ++i) {
        const uint32_t b0 = in[3 * i], b1 = in[3 * i + 1], b2 = in[3 * i + 2];
        const uint32_t a = b0 | ((b1 & 0xf) << 8);
        const uint32_t b = (b1 >> 4) | (b2 << 4);
        bad |= static_cast<uint32_t>(a >= Q) | static_cast<uint32_t>(b >= Q);
        out[2 * i] = static_cast<Fq>(a);
        out[2 * i + 1] = static_cast<Fq>(b);
    }
    return bad == 0;
}

// The extension field F_{q^16} = F_q[X] / (X^16 - 3).
constexpr size_t EXT_DEGREE = 16;
constexpr Fq EXT_MODULUS_CONST = 3;           // X^16 = 3
constexpr size_t FQ16_BYTES = 2 * EXT_DEGREE; // serialized for hashing: 16 little-endian uint16s

struct Fq16 {
    std::array<Fq, EXT_DEGREE> c{}; // c[i] is the coefficient of X^i

    static constexpr Fq16 zero() { return {}; }
    static constexpr Fq16 constant(Fq a) {
        Fq16 out;
        out.c[0] = a;
        return out;
    }
    // X^k for k < 16.
    static constexpr Fq16 monomial(size_t k) {
        Fq16 out;
        out.c[k] = 1;
        return out;
    }

    friend constexpr bool operator==(const Fq16&, const Fq16&) = default;

    constexpr Fq16& operator+=(const Fq16& o) {
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            c[i] = fq_add(c[i], o.c[i]);
        }
        return *this;
    }
    constexpr Fq16& operator-=(const Fq16& o) {
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            c[i] = fq_sub(c[i], o.c[i]);
        }
        return *this;
    }
    friend constexpr Fq16 operator+(Fq16 a, const Fq16& b) { return a += b; }
    friend constexpr Fq16 operator-(Fq16 a, const Fq16& b) { return a -= b; }

    // Product with a scalar in F_q.
    friend constexpr Fq16 operator*(Fq s, const Fq16& a) {
        Fq16 out;
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            out.c[i] = fq_mul(s, a.c[i]);
        }
        return out;
    }

    // this += s * a for a scalar s in F_q.
    constexpr void add_scaled(Fq s, const Fq16& a) {
        static_assert(uint64_t{Q - 1} + uint64_t{Q - 1} * (Q - 1) < (uint64_t{1} << 32));
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            c[i] = fq_reduce(uint32_t{c[i]} + uint32_t{s} * uint32_t{a.c[i]});
        }
    }

    friend constexpr Fq16 operator*(const Fq16& a, const Fq16& b) {
        // Schoolbook multiplication with lazy reduction. Each of the 31 coefficients of the
        // product is a sum of at most 16 products < q^2, i.e., < 2^28. Folding X^(16 + k) = 3 X^k
        // adds at most 3 * 2^28, so the 32-bit accumulators never overflow.
        static_assert(uint64_t{EXT_DEGREE} * (Q - 1) * (Q - 1) * (1 + EXT_MODULUS_CONST) <
                      (uint64_t{1} << 32));
        std::array<uint32_t, 2 * EXT_DEGREE - 1> acc{};
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            for (size_t j = 0; j < EXT_DEGREE; ++j) {
                acc[i + j] += uint32_t{a.c[i]} * uint32_t{b.c[j]};
            }
        }
        Fq16 out;
        for (size_t k = 0; k < EXT_DEGREE - 1; ++k) {
            out.c[k] = fq_reduce(acc[k] + EXT_MODULUS_CONST * acc[k + EXT_DEGREE]);
        }
        out.c[EXT_DEGREE - 1] = fq_reduce(acc[EXT_DEGREE - 1]);
        return out;
    }
    constexpr Fq16& operator*=(const Fq16& o) { return *this = *this * o; }

    // a * X^k for k < 16.
    constexpr Fq16 mul_monomial(size_t k) const {
        Fq16 out;
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            const size_t j = i + k;
            if (j < EXT_DEGREE) {
                out.c[j] = c[i];
            } else {
                out.c[j - EXT_DEGREE] = fq_mul(EXT_MODULUS_CONST, c[i]);
            }
        }
        return out;
    }

    void serialize(std::span<uint8_t, FQ16_BYTES> out) const {
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            out[2 * i] = static_cast<uint8_t>(c[i]);
            out[2 * i + 1] = static_cast<uint8_t>(c[i] >> 8);
        }
    }
    std::array<uint8_t, FQ16_BYTES> serialize() const {
        std::array<uint8_t, FQ16_BYTES> out;
        serialize(out);
        return out;
    }
};

// Sanity checks of the claims above.
static_assert(Q % 4 == 1);
static_assert(fq_pow(EXT_MODULUS_CONST, (Q - 1) / 2) == Q - 1); // 3 is a non-residue

} // namespace vole_mole::voleith_fq::detail

#endif
