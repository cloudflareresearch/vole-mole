// GF(2^128) in the clear, as QuickSilver represents it (faest::poly128, reduced modulo
// x^128 + x^7 + x^2 + x + 1), and a generator of its multiplicative group.
//
// An element is stored as 16 bytes, little-endian: bit j (bit j % 8 of byte j / 8) is the
// coefficient of x^j. A committed element is 128 committed bits in this order (see qs_element in
// tree_sumcheck.hpp).

#ifndef VOLE_MOLE_SUMCHECK_GF128_HPP
#define VOLE_MOLE_SUMCHECK_GF128_HPP

#include "polynomials.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>

namespace vole_mole::sumcheck::detail {

using Gf = faest::poly128;
using U128 = unsigned __int128;

constexpr size_t GF_BYTES = 16;

inline Gf gf_zero() { return Gf::set_zero(); }
inline Gf gf_one() { return Gf::set_low32(1); }
inline Gf gf_mul(Gf a, Gf b) { return (a * b).template reduce_to<128>(); }
inline Gf gf_sqr(Gf a) { return gf_mul(a, a); }
inline bool gf_eq(Gf a, Gf b) { return a == b; }

inline Gf gf_load(const uint8_t* p) { return Gf::load(p); }
inline void gf_store(Gf a, uint8_t* p) { a.store(p); }

// The element with the 128-bit integer v as its coefficient vector.
inline Gf gf_from_u128(U128 v) {
    std::array<uint8_t, GF_BYTES> b{};
    for (size_t i = 0; i < GF_BYTES; ++i) {
        b[i] = static_cast<uint8_t>(v >> (8 * i));
    }
    return gf_load(b.data());
}

// x^j.
inline Gf gf_monomial(size_t j) { return gf_from_u128(U128{1} << j); }

// a^e.
inline Gf gf_pow(Gf a, U128 e) {
    Gf out = gf_one();
    while (e != 0) {
        if ((e & 1) != 0) {
            out = gf_mul(out, a);
        }
        a = gf_sqr(a);
        e >>= 1;
    }
    return out;
}

// The order of the multiplicative group, and its prime factors.
constexpr U128 GROUP_ORDER = ~U128{0}; // 2^128 - 1
constexpr std::array<U128, 9> GROUP_ORDER_FACTORS = {
    3, 5, 17, 257, 641, 65537, 274177, 6700417, U128{67280421310721}};
static_assert([] {
    U128 p = 1;
    for (const U128 f : GROUP_ORDER_FACTORS) {
        p *= f;
    }
    return p == GROUP_ORDER;
}());

// g^e for a signed exponent e (|e| < 2^127).
inline Gf gf_signed_pow(Gf g, __int128 e) {
    if (e >= 0) {
        return gf_pow(g, static_cast<U128>(e));
    }
    return gf_pow(g, GROUP_ORDER - static_cast<U128>(-e));
}

// The generator g: the least element (as an integer) >= 2 of order 2^128 - 1, i.e., with
// g^((2^128 - 1) / p) != 1 for every prime factor p.
inline Gf generator() {
    static const Gf g = [] {
        for (U128 c = 2; c < 256; ++c) {
            const Gf cand = gf_from_u128(c);
            bool ok = true;
            for (const U128 p : GROUP_ORDER_FACTORS) {
                if (gf_eq(gf_pow(cand, GROUP_ORDER / p), gf_one())) {
                    ok = false;
                    break;
                }
            }
            if (ok) {
                return cand;
            }
        }
        throw std::logic_error("sumcheck: no generator");
    }();
    return g;
}

} // namespace vole_mole::sumcheck::detail

#endif
