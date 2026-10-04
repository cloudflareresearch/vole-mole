// QuickSilver-committed elements of GF(256).
//
// Many of our witness values are elements of the GF(256) subfield of GF(2^128), e.g., UOV
// preimages. The QuickSilver prover represents a committed value of degree d by d MAC coefficients
// and the value, all in GF(2^128). For a value in GF(256), qs_gf256 instead keeps the value as a
// byte: this halves the size of a value of degree 1, the value of a product is a product in
// GF(256), and the values of many committed elements can be processed 16 at a time (see
// gf256_madd). For the verifier (and any other QuickSilver state, such as test stand-ins), qs_gf256
// is just quicksilver_gfsecpar, which represents the value in the same way either way.

#ifndef VOLE_MOLE_QS_GF256_HPP
#define VOLE_MOLE_QS_GF256_HPP

#include "gf256.hpp"

#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <type_traits>

namespace vole_mole::detail {

// Whether QS is faest-arch-opt's QuickSilver prover.
template <typename QS> constexpr bool IS_QS_PROVER = false;
template <faest::secpar S, size_t max_deg>
constexpr bool IS_QS_PROVER<faest::quicksilver_state<S, false, max_deg>> = true;

// The embedding of GF(256) into GF(2^128).
template <faest::secpar S> faest::poly_secpar<S> gf256_embed(uint8_t a) {
    return faest::poly_secpar<S>::from_8_byte(a);
}

// The prover's representation of a committed element of GF(256) of degree `deg`: x = M(X) + v
// X^deg, where M is the MAC polynomial (of degree < deg) and v the value.
template <typename QS, size_t deg> struct QsGf256Prover {
    static constexpr faest::secpar S = QS::secpar_v;
    using poly = faest::poly_secpar<S>;

    faest::poly2d<deg, QS::secpar_bits> mac = faest::poly2d<deg, QS::secpar_bits>::set_zero();
    uint8_t value = 0;

    QsGf256Prover operator+(const QsGf256Prover& o) const {
        QsGf256Prover out;
        out.mac = mac + o.mac;
        out.value = value ^ o.value;
        return out;
    }

    // Addition of a public constant.
    QsGf256Prover operator+(uint8_t c) const {
        QsGf256Prover out = *this;
        out.value ^= c;
        return out;
    }

    template <typename T> QsGf256Prover& operator+=(const T& o) {
        *this = *this + o;
        return *this;
    }
};

// A QuickSilver-committed element of GF(256) of degree `deg`.
template <typename QS, size_t deg>
using qs_gf256 = std::conditional_t<IS_QS_PROVER<QS>, QsGf256Prover<QS, deg>,
                                    faest::quicksilver_gfsecpar<QS, deg>>;

// The 8 witness bits starting at bit_index (a multiple of 8) as a committed element of GF(256),
// with bit j as the coefficient of x^j. The same as QS::load_witness_8_bits_and_combine.
template <typename QS> qs_gf256<QS, 1> qs_load_gf256(const QS* qs, size_t bit_index) {
    if constexpr (IS_QS_PROVER<QS>) {
        assert(bit_index % 8 == 0);
        qs_gf256<QS, 1> out;
        out.mac.coeffs[0] = qs->load_witness_8_bits_and_combine(bit_index).mac.coeffs[0];
        out.value = qs->witness[bit_index / 8];
        return out;
    } else {
        return qs->load_witness_8_bits_and_combine(bit_index);
    }
}

// The same value as an element of GF(2^128), e.g., for constraints.
template <typename QS, size_t deg>
faest::quicksilver_gfsecpar<QS, deg> qs_to_gfsecpar(const QsGf256Prover<QS, deg>& x) {
    faest::quicksilver_gfsecpar<QS, deg> out(static_cast<const QS*>(nullptr));
    for (size_t i = 0; i < deg; ++i) {
        out.mac.coeffs[i] = x.mac.coeffs[i];
    }
    out.value() = gf256_embed<QS::secpar_v>(x.value);
    return out;
}
template <typename QS, size_t deg>
faest::quicksilver_gfsecpar<QS, deg> qs_to_gfsecpar(const faest::quicksilver_gfsecpar<QS, deg>& x) {
    return x;
}

// Multiplication by a public constant c.
template <typename QS, size_t deg>
QsGf256Prover<QS, deg> qs_mul_const(uint8_t c, const QsGf256Prover<QS, deg>& x) {
    const auto embed_c = gf256_embed<QS::secpar_v>(c);
    QsGf256Prover<QS, deg> out;
    for (size_t i = 0; i < deg; ++i) {
        out.mac.coeffs[i] = (embed_c * x.mac.coeffs[i]).template reduce_to<QS::secpar_bits>();
    }
    out.value = gf256_mul(c, x.value);
    return out;
}
template <typename QS, size_t deg>
faest::quicksilver_gfsecpar<QS, deg> qs_mul_const(uint8_t c,
                                                  const faest::quicksilver_gfsecpar<QS, deg>& x) {
    return gf256_embed<QS::secpar_v>(c) * x;
}

// Product of two committed elements of GF(256). If a = A(X) + a_v X^da and b = B(X) + b_v X^db,
// then a b = A B + b_v A X^db + a_v B X^da + a_v b_v X^(da + db), where a_v b_v is a product in
// GF(256).
template <typename QS, size_t da, size_t db>
QsGf256Prover<QS, da + db> qs_mul(const QsGf256Prover<QS, da>& a, const QsGf256Prover<QS, db>& b) {
    const auto embed_a = gf256_embed<QS::secpar_v>(a.value);
    const auto embed_b = gf256_embed<QS::secpar_v>(b.value);
    auto mac = faest::poly2d<da + db, 2 * QS::secpar_bits>::set_zero();
    for (size_t i = 0; i < da; ++i) {
        for (size_t j = 0; j < db; ++j) {
            mac.coeffs[i + j] += a.mac.coeffs[i] * b.mac.coeffs[j];
        }
        mac.coeffs[i + db] += embed_b * a.mac.coeffs[i];
    }
    for (size_t j = 0; j < db; ++j) {
        mac.coeffs[j + da] += embed_a * b.mac.coeffs[j];
    }
    QsGf256Prover<QS, da + db> out;
    out.mac = mac.template reduce_to<QS::secpar_bits>();
    out.value = gf256_mul(a.value, b.value);
    return out;
}
template <typename QS, size_t da, size_t db>
faest::quicksilver_gfsecpar<QS, da + db> qs_mul(const faest::quicksilver_gfsecpar<QS, da>& a,
                                                const faest::quicksilver_gfsecpar<QS, db>& b) {
    return a * b;
}

} // namespace vole_mole::detail

#endif
