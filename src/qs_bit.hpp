// QuickSilver-committed bits.
//
// Many of our witness values are bits, e.g., the Keccak state and selector bits. We represent these
// as `quicksilver_gf2` rather than `quicksilver_gfsecpar`: the prover represents a value of degree
// d by the d MAC coefficients in GF(2^128) and the value bit, rather than d + 1 coefficients in
// GF(2^128). A product of bits of degree d1 and d2 then costs d1 d2 rather than (d1 + 1) (d2 + 1)
// multiplications in GF(2^128). For the verifier, both are represented the same way.

#ifndef VOLE_MOLE_QS_BIT_HPP
#define VOLE_MOLE_QS_BIT_HPP

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <cstddef>

namespace vole_mole::detail {

// A QuickSilver-committed bit of degree `deg`.
template <typename QS, size_t deg> using qs_bit = faest::quicksilver_gf2<QS, deg>;

// The same bit as an element of GF(2^128), as needed for constraints.
template <typename QS, size_t deg>
faest::quicksilver_gfsecpar<QS, deg> qs_to_gfsecpar(const qs_bit<QS, deg>& x) {
    return faest::quicksilver_gfsecpar<QS, deg>(x);
}

// Product of two committed bits.
//
// faest-arch-opt declares this product, but its prover implementation doesn't compile (FAEST itself
// never multiplies two GF(2) values of positive degree), so we do it here. If a = A(X) + a_v X^da
// and b = B(X) + b_v X^db, where A and B are the MAC polynomials (of degree < da and < db) and a_v
// and b_v the value bits, then a b = A B + b_v A X^db + a_v B X^da + a_v b_v X^(da + db).
template <typename QS, size_t da, size_t db>
qs_bit<QS, da + db> qs_mul(const qs_bit<QS, da>& a, const qs_bit<QS, db>& b) {
    if constexpr (requires { a.value_; }) {
        qs_bit<QS, da + db> out(static_cast<const QS*>(nullptr));
        out.mac = faest::mul_reduce<QS::secpar_bits>(a.mac, b.mac);
        for (size_t i = 0; i < da; ++i) {
            out.mac.coeffs[i + db] += b.value() * a.mac.coeffs[i];
        }
        for (size_t i = 0; i < db; ++i) {
            out.mac.coeffs[i + da] += a.value() * b.mac.coeffs[i];
        }
        out.value() = faest::poly1::set_all(a.value().data & b.value().data);
        return out;
    } else {
        return a * b;
    }
}

// Product of a committed bit and a committed element of GF(2^128).
//
// As above: if a = A(X) + a_v X^da, where A is the MAC polynomial (of degree < da) and a_v the
// value bit, and b = B(X) (of degree db), then a b = A B + a_v B X^da. This costs da (db + 1)
// rather than (da + 1) (db + 1) multiplications in GF(2^128). (As for the product of two bits,
// faest-arch-opt's prover implementation doesn't compile.)
template <typename QS, size_t da, size_t db>
faest::quicksilver_gfsecpar<QS, da + db> qs_mul(const qs_bit<QS, da>& a,
                                                const faest::quicksilver_gfsecpar<QS, db>& b) {
    if constexpr (requires { a.value_; }) {
        faest::quicksilver_gfsecpar<QS, da + db> out(static_cast<const QS*>(nullptr));
        out.mac = faest::mul_reduce<QS::secpar_bits>(a.mac, b.mac);
        for (size_t i = 0; i <= db; ++i) {
            out.mac.coeffs[i + da] += a.value() * b.mac.coeffs[i];
        }
        return out;
    } else {
        return faest::quicksilver_gfsecpar<QS, da>(a) * b;
    }
}

// Add the constraint that x is a bit, i.e., x (x + 1) = 0. (As faest-arch-opt's
// add_bit_constraint, but with the cheaper product of bits.)
template <typename QS> void qs_add_bit_constraint(QS* qs, const qs_bit<QS, 1>& x) {
    qs->add_constraint(qs_to_gfsecpar(qs_mul<QS, 1, 1>(x, x + faest::poly1(1))));
}

} // namespace vole_mole::detail

#endif
