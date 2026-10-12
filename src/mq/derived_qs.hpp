// QuickSilver for a witness derived with the MQ PRG.
//
// If the witness w is derived from a committed key K as w = e + G(K) (see "Derived witnesses" in
// voleith.hpp), then each witness bit is a committed value of degree DEGREE = 2 rather than 1, and
// so every value computed from the witness has DEGREE times the degree it would have had otherwise.
// DerivedQS<QS> lets a relation's constraints be evaluated on such a witness without changing
// them: it presents the derived witness through the same interface as QS (get_witness_bit,
// load_witness_8_bits_and_combine, add_constraint), and a value of degree d over DerivedQS<QS> is a
// value of degree DEGREE * d over QS. Sums, products, and lifts scale with the degree, so the
// relation's degree bookkeeping carries over unchanged, and QS::max_degree must be DEGREE times the
// relation's.

#ifndef VOLE_MOLE_MQ_DERIVED_QS_HPP
#define VOLE_MOLE_MQ_DERIVED_QS_HPP

#include "mq/prg.hpp"
#include "qs_bit.hpp"

#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <span>

namespace vole_mole::detail {

template <typename QS> struct DerivedQS {
    using inner_qs = QS;
    static constexpr size_t SCALE = mq::detail::DEGREE;

    static constexpr bool is_verifier = QS::is_verifier;
    static constexpr faest::secpar secpar_v = QS::secpar_v;
    static constexpr size_t secpar_bits = QS::secpar_bits;
    static_assert(QS::max_degree % SCALE == 0);
    static constexpr size_t max_degree = QS::max_degree / SCALE;

    QS* inner;
    // The committed bits of the derived witness, of degree SCALE over QS.
    std::span<const faest::quicksilver_gf2<QS, SCALE>> witness;

    faest::quicksilver_gf2<DerivedQS, 1> get_witness_bit(size_t i) const;
    // The 8 bits starting at bit i, combined into an element of GF(256), as faest-arch-opt does.
    faest::quicksilver_gfsecpar<DerivedQS, 1> load_witness_8_bits_and_combine(size_t i) const;

    template <size_t deg> void add_constraint(const faest::quicksilver_gfsecpar<DerivedQS, deg>& x);
};

} // namespace vole_mole::detail

// A committed bit of degree `deg` over DerivedQS<QS>, i.e., of degree SCALE * deg over QS.
template <typename QS, size_t deg>
struct faest::quicksilver_gf2<vole_mole::detail::DerivedQS<QS>, deg> {
    using quicksilver = vole_mole::detail::DerivedQS<QS>;
    using inner_t = faest::quicksilver_gf2<QS, quicksilver::SCALE * deg>;

    inner_t inner;

    quicksilver_gf2() = default;
    explicit quicksilver_gf2(const inner_t& x) : inner(x) {}
    quicksilver_gf2(const quicksilver* state) : inner(state->inner) {}
    quicksilver_gf2(poly1 const_value, const quicksilver* state)
        : inner(const_value, state->inner) {}
    template <size_t deg2>
    quicksilver_gf2(poly1 const_value, const quicksilver_gf2<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    template <size_t deg2>
    quicksilver_gf2(poly1 const_value, const quicksilver_gfsecpar<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    template <size_t deg2>
        requires(deg > deg2)
    quicksilver_gf2(const quicksilver_gf2<quicksilver, deg2>& other) : inner(other.inner) {}

    quicksilver_gf2 operator+(const quicksilver_gf2& other) const {
        return quicksilver_gf2(inner + other.inner);
    }
    quicksilver_gfsecpar<quicksilver, deg>
    operator+(const quicksilver_gfsecpar<quicksilver, deg>& other) const {
        return other + *this;
    }
    template <typename T> quicksilver_gf2& operator+=(const T& other) {
        *this = *this + other;
        return *this;
    }
    template <typename T> quicksilver_gf2& operator*=(const T& other) {
        *this = *this * other;
        return *this;
    }
};

// A committed element of GF(2^128) of degree `deg` over DerivedQS<QS>, i.e., of degree SCALE * deg
// over QS.
template <typename QS, size_t deg>
struct faest::quicksilver_gfsecpar<vole_mole::detail::DerivedQS<QS>, deg> {
    using quicksilver = vole_mole::detail::DerivedQS<QS>;
    using inner_t = faest::quicksilver_gfsecpar<QS, quicksilver::SCALE * deg>;
    using poly = poly_secpar<QS::secpar_v>;

    inner_t inner;

    quicksilver_gfsecpar() = default;
    explicit quicksilver_gfsecpar(const inner_t& x) : inner(x) {}
    quicksilver_gfsecpar(const quicksilver* state) : inner(state->inner) {}
    quicksilver_gfsecpar(poly1 const_value, const quicksilver* state)
        : inner(const_value, state->inner) {}
    quicksilver_gfsecpar(poly const_value, const quicksilver* state)
        : inner(const_value, state->inner) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly1 const_value, const quicksilver_gf2<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly const_value, const quicksilver_gf2<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly1 const_value,
                         const quicksilver_gfsecpar<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly const_value,
                         const quicksilver_gfsecpar<quicksilver, deg2>& state_from)
        : inner(const_value, state_from.inner) {}
    quicksilver_gfsecpar(const quicksilver_gf2<quicksilver, deg>& other)
        : inner(inner_t(other.inner)) {}
    template <size_t deg2>
        requires(deg > deg2)
    quicksilver_gfsecpar(const quicksilver_gfsecpar<quicksilver, deg2>& other)
        : inner(other.inner) {}
    template <size_t deg2>
        requires(deg > deg2)
    quicksilver_gfsecpar(const quicksilver_gf2<quicksilver, deg2>& other) : inner(other.inner) {}

    quicksilver_gfsecpar operator+(const quicksilver_gfsecpar& other) const {
        return quicksilver_gfsecpar(inner + other.inner);
    }
    quicksilver_gfsecpar operator+(const quicksilver_gf2<quicksilver, deg>& other) const {
        return *this + quicksilver_gfsecpar(other);
    }
    template <typename T> quicksilver_gfsecpar& operator+=(const T& other) {
        *this = *this + other;
        return *this;
    }
    template <typename T> quicksilver_gfsecpar& operator*=(const T& other) {
        *this = *this * other;
        return *this;
    }

    static quicksilver_gfsecpar combine_8_bits(const quicksilver_gf2<quicksilver, deg>* qs_bits) {
        std::array<faest::quicksilver_gf2<QS, quicksilver::SCALE * deg>, 8> bits;
        for (size_t j = 0; j < 8; ++j) {
            bits[j] = qs_bits[j].inner;
        }
        return quicksilver_gfsecpar(inner_t::combine_8_bits(bits.data()));
    }
};

namespace vole_mole::detail {

// Products over DerivedQS are products over QS. These are found by argument-dependent lookup and
// are more specialized than faest-arch-opt's generic products, so they're preferred for DerivedQS.
// Products involving bits use qs_mul, which is cheaper than faest-arch-opt's products (see
// qs_bit.hpp).
template <typename QS, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a + deg_b>
operator*(const faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a>& a,
          const faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_b>& b) {
    return faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a + deg_b>(a.inner * b.inner);
}

template <typename QS, size_t deg_a, size_t deg_b>
faest::quicksilver_gf2<DerivedQS<QS>, deg_a + deg_b>
operator*(const faest::quicksilver_gf2<DerivedQS<QS>, deg_a>& a,
          const faest::quicksilver_gf2<DerivedQS<QS>, deg_b>& b) {
    constexpr size_t S = DerivedQS<QS>::SCALE;
    return faest::quicksilver_gf2<DerivedQS<QS>, deg_a + deg_b>(
        qs_mul<QS, S * deg_a, S * deg_b>(a.inner, b.inner));
}

template <typename QS, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a + deg_b>
operator*(const faest::quicksilver_gf2<DerivedQS<QS>, deg_a>& a,
          const faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_b>& b) {
    constexpr size_t S = DerivedQS<QS>::SCALE;
    return faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a + deg_b>(
        qs_mul<QS, S * deg_a, S * deg_b>(a.inner, b.inner));
}

template <typename QS, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a + deg_b>
operator*(const faest::quicksilver_gfsecpar<DerivedQS<QS>, deg_a>& a,
          const faest::quicksilver_gf2<DerivedQS<QS>, deg_b>& b) {
    return b * a;
}

template <typename QS>
faest::quicksilver_gf2<DerivedQS<QS>, 1> DerivedQS<QS>::get_witness_bit(size_t i) const {
    return faest::quicksilver_gf2<DerivedQS, 1>(witness[i]);
}

template <typename QS>
faest::quicksilver_gfsecpar<DerivedQS<QS>, 1>
DerivedQS<QS>::load_witness_8_bits_and_combine(size_t i) const {
    std::array<faest::quicksilver_gf2<DerivedQS, 1>, 8> bits;
    for (size_t j = 0; j < 8; ++j) {
        bits[j] = get_witness_bit(i + j);
    }
    return faest::quicksilver_gfsecpar<DerivedQS, 1>::combine_8_bits(bits.data());
}

template <typename QS>
template <size_t deg>
void DerivedQS<QS>::add_constraint(const faest::quicksilver_gfsecpar<DerivedQS, deg>& x) {
    inner->add_constraint(x.inner);
}

} // namespace vole_mole::detail

#endif
