// Batched QuickSilver constraints.
//
// faest-arch-opt's add_constraint feeds each coefficient of a constraint (lifted to the maximum
// degree D) to two universal hashes, which costs about 2 D products in GF(2^128) per constraint,
// whatever its degree. QsBatch instead adds a random linear combination sum_j r^j e_j of each batch
// of up to SIZE constraints e_1, e_2, ... as a single constraint, for a public r derived from the
// QuickSilver challenge (so after the prover is committed to the witness). The prover multiplies
// only the d MAC coefficients of a constraint of degree d by r^j, and the verifier its one MAC, and
// both accumulate the unreduced products, reducing once per batch. If some e_j doesn't hold, then
// the combination doesn't either, except with probability at most SIZE / 2^128 over r.
//
// The relation then adds ceil(n / SIZE) constraints to QuickSilver for n batched ones (see
// qs_batches).

#ifndef VOLE_MOLE_QS_BATCH_HPP
#define VOLE_MOLE_QS_BATCH_HPP

#include "mq/derived_qs.hpp"

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>

namespace vole_mole::detail {

constexpr size_t QS_BATCH_SIZE = 64;

// The number of constraints that QsBatch adds to QuickSilver for n batched constraints.
constexpr size_t qs_batches(size_t n) { return (n + QS_BATCH_SIZE - 1) / QS_BATCH_SIZE; }

namespace batch_impl {

// The QuickSilver state that a relation's values are over: QS itself, or the inner state of
// DerivedQS (whose values of degree d are values of degree SCALE d over it).
template <typename QS> struct base {
    using type = QS;
    template <size_t d> static const auto& of(const faest::quicksilver_gfsecpar<QS, d>& e) {
        return e;
    }
    template <size_t d> static auto wrap(const faest::quicksilver_gfsecpar<type, d>& e) {
        return e;
    }
};
template <typename Q> struct base<DerivedQS<Q>> {
    using type = Q;
    template <size_t d>
    static const auto& of(const faest::quicksilver_gfsecpar<DerivedQS<Q>, d>& e) {
        return e.inner;
    }
    template <size_t d> static auto wrap(const faest::quicksilver_gfsecpar<type, d>& e) {
        static_assert(d % DerivedQS<Q>::SCALE == 0);
        return faest::quicksilver_gfsecpar<DerivedQS<Q>, d / DerivedQS<Q>::SCALE>(e);
    }
};

} // namespace batch_impl

template <typename QS> class QsBatch {
    using Base = batch_impl::base<QS>;
    using BQS = typename Base::type;
    static constexpr size_t D = BQS::max_degree;
    static constexpr bool VERIFIER = BQS::is_verifier;
    using Poly = faest::poly_secpar<BQS::secpar_v>;
    using Wide = faest::poly_2secpar<BQS::secpar_v>;

  public:
    QsBatch(QS* qs, const Poly& r) : qs_(qs) {
        Poly p = r;
        for (size_t j = 0; j < QS_BATCH_SIZE; ++j) {
            pows_[j] = p;
            p = (p * r).template reduce_to<BQS::secpar_bits>();
        }
        reset();
    }

    template <size_t d> void add(const faest::quicksilver_gfsecpar<QS, d>& x) {
        add_base(Base::of(x));
        if (++n_ == QS_BATCH_SIZE) {
            flush();
        }
    }

    // Add the pending batch, if any.
    void flush() {
        if (n_ == 0) {
            return;
        }
        faest::quicksilver_gfsecpar<BQS, D> out;
        if constexpr (VERIFIER) {
            Poly sum = acc_[D].template reduce_to<BQS::secpar_bits>();
            for (size_t d = 0; d < D; ++d) {
                const Poly a = acc_[d].template reduce_to<BQS::secpar_bits>();
                sum =
                    sum + ((*delta_powers_)[D - d - 1] * a).template reduce_to<BQS::secpar_bits>();
            }
            out.mac = sum;
            out.delta_powers = delta_powers_;
        } else {
            for (size_t k = 0; k < D; ++k) {
                out.mac.coeffs[k] = acc_[k].template reduce_to<BQS::secpar_bits>();
            }
            // The value is zero if all the constraints hold (which faest-arch-opt asserts).
            out.mac.coeffs[D] = bad_ ? Poly::from_1(faest::poly1(1)) : Poly::set_zero();
        }
        qs_->add_constraint(Base::wrap(out));
        reset();
    }

  private:
    template <size_t bd> void add_base(const faest::quicksilver_gfsecpar<BQS, bd>& e) {
        static_assert(bd <= D);
        const Poly& p = pows_[n_];
        if constexpr (VERIFIER) {
            // e = MAC(e) + value(e) Delta^bd, which lifted to degree D is MAC(e) Delta^(D - bd).
            acc_[bd] = acc_[bd] + p * e.mac;
            delta_powers_ = e.delta_powers;
        } else {
            // The coefficients of e's MAC polynomial, lifted to degree D.
            for (size_t i = 0; i < bd; ++i) {
                acc_[i + D - bd] = acc_[i + D - bd] + p * e.mac.coeffs[i];
            }
            bad_ = bad_ || !(e.value() == Poly::set_zero());
        }
    }

    void reset() {
        n_ = 0;
        bad_ = false;
        for (auto& a : acc_) {
            a = Wide::set_zero();
        }
    }

    QS* qs_;
    std::array<Poly, QS_BATCH_SIZE> pows_; // r, r^2, ..., r^SIZE
    size_t n_ = 0;
    bool bad_ = false;
    // Prover: the coefficients of the combination's MAC polynomial, of degree D. Verifier: the
    // combination's MACs by degree (0, ..., D).
    std::array<Wide, VERIFIER ? D + 1 : D> acc_;
    const std::array<Poly, D>* delta_powers_ = nullptr;
};

} // namespace vole_mole::detail

#endif
