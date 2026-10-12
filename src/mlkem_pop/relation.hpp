// The VOLEitH relation for the ML-KEM proof of possession:
//
//   Instance: ek = ByteEncode_12(t-hat) || rho, and the context
//   Witness:  s in R_q^k
//   Constraints: s and e := NTT^-1(t-hat - A-hat * NTT(s)) have coefficients in [-eta_1, eta_1]
//
// Arithmetization: The witness is the k * 256 coefficients of s, as elements of F_q. Since the NTT,
// NTT^-1, and multiplication by the public matrix A-hat are F_q-linear, e is an affine function
// of the committed s, so it needn't be committed separately:
//
//   e = L(s) + e_0,  where L(s) = -NTT^-1(A-hat * NTT(s)) and e_0 = NTT^-1(t-hat).
//
// The range constraints are root constraints of f(x) = x (x^2 - 1) ... (x^2 - eta_1^2), which has
// degree 2 eta_1 + 1 and vanishes exactly on [-eta_1, eta_1]. There are 2 * k * 256 of them.

#ifndef VOLE_MOLE_MLKEM_POP_RELATION_HPP
#define VOLE_MOLE_MLKEM_POP_RELATION_HPP

#include "vole_mole/mlkem.hpp"

#include "dst.hpp"
#include "mlkem/mlkem.hpp"
#include "voleith_fq/field.hpp"
#include "voleith_fq/voleith.hpp"

#include "hash.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <type_traits>

namespace vole_mole::mlkem_pop::detail {

using namespace vole_mole::detail;
using mlkem::detail::Poly;
using voleith_fq::detail::Fq;

// The coefficients f[0], ..., f[2 eta + 1] of f(x) = x prod_{a = 1}^{eta} (x^2 - a^2).
template <size_t ETA> constexpr std::array<Fq, 2 * ETA + 2> range_poly() {
    using namespace voleith_fq::detail;
    std::array<Fq, 2 * ETA + 2> f{};
    f[1] = 1; // x
    size_t deg = 1;
    for (size_t a = 1; a <= ETA; ++a) {
        // f *= x^2 - a^2
        std::array<Fq, 2 * ETA + 2> g{};
        const Fq a2 = fq_from_int(static_cast<int32_t>(a * a));
        for (size_t i = 0; i <= deg; ++i) {
            g[i + 2] = fq_add(g[i + 2], f[i]);
            g[i] = fq_sub(g[i], fq_mul(a2, f[i]));
        }
        f = g;
        deg += 2;
    }
    return f;
}
static_assert(range_poly<2>() ==
              std::array<Fq, 6>{0, 4, 0, voleith_fq::detail::Q - 5, 0, 1}); // x^5 - 5x^3 + 4x

template <mlkem::ParamSet P> struct PopRelation {
    static constexpr size_t K = P::K;
    static constexpr size_t ETA = P::ETA1;
    static constexpr size_t WITNESS_LEN = K * mlkem::detail::N;
    static constexpr size_t DEGREE = 2 * ETA + 1;

    static constexpr std::span<const uint8_t> DST =
        std::is_same_v<P, mlkem::MlKem512>   ? std::span(MLKEM_POP_PROOF_512_DST)
        : std::is_same_v<P, mlkem::MlKem768> ? std::span(MLKEM_POP_PROOF_768_DST)
                                             : std::span(MLKEM_POP_PROOF_1024_DST);

    struct instance {
        const mlkem::EncapsKey<P>* ek;
        std::span<const uint8_t> context;
        const mlkem::detail::ParsedEncapsKey<P>* parsed;
        std::array<Poly, K> e0; // NTT^-1(t-hat)
    };

    static instance make_instance(const mlkem::EncapsKey<P>& ek, std::span<const uint8_t> context,
                                  const mlkem::detail::ParsedEncapsKey<P>& parsed) {
        instance x{&ek, context, &parsed, parsed.t_hat};
        for (auto& e : x.e0) {
            mlkem::detail::inv_ntt(e);
        }
        return x;
    }

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update(*x.ek);
        const uint64_t len = x.context.size();
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(len >> (8 * i)));
        }
        h.update(x.context);
    }

    // L(s) = -NTT^-1(A-hat * NTT(s)), on vectors of K polynomials.
    static void linear_map(const mlkem::detail::ParsedEncapsKey<P>& parsed, std::span<const Fq> s,
                           std::span<Fq> out) {
        using mlkem::detail::N;
        std::array<Poly, K> s_hat;
        for (size_t j = 0; j < K; ++j) {
            std::copy_n(s.begin() + static_cast<ptrdiff_t>(j * N), N, s_hat[j].begin());
            mlkem::detail::ntt(s_hat[j]);
        }
        for (size_t i = 0; i < K; ++i) {
            Poly acc{};
            for (size_t j = 0; j < K; ++j) {
                mlkem::detail::multiply_ntts_acc(acc, parsed.a_hat[i * K + j], s_hat[j]);
            }
            mlkem::detail::inv_ntt(acc);
            for (size_t n = 0; n < N; ++n) {
                out[i * N + n] = voleith_fq::detail::fq_neg(acc[n]);
            }
        }
    }

    template <typename QS> static void constraints(QS& qs, const instance& x) {
        static constexpr auto F = range_poly<ETA>();

        // s is short.
        qs.constrain_roots(qs.witness(), std::span(F));

        // e = L(s) + e0 is short.
        auto e = qs.apply_linear(
            qs.witness(), WITNESS_LEN,
            [&](std::span<const Fq> in, std::span<Fq> out) { linear_map(*x.parsed, in, out); });
        std::array<Fq, WITNESS_LEN> e0;
        for (size_t i = 0; i < K; ++i) {
            std::ranges::copy(x.e0[i], e0.begin() + static_cast<ptrdiff_t>(i * mlkem::detail::N));
        }
        qs.add_constant(e, e0);
        qs.constrain_roots(e, std::span(F));
    }
};

template <mlkem::ParamSet P>
constexpr size_t PROOF_BYTES_CHECK = voleith_fq::detail::PROOF_BYTES<PopRelation<P>>;

} // namespace vole_mole::mlkem_pop::detail

#endif
