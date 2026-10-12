#include "vole_mole/mlkem_pop.hpp"

#include "vole_mole/mlkem.hpp"
#include "vole_mole/random.hpp"

#include "mlkem/mlkem.hpp"
#include "mlkem_pop/relation.hpp"
#include "mlkem_pop/seeded.hpp"
#include "voleith_fq/field.hpp"
#include "voleith_fq/voleith.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>

namespace vole_mole::mlkem_pop {

using mlkem::MlKem1024;
using mlkem::MlKem512;
using mlkem::MlKem768;

namespace detail {

namespace {

using voleith_fq::detail::fq_add;
using voleith_fq::detail::fq_centered;

template <mlkem::ParamSet P> using Relation = PopRelation<P>;
template <mlkem::ParamSet P> constexpr size_t L = Relation<P>::WITNESS_LEN;

static_assert(PROOF_BYTES<MlKem512> == PROOF_BYTES_CHECK<MlKem512>);
static_assert(PROOF_BYTES<MlKem768> == PROOF_BYTES_CHECK<MlKem768>);
static_assert(PROOF_BYTES<MlKem1024> == PROOF_BYTES_CHECK<MlKem1024>);

// Returns 0 if every element of x is in [-eta, eta], and nonzero otherwise, without branching on
// the elements.
template <size_t ETA> uint32_t out_of_range(std::span<const Fq> x) {
    uint32_t bad = 0;
    for (const Fq a : x) {
        const int32_t c = fq_centered(a);
        bad |= static_cast<uint32_t>((int32_t{ETA} - c) | (c + int32_t{ETA})) >> 31;
    }
    return bad;
}

template <mlkem::ParamSet P>
Proof<P> prove_instance(const typename Relation<P>::instance& x, std::span<const Fq, L<P>> s,
                        const ProveSeed& rho) {
    Proof<P> proof;
    voleith_fq::detail::prove<Relation<P>>(proof, x, s, rho);
    return proof;
}

} // namespace

template <mlkem::ParamSet P>
Proof<P> prove_with_seed(const mlkem::DecapsKey<P>& dk, std::span<const uint8_t> context,
                         const ProveSeed& rho) {
    using Parts = mlkem::detail::DecapsKeyParts<P>;
    using mlkem::detail::N;
    using mlkem::detail::POLY_BYTES;
    constexpr size_t K = P::K;

    // Check the decapsulation key (FIPS 203, Section 7.3) and parse it.
    mlkem::EncapsKey<P> ek;
    std::copy_n(dk.begin() + Parts::OFF_EK, ek.size(), ek.begin());
    const auto h = mlkem::detail::hash_h(ek);
    if (!std::equal(h.begin(), h.end(), dk.begin() + Parts::OFF_H)) {
        throw std::invalid_argument("ML-KEM PoP: decapsulation key fails the hash check");
    }
    const auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    if (!parsed) {
        throw std::invalid_argument("ML-KEM PoP: encapsulation key fails the modulus check");
    }

    // The witness s = NTT^-1(s-hat).
    std::array<Fq, L<P>> s;
    bool ok = true;
    for (size_t i = 0; i < K; ++i) {
        const auto s_i = std::span(s).subspan(i * N).template first<N>();
        ok &= mlkem::detail::decode12(
            std::span(dk).subspan(Parts::OFF_S_HAT + i * POLY_BYTES).template first<POLY_BYTES>(),
            s_i);
        mlkem::detail::inv_ntt(s_i);
    }
    if (!ok) {
        throw std::invalid_argument("ML-KEM PoP: decapsulation key's s-hat isn't reduced modulo q");
    }

    // Check that s and e = L(s) + e0 are short, i.e., that the witness is valid.
    const auto x = Relation<P>::make_instance(ek, context, *parsed);
    std::array<Fq, L<P>> e;
    Relation<P>::linear_map(*parsed, s, e);
    for (size_t i = 0; i < K; ++i) {
        for (size_t n = 0; n < N; ++n) {
            e[i * N + n] = fq_add(e[i * N + n], x.e0[i][n]);
        }
    }
    const uint32_t bad = out_of_range<P::ETA1>(s) | out_of_range<P::ETA1>(e);
    if (bad != 0) {
        throw std::invalid_argument("ML-KEM PoP: the decapsulation key's secret isn't short");
    }

    return prove_instance<P>(x, s, rho);
}

template <mlkem::ParamSet P>
Proof<P> prove_unchecked(const mlkem::EncapsKey<P>& ek,
                         std::span<const Fq, PopRelation<P>::WITNESS_LEN> s,
                         std::span<const uint8_t> context, const ProveSeed& rho) {
    const auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    if (!parsed) {
        throw std::invalid_argument("ML-KEM PoP: encapsulation key fails the modulus check");
    }
    return prove_instance<P>(Relation<P>::make_instance(ek, context, *parsed), s, rho);
}

#define VOLE_MOLE_INSTANTIATE(P)                                                                   \
    template Proof<P> prove_with_seed<P>(const mlkem::DecapsKey<P>&, std::span<const uint8_t>,     \
                                         const ProveSeed&);                                        \
    template Proof<P> prove_unchecked<P>(const mlkem::EncapsKey<P>&,                               \
                                         std::span<const Fq, PopRelation<P>::WITNESS_LEN>,         \
                                         std::span<const uint8_t>, const ProveSeed&);
VOLE_MOLE_INSTANTIATE(MlKem512)
VOLE_MOLE_INSTANTIATE(MlKem768)
VOLE_MOLE_INSTANTIATE(MlKem1024)
#undef VOLE_MOLE_INSTANTIATE

} // namespace detail

template <mlkem::ParamSet P>
Proof<P> prove(const mlkem::DecapsKey<P>& dk, std::span<const uint8_t> context) {
    return detail::prove_with_seed<P>(dk, context,
                                      random_bytes<voleith_fq::detail::PROVE_SEED_BYTES>());
}

template <mlkem::ParamSet P>
bool verify(const mlkem::EncapsKey<P>& ek, std::span<const uint8_t> context,
            const Proof<P>& proof) {
    const auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    if (!parsed) {
        return false;
    }
    using R = detail::PopRelation<P>;
    return voleith_fq::detail::verify<R>(proof, R::make_instance(ek, context, *parsed));
}

template Proof<MlKem512> prove<MlKem512>(const mlkem::DecapsKey<MlKem512>&,
                                         std::span<const uint8_t>);
template Proof<MlKem768> prove<MlKem768>(const mlkem::DecapsKey<MlKem768>&,
                                         std::span<const uint8_t>);
template Proof<MlKem1024> prove<MlKem1024>(const mlkem::DecapsKey<MlKem1024>&,
                                           std::span<const uint8_t>);
template bool verify<MlKem512>(const mlkem::EncapsKey<MlKem512>&, std::span<const uint8_t>,
                               const Proof<MlKem512>&);
template bool verify<MlKem768>(const mlkem::EncapsKey<MlKem768>&, std::span<const uint8_t>,
                               const Proof<MlKem768>&);
template bool verify<MlKem1024>(const mlkem::EncapsKey<MlKem1024>&, std::span<const uint8_t>,
                                const Proof<MlKem1024>&);

} // namespace vole_mole::mlkem_pop
