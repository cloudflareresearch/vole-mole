// Helpers for testing and benchmarking the ML-KEM PoP with a derived witness (experimental).

#ifndef VOLE_MOLE_TESTS_MLKEM_POP_PRG_HELPERS_HPP
#define VOLE_MOLE_TESTS_MLKEM_POP_PRG_HELPERS_HPP

#include "vole_mole/mlkem.hpp"

#include "mlkem/mlkem.hpp"        // internal
#include "mlkem_pop/relation.hpp" // internal
#include "voleith_fq/field.hpp"   // internal
#include "voleith_fq/voleith.hpp" // internal

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::test::mlkem_pop_prg {

using voleith_fq::detail::Fq;

template <mlkem::ParamSet P, typename Prg> using Rel = mlkem_pop::detail::PopRelation<P, Prg>;
template <mlkem::ParamSet P, typename Prg>
constexpr size_t PROOF_BYTES = voleith_fq::detail::PROOF_BYTES<Rel<P, Prg>>;
template <mlkem::ParamSet P, typename Prg> using Proof = std::array<uint8_t, PROOF_BYTES<P, Prg>>;

// The witness s = NTT^-1(s-hat) of a decapsulation key.
template <mlkem::ParamSet P> std::vector<Fq> witness_of(const mlkem::DecapsKey<P>& dk) {
    std::vector<Fq> s(P::K * 256);
    for (size_t i = 0; i < P::K; ++i) {
        const auto s_i = std::span(s).subspan(i * 256).template first<256>();
        mlkem::detail::decode12(std::span(dk).subspan(384 * i).template first<384>(), s_i);
        mlkem::detail::inv_ntt(s_i);
    }
    return s;
}

template <mlkem::ParamSet P, typename Prg>
Proof<P, Prg> prove(const mlkem::EncapsKey<P>& ek, const std::vector<Fq>& s,
                    std::span<const uint8_t> context, const voleith_fq::detail::ProveSeed& rho) {
    using R = Rel<P, Prg>;
    const auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    Proof<P, Prg> proof;
    voleith_fq::detail::prove<R>(proof, R::make_instance(ek, context, *parsed),
                                 std::span<const Fq, R::WITNESS_LEN>(s), rho);
    return proof;
}

template <mlkem::ParamSet P, typename Prg>
bool verify(const mlkem::EncapsKey<P>& ek, std::span<const uint8_t> context,
            const Proof<P, Prg>& proof) {
    using R = Rel<P, Prg>;
    const auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    if (!parsed) {
        return false;
    }
    return voleith_fq::detail::verify<R>(proof, R::make_instance(ek, context, *parsed));
}

} // namespace vole_mole::test::mlkem_pop_prg

#endif
