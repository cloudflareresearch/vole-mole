// Deterministic functions used to implement the randomized ML-KEM proof of possession API.

#ifndef VOLE_MOLE_MLKEM_POP_SEEDED_HPP
#define VOLE_MOLE_MLKEM_POP_SEEDED_HPP

#include "vole_mole/mlkem.hpp"
#include "vole_mole/mlkem_pop.hpp"

#include "mlkem_pop/relation.hpp"
#include "voleith_fq/voleith.hpp"

#include <cstdint>
#include <span>

namespace vole_mole::mlkem_pop::detail {

using voleith_fq::detail::ProveSeed;

// As prove(), using rho as the prover's randomness.
template <mlkem::ParamSet P>
Proof<P> prove_with_seed(const mlkem::DecapsKey<P>& dk, std::span<const uint8_t> context,
                         const ProveSeed& rho);

// Prove the relation for ek with the given witness s (in the normal domain) without checking that
// it is valid. If it isn't, the proof is invalid. For testing soundness.
//
// Throws std::invalid_argument if ek fails the modulus check and std::bad_alloc if memory
// allocation fails.
template <mlkem::ParamSet P>
Proof<P> prove_unchecked(const mlkem::EncapsKey<P>& ek,
                         std::span<const Fq, PopRelation<P>::WITNESS_LEN> s,
                         std::span<const uint8_t> context, const ProveSeed& rho);

} // namespace vole_mole::mlkem_pop::detail

#endif
