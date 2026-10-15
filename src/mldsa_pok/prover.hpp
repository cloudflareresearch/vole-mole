// The prover's internals for the ML-DSA proof of knowledge, exposed for testing.

#ifndef VOLE_MOLE_MLDSA_POK_PROVER_HPP
#define VOLE_MOLE_MLDSA_POK_PROVER_HPP

#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include "mldsa/mldsa.hpp"
#include "mldsa_pok/relation.hpp"

#include <array>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

struct Witness {
    std::vector<uint8_t> prefix; // the witness, except the answer to the checks
};

using Rho = std::array<uint8_t, 32>;

// The witness for msg and a decoded signature on it. Throws std::invalid_argument if the signature
// isn't valid.
Witness make_witness(const Statement& stmt, const Message& msg,
                     const mldsa::detail::DecodedSignature<P>& sig);

// A proof for the given witness, which isn't checked. If it isn't valid, the proof is invalid.
Proof prove_witness(const Statement& stmt, const Witness& w, const Rho& rho);

// As prove(), with the given randomness.
Proof prove_with_seed(const mldsa::PublicKey<P>& pk, const Message& msg,
                      const mldsa::Signature<P>& sig, const Rho& rho);

// Verifies a proof for the statement.
bool verify_proof(const Statement& stmt, std::span<const uint8_t, PROOF_BYTES_> proof);

} // namespace vole_mole::mldsa_pok::detail

#endif
