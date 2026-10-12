// EXPERIMENTAL: a zero-knowledge proof of knowledge of an ML-DSA-44 signature.
//
// The prover holds a valid ML-DSA-44 signature sigma on a message M with context ctx under a
// public key pk, and convinces the verifier, who knows pk, M, and ctx, that it knows such a
// signature, without revealing anything else about it: the signature (c-tilde, z, h) stays
// hidden. This is useful, e.g., to show possession of a credential without making the signature
// itself transferable or linkable.
//
// The statement is exactly ML-DSA.Verify (FIPS 204, Algorithm 3, with the external interface):
// the prover knows c-tilde, z with ||z||_inf < gamma1 - beta, and h with at most omega ones such
// that c-tilde = H(mu || w1Encode(UseHint(h, A z - c t1 2^d)), lambda / 4) for
// c = SampleInBall(c-tilde) and mu = H(H(pk) || 0 || |ctx| || ctx || M).
//
// The proof is a single binary VOLE-in-the-Head proof (FAEST's, extended to long witnesses by
// deriving the witness from a short key with a local PRG), and the arithmetic modulo q is checked
// with random linear combinations. See src/mldsa_pok/relation.hpp. Zero knowledge rests on the
// local PRG being a PRG, whose key length is a rough estimate that hasn't been checked against the
// literature (see tools/local_key_bits.py).

#ifndef VOLE_MOLE_MLDSA_POK_HPP
#define VOLE_MOLE_MLDSA_POK_HPP

#include "vole_mole/mldsa.hpp"

#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok {

// Version of the proof, used for domain separation.
constexpr uint8_t VERSION = 0;

// The size of a proof in bytes.
extern const size_t PROOF_BYTES;

using Proof = std::vector<uint8_t>;

// Prove knowledge of the signature sig on msg with context ctx under pk.
//
// Throws std::invalid_argument if sig isn't a valid signature (or ctx is too long), and
// std::runtime_error if the operating system's random number generator fails or if the signature
// can't be proven: this happens for about one in 2^16 signatures, whose verification hits a
// boundary case that the proof doesn't cover (see relation.hpp); a fresh signature will do.
// Throws std::bad_alloc if memory allocation fails.
Proof prove(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> msg,
            std::span<const uint8_t> ctx, const mldsa::Signature<mldsa::MlDsa44>& sig);

// Verify a proof of knowledge of a signature on msg with context ctx under pk. Returns false if
// the proof is invalid (or ctx is too long).
//
// Throws std::bad_alloc if memory allocation fails. An invalid proof never causes an exception.
bool verify(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> msg,
            std::span<const uint8_t> ctx, std::span<const uint8_t> proof);

} // namespace vole_mole::mldsa_pok

#endif
