// EXPERIMENTAL: a zero-knowledge proof of knowledge of an ML-DSA-44 signature on a hidden message.
//
// The prover holds a message M and a valid ML-DSA-44 signature sigma on M (with an empty context
// string) under a public key pk, and convinces the verifier, who knows only pk, that it knows such
// a pair, without revealing anything else: both M and the signature (c-tilde, z, h) stay hidden.
//
// The statement is exactly ML-DSA.Verify (FIPS 204, Algorithm 3, with the external interface):
// the prover knows M, c-tilde, z with ||z||_inf < gamma1 - beta, and h with at most omega ones
// such that c-tilde = H(mu || w1Encode(UseHint(h, A z - c t1 2^d)), lambda / 4) for
// c = SampleInBall(c-tilde) and mu = H(H(pk) || 0 || 0 || M). Every valid signature can be proven.
//
// This standalone proof mainly exercises the circuit for ML-DSA verification on a hidden message
// (src/mldsa_pok/verify_gadget.hpp), which is meant to be part of larger statements, where M comes
// from elsewhere in the circuit (e.g., a hash of attributes, or a key).
//
// The proof is a single binary VOLE-in-the-Head proof (FAEST's, extended to long witnesses by
// deriving the witness from a short key with a local PRG), and the arithmetic modulo q is checked
// with random linear combinations. See src/mldsa_pok/relation.hpp. Zero knowledge rests on the
// local PRG being a PRG, whose key length is a rough estimate that hasn't been checked against the
// literature (see tools/local_key_bits.py).

#ifndef VOLE_MOLE_MLDSA_POK_HPP
#define VOLE_MOLE_MLDSA_POK_HPP

#include "vole_mole/mldsa.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok {

// Version of the proof, used for domain separation.
constexpr uint8_t VERSION = 1;

// The length of the hidden message, e.g., a hash of the actual message.
constexpr size_t MESSAGE_BYTES = 32;
using Message = std::array<uint8_t, MESSAGE_BYTES>;

// The size of a proof in bytes.
extern const size_t PROOF_BYTES;

using Proof = std::vector<uint8_t>;

// Prove knowledge of msg and the signature sig on msg (with an empty context string) under pk.
//
// Throws std::invalid_argument if sig isn't a valid signature on msg, std::runtime_error if the
// operating system's random number generator fails or (with negligible probability) if proof
// generation fails, and std::bad_alloc if memory allocation fails.
Proof prove(const mldsa::PublicKey<mldsa::MlDsa44>& pk, const Message& msg,
            const mldsa::Signature<mldsa::MlDsa44>& sig);

// Verify a proof of knowledge of a message and a signature on it under pk. Returns false if the
// proof is invalid.
//
// Throws std::bad_alloc if memory allocation fails. An invalid proof never causes an exception.
bool verify(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> proof);

} // namespace vole_mole::mldsa_pok

#endif
