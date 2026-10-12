// Proof of possession (PoP) of an ML-KEM decapsulation key.
//
// A KEM key can't sign, so it can't prove possession of its private key the way a signature key
// does in a certificate signing request. Instead, the holder of an ML-KEM key pair (ek, dk) proves
// in zero knowledge that it knows the secret behind ek. The proof is bound to a context string,
// e.g., a challenge chosen by the verifier, the subject of a certificate, or a transcript.
//
// The statement. An ML-KEM encapsulation key is ek = ByteEncode_12(t-hat) || rho, where
// t-hat = A-hat * NTT(s) + NTT(e) for a matrix A-hat expanded from rho and secret vectors s and e
// with coefficients in [-eta_1, eta_1]. The prover shows knowledge of (s, e) with coefficients in
// [-eta_1, eta_1] such that
//
//   t-hat = A-hat * NTT(s) + NTT(e)  (mod q).
//
// Such an (s, e) is exactly what decryption requires: anyone who knows it can decapsulate (the
// rest of dk, namely H(ek) and the implicit rejection seed z, is derivable from ek or irrelevant
// for valid ciphertexts). Note this is not a proof that ek was generated honestly from a seed.
//
// The proof system is VOLE-in-the-Head over F_3329 (see src/voleith_fq/voleith.hpp). It is
// non-interactive (Fiat-Shamir), zero-knowledge, and has about 125 bits of soundness.

#ifndef VOLE_MOLE_MLKEM_POP_HPP
#define VOLE_MOLE_MLKEM_POP_HPP

#include "vole_mole/mlkem.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::mlkem_pop {

// Version of the proof of possession, used for domain separation.
constexpr uint8_t VERSION = 0;

template <mlkem::ParamSet P> constexpr size_t PROOF_BYTES = 0;
template <> inline constexpr size_t PROOF_BYTES<mlkem::MlKem512> = 17568;
template <> inline constexpr size_t PROOF_BYTES<mlkem::MlKem768> = 22944;
template <> inline constexpr size_t PROOF_BYTES<mlkem::MlKem1024> = 29088;

template <mlkem::ParamSet P> using Proof = std::array<uint8_t, PROOF_BYTES<P>>;

// Prove possession of dk, binding the proof to context. The statement is about the encapsulation
// key embedded in dk.
//
// Throws std::invalid_argument if dk isn't a valid ML-KEM decapsulation key (i.e., it fails the
// hash check of FIPS 203, Section 7.3, its encapsulation key fails the modulus check, or its
// secret isn't short), std::bad_alloc if memory allocation fails, and std::runtime_error if the
// operating system's random number generator fails.
template <mlkem::ParamSet P>
Proof<P> prove(const mlkem::DecapsKey<P>& dk, std::span<const uint8_t> context);

// Verify a proof of possession of the decapsulation key for ek, bound to context. Returns false
// if the proof is invalid or ek fails the modulus check (FIPS 203, Section 7.2).
//
// Throws std::bad_alloc if memory allocation fails. An invalid proof never causes an exception.
template <mlkem::ParamSet P>
bool verify(const mlkem::EncapsKey<P>& ek, std::span<const uint8_t> context, const Proof<P>& proof);

extern template Proof<mlkem::MlKem512>
prove<mlkem::MlKem512>(const mlkem::DecapsKey<mlkem::MlKem512>&, std::span<const uint8_t>);
extern template Proof<mlkem::MlKem768>
prove<mlkem::MlKem768>(const mlkem::DecapsKey<mlkem::MlKem768>&, std::span<const uint8_t>);
extern template Proof<mlkem::MlKem1024>
prove<mlkem::MlKem1024>(const mlkem::DecapsKey<mlkem::MlKem1024>&, std::span<const uint8_t>);
extern template bool verify<mlkem::MlKem512>(const mlkem::EncapsKey<mlkem::MlKem512>&,
                                             std::span<const uint8_t>,
                                             const Proof<mlkem::MlKem512>&);
extern template bool verify<mlkem::MlKem768>(const mlkem::EncapsKey<mlkem::MlKem768>&,
                                             std::span<const uint8_t>,
                                             const Proof<mlkem::MlKem768>&);
extern template bool verify<mlkem::MlKem1024>(const mlkem::EncapsKey<mlkem::MlKem1024>&,
                                              std::span<const uint8_t>,
                                              const Proof<mlkem::MlKem1024>&);

} // namespace vole_mole::mlkem_pop

#endif
