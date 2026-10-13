// An experimental zero-knowledge proof of knowledge of an ECDSA-P256-SHA256 signature (FIPS 186-5)
// on a hidden message, with VOLE-in-the-Head.
//
// The prover holds a message msg and a signature (r, s) on msg under a public key pk. The proof
// convinces the verifier that the prover knows such a message and signature, without revealing
// either: only pk, the length of msg, and a context string bound to the proof are public. See
// src/ecdsa_pok/relation.hpp for how it works.
//
// WARNING: This is a proof of concept. The prover's computations on the signature and the message
// are not constant time.

#ifndef VOLE_MOLE_ECDSA_POK_HPP
#define VOLE_MOLE_ECDSA_POK_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::ecdsa_pok {

// Version of the proof, for domain separation.
constexpr uint8_t VERSION = 0;

// SEC 1 uncompressed public key: 0x04 || x || y.
constexpr size_t PUBLIC_KEY_BYTES = 65;
using PublicKey = std::array<uint8_t, PUBLIC_KEY_BYTES>;

// r || s, each 32 big-endian bytes.
constexpr size_t SIGNATURE_BYTES = 64;
using Signature = std::array<uint8_t, SIGNATURE_BYTES>;

// The message is at most MAX_MESSAGE_BYTES long (MAX_BLOCKS blocks of SHA-256).
constexpr size_t MAX_BLOCKS = 2;
constexpr size_t MAX_MESSAGE_BYTES = 64 * MAX_BLOCKS - 9;

// The VOLEitH parameters, from the fastest to the smallest proofs: `fast` is like FAEST-128f, and
// `small` like FAEST-128s; `medium` is like `fast` but with deeper trees for the proof over the
// fields of P-256, which dominates the proof size.
enum class Vole : uint8_t { fast = 0, medium = 1, small = 2 };

// How the witness of the binary proof is committed: directly (`none`), or derived from a short key
// with a PRG, which makes the proof much smaller (see "Derived witnesses" in src/voleith.hpp):
// `local` is the local PRG with 2 products per output, whose security assumption is less studied
// and whose key length is a rough estimate (experimental); `mq` is the dense MQ PRG (2 instances),
// which is slower.
enum class WitnessPrg : uint8_t { none = 0, local = 1, mq = 2 };

struct Params {
    Vole vole = Vole::fast;
    WitnessPrg prg = WitnessPrg::local;
};

// The length of a proof for a message of msg_len bytes.
//
// Throws std::invalid_argument if msg_len > MAX_MESSAGE_BYTES.
size_t proof_bytes(size_t msg_len, Params params = {});

// Prove knowledge of msg and sig, a valid signature on msg under pk. ctx is bound to the proof.
//
// Throws std::invalid_argument if pk isn't a valid public key, if sig isn't a valid signature on
// msg under pk, or if msg is longer than MAX_MESSAGE_BYTES; std::runtime_error if the operating
// system's random number generator fails, or if proof generation fails (which happens with
// negligible probability); and std::bad_alloc if memory allocation fails.
std::vector<uint8_t> prove(const PublicKey& pk, std::span<const uint8_t> msg, const Signature& sig,
                           std::span<const uint8_t> ctx, Params params = {});

// Verify a proof of knowledge of a message of msg_len bytes and a valid signature on it under pk,
// for context ctx. Returns false if the proof is invalid (including if it has the wrong length, or
// if pk isn't a valid public key).
//
// Throws std::bad_alloc if memory allocation fails.
bool verify(const PublicKey& pk, size_t msg_len, std::span<const uint8_t> ctx,
            std::span<const uint8_t> proof, Params params = {});

} // namespace vole_mole::ecdsa_pok

#endif
