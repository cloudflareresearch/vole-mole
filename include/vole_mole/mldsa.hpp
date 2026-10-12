// ML-DSA (FIPS 204): key generation, signing, and verification.
//
// This is a straightforward (not hardened or optimized) implementation of the external ("pure")
// ML-DSA interface. It's what's needed to produce and check the signatures of which
// vole_mole::mldsa_pok proves knowledge.

#ifndef VOLE_MOLE_MLDSA_HPP
#define VOLE_MOLE_MLDSA_HPP

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::mldsa {

// The parameter sets of FIPS 204, Table 1.
struct MlDsa44 {
    static constexpr size_t K = 4;
    static constexpr size_t L = 4;
    static constexpr size_t ETA = 2;
    static constexpr size_t TAU = 39;
    static constexpr size_t LAMBDA = 128;
    static constexpr uint32_t GAMMA1 = uint32_t{1} << 17;
    static constexpr uint32_t GAMMA2 = (8380417 - 1) / 88;
    static constexpr size_t OMEGA = 80;
};
struct MlDsa65 {
    static constexpr size_t K = 6;
    static constexpr size_t L = 5;
    static constexpr size_t ETA = 4;
    static constexpr size_t TAU = 49;
    static constexpr size_t LAMBDA = 192;
    static constexpr uint32_t GAMMA1 = uint32_t{1} << 19;
    static constexpr uint32_t GAMMA2 = (8380417 - 1) / 32;
    static constexpr size_t OMEGA = 55;
};
struct MlDsa87 {
    static constexpr size_t K = 8;
    static constexpr size_t L = 7;
    static constexpr size_t ETA = 2;
    static constexpr size_t TAU = 60;
    static constexpr size_t LAMBDA = 256;
    static constexpr uint32_t GAMMA1 = uint32_t{1} << 19;
    static constexpr uint32_t GAMMA2 = (8380417 - 1) / 32;
    static constexpr size_t OMEGA = 75;
};

template <typename P>
concept ParamSet = std::same_as<P, MlDsa44> || std::same_as<P, MlDsa65> || std::same_as<P, MlDsa87>;

namespace detail {
constexpr size_t bitlen(uint64_t x) { return x == 0 ? 0 : 1 + bitlen(x >> 1); }
} // namespace detail

// The seed xi from which ML-DSA.KeyGen_internal derives a key pair.
constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

// The randomness of ML-DSA.Sign_internal: random for hedged signing, zero for deterministic.
constexpr size_t RND_BYTES = 32;
using Rnd = std::array<uint8_t, RND_BYTES>;

// FIPS 204, Table 2.
template <ParamSet P> constexpr size_t PUBLIC_KEY_BYTES = 32 + 32 * P::K * 10;
template <ParamSet P>
constexpr size_t SECRET_KEY_BYTES =
    128 + 32 * (P::K + P::L) * detail::bitlen(2 * P::ETA) + 32 * 13 * P::K;
template <ParamSet P>
constexpr size_t SIGNATURE_BYTES =
    P::LAMBDA / 4 + P::L * 32 * (1 + detail::bitlen(P::GAMMA1 - 1)) + P::OMEGA + P::K;

template <ParamSet P> using PublicKey = std::array<uint8_t, PUBLIC_KEY_BYTES<P>>;
template <ParamSet P> using SecretKey = std::array<uint8_t, SECRET_KEY_BYTES<P>>;
template <ParamSet P> using Signature = std::array<uint8_t, SIGNATURE_BYTES<P>>;

template <ParamSet P> struct KeyPair {
    PublicKey<P> pk;
    SecretKey<P> sk;
};

// The maximum length of a context string.
constexpr size_t MAX_CONTEXT_BYTES = 255;

// ML-DSA.KeyGen_internal(xi) (FIPS 204, Algorithm 6).
template <ParamSet P> KeyPair<P> keygen(const Seed& xi);

// ML-DSA.KeyGen() (FIPS 204, Algorithm 1). Throws std::runtime_error if the operating system's
// random number generator fails.
template <ParamSet P> KeyPair<P> keygen();

// ML-DSA.Sign(sk, M, ctx) (FIPS 204, Algorithm 2) with the given randomness `rnd` (all zero for
// the deterministic variant). Throws std::invalid_argument if ctx is longer than
// MAX_CONTEXT_BYTES.
template <ParamSet P>
Signature<P> sign(const SecretKey<P>& sk, std::span<const uint8_t> msg,
                  std::span<const uint8_t> ctx, const Rnd& rnd);

// ML-DSA.Sign(sk, M, ctx) (FIPS 204, Algorithm 2), hedged with fresh randomness. Throws
// std::invalid_argument if ctx is too long and std::runtime_error if the operating system's random
// number generator fails.
template <ParamSet P>
Signature<P> sign(const SecretKey<P>& sk, std::span<const uint8_t> msg,
                  std::span<const uint8_t> ctx);

// ML-DSA.Verify(pk, M, sigma, ctx) (FIPS 204, Algorithm 3). Returns false if ctx is too long.
template <ParamSet P>
bool verify(const PublicKey<P>& pk, std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
            const Signature<P>& sig);

#define VOLE_MOLE_MLDSA_EXTERN(P)                                                                  \
    extern template KeyPair<P> keygen<P>(const Seed&);                                             \
    extern template KeyPair<P> keygen<P>();                                                        \
    extern template Signature<P> sign<P>(const SecretKey<P>&, std::span<const uint8_t>,            \
                                         std::span<const uint8_t>, const Rnd&);                    \
    extern template Signature<P> sign<P>(const SecretKey<P>&, std::span<const uint8_t>,            \
                                         std::span<const uint8_t>);                                \
    extern template bool verify<P>(const PublicKey<P>&, std::span<const uint8_t>,                  \
                                   std::span<const uint8_t>, const Signature<P>&);
VOLE_MOLE_MLDSA_EXTERN(MlDsa44)
VOLE_MOLE_MLDSA_EXTERN(MlDsa65)
VOLE_MOLE_MLDSA_EXTERN(MlDsa87)
#undef VOLE_MOLE_MLDSA_EXTERN

} // namespace vole_mole::mldsa

#endif
