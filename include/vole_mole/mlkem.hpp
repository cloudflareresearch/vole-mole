// ML-KEM (FIPS 203) key generation.
//
// Only key generation is implemented: it's what's needed to produce the keys for which
// vole_mole::mlkem_pop proves possession. Encapsulation and decapsulation are out of scope.

#ifndef VOLE_MOLE_MLKEM_HPP
#define VOLE_MOLE_MLKEM_HPP

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>

namespace vole_mole::mlkem {

// The parameter sets of FIPS 203, Table 2. Only the parameters relevant to key generation are
// listed.
struct MlKem512 {
    static constexpr size_t K = 2;
    static constexpr size_t ETA1 = 3;
};
struct MlKem768 {
    static constexpr size_t K = 3;
    static constexpr size_t ETA1 = 2;
};
struct MlKem1024 {
    static constexpr size_t K = 4;
    static constexpr size_t ETA1 = 2;
};

template <typename P>
concept ParamSet =
    std::same_as<P, MlKem512> || std::same_as<P, MlKem768> || std::same_as<P, MlKem1024>;

// The seed (d, z) from which ML-KEM.KeyGen_internal derives a key pair: d || z.
constexpr size_t SEED_BYTES = 64;
using Seed = std::array<uint8_t, SEED_BYTES>;

template <ParamSet P> constexpr size_t ENCAPS_KEY_BYTES = 384 * P::K + 32;
template <ParamSet P> constexpr size_t DECAPS_KEY_BYTES = 768 * P::K + 96;

template <ParamSet P> using EncapsKey = std::array<uint8_t, ENCAPS_KEY_BYTES<P>>;
template <ParamSet P> using DecapsKey = std::array<uint8_t, DECAPS_KEY_BYTES<P>>;

template <ParamSet P> struct KeyPair {
    EncapsKey<P> ek;
    DecapsKey<P> dk;
};

// ML-KEM.KeyGen_internal(d, z) (FIPS 203, Algorithm 16), where seed = d || z.
template <ParamSet P> KeyPair<P> keygen(const Seed& seed);

// ML-KEM.KeyGen() (FIPS 203, Algorithm 19): key generation from a fresh random seed.
//
// Throws std::runtime_error if the operating system's random number generator fails.
template <ParamSet P> KeyPair<P> keygen();

extern template KeyPair<MlKem512> keygen<MlKem512>(const Seed&);
extern template KeyPair<MlKem768> keygen<MlKem768>(const Seed&);
extern template KeyPair<MlKem1024> keygen<MlKem1024>(const Seed&);
extern template KeyPair<MlKem512> keygen<MlKem512>();
extern template KeyPair<MlKem768> keygen<MlKem768>();
extern template KeyPair<MlKem1024> keygen<MlKem1024>();

} // namespace vole_mole::mlkem

#endif
