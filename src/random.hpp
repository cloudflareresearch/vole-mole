// Randomness from the operating system's random number generator.

#ifndef VOLE_MOLE_RANDOM_HPP
#define VOLE_MOLE_RANDOM_HPP

extern "C" {
#include "randomness.h" // from faest-arch-opt
}

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>

namespace vole_mole::detail {

// Return N random bytes.
//
// Throws std::runtime_error if the operating system's random number generator fails.
template <size_t N> std::array<uint8_t, N> random_bytes() {
    std::array<uint8_t, N> out;
    if (rand_bytes(out.data(), out.size()) != 0) {
        throw std::runtime_error("failed to get randomness from the operating system");
    }
    return out;
}

} // namespace vole_mole::detail

#endif
