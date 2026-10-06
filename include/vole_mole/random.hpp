// Cryptographically secure randomness from the operating system.

#ifndef VOLE_MOLE_RANDOM_HPP
#define VOLE_MOLE_RANDOM_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole {

// Fill `out` with bytes from the operating system's cryptographically secure random number
// generator (e.g., getrandom() on Linux and arc4random_buf() on macOS).
//
// Throws std::runtime_error if the operating system's random number generator fails, e.g., because
// it hasn't been seeded yet early in boot. The contents of `out` are then unspecified.
void random_bytes(std::span<uint8_t> out);

// Return N bytes from the operating system's cryptographically secure random number generator.
//
// Throws as for random_bytes(std::span<uint8_t>).
template <size_t N> std::array<uint8_t, N> random_bytes() {
    std::array<uint8_t, N> out;
    random_bytes(out);
    return out;
}

} // namespace vole_mole

#endif
