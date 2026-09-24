// Constants for Keccak-p[800, 12].

#ifndef VOLE_MOLE_KECCAK_TABLES_HPP
#define VOLE_MOLE_KECCAK_TABLES_HPP

#include "vole_mole/keccak.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::detail {

constexpr size_t KECCAK_W = 32; // lane size for b = 800
constexpr size_t KECCAK_L = 5;  // log2(KECCAK_W)
static_assert(25 * KECCAK_W == 8 * KP800_STATE_BYTES);
static_assert(size_t{1} << KECCAK_L == KECCAK_W);

// FIPS 202, Algorithm 5.
constexpr uint32_t keccak_rc_bit(size_t t) {
    if (t % 255 == 0) {
        return 1;
    }
    uint32_t r = 1; // bit i of r is R[i]
    for (size_t i = 1; i <= t % 255; ++i) {
        r <<= 1; // R = 0 || R
        const uint32_t r8 = (r >> 8) & 1;
        r ^= r8 | (r8 << 4) | (r8 << 5) | (r8 << 6);
        r &= 0xff; // R = Trunc_8(R)
    }
    return r & 1;
}

// Round constant for round index `ir` (FIPS 202, Algorithm 6), truncated to a 32-bit lane.
constexpr uint32_t keccak_round_constant(size_t ir) {
    uint32_t rc = 0;
    for (size_t j = 0; j <= KECCAK_L; ++j) {
        rc |= keccak_rc_bit(j + 7 * ir) << ((1u << j) - 1);
    }
    return rc;
}

// Round constants for Keccak-p[800, 12]. Keccak-p[800, 12] uses round indices
// 12 + 2l - 12, ..., 12 + 2l - 1, i.e., the last 12 of the 22 rounds of Keccak-f[800].
constexpr std::array<uint32_t, 12> KP800_RC = [] {
    std::array<uint32_t, 12> out{};
    for (size_t i = 0; i < 12; ++i) {
        out[i] = keccak_round_constant(12 + 2 * KECCAK_L - 12 + i);
    }
    return out;
}();

// Rho rotation offsets (FIPS 202, Algorithm 2), indexed [x][y], reduced mod w.
constexpr std::array<std::array<unsigned, 5>, 5> KECCAK_RHO = [] {
    std::array<std::array<unsigned, 5>, 5> out{};
    size_t x = 1, y = 0;
    for (size_t t = 0; t < 24; ++t) {
        out[x][y] = ((t + 1) * (t + 2) / 2) % KECCAK_W;
        const size_t nx = y, ny = (2 * x + 3 * y) % 5;
        x = nx;
        y = ny;
    }
    return out;
}();

// Index of bit z of lane (x, y) in the 800-bit state (FIPS 202, Section 3.1.2).
constexpr size_t keccak_bit_index(size_t x, size_t y, size_t z) {
    return KECCAK_W * (5 * y + x) + z;
}

// Sanity checks against well-known values of the 64-bit constants (low 32 bits).
static_assert(KP800_RC[0] == 0x80008009u);  // RC[10] = 0x0000000080008009
static_assert(KP800_RC[11] == 0x00008080u); // RC[21] = 0x8000000000008080
static_assert(KECCAK_RHO[1][0] == 1 && KECCAK_RHO[0][2] == 3 && KECCAK_RHO[1][1] == 44 % 32);

} // namespace vole_mole::detail

#endif
