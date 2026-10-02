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

// Inverse of theta.
//
// theta adds D[x][z] = C[x-1][z] + C[x+1][z-1] to each bit of column (x, z), where C[x][z] is the
// parity of column (x, z) of the input. Since a column has an odd number of bits (5), the column
// parities of the output are C' = C + D = (1 + M) C, where M is the linear map C -> D. Hence
//
//   D = M C = M (1 + M)^{-1} C' = ((1 + M)^{-1} + 1) C',
//
// so theta is inverted by adding the same D to each column of its output.
//
// (1 + M)^{-1} is dense, but has a sparse factorization: M = X^-1 + X Z^-1, where X and Z are the
// translations by 1 in x and z, which commute. Over GF(2), squaring is linear, so
//
//   (1 + M) (1 + M) (1 + M^2) (1 + M^4) ... (1 + M^(w/2)) = 1 + M^w = 1 + X^-w + X^w,
//
// as Z^w = 1. Hence (1 + M)^{-1} = Q^{-1} (1 + M) (1 + M^2) ... (1 + M^(w/2)) where Q^{-1} is the
// inverse of 1 + X^-w + X^w, a polynomial in X modulo X^5 + 1.
//
// Bit i of KECCAK_THETA_INV_Q is the coefficient of X^i of Q^{-1}.
constexpr uint8_t KECCAK_THETA_INV_Q = [] {
    const auto mul = [](unsigned a, unsigned b) { // in GF(2)[X] / (X^5 + 1)
        unsigned out = 0;
        for (size_t i = 0; i < 5; ++i) {
            for (size_t j = 0; j < 5; ++j) {
                if (((a >> i) & 1) && ((b >> j) & 1)) {
                    out ^= 1u << ((i + j) % 5);
                }
            }
        }
        return out;
    };
    const unsigned q = 1u ^ (1u << (5 - KECCAK_W % 5) % 5) ^ (1u << KECCAK_W % 5);
    for (unsigned r = 1; r < 32; ++r) {
        if (mul(q, r) == 1) {
            return static_cast<uint8_t>(r);
        }
    }
    throw "theta is not invertible"; // not a constant expression: fails compilation
}();
static_assert(KECCAK_THETA_INV_Q == 0b10011); // (1 + X^2 + X^3)^{-1} = 1 + X + X^4
// Sanity checks against well-known values of the 64-bit constants (low 32 bits).
static_assert(KP800_RC[0] == 0x80008009u);  // RC[10] = 0x0000000080008009
static_assert(KP800_RC[11] == 0x00008080u); // RC[21] = 0x8000000000008080
static_assert(KECCAK_RHO[1][0] == 1 && KECCAK_RHO[0][2] == 3 && KECCAK_RHO[1][1] == 44 % 32);

} // namespace vole_mole::detail

#endif
