// Constants for Keccak-p[b, n_r] with lanes of w = b / 25 bits, for the two instances we use:
// Keccak-p[800, 12] (`Kp800`) and Keccak-f[1600] = Keccak-p[1600, 24] (`Kf1600`, as in SHA-3 and
// SHAKE).

#ifndef VOLE_MOLE_KECCAK_TABLES_HPP
#define VOLE_MOLE_KECCAK_TABLES_HPP

#include "vole_mole/keccak.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::detail {

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

// Round constant for round index `ir` (FIPS 202, Algorithm 6) for lanes of 2^l bits.
constexpr uint64_t keccak_round_constant(size_t l, size_t ir) {
    uint64_t rc = 0;
    for (size_t j = 0; j <= l; ++j) {
        rc |= uint64_t{keccak_rc_bit(j + 7 * ir)} << ((size_t{1} << j) - 1);
    }
    return rc;
}

// The constants of Keccak-p[25 * 2^L, ROUNDS].
template <size_t L, size_t ROUNDS_> struct KeccakSpec {
    static constexpr size_t W = size_t{1} << L; // lane size
    static constexpr size_t LOG_W = L;
    static constexpr size_t ROUNDS = ROUNDS_;
    static constexpr size_t STATE_BITS = 25 * W;
    static constexpr size_t STATE_BYTES = STATE_BITS / 8;
    using State = std::array<uint8_t, STATE_BYTES>;

    // Round constants. Keccak-p[b, n_r] uses round indices 12 + 2l - n_r, ..., 12 + 2l - 1, i.e.,
    // the last n_r rounds of Keccak-f[b] (FIPS 202, Section 3.3).
    static constexpr std::array<uint64_t, ROUNDS> RC = [] {
        std::array<uint64_t, ROUNDS> out{};
        for (size_t i = 0; i < ROUNDS; ++i) {
            out[i] = keccak_round_constant(L, 12 + 2 * L - ROUNDS + i);
        }
        return out;
    }();

    // Rho rotation offsets (FIPS 202, Algorithm 2), indexed [x][y], reduced mod w.
    static constexpr std::array<std::array<unsigned, 5>, 5> RHO = [] {
        std::array<std::array<unsigned, 5>, 5> out{};
        size_t x = 1, y = 0;
        for (size_t t = 0; t < 24; ++t) {
            out[x][y] = static_cast<unsigned>(((t + 1) * (t + 2) / 2) % W);
            const size_t nx = y, ny = (2 * x + 3 * y) % 5;
            x = nx;
            y = ny;
        }
        return out;
    }();

    // Index of bit z of lane (x, y) in the state (FIPS 202, Section 3.1.2).
    static constexpr size_t bit_index(size_t x, size_t y, size_t z) { return W * (5 * y + x) + z; }

    // Inverse of theta.
    //
    // theta adds D[x][z] = C[x-1][z] + C[x+1][z-1] to each bit of column (x, z), where C[x][z] is
    // the parity of column (x, z) of the input. Since a column has an odd number of bits (5), the
    // column parities of the output are C' = C + D = (1 + M) C, where M is the linear map C -> D.
    // Hence
    //
    //   D = M C = M (1 + M)^{-1} C' = ((1 + M)^{-1} + 1) C',
    //
    // so theta is inverted by adding the same D to each column of its output.
    //
    // (1 + M)^{-1} is dense, but has a sparse factorization: M = X^-1 + X Z^-1, where X and Z are
    // the translations by 1 in x and z, which commute. Over GF(2), squaring is linear, so
    //
    //   (1 + M) (1 + M) (1 + M^2) (1 + M^4) ... (1 + M^(w/2)) = 1 + M^w = 1 + X^-w + X^w,
    //
    // as Z^w = 1. Hence (1 + M)^{-1} = Q^{-1} (1 + M) (1 + M^2) ... (1 + M^(w/2)) where Q^{-1} is
    // the inverse of 1 + X^-w + X^w, a polynomial in X modulo X^5 + 1.
    //
    // Bit i of THETA_INV_Q is the coefficient of X^i of Q^{-1}.
    static constexpr uint8_t THETA_INV_Q = [] {
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
        const unsigned q = 1u ^ (1u << (5 - W % 5) % 5) ^ (1u << W % 5);
        for (unsigned r = 1; r < 32; ++r) {
            if (mul(q, r) == 1) {
                return static_cast<uint8_t>(r);
            }
        }
        throw "theta is not invertible"; // not a constant expression: fails compilation
    }();
};

using Kp800 = KeccakSpec<5, KP800_ROUNDS>;
using Kf1600 = KeccakSpec<6, KF1600_ROUNDS>;
static_assert(Kp800::STATE_BYTES == KP800_STATE_BYTES);
static_assert(Kf1600::STATE_BYTES == KF1600_STATE_BYTES);

// Names for Keccak-p[800, 12], which predate KeccakSpec.
constexpr size_t KECCAK_W = Kp800::W;
constexpr size_t KECCAK_L = Kp800::LOG_W;
constexpr auto KECCAK_RHO = Kp800::RHO;
constexpr uint8_t KECCAK_THETA_INV_Q = Kp800::THETA_INV_Q;
constexpr size_t keccak_bit_index(size_t x, size_t y, size_t z) {
    return Kp800::bit_index(x, y, z);
}

static_assert(Kp800::THETA_INV_Q == 0b10011); // (1 + X^2 + X^3)^{-1} = 1 + X + X^4
// Sanity checks against well-known values of the 64-bit constants (FIPS 202 and the Keccak team's
// reference), which Keccak-p[800, 12] truncates to their low 32 bits.
static_assert(Kp800::RC[0] == 0x80008009u);  // RC[10] = 0x0000000080008009
static_assert(Kp800::RC[11] == 0x00008080u); // RC[21] = 0x8000000000008080
static_assert(Kp800::RHO[1][0] == 1 && Kp800::RHO[0][2] == 3 && Kp800::RHO[1][1] == 44 % 32);
static_assert(Kf1600::RC[0] == 0x0000000000000001u);
static_assert(Kf1600::RC[1] == 0x0000000000008082u);
static_assert(Kf1600::RC[10] == 0x0000000080008009u);
static_assert(Kf1600::RC[21] == 0x8000000000008080u);
static_assert(Kf1600::RC[23] == 0x8000000080008008u);
static_assert(Kf1600::RHO[1][1] == 44 && Kf1600::RHO[4][4] == 14 && Kf1600::RHO[0][4] == 18);

} // namespace vole_mole::detail

#endif
