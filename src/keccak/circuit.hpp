// Bit-level description of a Keccak-p[800] round, generic over the type of a state bit.
//
// A round is comprised of a sequence of step mappings (FIPS 202, Section 3.2): theta, rho, and pi
// are all linear; chi is a non-linear AND per bit; and iota is affine (adds a constant). If the
// input bits are polynomials of degree d in the witness, the output bits have degree 2d.
//
// The same code is instantiated with QuickSilver values to generate constraints and with a
// plain bit type to test the circuit against the plaintext implementation.

#ifndef VOLE_MOLE_KECCAK_CIRCUIT_HPP
#define VOLE_MOLE_KECCAK_CIRCUIT_HPP

#include "vole_mole/keccak.hpp"

#include "keccak/tables.hpp"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace vole_mole::detail {

// theta, rho, pi. `T` only needs `T + T` (XOR). Input and output have KP800_STATE_BITS entries.
template <typename T> std::vector<T> keccak_theta_rho_pi(const std::vector<T>& a) {
    constexpr size_t w = KECCAK_W;
    const auto idx = keccak_bit_index;

    // theta: C[x][z] = xor_y A[x][y][z], D[x][z] = C[x-1][z] ^ C[x+1][z-1]
    std::vector<T> c, d;
    c.reserve(5 * w);
    d.reserve(5 * w);
    for (size_t x = 0; x < 5; ++x) {
        for (size_t z = 0; z < w; ++z) {
            c.push_back(a[idx(x, 0, z)] + a[idx(x, 1, z)] + a[idx(x, 2, z)] + a[idx(x, 3, z)] +
                        a[idx(x, 4, z)]);
        }
    }
    for (size_t x = 0; x < 5; ++x) {
        for (size_t z = 0; z < w; ++z) {
            d.push_back(c[w * ((x + 4) % 5) + z] + c[w * ((x + 1) % 5) + (z + w - 1) % w]);
        }
    }

    // rho, pi: B[x][y][z] = A'[x'][y'][z - rho[x'][y']], where (x', y') = ((x + 3y) % 5, x) and
    // A' = theta(A).
    std::vector<T> b;
    b.reserve(KP800_STATE_BITS);
    for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
        const size_t lane = i / w, z = i % w, x = lane % 5, y = lane / 5;
        const size_t sx = (x + 3 * y) % 5, sy = x;
        const size_t sz = (z + w - KECCAK_RHO[sx][sy]) % w;
        b.push_back(a[idx(sx, sy, sz)] + d[w * sx + sz]);
    }
    return b;
}

// Full round `round` (0-based index into Keccak-p[800, 12]).
//
// `Chi` computes `a ^ (~b & c)` from three bits of the input type (and in doing so doubles the
// degree); `AddConst` XORs a public bit into a bit of the output type.
template <typename In, typename Chi, typename AddConst>
auto keccak_round(const std::vector<In>& in, size_t round, Chi chi, AddConst add_const) {
    constexpr size_t w = KECCAK_W;
    const auto idx = keccak_bit_index;

    const std::vector<In> b = keccak_theta_rho_pi(in);

    using Out = decltype(chi(b[0], b[0], b[0]));
    std::vector<Out> out;
    out.reserve(KP800_STATE_BITS);
    for (size_t y = 0; y < 5; ++y) {
        for (size_t x = 0; x < 5; ++x) {
            for (size_t z = 0; z < w; ++z) {
                out.push_back(
                    chi(b[idx(x, y, z)], b[idx((x + 1) % 5, y, z)], b[idx((x + 2) % 5, y, z)]));
            }
        }
    }

    // iota: only lane (0, 0) is affected.
    const uint32_t rc = KP800_RC[round];
    for (size_t z = 0; z < w; ++z) {
        if ((rc >> z) & 1) {
            out[idx(0, 0, z)] = add_const(out[idx(0, 0, z)]);
        }
    }
    return out;
}

} // namespace vole_mole::detail

#endif
