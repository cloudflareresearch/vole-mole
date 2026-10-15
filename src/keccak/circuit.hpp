// Bit-level description of a Keccak-p round, generic over the instance (`Spec`, see tables.hpp;
// Keccak-p[800, 12] by default) and over the type of a state bit.
//
// A round is comprised of a sequence of step mappings (FIPS 202, Section 3.2): theta, rho, and pi
// are all linear; chi is a non-linear AND per bit; and iota is affine (adds a constant). If the
// input bits are polynomials of degree d in the witness, the output bits have degree 2d.
//
// The inverse of a round is also described: the inverse of chi (on a row of 5 bits) has degree 3,
// and the inverses of theta, rho, pi, and iota are again linear or affine. If the input bits of an
// inverse round have degree d, the output bits have degree 3d.
//
// The same code is instantiated with QuickSilver values to generate constraints and with a
// plain bit type to test the circuit against the plaintext implementation.

#ifndef VOLE_MOLE_KECCAK_CIRCUIT_HPP
#define VOLE_MOLE_KECCAK_CIRCUIT_HPP

#include "keccak/tables.hpp"

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

namespace vole_mole::detail {

// theta, rho, pi. `T` only needs `T + T` (XOR). Input and output have Spec::STATE_BITS entries.
template <typename Spec = Kp800, typename T>
std::vector<T> keccak_theta_rho_pi(const std::vector<T>& a) {
    constexpr size_t w = Spec::W;
    const auto idx = Spec::bit_index;

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
    b.reserve(Spec::STATE_BITS);
    for (size_t i = 0; i < Spec::STATE_BITS; ++i) {
        const size_t lane = i / w, z = i % w, x = lane % 5, y = lane / 5;
        const size_t sx = (x + 3 * y) % 5, sy = x;
        const size_t sz = (z + w - Spec::RHO[sx][sy]) % w;
        b.push_back(a[idx(sx, sy, sz)] + d[w * sx + sz]);
    }
    return b;
}

// Full round `round` (0-based index into the rounds of Spec). Only the first `num_out_bits` bits
// of the output are computed (all of them if `num_out_bits` is 0).
//
// `Chi` computes `a ^ (~b & c)` from three bits of the input type (and in doing so doubles the
// degree); `AddConst` XORs a public bit into a bit of the output type.
template <typename Spec = Kp800, typename In, typename Chi, typename AddConst>
auto keccak_round(const std::vector<In>& in, size_t round, Chi chi, AddConst add_const,
                  size_t num_out_bits = 0) {
    constexpr size_t w = Spec::W;
    const auto idx = Spec::bit_index;
    if (num_out_bits == 0) {
        num_out_bits = Spec::STATE_BITS;
    }

    const std::vector<In> b = keccak_theta_rho_pi<Spec>(in);

    using Out = decltype(chi(b[0], b[0], b[0]));
    std::vector<Out> out;
    out.reserve(num_out_bits);
    for (size_t i = 0; i < num_out_bits; ++i) {
        const size_t lane = i / w, z = i % w, x = lane % 5, y = lane / 5;
        out.push_back(chi(b[i], b[idx((x + 1) % 5, y, z)], b[idx((x + 2) % 5, y, z)]));
    }

    // iota: only lane (0, 0) is affected.
    const uint64_t rc = Spec::RC[round];
    for (size_t z = 0; z < w && z < num_out_bits; ++z) {
        if ((rc >> z) & 1) {
            out[idx(0, 0, z)] = add_const(out[idx(0, 0, z)]);
        }
    }
    return out;
}

// Inverse of `keccak_theta_rho_pi`. `T` only needs `T + T` (XOR).
template <typename Spec = Kp800, typename T>
std::vector<T> keccak_theta_rho_pi_inverse(const std::vector<T>& b) {
    constexpr size_t w = Spec::W;
    const auto idx = Spec::bit_index;

    // pi^-1, rho^-1: A'[x'][y'][z'] = B[x][y][z], where x = y', y = 2 (x' - y') % 5 (the inverse of
    // (x', y') = ((x + 3y) % 5, x)), and z = z' + rho[x'][y'].
    std::vector<T> a;
    a.reserve(Spec::STATE_BITS);
    for (size_t i = 0; i < Spec::STATE_BITS; ++i) {
        const size_t lane = i / w, sz = i % w, sx = lane % 5, sy = lane / 5;
        const size_t x = sy, y = (2 * (sx + 5 - sy)) % 5;
        const size_t z = (sz + Spec::RHO[sx][sy]) % w;
        a.push_back(b[idx(x, y, z)]);
    }

    // theta^-1: see KeccakSpec::THETA_INV_Q. Column parities C' of the output of theta (index w x +
    // z).
    std::vector<T> c;
    c.reserve(5 * w);
    for (size_t x = 0; x < 5; ++x) {
        for (size_t z = 0; z < w; ++z) {
            c.push_back(a[idx(x, 0, z)] + a[idx(x, 1, z)] + a[idx(x, 2, z)] + a[idx(x, 3, z)] +
                        a[idx(x, 4, z)]);
        }
    }

    // p = (1 + M) (1 + M^2) ... (1 + M^(w/2)) C', where M^s C[x][z] = C[x-s][z] + C[x+s][z-s].
    std::vector<T> p = c;
    for (size_t s = 1; s < w; s *= 2) {
        std::vector<T> next;
        next.reserve(5 * w);
        for (size_t x = 0; x < 5; ++x) {
            for (size_t z = 0; z < w; ++z) {
                next.push_back(p[w * x + z] + p[w * ((x + 5 - s % 5) % 5) + z] +
                               p[w * ((x + s) % 5) + (z + w - s) % w]);
            }
        }
        p = std::move(next);
    }

    // D = Q^{-1} p + C', where X^i p[x][z] = p[x + i][z].
    std::vector<T> d;
    d.reserve(5 * w);
    for (size_t x = 0; x < 5; ++x) {
        for (size_t z = 0; z < w; ++z) {
            T acc = c[w * x + z];
            for (size_t i = 0; i < 5; ++i) {
                if ((Spec::THETA_INV_Q >> i) & 1) {
                    acc = acc + p[w * ((x + i) % 5) + z];
                }
            }
            d.push_back(acc);
        }
    }
    for (size_t i = 0; i < Spec::STATE_BITS; ++i) {
        const size_t lane = i / w, z = i % w, x = lane % 5;
        a[i] = a[i] + d[w * x + z];
    }
    return a;
}

// Inverse of the non-linear part (chi, iota) of round `round` (0-based index into the rounds of
// Spec), i.e., the result of `keccak_theta_rho_pi` on the input of the round.
//
// `ChiInv` computes bit x of the inverse of chi on a row from bits x, ..., x + 4 (mod 5) of the row
// of the input type, i.e., `a ^ (~b & (c ^ (~d & e)))` (and in doing so triples the degree);
// `AddConst` XORs a public bit into a bit of the input type.
template <typename Spec = Kp800, typename In, typename ChiInv, typename AddConst>
auto keccak_iota_chi_inverse(const std::vector<In>& in, size_t round, ChiInv chi_inv,
                             AddConst add_const) {
    constexpr size_t w = Spec::W;
    const auto idx = Spec::bit_index;

    // iota^-1 = iota
    std::vector<In> a = in;
    const uint64_t rc = Spec::RC[round];
    for (size_t z = 0; z < w; ++z) {
        if ((rc >> z) & 1) {
            a[idx(0, 0, z)] = add_const(a[idx(0, 0, z)]);
        }
    }

    using Out = decltype(chi_inv(a[0], a[0], a[0], a[0], a[0]));
    std::vector<Out> b;
    b.reserve(Spec::STATE_BITS);
    for (size_t y = 0; y < 5; ++y) {
        for (size_t x = 0; x < 5; ++x) {
            for (size_t z = 0; z < w; ++z) {
                b.push_back(chi_inv(a[idx(x, y, z)], a[idx((x + 1) % 5, y, z)],
                                    a[idx((x + 2) % 5, y, z)], a[idx((x + 3) % 5, y, z)],
                                    a[idx((x + 4) % 5, y, z)]));
            }
        }
    }
    return b;
}

// Inverse of round `round` (0-based index into the rounds of Spec). See `keccak_iota_chi_inverse`
// for `ChiInv` and `AddConst`.
//
// Note that the inverse of theta is more expensive than theta: for Keccak-p[800], each bit of the
// output depends on 86 column parities of the input, rather than 2. (Thanks to the factorization
// described at KeccakSpec::THETA_INV_Q, computing them all costs 13 rather than 2 additions per
// column.)
template <typename Spec = Kp800, typename In, typename ChiInv, typename AddConst>
auto keccak_round_inverse(const std::vector<In>& in, size_t round, ChiInv chi_inv,
                          AddConst add_const) {
    return keccak_theta_rho_pi_inverse<Spec>(
        keccak_iota_chi_inverse<Spec>(in, round, chi_inv, add_const));
}

} // namespace vole_mole::detail

#endif
