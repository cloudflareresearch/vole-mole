// Internal access to the UOV public key, e.g., for proving statements about its public map in zero
// knowledge.

#ifndef VOLE_MOLE_UOV_PUBLIC_KEY_HPP
#define VOLE_MOLE_UOV_PUBLIC_KEY_HPP

#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::uov::detail {

// Number of vinegar variables. The last M variables are the oil variables.
constexpr size_t V = N - M;

constexpr size_t triangle(size_t n) { return n * (n + 1) / 2; }

// Size of the expanded public map: M coefficients for each monomial x_i * x_j with i <= j.
constexpr size_t EXPANDED_PUBLIC_KEY_BYTES = M * triangle(N);

constexpr size_t PUBLIC_KEY_DIGEST_BYTES = 32;
using PublicKeyDigest = std::array<uint8_t, PUBLIC_KEY_DIGEST_BYTES>;

struct PublicKeyAccess {
    // The expanded public map of `pk` in pqov's layout (see `for_each_monomial`).
    static std::span<const uint8_t, EXPANDED_PUBLIC_KEY_BYTES> expanded(const PublicKey& pk);

    // A digest of the compressed public key (SHAKE256), which identifies the key.
    static const PublicKeyDigest& digest(const PublicKey& pk);
};

// Call f(i, j, coeffs) for each monomial x_i * x_j (i <= j) of the public map P, where coeffs
// holds the coefficients of the monomial in each of the M components of P, i.e., P(x)[k] is the
// sum of coeffs[k] * x_i * x_j over all monomials, with arithmetic in GF(256).
//
// Monomials are visited in increasing order of i, so all monomials for a given i are visited
// consecutively.
//
// The UOV v3 spec lays out the expanded public map as three upper-triangular or rectangular blocks,
// stored one after the other: P1 (vinegar x vinegar), P2 (vinegar x oil), and P3 (oil x oil). Each
// block is stored row by row.
template <typename F>
void for_each_monomial(std::span<const uint8_t, EXPANDED_PUBLIC_KEY_BYTES> pk, F&& f) {
    const uint8_t* p1 = pk.data();
    const uint8_t* p2 = p1 + M * triangle(V);
    const uint8_t* p3 = p2 + M * V * M;
    for (size_t i = 0; i < V; ++i) {
        for (size_t j = i; j < V; ++j, p1 += M) {
            f(i, j, std::span<const uint8_t, M>(p1, M));
        }
        for (size_t j = V; j < N; ++j, p2 += M) {
            f(i, j, std::span<const uint8_t, M>(p2, M));
        }
    }
    for (size_t i = V; i < N; ++i) {
        for (size_t j = i; j < N; ++j, p3 += M) {
            f(i, j, std::span<const uint8_t, M>(p3, M));
        }
    }
}

} // namespace vole_mole::uov::detail

#endif
