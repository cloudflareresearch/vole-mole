// Evaluation of the UOV public map on QuickSilver-committed values, for proving statements of the
// form P(s) = t in zero knowledge.
//
// UOV is defined over GF(256), and faest-arch-opt embeds GF(256) (as the AES field) into GF(2^128),
// so we can evaluate P directly on committed field elements. Each component of P is a quadratic
// form in s, so if the elements of s have degree 1, then the components of P(s) have degree 2.

#ifndef VOLE_MOLE_UOV_CIRCUIT_HPP
#define VOLE_MOLE_UOV_CIRCUIT_HPP

#include "vole_mole/uov.hpp"

#include "uov/public_key.hpp"

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::uov::detail {

// A QuickSilver-committed element of GF(2^128) of degree `deg`.
template <typename QS, size_t deg> using qs_val = faest::quicksilver_gfsecpar<QS, deg>;

// The embedding of a GF(256) element into GF(2^128).
template <typename QS> faest::poly_secpar<QS::secpar_v> embed(uint8_t a) {
    return faest::poly_secpar<QS::secpar_v>::from_8_byte(a);
}

// Multiplication of a committed value x by public GF(256) constants. Multiplication by a constant
// is linear in the constant, so we precompute the products of x with each 4-bit constant in the
// low and high nibble; then a * x = lo[a & 0xf] + hi[a >> 4] costs two additions rather than a
// multiplication in GF(2^128).
template <typename QS> class Gf256MulTable {
  public:
    Gf256MulTable() = default;

    explicit Gf256MulTable(const qs_val<QS, 1>& x) {
        lo_[0] = hi_[0] = x + x; // zero
        for (size_t b = 0; b < 4; ++b) {
            lo_[size_t{1} << b] = embed<QS>(static_cast<uint8_t>(1u << b)) * x;
            hi_[size_t{1} << b] = embed<QS>(static_cast<uint8_t>(16u << b)) * x;
        }
        for (size_t n = 3; n < 16; ++n) {
            // Powers of two are already initialized; build other entries from their lowest set bit.
            const size_t low_bit = n & (~n + 1);
            if (n != low_bit) {
                lo_[n] = lo_[n ^ low_bit] + lo_[low_bit];
                hi_[n] = hi_[n ^ low_bit] + hi_[low_bit];
            }
        }
    }

    qs_val<QS, 1> mul(uint8_t a) const { return lo_[a & 0xf] + hi_[a >> 4]; }

  private:
    std::array<qs_val<QS, 1>, 16> lo_;
    std::array<qs_val<QS, 1>, 16> hi_;
};

// Evaluate the public map P at the committed preimage s, returning the masked target P(s).
template <typename QS>
std::array<qs_val<QS, 2>, M> qs_eval_public_map(const PublicKey& pk,
                                                std::span<const qs_val<QS, 1>, N> s) {
    using qs_1 = qs_val<QS, 1>;
    using qs_2 = qs_val<QS, 2>;

    std::vector<Gf256MulTable<QS>> s_mul;
    s_mul.reserve(N);
    for (const qs_1& s_j : s) {
        s_mul.emplace_back(s_j);
    }

    // Evaluate P(s) as sum_i s_i * (sum_{j >= i} a_{ij} * s_j), where a_{ij} is the vector of
    // coefficients of s_i * s_j.
    const qs_1 zero_1 = s[0] + s[0];
    std::array<qs_2, M> p;
    p.fill(zero_1 * zero_1);
    std::array<qs_1, M> row; // sum_{j >= i} a_{ij} * s_j for the current i
    row.fill(zero_1);
    size_t current_i = 0;
    const auto finish_row = [&](size_t i) {
        for (size_t k = 0; k < M; ++k) {
            p[k] += s[i] * row[k];
            row[k] = zero_1;
        }
    };
    for_each_monomial(PublicKeyAccess::expanded(pk),
                      [&](size_t i, size_t j, std::span<const uint8_t, M> coeffs) {
                          if (i != current_i) {
                              finish_row(current_i);
                              current_i = i;
                          }
                          for (size_t k = 0; k < M; ++k) {
                              row[k] += s_mul[j].mul(coeffs[k]);
                          }
                      });
    finish_row(current_i);
    return p;
}

} // namespace vole_mole::uov::detail

#endif
