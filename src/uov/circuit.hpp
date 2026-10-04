// Evaluation of the UOV public map on QuickSilver-committed values, for proving statements of the
// form P(s) = t in zero knowledge.
//
// UOV is defined over GF(256), and faest-arch-opt embeds GF(256) (as the AES field) into GF(2^128),
// so we can evaluate P directly on committed field elements. Each component of P is a quadratic
// form in s, so if the elements of s have degree 1, then the components of P(s) have degree 2.

#ifndef VOLE_MOLE_UOV_CIRCUIT_HPP
#define VOLE_MOLE_UOV_CIRCUIT_HPP

#include "vole_mole/uov.hpp"

#include "gf256.hpp"
#include "qs_gf256.hpp"
#include "uov/public_key.hpp"

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::uov::detail {

using vole_mole::detail::gf256_madd;
using vole_mole::detail::gf256_padded;
using vole_mole::detail::Gf256MulByConst;
using vole_mole::detail::IS_QS_PROVER;
using vole_mole::detail::qs_gf256;

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

// Evaluate the public map P at the committed preimage s, returning the masked target P(s). This is
// the generic implementation, for any QuickSilver state; see qs_eval_public_map.
template <typename QS>
std::array<qs_val<QS, 2>, M> qs_eval_public_map_generic(const PublicKey& pk,
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

// The same as qs_eval_public_map_generic, for the QuickSilver prover.
//
// The values of s, and hence of the rows, are in GF(256) (see qs_gf256.hpp): the row accumulation
// (the bulk of the cost) handles one coefficient in GF(2^128) (as the verifier does) and M bytes,
// which we process 16 at a time (see gf256_madd), rather than two coefficients in GF(2^128). This
// also lets us compute the products s_i * row with 2 rather than 4 multiplications in GF(2^128),
// without intermediate reductions. The result is the same as qs_eval_public_map_generic's.
template <typename QS>
    requires IS_QS_PROVER<QS>
std::array<qs_val<QS, 2>, M> qs_eval_public_map_prover(const PublicKey& pk,
                                                       std::span<const qs_gf256<QS, 1>, N> s) {
    constexpr faest::secpar S = QS::secpar_v;
    using poly = faest::poly_secpar<S>;
    using poly2 = faest::poly_2secpar<S>;

    // For each s_j = m_j X + v_j: the multiples of m_j by 4-bit constants in the low and high
    // nibble (as for Gf256MulTable), and multiplication by v_j in GF(256).
    struct MulTable {
        std::array<poly, 16> lo, hi;
        Gf256MulByConst mul_value;

        poly mul_mac(uint8_t a) const { return lo[a & 0xf] + hi[a >> 4]; }
    };
    std::vector<MulTable> s_mul(N);
    std::array<poly, N> mac;
    std::array<uint8_t, N> value;
    for (size_t j = 0; j < N; ++j) {
        mac[j] = s[j].mac.coeffs[0];
        value[j] = s[j].value;
        MulTable& t = s_mul[j];
        t.lo[0] = t.hi[0] = poly::set_zero();
        for (size_t b = 0; b < 4; ++b) {
            t.lo[size_t{1} << b] = (embed<QS>(static_cast<uint8_t>(1u << b)) * mac[j])
                                       .template reduce_to<QS::secpar_bits>();
            t.hi[size_t{1} << b] = (embed<QS>(static_cast<uint8_t>(16u << b)) * mac[j])
                                       .template reduce_to<QS::secpar_bits>();
        }
        for (size_t n = 3; n < 16; ++n) {
            const size_t low_bit = n & (~n + 1);
            if (n != low_bit) {
                t.lo[n] = t.lo[n ^ low_bit] + t.lo[low_bit];
                t.hi[n] = t.hi[n ^ low_bit] + t.hi[low_bit];
            }
        }
        t.mul_value = Gf256MulByConst(value[j]);
    }

    // P(s)[k] = p2[k] X^2 + p1[k] X + p0[k]. p0 and p1 are accumulated without reduction.
    std::array<poly2, M> p0, p1;
    p0.fill(poly2::set_zero());
    p1.fill(poly2::set_zero());
    std::array<uint8_t, M> p2{};

    // row[k] = sum_{j >= i} a_{ij}[k] * s_j for the current i, with MAC row_mac[k] and value
    // row_value[k].
    std::array<poly, M> row_mac;
    std::array<uint8_t, gf256_padded(M)> row_value{};
    row_mac.fill(poly::set_zero());
    size_t current_i = 0;
    const auto finish_row = [&](size_t i) {
        // s_i * row = m_i m_row X^2 + (m_i v_row + v_i m_row) X + v_i v_row
        const poly embed_v_i = embed<QS>(value[i]);
        for (size_t k = 0; k < M; ++k) {
            p0[k] += mac[i] * row_mac[k];
            p1[k] += poly2::from(s_mul[i].mul_mac(row_value[k])) + embed_v_i * row_mac[k];
            p2[k] ^= s_mul[i].mul_value(row_value[k]);
            row_mac[k] = poly::set_zero();
            row_value[k] = 0;
        }
    };
    for_each_monomial(PublicKeyAccess::expanded(pk),
                      [&](size_t i, size_t j, std::span<const uint8_t, M> coeffs) {
                          if (i != current_i) {
                              finish_row(current_i);
                              current_i = i;
                          }
                          const MulTable& t = s_mul[j];
                          for (size_t k = 0; k < M; ++k) {
                              row_mac[k] += t.mul_mac(coeffs[k]);
                          }
                          gf256_madd(row_value, coeffs, t.mul_value);
                      });
    finish_row(current_i);

    std::array<qs_val<QS, 2>, M> out;
    for (size_t k = 0; k < M; ++k) {
        out[k].mac.coeffs[0] = p0[k].template reduce_to<QS::secpar_bits>();
        out[k].mac.coeffs[1] = p1[k].template reduce_to<QS::secpar_bits>();
        out[k].mac.coeffs[2] = embed<QS>(p2[k]);
    }
    return out;
}

// Evaluate the public map P at the committed preimage s, returning the masked target P(s).
template <typename QS>
std::array<qs_val<QS, 2>, M> qs_eval_public_map(const PublicKey& pk,
                                                std::span<const qs_gf256<QS, 1>, N> s) {
    if constexpr (IS_QS_PROVER<QS>) {
        return qs_eval_public_map_prover<QS>(pk, s);
    } else {
        return qs_eval_public_map_generic<QS>(pk, s);
    }
}

} // namespace vole_mole::uov::detail

#endif
