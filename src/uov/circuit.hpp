// Evaluation of the UOV public map on QuickSilver-committed values, for proving statements of the
// form P(s) = t in zero knowledge.
//
// UOV is defined over GF(256), and faest-arch-opt embeds GF(256) (as the AES field) into GF(2^128),
// so we can evaluate P directly on committed field elements. Each component of P is a quadratic
// form in s, so if the elements of s have degree 1, then the components of P(s) have degree 2.
//
// Rather than evaluating each of the M components, we evaluate a random linear combination of them
// (see Combination below).

#ifndef VOLE_MOLE_UOV_CIRCUIT_HPP
#define VOLE_MOLE_UOV_CIRCUIT_HPP

#include "vole_mole/uov.hpp"

#include "gf256.hpp"
#include "qs_gf256.hpp"
#include "uov/public_key.hpp"

#include "hash.hpp"        // from faest-arch-opt
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

// A random linear combination of the M components of the public map, which lets us prove
// P(s) = t with a single constraint sum_k l[k] * (P(s)[k] - t[k]) = 0 rather than M of them
// (<https://ia.cr/2026/109>, Section 8, "Evaluation of MAYO").
//
// Soundness: The coefficients l[k] are uniform elements of GF(2^128) derived from the QuickSilver
// challenge, i.e., after the prover is committed to the witness. If P(s)[k] != t[k] for some k,
// then the combination vanishes with probability 2^-128 over the choice of l[k].
//
// Since l is public, we compute the combined coefficient sum_k l[k] * a[k] of each monomial in the
// clear, so evaluating the combination on committed values costs one multiplication by a public
// constant per monomial rather than M.
template <typename QS> class Combination {
  public:
    using poly = faest::poly_secpar<QS::secpar_v>;
    static constexpr size_t POLY_BYTES = faest::secpar_to_bytes(QS::secpar_v);
    static constexpr size_t SEED_BYTES = M * POLY_BYTES;

    // Derive l from the QuickSilver challenge chal2 and a domain separation tag.
    Combination(std::span<const uint8_t> chal2, std::span<const uint8_t> dst) {
        std::array<uint8_t, SEED_BYTES> seed;
        faest::hash_state hasher;
        hasher.init(QS::secpar_v);
        hasher.update(chal2);
        hasher.update(dst);
        hasher.finalize(seed);
        std::array<poly, M> l;
        for (size_t k = 0; k < M; ++k) {
            l[k] = poly::load(&seed[k * POLY_BYTES]);
        }
        init(l);
    }

    // Use the given coefficients.
    explicit Combination(const std::array<poly, M>& l) { init(l); }

    const poly& coeff(size_t k) const { return l_[k]; }

    // sum_k l[k] * a[k] for a vector a of GF(256) elements.
    poly combine(std::span<const uint8_t, M> a) const {
        poly out = tables_[0][a[0]];
        for (size_t k = 1; k < M; ++k) {
            out = out + tables_[k][a[k]];
        }
        return out;
    }

  private:
    void init(const std::array<poly, M>& l) {
        l_ = l;
        tables_.resize(M);
        for (size_t k = 0; k < M; ++k) {
            // tables_[k][a] = l[k] * a. Since it's linear in a, we only need to multiply for the
            // powers of two, and build the other entries from their lowest set bit.
            auto& t = tables_[k];
            t[0] = poly::set_zero();
            for (size_t b = 0; b < 8; ++b) {
                t[size_t{1} << b] = (l[k] * embed<QS>(static_cast<uint8_t>(1u << b)))
                                        .template reduce_to<faest::secpar_to_bits(QS::secpar_v)>();
            }
            for (size_t a = 3; a < 256; ++a) {
                const size_t low_bit = a & (~a + 1);
                if (a != low_bit) {
                    t[a] = t[a ^ low_bit] + t[low_bit];
                }
            }
        }
    }

    std::array<poly, M> l_;
    std::vector<std::array<poly, 256>> tables_; // M tables of 4 KiB each, so on the heap
};

// Evaluate sum_k l[k] * P(s)[k] at the committed preimage s, where l is the given combination.
// This is the generic implementation, for any QuickSilver state; see
// qs_eval_combined_public_map.
template <typename QS>
qs_val<QS, 2> qs_eval_combined_public_map_generic(const PublicKey& pk,
                                                  std::span<const qs_val<QS, 1>, N> s,
                                                  const Combination<QS>& l) {
    using qs_1 = qs_val<QS, 1>;
    using qs_2 = qs_val<QS, 2>;

    // Evaluate as sum_i s_i * (sum_{j >= i} c_{ij} * s_j), where c_{ij} is the combined
    // coefficient of s_i * s_j.
    const qs_1 zero_1 = s[0] + s[0];
    qs_2 y = zero_1 * zero_1;
    qs_1 row = zero_1; // sum_{j >= i} c_{ij} * s_j for the current i
    size_t current_i = 0;
    for_each_monomial(PublicKeyAccess::expanded(pk),
                      [&](size_t i, size_t j, std::span<const uint8_t, M> coeffs) {
                          if (i != current_i) {
                              y += s[current_i] * row;
                              row = zero_1;
                              current_i = i;
                          }
                          row += l.combine(coeffs) * s[j];
                      });
    y += s[current_i] * row;
    return y;
}

// The same as qs_eval_combined_public_map_generic, for the QuickSilver prover.
//
// Write s_j = m_j X^0 + v_j X^1, with MAC m_j and value v_j in GF(256) (see qs_gf256.hpp). The
// MAC of row_i = sum_{j >= i} c_{ij} * s_j needs the combined coefficients c_{ij}, but its value is
//
//   sum_j c_{ij} v_j = sum_k l[k] * (sum_j a_{ij}[k] v_j),
//
// so we accumulate the M bytes sum_j a_{ij}[k] v_j with gf256_madd and combine them once per row
// rather than once per monomial. All products are accumulated without reduction. The result is the
// same as qs_eval_combined_public_map_generic's.
template <typename QS>
    requires IS_QS_PROVER<QS>
qs_val<QS, 2> qs_eval_combined_public_map_prover(const PublicKey& pk,
                                                 std::span<const qs_gf256<QS, 1>, N> s,
                                                 const Combination<QS>& l) {
    constexpr faest::secpar S = QS::secpar_v;
    using poly = faest::poly_secpar<S>;
    using poly2 = faest::poly_2secpar<S>;

    std::array<poly, N> mac;
    std::array<uint8_t, N> value;
    std::vector<Gf256MulByConst> mul_value(N);
    for (size_t j = 0; j < N; ++j) {
        mac[j] = s[j].mac.coeffs[0];
        value[j] = s[j].value;
        mul_value[j] = Gf256MulByConst(value[j]);
    }

    // y = y0 + y1 X + y2 X^2, accumulated without reduction.
    poly2 y0 = poly2::set_zero(), y1 = poly2::set_zero(), y2 = poly2::set_zero();

    // The MAC (unreduced) and the uncombined value of row_i for the current i.
    poly2 row_mac = poly2::set_zero();
    std::array<uint8_t, gf256_padded(M)> row_value{};
    size_t current_i = 0;
    const auto finish_row = [&](size_t i) {
        // s_i * row = m_i m_row + (m_i v_row + v_i m_row) X + v_i v_row X^2
        const poly m_row = row_mac.template reduce_to<QS::secpar_bits>();
        const poly v_row = l.combine(std::span<const uint8_t, M>(row_value.data(), M));
        const poly embed_v_i = embed<QS>(value[i]);
        y0 += mac[i] * m_row;
        y1 += mac[i] * v_row + embed_v_i * m_row;
        y2 += embed_v_i * v_row;
        row_mac = poly2::set_zero();
        row_value.fill(0);
    };
    for_each_monomial(PublicKeyAccess::expanded(pk),
                      [&](size_t i, size_t j, std::span<const uint8_t, M> coeffs) {
                          if (i != current_i) {
                              finish_row(current_i);
                              current_i = i;
                          }
                          row_mac += l.combine(coeffs) * mac[j];
                          gf256_madd(row_value, coeffs, mul_value[j]);
                      });
    finish_row(current_i);

    qs_val<QS, 2> out;
    out.mac.coeffs[0] = y0.template reduce_to<QS::secpar_bits>();
    out.mac.coeffs[1] = y1.template reduce_to<QS::secpar_bits>();
    out.mac.coeffs[2] = y2.template reduce_to<QS::secpar_bits>();
    return out;
}

// Evaluate sum_k l[k] * P(s)[k] at the committed preimage s, where l is the given combination.
template <typename QS>
qs_val<QS, 2> qs_eval_combined_public_map(const PublicKey& pk,
                                          std::span<const qs_gf256<QS, 1>, N> s,
                                          const Combination<QS>& l) {
    if constexpr (IS_QS_PROVER<QS>) {
        return qs_eval_combined_public_map_prover<QS>(pk, s, l);
    } else {
        return qs_eval_combined_public_map_generic<QS>(pk, s, l);
    }
}

} // namespace vole_mole::uov::detail

#endif
