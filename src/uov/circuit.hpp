// Evaluation of the UOV public map on QuickSilver-committed values, for proving statements of the
// form P(s) = t in zero knowledge.
//
// UOV is defined over GF(256), and faest-arch-opt embeds GF(256) (as the AES field) into GF(2^128),
// so we can evaluate P directly on committed field elements. Each component of P is a quadratic
// form in s, so if the elements of s have degree 1, then the components of P(s) have degree 2.
//
// Rather than evaluating each of the M components, we evaluate a random linear combination of them.

#ifndef VOLE_MOLE_UOV_CIRCUIT_HPP
#define VOLE_MOLE_UOV_CIRCUIT_HPP

#include "vole_mole/uov.hpp"

#include "uov/public_key.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
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

// A random linear combination of the M components of the target, which lets us prove
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
    static constexpr size_t CHALLENGE_BYTES =
        faest::QS_CONSTANTS<QS::secpar_v, QS::max_degree>::CHALLENGE_BYTES;
    static constexpr size_t POLY_BYTES = faest::secpar_to_bytes(QS::secpar_v);
    static constexpr size_t L_BYTES = M * POLY_BYTES;

    // Derive l from the QuickSilver challenge chal2 and a domain separation tag.
    Combination(std::span<const uint8_t, CHALLENGE_BYTES> chal2, std::span<const uint8_t> dst) {
        std::array<uint8_t, L_BYTES> l_bytes;
        faest::hash_state hasher;
        hasher.init(QS::secpar_v);
        hasher.update(chal2);
        hasher.update(dst);
        hasher.finalize(l_bytes);
        std::array<poly, M> l;
        for (size_t k = 0; k < M; ++k) {
            l[k] = poly::load(&l_bytes[k * POLY_BYTES]);
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
template <typename QS>
qs_val<QS, 2> qs_eval_combined_public_map(const PublicKey& pk, std::span<const qs_val<QS, 1>, N> s,
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

} // namespace vole_mole::uov::detail

#endif
