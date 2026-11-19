// Two product trees, proven by a GKR-style sumcheck on QuickSilver-committed values (see
// docs/sumcheck-modq.md, section 2).
//
// The trees have 2^D leaves each, stacked: leaf l = T 2^D + i of tree T. Layer d (d <= D) has
// 2^(d+1) nodes, V_d(nu) = V_{d+1}(2 nu) V_{d+1}(2 nu + 1), so V_0 holds the two roots. Leaves are
// affine in committed bits: L_l = 1 + c_l x_l, or the constant 1. The protocol shows
// V_0 = (R_0, R_1) for public R_T.
//
// Messages and challenges, in order (each message is followed by one challenge):
//
//   - a message before the protocol (e.g., committed quotient bits), then challenge tau_0;
//   - for each layer d = 0, ..., D - 1: for each round j = 0, ..., d, the message (t_1, t_2) and
//     challenge rho_j; then, if d < D - 1, the message (a, b) and challenge tau.
//
// Each message of the protocol is two committed elements of GF(2^128) (32 bytes, see gf128.hpp),
// so the prover's part is NUM_ELEMS elements. The verifier's checks are D constraints of degree 2
// on committed values, and linear bookkeeping.
//
// Fiat-Shamir: Chain derives the challenges from the masked messages (see voleith_fs.hpp).

#ifndef VOLE_MOLE_SUMCHECK_TREE_SUMCHECK_HPP
#define VOLE_MOLE_SUMCHECK_TREE_SUMCHECK_HPP

#include "sumcheck/gf128.hpp"

#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

namespace vole_mole::sumcheck::detail {

// The Fiat-Shamir chain: h_{-1} = seed, h_i = H(dst || h_{i-1} || m_i), and challenge i is the
// first 16 bytes of h_i.
class Chain {
  public:
    Chain(std::span<const uint8_t> dst, std::span<const uint8_t> seed) : dst_(dst) {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(dst_);
        h.update(seed);
        h.finalize(state_);
    }

    Gf next(std::span<const uint8_t> masked_message) {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(dst_);
        h.update(state_);
        h.update(masked_message);
        h.finalize(state_);
        return gf_load(state_.data());
    }

  private:
    std::span<const uint8_t> dst_;
    std::array<uint8_t, 32> state_;
};

// eq(z, nu) = prod_j (nu_j ? z_j : 1 + z_j) for all nu with z.size() bits (bit j of nu is
// variable j).
inline std::vector<Gf> eq_table(std::span<const Gf> z) {
    std::vector<Gf> t(size_t{1} << z.size());
    t[0] = gf_one();
    size_t len = 1;
    for (size_t jj = z.size(); jj-- > 0;) {
        // t[0, len) is over bits jj + 1, ...; extend with bit jj as the new bit 0.
        const Gf one_z = z[jj] + gf_one();
        for (size_t m = len; m-- > 0;) {
            t[2 * m + 1] = gf_mul(t[m], z[jj]);
            t[2 * m] = gf_mul(t[m], one_z);
        }
        len *= 2;
    }
    return t;
}

// A committed element of GF(2^128) from its 128 committed bits, bit(j) for the coefficient of x^j.
template <typename QS, typename BitAt>
faest::quicksilver_gfsecpar<QS, 1> qs_element(const QS* qs, BitAt&& bit) {
    using E = faest::quicksilver_gfsecpar<QS, 1>;
    static const std::array<Gf, 128> monomials = [] {
        std::array<Gf, 128> m;
        for (size_t j = 0; j < 128; ++j) {
            m[j] = gf_monomial(j);
        }
        return m;
    }();
    (void)qs;
    E acc(bit(0));
    for (size_t j = 1; j < 128; ++j) {
        acc = acc + monomials[j] * E(bit(j));
    }
    return acc;
}

template <size_t D_> struct TreeSumcheck {
    static constexpr size_t D = D_;
    static_assert(D >= 1);
    static constexpr size_t NUM_LEAVES = size_t{2} << D; // both trees
    static constexpr size_t NUM_ROUNDS = D * (D + 1) / 2;
    static constexpr size_t NUM_ELEMS = 2 * NUM_ROUNDS + 2 * (D - 1);
    static constexpr size_t MESSAGE_BYTES = 2 * GF_BYTES;
    static constexpr size_t ELEM_BYTES = NUM_ELEMS * GF_BYTES;
    // tau_0, then one per message.
    static constexpr size_t NUM_CHALLENGES = 1 + NUM_ROUNDS + (D - 1);
    static_assert(NUM_CHALLENGES == 1 + NUM_ELEMS / 2);
    // One degree-2 constraint per layer.
    static constexpr size_t NUM_CONSTRAINTS = D;

    // The prover, given all leaf values and tau_0. Writes the NUM_ELEMS elements to `out`, and
    // calls next(i) after message i >= 1 (elements 2 (i - 1) and 2 (i - 1) + 1) is written, which
    // returns challenge i. The leaves needn't satisfy the claim (the proof is then invalid).
    template <typename Next>
    static void prove(std::vector<Gf> leaves, Gf tau0, std::span<uint8_t, ELEM_BYTES> out,
                      Next&& next) {
        assert(leaves.size() == NUM_LEAVES);
        // layers[d] has 2^(d+1) nodes.
        std::vector<std::vector<Gf>> layers(D + 1);
        layers[D] = std::move(leaves);
        for (size_t d = D; d-- > 0;) {
            const auto& up = layers[d + 1];
            auto& v = layers[d];
            v.resize(up.size() / 2);
            for (size_t n = 0; n < v.size(); ++n) {
                v[n] = gf_mul(up[2 * n], up[2 * n + 1]);
            }
        }

        size_t elem = 0;
        size_t msg = 1;
        const auto send = [&](Gf x) { gf_store(x, out.data() + GF_BYTES * elem++); };

        std::vector<Gf> z = {tau0};
        std::vector<Gf> a_arr, b_arr, rho;
        std::vector<std::vector<Gf>> suffix(D);
#ifndef NDEBUG
        Gf claim = gf_mul(tau0 + gf_one(), layers[0][0]) + gf_mul(tau0, layers[0][1]);
#endif
        for (size_t d = 0; d < D; ++d) {
            const auto& up = layers[d + 1];
            const size_t nodes = up.size() / 2;
            a_arr.resize(nodes);
            b_arr.resize(nodes);
            for (size_t n = 0; n < nodes; ++n) {
                a_arr[n] = up[2 * n];
                b_arr[n] = up[2 * n + 1];
            }
            // suffix[j][m] = eq(z_{j+1..d}, m) for j = 0, ..., d.
            suffix[d] = {gf_one()};
            for (size_t j = d; j >= 1; --j) {
                const auto& s = suffix[j];
                auto& t = suffix[j - 1];
                t.resize(2 * s.size());
                const Gf one_z = z[j] + gf_one();
                for (size_t m = 0; m < s.size(); ++m) {
                    t[2 * m] = gf_mul(s[m], one_z);
                    t[2 * m + 1] = gf_mul(s[m], z[j]);
                }
            }
            rho.clear();
            for (size_t j = 0; j <= d; ++j) {
                const auto& e = suffix[j];
                const size_t half = e.size();
                Gf p0 = gf_zero(), p1 = gf_zero(), p2 = gf_zero();
                for (size_t m = 0; m < half; ++m) {
                    const Gf a0 = a_arr[2 * m], a1 = a_arr[2 * m + 1];
                    const Gf b0 = b_arr[2 * m], b1 = b_arr[2 * m + 1];
                    p0 += gf_mul(e[m], gf_mul(a0, b0));
                    p1 += gf_mul(e[m], gf_mul(a1, b1));
                    p2 += gf_mul(e[m], gf_mul(a0 + a1, b0 + b1));
                }
                const Gf t1 = p1 + p0 + p2;
                const Gf t2 = p2;
#ifndef NDEBUG
                assert(gf_eq(claim, p0 + gf_mul(z[j], t1 + t2)));
#endif
                send(t1);
                send(t2);
                const Gf r = next(msg++);
#ifndef NDEBUG
                claim = p0 + gf_mul(r, t1) + gf_mul(gf_sqr(r), t2);
#endif
                for (size_t m = 0; m < half; ++m) {
                    const Gf a0 = a_arr[2 * m], a1 = a_arr[2 * m + 1];
                    const Gf b0 = b_arr[2 * m], b1 = b_arr[2 * m + 1];
                    a_arr[m] = a0 + gf_mul(r, a0 + a1);
                    b_arr[m] = b0 + gf_mul(r, b0 + b1);
                }
                a_arr.resize(half);
                b_arr.resize(half);
                rho.push_back(r);
            }
            const Gf a = a_arr[0], b = b_arr[0];
#ifndef NDEBUG
            assert(gf_eq(claim, gf_mul(a, b)));
#endif
            if (d + 1 < D) {
                send(a);
                send(b);
                const Gf tau = next(msg++);
                z.assign(1, tau);
                z.insert(z.end(), rho.begin(), rho.end());
#ifndef NDEBUG
                claim = a + gf_mul(tau, a + b);
#endif
            }
        }
        assert(elem == NUM_ELEMS && msg == NUM_CHALLENGES);
    }

    // The verifier's constraints (and the prover's, on committed values). `challenges` are all
    // challenges, elem(e) is committed element e of the prover's part (a
    // quicksilver_gfsecpar<QS, 1>), and leaf_forms(eq) returns the committed values (A, B) of
    // sum_nu eq[nu] L_{2 nu} and sum_nu eq[nu] L_{2 nu + 1}, given eq[nu] for the 2^D nodes nu of
    // layer D - 1.
    template <typename QS, typename ElemAt, typename LeafForms>
    static void constraints(QS* qs, std::span<const Gf, NUM_CHALLENGES> challenges,
                            const std::array<Gf, 2>& roots, ElemAt&& elem, LeafForms&& leaf_forms) {
        using E = faest::quicksilver_gfsecpar<QS, 1>;
        using E2 = faest::quicksilver_gfsecpar<QS, 2>;
        size_t ch = 0;
        size_t e = 0;
        const Gf tau0 = challenges[ch++];
        E claim(gf_mul(tau0 + gf_one(), roots[0]) + gf_mul(tau0, roots[1]), qs);
        std::vector<Gf> z = {tau0};
        std::vector<Gf> rho;
        for (size_t d = 0; d < D; ++d) {
            rho.clear();
            for (size_t j = 0; j <= d; ++j) {
                const E t1 = elem(e++);
                const E t2 = elem(e++);
                const Gf r = challenges[ch++];
                claim = claim + (z[j] + r) * t1 + (z[j] + gf_sqr(r)) * t2;
                rho.push_back(r);
            }
            if (d + 1 < D) {
                const E a = elem(e++);
                const E b = elem(e++);
                qs->add_constraint(E2(claim) + a * b);
                const Gf tau = challenges[ch++];
                claim = a + tau * (a + b);
                z.assign(1, tau);
                z.insert(z.end(), rho.begin(), rho.end());
            } else {
                const auto eq = eq_table(rho);
                const auto [a, b] = leaf_forms(std::span<const Gf>(eq));
                qs->add_constraint(E2(claim) + a * b);
            }
        }
        assert(ch == NUM_CHALLENGES && e == NUM_ELEMS);
    }

    // leaf_forms for leaves L_l = 1 + coef[l] x_{leaf_bit[l]}, or 1 if leaf_bit[l] == NO_BIT, over
    // `num_bits` committed bits bit(i) (quicksilver_gf2<QS, 1>).
    static constexpr uint32_t NO_BIT = ~uint32_t{0};
    template <typename QS, typename BitAt>
    static std::pair<faest::quicksilver_gfsecpar<QS, 1>, faest::quicksilver_gfsecpar<QS, 1>>
    affine_leaf_forms(const QS* qs, std::span<const Gf> eq, std::span<const Gf> coef,
                      std::span<const uint32_t> leaf_bit, size_t num_bits, BitAt&& bit) {
        using E = faest::quicksilver_gfsecpar<QS, 1>;
        assert(eq.size() == NUM_LEAVES / 2 && coef.size() == NUM_LEAVES &&
               leaf_bit.size() == NUM_LEAVES);
        // The weight of each bit in A and in B. (sum_nu eq[nu] = 1 covers the constant terms.)
        std::vector<Gf> wa(num_bits, gf_zero()), wb(num_bits, gf_zero());
        for (size_t l = 0; l < NUM_LEAVES; ++l) {
            if (leaf_bit[l] != NO_BIT) {
                auto& w = (l & 1) != 0 ? wb : wa;
                w[leaf_bit[l]] += gf_mul(eq[l >> 1], coef[l]);
            }
        }
        E a(gf_one(), qs);
        E b(gf_one(), qs);
        const Gf zero = gf_zero();
        for (size_t i = 0; i < num_bits; ++i) {
            if (!gf_eq(wa[i], zero) || !gf_eq(wb[i], zero)) {
                const E x(bit(i));
                if (!gf_eq(wa[i], zero)) {
                    a = a + wa[i] * x;
                }
                if (!gf_eq(wb[i], zero)) {
                    b = b + wb[i] * x;
                }
            }
        }
        return {a, b};
    }
};

} // namespace vole_mole::sumcheck::detail

#endif
