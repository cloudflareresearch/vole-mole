// Six linear equations modulo a prime q < 2^24 on committed bits, checked as two product trees in
// the exponent of GF(2^128)^* and proven by sumcheck (see docs/sumcheck-modq.md). A replacement
// for modq::detail::ModQ (modq/modq.hpp), with the same Spec and the same semantics:
//
//   sum_j W_{k,j} (x_j - offset(j)) = A_k (mod q)  for each check k < 6,
//
// for the values x_j = sum_i 2^t_{j,i} x_{j,i} of committed bits x_{j,i}, i < value_bits(j),
// t_{j,i} = bit_shift(j, i). (Spec's NUM_CHECKS must be 6; DIGIT_EXPS, COUNTER_LOG and
// CARRY_BUDGET are ignored.)
//
// The answer, committed after the weights are known, is the 6 quotients (KAPPA bits each, padded
// to Q_BYTES), then the elements of the tree sumcheck, in the order of its messages. Message 0 is
// the quotients; each later message is MESSAGE_BYTES bytes.

#ifndef VOLE_MOLE_SUMCHECK_EXP_MODQ_HPP
#define VOLE_MOLE_SUMCHECK_EXP_MODQ_HPP

#include "sumcheck/gf128.hpp"
#include "sumcheck/tree_sumcheck.hpp"

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

namespace vole_mole::sumcheck::detail {

template <typename Spec> struct ExpModQ {
    using Elem = uint32_t; // in [0, Q)
    static constexpr uint32_t Q = Spec::Q;
    static_assert(Q > 2 && Q < (uint32_t{1} << 24));
    static constexpr size_t NUM_VALUES = Spec::NUM_VALUES;
    static constexpr size_t NUM_CHECKS = Spec::NUM_CHECKS;
    static_assert(NUM_CHECKS == 6, "two trees of three lanes");
    static constexpr size_t LANES = 3;
    static constexpr size_t TREES = 2;

    static constexpr size_t NUM_BITS = [] {
        size_t s = 0;
        for (size_t j = 0; j < NUM_VALUES; ++j) {
            s += Spec::value_bits(j);
        }
        return s;
    }();
    static_assert(NUM_BITS >= 2);
    static constexpr size_t MAX_SHIFT = [] {
        size_t m = 0;
        for (size_t j = 0; j < NUM_VALUES; ++j) {
            for (size_t i = 0; i < Spec::value_bits(j); ++i) {
                m = Spec::bit_shift(j, i) > m ? Spec::bit_shift(j, i) : m;
            }
        }
        return m;
    }();
    static_assert(MAX_SHIFT < 32);

    // Each bit weight is in [0, q), so S_k = sum w x is in [0, NUM_BITS (q - 1)], and an honest
    // quotient (S_k - B_k) / q is in [0, NUM_BITS) (KAPPA bits). A lane holds any S_k and any
    // B_k + q k for a KAPPA-bit k, both less than 2^LAMBDA; three lanes fit with room to spare in
    // 2^128 - 1, the order of the group (see "Exactness" in the design note).
    static constexpr size_t KAPPA = std::bit_width(NUM_BITS - 1);
    static constexpr size_t LAMBDA = KAPPA + std::bit_width(Q);
    static_assert(uint64_t{Q} * NUM_BITS <= (uint64_t{1} << LAMBDA));
    static_assert(LANES * LAMBDA < 127);

    // Leaves per tree: the data bits, then the quotient bits of the tree's three checks.
    static constexpr size_t TREE_LEAVES = NUM_BITS + LANES * KAPPA;
    static constexpr size_t D = std::bit_width(TREE_LEAVES - 1);
    using Tree = TreeSumcheck<D>;
    static constexpr size_t Q_BITS = NUM_CHECKS * KAPPA;
    static constexpr size_t Q_BYTES = (Q_BITS + 7) / 8;
    static constexpr size_t MESSAGE_BYTES = Tree::MESSAGE_BYTES;
    static constexpr size_t ANSWER_BYTES = Q_BYTES + Tree::ELEM_BYTES;
    static constexpr size_t ANSWER_BITS = 8 * ANSWER_BYTES;
    static constexpr size_t NUM_CHALLENGES = Tree::NUM_CHALLENGES;
    static constexpr size_t NUM_CONSTRAINTS = Tree::NUM_CONSTRAINTS;
    // The committed bits the leaves use: the data bits, then the quotient bits (bit s of check k
    // at NUM_BITS + KAPPA k + s, as in the answer).
    static constexpr size_t NUM_LEAF_BITS = NUM_BITS + Q_BITS;

    using Challenges = std::array<Gf, NUM_CHALLENGES>;

    // The public encoding of the checks.
    struct Encoded {
        std::vector<Gf> coef;            // per leaf: h - 1 for L = 1 + x (h - 1)
        std::array<Gf, TREES> roots;     // g^(packed B)
        std::array<Elem, NUM_CHECKS> b;  // B_k
        std::vector<Elem> value_weights; // W_{k,j} at k NUM_VALUES + j
    };

    static Elem add(Elem a, Elem b) { return a + b >= Q ? a + b - Q : a + b; }
    static Elem mul(Elem a, Elem b) { return static_cast<Elem>(uint64_t{a} * b % Q); }

    // The (j, i) of each data bit, in order.
    static const std::vector<std::pair<uint32_t, uint8_t>>& bit_values() {
        static const auto v = [] {
            std::vector<std::pair<uint32_t, uint8_t>> out;
            out.reserve(NUM_BITS);
            for (size_t j = 0; j < NUM_VALUES; ++j) {
                for (size_t i = 0; i < Spec::value_bits(j); ++i) {
                    out.emplace_back(static_cast<uint32_t>(j), static_cast<uint8_t>(i));
                }
            }
            return out;
        }();
        return v;
    }

    // The committed bit of each leaf (Tree::NO_BIT for padding).
    static const std::vector<uint32_t>& leaf_bits() {
        static const auto v = [] {
            std::vector<uint32_t> out(Tree::NUM_LEAVES, Tree::NO_BIT);
            for (size_t t = 0; t < TREES; ++t) {
                const size_t base = t << D;
                for (size_t b = 0; b < NUM_BITS; ++b) {
                    out[base + b] = static_cast<uint32_t>(b);
                }
                for (size_t s = 0; s < LANES * KAPPA; ++s) {
                    out[base + NUM_BITS + s] =
                        static_cast<uint32_t>(NUM_BITS + LANES * KAPPA * t + s);
                }
            }
            return out;
        }();
        return v;
    }

    // The packed exponent sum_l 2^(LAMBDA l) v_l.
    static U128 pack(const std::array<Elem, LANES>& v) {
        U128 e = 0;
        for (size_t l = 0; l < LANES; ++l) {
            e += U128{v[l]} << (LAMBDA * l);
        }
        return e;
    }

    struct Tables {
        Gf g;
        // fixed[l][y][v] = g^(v 2^(8 y + LAMBDA l)), for the first bit of each value.
        std::array<std::array<std::array<Gf, 256>, 3>, LANES> fixed;
        // corr[code] = g^(-q sum_l code_l 2^(LAMBDA l)), after doubling the lanes.
        std::array<Gf, 1 << LANES> corr;
        // quot[l][s] = g^(-q 2^(LAMBDA l + s)) - 1.
        std::array<std::array<Gf, KAPPA>, LANES> quot;
    };
    static const Tables& tables() {
        static const Tables t = [] {
            Tables t;
            t.g = generator();
            for (size_t l = 0; l < LANES; ++l) {
                for (size_t y = 0; y < 3; ++y) {
                    const Gf base = gf_pow(t.g, U128{1} << (8 * y + LAMBDA * l));
                    Gf p = gf_one();
                    for (size_t v = 0; v < 256; ++v) {
                        t.fixed[l][y][v] = p;
                        p = gf_mul(p, base);
                    }
                }
                for (size_t s = 0; s < KAPPA; ++s) {
                    t.quot[l][s] =
                        gf_signed_pow(t.g, -static_cast<__int128>(U128{Q} << (LAMBDA * l + s))) +
                        gf_one();
                }
            }
            for (size_t code = 0; code < t.corr.size(); ++code) {
                std::array<Elem, LANES> eps{};
                for (size_t l = 0; l < LANES; ++l) {
                    eps[l] = (code >> l) & 1;
                }
                t.corr[code] = gf_signed_pow(t.g, -static_cast<__int128>(U128{Q} * pack(eps)));
            }
            return t;
        }();
        return t;
    }

    static Gf fixed_power(const Tables& t, const std::array<Elem, LANES>& v) {
        Gf p = gf_one();
        for (size_t l = 0; l < LANES; ++l) {
            for (size_t y = 0; y < 3; ++y) {
                const auto byte = static_cast<uint8_t>(v[l] >> (8 * y));
                if (byte != 0) {
                    p = gf_mul(p, t.fixed[l][y][byte]);
                }
            }
        }
        return p;
    }

    // The encoding for W_{k,j} = value_weights[k NUM_VALUES + j] and A_k = constants[k].
    static Encoded encode(std::span<const Elem> value_weights,
                          const std::array<Elem, NUM_CHECKS>& constants = {}) {
        const Tables& tab = tables();
        Encoded enc;
        enc.value_weights.assign(value_weights.begin(), value_weights.end());
        enc.coef.assign(Tree::NUM_LEAVES, gf_zero());
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            Elem b = constants[k];
            for (size_t j = 0; j < NUM_VALUES; ++j) {
                b = add(b, mul(value_weights[k * NUM_VALUES + j], Spec::offset(j)));
            }
            enc.b[k] = b;
        }
        for (size_t t = 0; t < TREES; ++t) {
            Gf* coef = enc.coef.data() + (t << D);
            size_t bit = 0;
            for (size_t j = 0; j < NUM_VALUES; ++j) {
                std::array<Elem, LANES> w0;
                for (size_t l = 0; l < LANES; ++l) {
                    w0[l] = value_weights[(LANES * t + l) * NUM_VALUES + j];
                }
                const Gf p0 = fixed_power(tab, w0);
                std::array<Elem, LANES> w = w0;
                Gf p = p0;
                size_t s = 0;
                for (size_t i = 0; i < Spec::value_bits(j); ++i, ++bit) {
                    const size_t target = Spec::bit_shift(j, i);
                    if (target < s) {
                        w = w0, p = p0, s = 0;
                    }
                    // g^(2 w mod q) = (g^w)^2 g^(-q eps), with eps = [2 w >= q] per lane.
                    for (; s < target; ++s) {
                        size_t code = 0;
                        for (size_t l = 0; l < LANES; ++l) {
                            Elem d = 2 * w[l];
                            if (d >= Q) {
                                d -= Q;
                                code |= size_t{1} << l;
                            }
                            w[l] = d;
                        }
                        p = gf_sqr(p);
                        if (code != 0) {
                            p = gf_mul(p, tab.corr[code]);
                        }
                    }
                    coef[bit] = p + gf_one();
                }
            }
            for (size_t l = 0; l < LANES; ++l) {
                for (size_t s = 0; s < KAPPA; ++s) {
                    coef[NUM_BITS + KAPPA * l + s] = tab.quot[l][s];
                }
            }
            enc.roots[t] =
                gf_pow(tab.g, pack({enc.b[LANES * t], enc.b[LANES * t + 1], enc.b[LANES * t + 2]}));
        }
        return enc;
    }

    // The honest quotients for the data bits x (one bool per bit, in order): floor((S_k - B_k) /
    // q), clamped to [0, 2^KAPPA). (If the checks don't hold, the proof will be invalid.)
    static std::array<uint32_t, NUM_CHECKS> quotients(const Encoded& enc,
                                                      std::span<const uint8_t> x) {
        std::array<uint32_t, NUM_CHECKS> out{};
        const auto& bv = bit_values();
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            int64_t s = 0;
            for (size_t b = 0; b < NUM_BITS; ++b) {
                if (x[b] != 0) {
                    const auto [j, i] = bv[b];
                    s += mul(enc.value_weights[k * NUM_VALUES + j],
                             static_cast<Elem>((uint64_t{1} << Spec::bit_shift(j, i)) % Q));
                }
            }
            const int64_t diff = s - int64_t{enc.b[k]};
            int64_t quot = diff >= 0 ? diff / Q : -((-diff + Q - 1) / Q);
            quot = quot < 0 ? 0 : quot;
            quot = quot >= (int64_t{1} << KAPPA) ? (int64_t{1} << KAPPA) - 1 : quot;
            out[k] = static_cast<uint32_t>(quot);
        }
        return out;
    }

    // The prover: writes the answer for the data bits given by value_bit(j, i) (a bool), with the
    // given quotients (quotients() for an honest prover). next(off, len) is called after each
    // message, answer[off, off + len), is written, and returns the next challenge (see
    // voleith_fs.hpp); the challenges are also written to `challenges`.
    template <typename ValueBit, typename Next>
    static void answer(const Encoded& enc, ValueBit&& value_bit,
                       std::span<uint8_t, ANSWER_BYTES> out, Next&& next, Challenges& challenges,
                       const std::array<uint32_t, NUM_CHECKS>* quotients_override = nullptr) {
        std::vector<uint8_t> x(NUM_BITS);
        {
            const auto& bv = bit_values();
            for (size_t b = 0; b < NUM_BITS; ++b) {
                x[b] = value_bit(bv[b].first, bv[b].second) ? 1 : 0;
            }
        }
        const auto quot = quotients_override ? *quotients_override : quotients(enc, x);
        std::ranges::fill(out, 0);
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            for (size_t s = 0; s < KAPPA; ++s) {
                const size_t i = KAPPA * k + s;
                out[i / 8] = static_cast<uint8_t>(out[i / 8] | (((quot[k] >> s) & 1) << (i % 8)));
            }
        }
        size_t ch = 0;
        challenges[ch++] = next(size_t{0}, Q_BYTES);

        std::vector<Gf> leaves(Tree::NUM_LEAVES, gf_one());
        const auto& lb = leaf_bits();
        for (size_t l = 0; l < Tree::NUM_LEAVES; ++l) {
            if (lb[l] == Tree::NO_BIT) {
                continue;
            }
            bool v;
            if (lb[l] < NUM_BITS) {
                v = x[lb[l]] != 0;
            } else {
                const size_t i = lb[l] - NUM_BITS;
                v = ((out[i / 8] >> (i % 8)) & 1) != 0;
            }
            if (v) {
                leaves[l] = enc.coef[l] + gf_one();
            }
        }
        Tree::prove(std::move(leaves), challenges[0],
                    out.template subspan<Q_BYTES, Tree::ELEM_BYTES>(), [&](size_t msg) {
                        const Gf c = next(Q_BYTES + MESSAGE_BYTES * (msg - 1), MESSAGE_BYTES);
                        challenges[ch++] = c;
                        return c;
                    });
    }

    // The challenges, from the masked answer (see voleith_fs.hpp) and a Chain on the seed.
    static Challenges challenges(Chain chain, std::span<const uint8_t, ANSWER_BYTES> masked) {
        Challenges c;
        c[0] = chain.next(masked.template first<Q_BYTES>());
        for (size_t i = 1; i < NUM_CHALLENGES; ++i) {
            c[i] = chain.next(masked.subspan(Q_BYTES + MESSAGE_BYTES * (i - 1), MESSAGE_BYTES));
        }
        return c;
    }

    // The constraints, with the answer at witness bit `answer_offset` and the data bits given by
    // value_bit(j, i) (a quicksilver_gf2<QS, 1>). Adds NUM_CONSTRAINTS constraints.
    template <typename QS, typename ValueBit>
    static void qs_constraints(QS* qs, const Encoded& enc, const Challenges& challenges,
                               size_t answer_offset, ValueBit&& value_bit) {
        const auto& bv = bit_values();
        const size_t elem_offset = answer_offset + 8 * Q_BYTES;
        Tree::constraints(
            qs, std::span<const Gf, NUM_CHALLENGES>(challenges), enc.roots,
            [&](size_t e) {
                return qs_element(
                    qs, [&](size_t j) { return qs->get_witness_bit(elem_offset + 128 * e + j); });
            },
            [&](std::span<const Gf> eq) {
                return Tree::affine_leaf_forms(
                    qs, eq, enc.coef, leaf_bits(), NUM_LEAF_BITS, [&](size_t b) {
                        if (b < NUM_BITS) {
                            return value_bit(bv[b].first, bv[b].second);
                        }
                        return qs->get_witness_bit(answer_offset + (b - NUM_BITS));
                    });
            });
    }
};

} // namespace vole_mole::sumcheck::detail

#endif
