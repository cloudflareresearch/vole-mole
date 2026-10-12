// Linear equations modulo a prime q < 2^24 on committed bits, in binary VOLEitH.
//
// Setting. The witness holds NUM_VALUES small non-negative integers as bits: value j is
// x_j = sum_i 2^t_{j,i} x_{j,i} for bits x_{j,i}, i < value_bits(j), and shifts
// t_{j,i} = bit_shift(j, i). After the bits are committed, the verifier picks NUM_CHECKS weight
// vectors W_k in Z_q^NUM_VALUES and constants A_k (in our use, random combinations of a system of
// linear equations, e.g., see mlkem_pop/binary.hpp), and the prover shows
//
//   sum_j W_{k,j} (x_j - offset(j)) = A_k (mod q)  for each check k.
//
// The circuit. Write B_k = A_k + sum_j W_{k,j} offset(j) (mod q), and give each bit (j, i) the
// weight w = W_{k,j} 2^t_{j,i} mod q, as a signed integer d = sum +-2^e (e < DIGIT_EXPS) with d = w
// (mod q) and the fewest digits +-2^e (see "Recoding" below). So S_k = sum d x over all bits is
// congruent to the left-hand side, with |S_k - B_k| < (Q_OFFSET - 1) q, and the prover commits
// (after the weights are known) to Q'_k = (S_k - B_k) / q + Q_OFFSET in [0, 2 Q_OFFSET), with
// Q_BITS bits. With -2^e x = 2^e (1 - x) - 2^e, the equation S_k - q (Q'_k - Q_OFFSET) = B_k
// becomes
//
//   sum_{+2^e digits} 2^e x + sum_{-2^e digits} 2^e (1 - x) + q sum_i 2^i (1 - Q'_{k,i})
//     = B_k + C_k + q (Q_OFFSET - 1) =: K_k,
//
// where C_k is the sum of the 2^e of the negative digits: a sum of committed bits and their
// complements with weights 2^e, which we check with column compression (see columns.hpp). Every
// assignment of the bits makes the left-hand side less than 2^COLUMNS, so checking it modulo
// 2^COLUMNS checks it over the integers, and that implies the equation modulo q. Conversely, Q'_k
// can take any value, so the circuit shows exactly the equation modulo q.
//
// Recoding. Only d mod q matters, so we may pick any d = w (mod q), and the cost of a bit is the
// number of digits of d. The non-adjacent form (NAF) of w or w - q has 7.6 digits on average.
// Allowing exponents e up to DIGIT_EXPS - 1 gives sparser representations: the fewest digits for
// each element of Z_q, found by breadth-first search over Z_q (recode_table(), an 8 MB table
// computed once, in about 1 s for q = 8380417 and DIGIT_EXPS = 96), average
//
//   DIGIT_EXPS      24    32    40    48    64    80    96    128   192
//   q = 8380417     7.50  6.62  5.97  5.47  4.88  4.47  4.14  3.83  3.46
//
//   DIGIT_EXPS      12    16    20    24    32    48    64
//   q = 3329        3.80  3.36  2.97  2.75  2.57  2.26  2.10
//
// The gains taper off because the powers 2^e mod q repeat with period ord_q(2), and for
// q = 2^23 - 2^13 + 1 they are structured for e >= 23. Wider representations only make the sums,
// the quotients and the number of columns larger, which costs little. We need DIGIT_EXPS <= 100 for
// the sums to fit in 128 bits.
//
// The counters commit to about 3/11 = 0.27 bits per input for COUNTER_LOG = 3 (0.50 for
// COUNTER_LOG = 2). The number of committed bits depends on the weights, so we reserve
// CARRY_BUDGET of them for all checks, and the prover retries with other weights if they need more
// (see the tests for the budgets).

#ifndef VOLE_MOLE_MODQ_MODQ_HPP
#define VOLE_MOLE_MODQ_MODQ_HPP

#include "modq/columns.hpp"

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::modq::detail {

// Spec provides:
//   Q: the prime modulus, less than 2^24;
//   NUM_VALUES, value_bits(j), bit_shift(j, i), offset(j) (in [0, q)): the values;
//   NUM_CHECKS: the number of checks;
//   COUNTER_LOG: counters have up to 2^(COUNTER_LOG + 1) - 1 inputs, i.e., constraints of degree
//     up to 2^COUNTER_LOG;
//   CARRY_BUDGET: the number of committed bits reserved for the counters of all checks, a
//     multiple of 8.
template <typename Spec> struct ModQ {
    using Elem = uint32_t; // in [0, Q)
    static constexpr uint32_t Q = Spec::Q;
    static_assert(Q > 2 && Q < (uint32_t{1} << 24));
    static constexpr size_t LOG_Q = std::bit_width(Q); // 2^(LOG_Q - 1) < q < 2^LOG_Q
    static constexpr Elem add(Elem a, Elem b) { return a + b >= Q ? a + b - Q : a + b; }
    static constexpr Elem mul(Elem a, Elem b) { return static_cast<Elem>(uint64_t{a} * b % Q); }
    static constexpr size_t NUM_VALUES = Spec::NUM_VALUES;
    static constexpr size_t NUM_CHECKS = Spec::NUM_CHECKS;
    static constexpr size_t COUNTER_LOG = Spec::COUNTER_LOG;
    static constexpr size_t CARRY_BUDGET = Spec::CARRY_BUDGET;
    static_assert(CARRY_BUDGET % 8 == 0);
    using Cols = Columns<COUNTER_LOG>;

    static constexpr size_t NUM_BITS = [] {
        size_t s = 0;
        for (size_t j = 0; j < NUM_VALUES; ++j) {
            s += Spec::value_bits(j);
        }
        return s;
    }();
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

    // Digits are +-2^e for e < DIGIT_EXPS.
    static constexpr size_t DIGIT_EXPS = Spec::DIGIT_EXPS;
    // The NAF of an element of [0, q) has digits 2^e with e <= LOG_Q, and at most
    // MAX_DIGITS = floor((LOG_Q + 2) / 2) <= 12 of them. So a minimal representation has at most
    // MAX_DIGITS digits, the sum of their 2^e is less than 12 2^(DIGIT_EXPS - 1) <
    // 2^(DIGIT_EXPS + 3), and that of all bits less than 2^(P + DIGIT_EXPS + 3) for P below.
    static_assert(LOG_Q + 1 <= DIGIT_EXPS && DIGIT_EXPS <= 100);
    static constexpr size_t MAX_DIGITS = (LOG_Q + 2) / 2;
    static constexpr size_t P = std::bit_width(NUM_BITS); // NUM_BITS < 2^P
    // |S_k - B_k| / q + 1 < 2^(P + DIGIT_EXPS + 3) / 2^(LOG_Q - 1) + 1
    //   <= 2^(P + DIGIT_EXPS + 4 - LOG_Q).
    static constexpr size_t Q_OFFSET_LOG = P + DIGIT_EXPS + 4 - LOG_Q;
    static constexpr size_t Q_BITS = Q_OFFSET_LOG + 1;
    static_assert(Q_BITS < 127);
    // The bits of q.
    static constexpr size_t MAX_EXP = LOG_Q - 1;
    // The left-hand side is less than 2^(P + DIGIT_EXPS + 3) + q 2^Q_BITS < 2^(P + DIGIT_EXPS + 6).
    static constexpr size_t COLUMNS = P + DIGIT_EXPS + 6;
    static_assert(COLUMNS < 128);
    using U128 = unsigned __int128;
    using I128 = __int128;
    static constexpr I128 Q_OFFSET = I128{1} << Q_OFFSET_LOG;

    // The committed bits of the prover's answer, in this order: Q'_{k,i} at k Q_BITS + i, padded to
    // a whole byte, then the counters' bits.
    static constexpr size_t Q_REGION_BITS = (NUM_CHECKS * Q_BITS + 7) / 8 * 8;
    static constexpr size_t ANSWER_BITS = Q_REGION_BITS + CARRY_BUDGET;
    static constexpr size_t ANSWER_BYTES = ANSWER_BITS / 8;

    // One constraint per counter bit (including the unused ones) and per column.
    static constexpr size_t NUM_BINARY_CONSTRAINTS = CARRY_BUDGET + NUM_CHECKS * COLUMNS;

    // A digit: 2^e or -2^e.
    struct Digit {
        uint8_t e : 7;
        uint8_t neg : 1;
    };

    // The weights of all checks, in the form the circuit needs.
    struct Weights {
        std::vector<Digit> digits;
        std::vector<uint32_t> start;      // the digits of bit b of check k start at k NUM_BITS + b
        std::vector<I128> d;              // the signed weight d of each bit, k NUM_BITS + b
        std::array<Elem, NUM_CHECKS> b;   // B_k
        std::array<U128, NUM_CHECKS> rhs; // K_k

        std::span<const Digit> of(size_t k, size_t bit) const {
            const size_t i = k * NUM_BITS + bit;
            return std::span(digits).subspan(start[i], start[i + 1] - start[i]);
        }
    };

    // For each v in Z_q, the last digit s 2^e of a representation of v with the fewest digits, as
    // 2 e + [s = -1] (and 255 for v = 0): the rest of the representation is that of v - s 2^e.
    // Computed once, by breadth-first search from 0 over the steps +-2^e mod q.
    static const std::vector<uint8_t>& recode_table() {
        static const std::vector<uint8_t> table = [] {
            std::vector<uint8_t> t(Q, 0xff);
            std::vector<uint32_t> queue;
            queue.reserve(Q);
            std::array<uint32_t, DIGIT_EXPS> pow{};
            pow[0] = 1;
            for (size_t e = 1; e < DIGIT_EXPS; ++e) {
                pow[e] = static_cast<uint32_t>(uint64_t{pow[e - 1]} * 2 % Q);
            }
            std::vector<bool> seen(Q, false);
            seen[0] = true;
            queue.push_back(0);
            for (size_t h = 0; h < queue.size(); ++h) {
                const uint32_t r = queue[h];
                for (size_t e = 0; e < DIGIT_EXPS; ++e) {
                    const uint32_t a = r + pow[e] >= Q ? r + pow[e] - Q : r + pow[e];
                    const uint32_t b = r >= pow[e] ? r - pow[e] : r + Q - pow[e];
                    if (!seen[a]) {
                        seen[a] = true;
                        t[a] = static_cast<uint8_t>(2 * e);
                        queue.push_back(a);
                    }
                    if (!seen[b]) {
                        seen[b] = true;
                        t[b] = static_cast<uint8_t>(2 * e + 1);
                        queue.push_back(b);
                    }
                }
            }
            return t;
        }();
        return table;
    }

    // A representation of v with the fewest digits; returns its value as an integer.
    static I128 recode(uint32_t v, std::vector<Digit>& out) {
        const auto& t = recode_table();
        I128 d = 0;
        for (size_t n = 0; v != 0; ++n) {
            if (n == MAX_DIGITS) {
                throw std::logic_error("modq: representation too long");
            }
            const uint8_t code = t[v];
            const auto e = static_cast<uint8_t>(code >> 1);
            const bool neg = (code & 1) != 0;
            out.push_back({e, static_cast<uint8_t>(neg)});
            const I128 p = I128{1} << e;
            d += neg ? -p : p;
            const auto pm = static_cast<uint32_t>(static_cast<U128>(p) % Q);
            v = neg ? (v + pm >= Q ? v + pm - Q : v + pm) : (v >= pm ? v - pm : v + Q - pm);
        }
        return d;
    }

    // The weights for W_{k,j} = value_weights[k NUM_VALUES + j] and A_k = constants[k].
    static Weights make_weights(std::span<const Elem> value_weights,
                                const std::array<Elem, NUM_CHECKS>& constants = {}) {
        Weights w;
        w.digits.reserve(NUM_CHECKS * NUM_BITS * 8);
        w.start.reserve(NUM_CHECKS * NUM_BITS + 1);
        w.d.reserve(NUM_CHECKS * NUM_BITS);
        w.start.push_back(0);
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            Elem b = constants[k];
            U128 c = 0;
            for (size_t j = 0; j < NUM_VALUES; ++j) {
                const Elem wj = value_weights[k * NUM_VALUES + j];
                b = add(b, mul(wj, Spec::offset(j)));
                for (size_t i = 0; i < Spec::value_bits(j); ++i) {
                    const Elem v =
                        mul(wj, static_cast<Elem>((uint64_t{1} << Spec::bit_shift(j, i)) % Q));
                    const size_t first = w.digits.size();
                    w.d.push_back(recode(v, w.digits));
                    for (size_t x = first; x < w.digits.size(); ++x) {
                        if (w.digits[x].neg) {
                            c += U128{1} << w.digits[x].e;
                        }
                    }
                    w.start.push_back(static_cast<uint32_t>(w.digits.size()));
                }
            }
            w.b[k] = b;
            w.rhs[k] = U128{b} + c + U128{Q} * static_cast<U128>(Q_OFFSET - 1);
        }
        return w;
    }

    // The circuit for all checks, generic over the representation of wires (see columns.hpp).
    // value_bit(j, i) is the wire of bit i of value j, q_bit(k, i) that of bit i of Q'_k, and
    // output(k, col, wire) receives the last wire of each column (which must be bit col of K_k).
    template <typename Ops, typename ValueBit, typename QBit, typename Output>
    static void circuit(Ops& ops, const Weights& w, ValueBit&& value_bit, QBit&& q_bit,
                        Output&& output) {
        using Wire = typename Ops::Wire;
        // The wires of the values don't depend on the check.
        std::vector<Wire> x;
        x.reserve(NUM_BITS);
        for (size_t j = 0; j < NUM_VALUES; ++j) {
            for (size_t i = 0; i < Spec::value_bits(j); ++i) {
                x.push_back(value_bit(j, i));
            }
        }
        std::vector<Wire> nx;
        nx.reserve(NUM_BITS);
        for (const Wire& a : x) {
            nx.push_back(ops.flip(a));
        }
        std::vector<std::vector<Wire>> cols(COLUMNS);
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            for (auto& col : cols) {
                col.clear();
            }
            for (size_t b = 0; b < NUM_BITS; ++b) {
                for (const Digit& dg : w.of(k, b)) {
                    cols[dg.e].push_back(dg.neg ? nx[b] : x[b]);
                }
            }
            for (size_t i = 0; i < Q_BITS; ++i) {
                const Wire nq = ops.flip(q_bit(k, i));
                for (size_t t = 0; t <= MAX_EXP; ++t) {
                    if ((Q >> t) & 1) {
                        cols[i + t].push_back(nq);
                    }
                }
            }
            Cols::reduce(ops, cols, [&](size_t col, const Wire& a) { output(k, col, a); });
        }
    }

    static size_t count_carries(const Weights& w) {
        typename Cols::CountOps ops;
        using W = typename Cols::CountOps::Wire;
        circuit(
            ops, w, [](size_t, size_t) { return W{}; }, [](size_t, size_t) { return W{}; },
            [](size_t, size_t, W) {});
        return ops.carries;
    }

    // S_k for the values given by value_bit(j, i) (a bool).
    template <typename ValueBit>
    static I128 weighted_sum(const Weights& w, size_t k, ValueBit&& value_bit) {
        I128 s = 0;
        size_t b = 0;
        for (size_t j = 0; j < NUM_VALUES; ++j) {
            for (size_t i = 0; i < Spec::value_bits(j); ++i, ++b) {
                if (value_bit(j, i)) {
                    s += w.d[k * NUM_BITS + b];
                }
            }
        }
        return s;
    }

    // Whether all equations hold for the values given by value_bit(j, i).
    template <typename ValueBit> static bool holds(const Weights& w, ValueBit&& value_bit) {
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            const I128 r = weighted_sum(w, k, value_bit) % I128{Q};
            if (static_cast<Elem>(r < 0 ? r + Q : r) != w.b[k]) {
                return false;
            }
        }
        return true;
    }

    // Computes the prover's answer (Q'_k and the counters' bits) in the clear, for the values
    // given by value_bit(j, i) (a bool), even if the equations don't hold (then the proof will be
    // invalid). Returns false if the budget is exceeded.
    template <typename ValueBit>
    static bool answer(const Weights& w, ValueBit&& value_bit,
                       std::span<uint8_t, ANSWER_BYTES> out) {
        std::ranges::fill(out, 0);
        const auto set = [&](size_t i, bool v) {
            out[i / 8] = static_cast<uint8_t>(out[i / 8] | (unsigned{v} << (i % 8)));
        };
        for (size_t k = 0; k < NUM_CHECKS; ++k) {
            const I128 diff = weighted_sum(w, k, value_bit) - I128{w.b[k]};
            // floor(diff / q)
            I128 quot = diff / I128{Q};
            if (diff % I128{Q} < 0) {
                --quot;
            }
            const I128 qq = quot + Q_OFFSET;
            for (size_t i = 0; i < Q_BITS; ++i) {
                set(k * Q_BITS + i, ((qq >> i) & 1) != 0);
            }
        }
        typename Cols::PlainOps ops{out, Q_REGION_BITS, CARRY_BUDGET};
        circuit(
            ops, w, [&](size_t j, size_t i) { return static_cast<uint8_t>(value_bit(j, i)); },
            [&](size_t k, size_t i) {
                return static_cast<uint8_t>((out[(k * Q_BITS + i) / 8] >> ((k * Q_BITS + i) % 8)) &
                                            1);
            },
            [](size_t, size_t, uint8_t) {});
        return ops.finish();
    }

    // The constraints, with the answer at witness bit `answer_offset`. Requires
    // count_carries(w) <= CARRY_BUDGET. Adds NUM_BINARY_CONSTRAINTS constraints.
    template <typename QS, typename ValueBit>
    static void qs_constraints(QS* qs, const Weights& w, size_t answer_offset,
                               ValueBit&& value_bit) {
        typename Cols::template QsOps<QS> ops{qs, answer_offset + Q_REGION_BITS, CARRY_BUDGET};
        circuit(
            ops, w, value_bit,
            [&](size_t k, size_t i) { return qs->get_witness_bit(answer_offset + k * Q_BITS + i); },
            [&](size_t k, size_t col, const auto& a) {
                ops.assert_equal(a, ((w.rhs[k] >> col) & 1) != 0);
            });
        ops.finish();
    }
};

} // namespace vole_mole::modq::detail

#endif
