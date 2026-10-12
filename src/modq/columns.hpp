// Integer sums of committed bits in binary VOLEitH, by column compression with counters.
//
// The input is a set of wires (committed bits, or GF(2)-linear combinations of them) arranged in
// columns by weight: the sum is S = sum_col 2^col sum_{w in column col} w, over the integers. The
// columns are reduced, from the lowest, to one wire each, which is then the bit of S (modulo
// 2^COLUMNS) for that column.
//
// A counter takes t <= MAX_INPUTS wires of a column and outputs the bits of their sum. Bit 0 is
// their sum in GF(2), which is linear, and stays in the column; bits i = 1, ..., COUNTER_LOG are
// committed and move to column + i. By Lucas' theorem, bit i of the popcount of x_1, ..., x_t is
// the elementary symmetric polynomial e_{2^i}(x_1, ..., x_t) modulo 2, of degree 2^i: that's the
// constraint for the committed bit. (A counter with 2^(COUNTER_LOG + 1) - 1 inputs eliminates
// 2^(COUNTER_LOG + 1) - 2 - COUNTER_LOG wires for COUNTER_LOG committed bits.) Carries out of the
// last column are dropped.
//
// The reduction is generic over the representation of wires (Ops::Wire):
//
//   - CountOps counts the committed bits;
//   - PlainOps computes the committed bits in the clear;
//   - QsOps evaluates the constraints on QuickSilver-committed bits.
//
// The committed bits are witness bits [first, first + budget); unused ones must be zero.

#ifndef VOLE_MOLE_MODQ_COLUMNS_HPP
#define VOLE_MOLE_MODQ_COLUMNS_HPP

#include "qs_bit.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <vector>

namespace vole_mole::modq::detail {

template <size_t COUNTER_LOG_> struct Columns {
    static constexpr size_t COUNTER_LOG = COUNTER_LOG_;
    static_assert(1 <= COUNTER_LOG && COUNTER_LOG <= 4);
    static constexpr size_t MAX_INPUTS = (size_t{1} << (COUNTER_LOG + 1)) - 1;

    // Reduce `cols` and call output(col, wire) with the final wire of each column.
    template <typename Ops, typename Output>
    static void reduce(Ops& ops, std::vector<std::vector<typename Ops::Wire>>& cols,
                       Output&& output) {
        using Wire = typename Ops::Wire;
        const size_t num_cols = cols.size();
        for (size_t col = 0; col < num_cols; ++col) {
            auto& c = cols[col];
            if (c.empty()) {
                c.push_back(ops.zero());
            }
            while (c.size() > 1) {
                if (col + 1 == num_cols) {
                    // Carries out of the last column are dropped, so just add.
                    const Wire a = c.back();
                    c.pop_back();
                    c.back() = ops.add(c.back(), a);
                    continue;
                }
                const size_t t = std::min(c.size(), MAX_INPUTS);
                const size_t outs =
                    std::min(static_cast<size_t>(std::bit_width(t)) - 1, num_cols - 1 - col);
                const std::span<const Wire> in(c.data() + c.size() - t, t);
                std::array<Wire, COUNTER_LOG> carries;
                ops.counter(in, std::span(carries).first(outs));
                Wire parity = in[0];
                for (size_t i = 1; i < t; ++i) {
                    parity = ops.add(parity, in[i]);
                }
                c.resize(c.size() - t);
                c.push_back(parity);
                for (size_t i = 0; i < outs; ++i) {
                    cols[col + 1 + i].push_back(carries[i]);
                }
            }
            output(col, c[0]);
        }
    }

    // Counts committed bits. A Wire carries no data.
    struct CountOps {
        struct Wire {};
        size_t carries = 0;
        Wire zero() { return {}; }
        Wire flip(Wire) { return {}; }
        Wire add(Wire, Wire) { return {}; }
        void counter(std::span<const Wire>, std::span<Wire> out) { carries += out.size(); }
    };

    // Computes the committed bits in the clear, writing them to bits [first, first + budget) of
    // `witness`. ok() is false if the budget is exceeded.
    struct PlainOps {
        using Wire = uint8_t; // 0 or 1 (not bool, to avoid std::vector<bool>)
        std::span<uint8_t> witness;
        size_t first;
        size_t budget;
        size_t next = 0;

        Wire zero() { return 0; }
        Wire flip(Wire a) { return a ^ 1; }
        Wire add(Wire a, Wire b) { return a ^ b; }
        void counter(std::span<const Wire> in, std::span<Wire> out) {
            const size_t sum = static_cast<size_t>(std::ranges::count(in, Wire{1}));
            for (size_t i = 0; i < out.size(); ++i) {
                out[i] = static_cast<Wire>((sum >> (i + 1)) & 1);
                if (next < budget) {
                    const size_t b = first + next;
                    witness[b / 8] = static_cast<uint8_t>((witness[b / 8] & ~(1u << (b % 8))) |
                                                          (unsigned{out[i]} << (b % 8)));
                }
                ++next;
            }
        }
        // Zero the unused bits. Returns false if the budget was exceeded.
        bool finish() {
            for (size_t i = next; i < budget; ++i) {
                const size_t b = first + i;
                witness[b / 8] = static_cast<uint8_t>(witness[b / 8] & ~(1u << (b % 8)));
            }
            return next <= budget;
        }
    };

    // Evaluates the constraints on committed bits: one per committed bit, including the unused
    // ones (which must be zero) after finish(), i.e., `budget` constraints in total.
    template <typename QS> struct QsOps {
        using Wire = vole_mole::detail::qs_bit<QS, 1>;
        QS* qs;
        size_t first;
        size_t budget;
        size_t next = 0;

        Wire zero() { return Wire(faest::poly1(0), qs); }
        Wire flip(const Wire& a) { return a + faest::poly1(1); }
        Wire add(const Wire& a, const Wire& b) { return a + b; }

        void counter(std::span<const Wire> in, std::span<Wire> out) {
            if (next + out.size() > budget) {
                throw std::logic_error("columns: carry budget exceeded");
            }
            for (auto& o : out) {
                o = qs->get_witness_bit(first + next++);
            }
            dispatch<1>(in, out);
        }
        // Constrain a = v (one constraint).
        void assert_equal(const Wire& a, bool v) {
            qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(a + faest::poly1(v)));
        }
        void finish() {
            for (; next < budget; ++next) {
                qs->add_constraint(
                    vole_mole::detail::qs_to_gfsecpar(qs->get_witness_bit(first + next)));
            }
        }

      private:
        template <size_t O> void dispatch(std::span<const Wire> in, std::span<const Wire> out) {
            if constexpr (O <= COUNTER_LOG) {
                if (out.size() == O) {
                    check_counter<O>(in, out);
                } else {
                    dispatch<O + 1>(in, out);
                }
            }
        }

        template <size_t k> using Bit = vole_mole::detail::qs_bit<QS, k>;

        // E_k = e_k(inputs so far) for k = 1, ..., KMAX.
        template <size_t... I> static auto make_esym(const Wire& zero, std::index_sequence<I...>) {
            return std::tuple<Bit<I + 1>...>(Bit<I + 1>(zero)...);
        }
        template <size_t k, typename Tuple> static void esym_step(Tuple& e, const Wire& x) {
            if constexpr (k == 1) {
                std::get<0>(e) = std::get<0>(e) + x;
            } else {
                std::get<k - 1>(e) =
                    std::get<k - 1>(e) + vole_mole::detail::qs_mul(std::get<k - 2>(e), x);
            }
        }
        template <size_t KMAX, typename Tuple, size_t... I>
        static void esym_update(Tuple& e, const Wire& x, std::index_sequence<I...>) {
            (esym_step<KMAX - I>(e, x), ...); // descending k, so E_{k-1} is the previous value
        }
        template <size_t i, typename Tuple>
        void constrain_bit(const Tuple& e, std::span<const Wire> out) {
            constexpr size_t K = size_t{1} << (i + 1);
            qs->add_constraint(
                vole_mole::detail::qs_to_gfsecpar(Bit<K>(out[i]) + std::get<K - 1>(e)));
        }
        template <typename Tuple, size_t... I>
        void constrain_bits(const Tuple& e, std::span<const Wire> out, std::index_sequence<I...>) {
            (constrain_bit<I>(e, out), ...);
        }

        // Bit i of the popcount of `in`, for i = 1, ..., O, equals e_{2^i}(in) modulo 2.
        template <size_t O>
        void check_counter(std::span<const Wire> in, std::span<const Wire> out) {
            constexpr size_t KMAX = size_t{1} << O;
            auto e = make_esym(zero(), std::make_index_sequence<KMAX>{});
            for (const auto& x : in) {
                esym_update<KMAX>(e, x, std::make_index_sequence<KMAX>{});
            }
            constrain_bits(e, out, std::make_index_sequence<O>{});
        }
    };
};

} // namespace vole_mole::modq::detail

#endif
