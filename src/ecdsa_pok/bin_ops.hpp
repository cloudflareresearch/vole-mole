// Binary circuits for the ECDSA proof of knowledge, generic over how wires are represented.
//
// A circuit is written once against an `Ops` object and run in three modes:
//
//   - CountOps counts the committed witness bits and the constraints;
//   - PlainOps computes the committed witness bits in the clear (for the prover), and counts the
//     constraints that don't hold;
//   - QsOps<QS> evaluates the constraints on QuickSilver-committed bits (prover or verifier).
//
// A Wire is a committed bit or a GF(2)-affine combination of committed bits. The circuit commits a
// new bit with commit(value), where `value` is the bit's value in PlainOps and is ignored in the
// other modes; committed bits are allocated sequentially, so the three modes agree on the layout.
//
// Integer sums of wires use column compression (Columns, adapted from PR #46's modq/columns.hpp):
// wires are arranged in columns by weight, and the columns are reduced, from the lowest, with
// counters. A counter takes t <= 2^(LOG + 1) - 1 wires of a column and outputs the bits of their
// sum. Bit 0 is their sum in GF(2), which is linear, and stays in the column; bits i = 1, ..., LOG
// are committed and move to column + i. By Lucas' theorem, bit i of the popcount of x_1, ..., x_t
// is the elementary symmetric polynomial e_{2^i}(x_1, ..., x_t) modulo 2, of degree 2^i: that's the
// constraint for the committed bit. Carries out of the last column are dropped, so the result is
// the sum modulo 2^(#columns).

#ifndef VOLE_MOLE_ECDSA_POK_BIN_OPS_HPP
#define VOLE_MOLE_ECDSA_POK_BIN_OPS_HPP

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

namespace vole_mole::ecdsa_pok::detail {

// Counters of size LOG take up to 2^(LOG + 1) - 1 wires and commit up to LOG carries, with
// constraints of degree up to 2^LOG. Smaller counters commit more carries but have lower degree,
// which makes QuickSilver cheaper; binary.hpp picks the sizes (`Shape`).
constexpr size_t MAX_COUNTER_LOG = 4;

struct CountOps {
    struct Wire {};
    size_t next = 0;        // committed bits
    size_t constraints = 0; // constraints

    Wire zero() const { return {}; }
    Wire one() const { return {}; }
    Wire flip(Wire) const { return {}; }
    Wire add(Wire, Wire) const { return {}; }
    Wire commit(bool) {
        ++next;
        return {};
    }
    void assert_eq(Wire, bool) { ++constraints; }
    void counter(std::span<const Wire>, std::span<Wire> out) {
        for (auto& o : out) {
            o = commit(false);
        }
        constraints += out.size();
    }
};

struct PlainOps {
    using Wire = uint8_t; // 0 or 1
    std::span<uint8_t> witness;
    size_t next = 0;
    size_t failed = 0; // constraints that don't hold
    size_t constraints = 0;

    Wire zero() const { return 0; }
    Wire one() const { return 1; }
    Wire flip(Wire a) const { return a ^ 1; }
    Wire add(Wire a, Wire b) const { return a ^ b; }
    Wire commit(bool v) {
        const size_t b = next++;
        if (b / 8 >= witness.size()) {
            throw std::logic_error("ecdsa_pok: witness overflow");
        }
        witness[b / 8] =
            static_cast<uint8_t>((witness[b / 8] & ~(1u << (b % 8))) | (unsigned{v} << (b % 8)));
        return v ? 1 : 0;
    }
    Wire bit(size_t i) const { return (witness[i / 8] >> (i % 8)) & 1; }
    void assert_eq(Wire a, bool v) {
        ++constraints;
        failed += (a != static_cast<Wire>(v));
    }
    void counter(std::span<const Wire> in, std::span<Wire> out) {
        const size_t sum = static_cast<size_t>(std::ranges::count(in, Wire{1}));
        for (size_t i = 0; i < out.size(); ++i) {
            out[i] = commit(((sum >> (i + 1)) & 1) != 0);
        }
        constraints += out.size();
    }
};

template <typename QS> struct QsOps {
    using Wire = vole_mole::detail::qs_bit<QS, 1>;
    QS* qs;
    size_t next = 0;
    size_t constraints = 0;

    Wire zero() const { return Wire(faest::poly1(0), qs); }
    Wire one() const { return Wire(faest::poly1(1), qs); }
    Wire flip(const Wire& a) const { return a + faest::poly1(1); }
    Wire add(const Wire& a, const Wire& b) const { return a + b; }
    Wire commit(bool) { return qs->get_witness_bit(next++); }
    Wire bit(size_t i) const { return qs->get_witness_bit(i); }
    void assert_eq(const Wire& a, bool v) {
        ++constraints;
        qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(a + faest::poly1(v)));
    }
    void counter(std::span<const Wire> in, std::span<Wire> out) {
        for (auto& o : out) {
            o = commit(false);
        }
        constraints += out.size();
        dispatch<1>(in, out);
    }

  private:
    // Counters whose constraints exceed the QuickSilver degree aren't instantiated (the circuit
    // doesn't use them).
    template <size_t O> void dispatch(std::span<const Wire> in, std::span<const Wire> out) {
        if constexpr (O <= MAX_COUNTER_LOG && (size_t{1} << O) <= QS::max_degree) {
            if (out.size() == O) {
                check_counter<O>(in, out);
            } else {
                dispatch<O + 1>(in, out);
            }
        } else {
            throw std::logic_error("ecdsa_pok: counter exceeds the QuickSilver degree");
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
        qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(Bit<K>(out[i]) + std::get<K - 1>(e)));
    }
    template <typename Tuple, size_t... I>
    void constrain_bits(const Tuple& e, std::span<const Wire> out, std::index_sequence<I...>) {
        (constrain_bit<I>(e, out), ...);
    }
    // Bit i of the popcount of `in`, for i = 1, ..., O, equals e_{2^i}(in) modulo 2.
    template <size_t O> void check_counter(std::span<const Wire> in, std::span<const Wire> out) {
        constexpr size_t KMAX = size_t{1} << O;
        auto e = make_esym(zero(), std::make_index_sequence<KMAX>{});
        for (const auto& x : in) {
            esym_update<KMAX>(e, x, std::make_index_sequence<KMAX>{});
        }
        constrain_bits(e, out, std::make_index_sequence<O>{});
    }
};

// Reduce `cols` with counters of size LOG and call output(col, wire) with the final wire of each
// column.
template <size_t LOG, typename Ops, typename Output>
void reduce_columns(Ops& ops, std::vector<std::vector<typename Ops::Wire>>& cols, Output&& output) {
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
            const size_t t = std::min(c.size(), (size_t{1} << (LOG + 1)) - 1);
            const size_t outs =
                std::min(static_cast<size_t>(std::bit_width(t)) - 1, num_cols - 1 - col);
            const std::span<const Wire> in(c.data() + c.size() - t, t);
            std::array<Wire, LOG> carries;
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

// A 32-bit word: either a public constant or 32 wires (least significant first).
template <typename Ops> struct Word {
    using Wire = typename Ops::Wire;
    bool is_const = false;
    uint32_t c = 0;
    std::array<Wire, 32> w{};

    static Word constant(uint32_t v) {
        Word out;
        out.is_const = true;
        out.c = v;
        return out;
    }
};

// A signed integer sum of wires and constants modulo 2^W, to be checked against a target.
template <typename Ops> class ColSum {
  public:
    using Wire = typename Ops::Wire;

    ColSum(Ops& ops, size_t width) : ops_(&ops), cols_(width), konst_(width, 0) {}

    size_t width() const { return cols_.size(); }

    // += w 2^col
    void add(const Wire& w, size_t col) {
        if (col < cols_.size()) {
            cols_[col].push_back(w);
        }
    }
    // -= w 2^col: -w = (1 - w) - 1.
    void sub(const Wire& w, size_t col) {
        if (col < cols_.size()) {
            cols_[col].push_back(ops_->flip(w));
            add_const_bit(col, true);
        }
    }
    // += v 2^shift (sub: -=).
    void add_const(uint64_t v, size_t shift, bool sub = false) {
        for (size_t i = 0; i < 64; ++i) {
            if ((v >> i) & 1) {
                add_const_bit(shift + i, sub);
            }
        }
    }
    void add_word(const Word<Ops>& x, size_t shift) {
        if (x.is_const) {
            add_const(x.c, shift);
        } else {
            for (size_t i = 0; i < 32; ++i) {
                add(x.w[i], shift + i);
            }
        }
    }
    void sub_word(const Word<Ops>& x, size_t shift) {
        if (x.is_const) {
            add_const(x.c, shift, true);
        } else {
            for (size_t i = 0; i < 32; ++i) {
                sub(x.w[i], shift + i);
            }
        }
    }

    // Reduce with counters of size LOG and call out(col, wire) with the bits of the sum.
    template <size_t LOG, typename Output> void reduce(Output&& out) {
        for (size_t i = 0; i < konst_.size(); ++i) {
            if (konst_[i]) {
                cols_[i].push_back(ops_->one());
            }
        }
        reduce_columns<LOG>(*ops_, cols_, out);
    }
    // Reduce and constrain the sum to be 0 modulo 2^W.
    template <size_t LOG> void assert_zero() {
        reduce<LOG>([&](size_t, const Wire& w) { ops_->assert_eq(w, false); });
    }

  private:
    // konst += (sub ? -1 : 1) 2^col, modulo 2^W.
    void add_const_bit(size_t col, bool sub) {
        for (size_t i = col; i < konst_.size(); ++i) {
            const uint8_t old = konst_[i];
            konst_[i] ^= 1;
            // Adding: stop unless the bit was 1. Subtracting: stop unless the bit was 0.
            if (sub ? old == 1 : old == 0) {
                break;
            }
        }
    }

    Ops* ops_;
    std::vector<std::vector<Wire>> cols_;
    std::vector<uint8_t> konst_;
};

} // namespace vole_mole::ecdsa_pok::detail

#endif
