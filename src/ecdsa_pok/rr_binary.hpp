// The binary part of the ECDSA proof with a hidden key and a revealed R (see rr_relation.hpp), in
// FAEST's VOLEitH (src/voleith.hpp). It commits to the public key Q as bits, so that a larger
// statement can use them (e.g., an mdoc's MSO, which contains Q), and links them to the proof over
// F_p, where Q is computed.
//
//   Instance: the statement digest, the link challenge, and the link value Z_p
//   Witness:  x_Q and y_Q as 256 bits each, the mask rho_p, and carries
//   Constraints:
//     - x_Q < p and y_Q < p;
//     - Z_p = c_x x_Q + c_y y_Q + rho_p over the integers, for the sparse weights c_x, c_y of the
//       link challenge (its xn_pos and xp_pos; link.hpp).
//
// As in binary.hpp, the carries of the link sum are committed after the link challenge, with a
// budget. Soundness of the link is as in relation.hpp: if (x_Q, y_Q) differs modulo p from Q over
// F_p, then c_x (x_Q - x_Q') + c_y (y_Q - y_Q') = rho_p' - rho_p (mod p), fixed before the
// challenge, holds with probability less than 2^-131.

#ifndef VOLE_MOLE_ECDSA_POK_RR_BINARY_HPP
#define VOLE_MOLE_ECDSA_POK_RR_BINARY_HPP

#include "dst.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/binary.hpp"
#include "ecdsa_pok/link.hpp"
#include "qs_bit.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::rr {

// c_x x_Q + c_y y_Q < 2^513; the mask is 128 bits wider.
constexpr size_t RHO_BITS = 513 + 128;
constexpr size_t Z_COLS = RHO_BITS + 1;
static_assert(8 * Z_BYTES >= Z_COLS);

constexpr size_t PREFIX_BITS = 2 * (256 + X_LT_P_BITS) + RHO_BITS;
constexpr size_t PREFIX_BYTES = (PREFIX_BITS + 7) / 8; // the last bits are unused

// The budget of carries of the link sum, for counters of size LOG. Over 3000 random challenges
// (test_ecdsa_pok_rr.cpp), their number has mean ~3304 and standard deviation ~23 (max 3399) for
// LOG = 4, and mean ~8454 and standard deviation ~15 (max 8509) for LOG = 2. So the budget is about
// 10 standard deviations above the mean; the prover retries with a fresh seed if it's exceeded.
template <size_t LOG> constexpr size_t LINK_BUDGET = LOG == 4 ? 8 * 442 : 8 * 1076;

template <Shape SH> constexpr size_t witness_bits() {
    return 8 * PREFIX_BYTES + LINK_BUDGET<SH.link_log>;
}

template <typename Ops> struct PrefixWires {
    std::vector<typename Ops::Wire> x, y, rho; // little endian
};

struct PrefixValues {
    std::array<uint8_t, 32> x, y;     // x_Q, y_Q, little endian
    std::array<uint8_t, Z_BYTES> rho; // little endian
};

// 256 committed bits of v, with v < p.
template <size_t LOG, typename Ops>
std::vector<typename Ops::Wire> canonical_coordinate(Ops& ops, const std::array<uint8_t, 32>* v) {
    using Wire = typename Ops::Wire;
    std::vector<Wire> out;
    out.reserve(256);
    for (size_t i = 0; i < 256; ++i) {
        out.push_back(ops.commit(v && get_bit(*v, i)));
    }
    ColSum<Ops> sum(ops, 257);
    for (size_t i = 0; i < 256; ++i) {
        sum.add(out[i], i);
        if (get_bit(TWO256_MINUS_P, i)) {
            sum.add(ops.one(), i);
        }
    }
    sum.template reduce<LOG>([&](size_t col, const Wire& w) {
        if (col == 256) {
            ops.assert_eq(w, false);
        }
    });
    return out;
}

template <size_t LOG, typename Ops>
PrefixWires<Ops> prefix_circuit(Ops& ops, const PrefixValues* vals) {
    PrefixWires<Ops> out;
    out.x = canonical_coordinate<LOG>(ops, vals ? &vals->x : nullptr);
    out.y = canonical_coordinate<LOG>(ops, vals ? &vals->y : nullptr);
    for (size_t i = 0; i < RHO_BITS; ++i) {
        out.rho.push_back(ops.commit(vals && get_bit(vals->rho, i)));
    }
    return out;
}

// The link sum Z_p. If `record`, then writes it to zp (PlainOps); otherwise, constrains it.
template <size_t LOG, typename Ops>
void link_sums(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
               std::span<uint8_t, Z_BYTES> zp, bool record) {
    using Wire = typename Ops::Wire;
    if (record) {
        std::ranges::fill(zp, 0);
    }
    ColSum<Ops> s(ops, Z_COLS);
    for (const uint16_t j : chal.xn_pos) {
        for (size_t i = 0; i < 256; ++i) {
            s.add(in.x[i], j + i);
        }
    }
    for (const uint16_t j : chal.xp_pos) {
        for (size_t i = 0; i < 256; ++i) {
            s.add(in.y[i], j + i);
        }
    }
    for (size_t i = 0; i < RHO_BITS; ++i) {
        s.add(in.rho[i], i);
    }
    s.template reduce<LOG>([&ops, zp, record](size_t col, const Wire& w) {
        if constexpr (std::is_same_v<Ops, PlainOps>) {
            if (record) {
                set_bit(zp, col, w != 0);
            }
        } else {
            (void)record;
        }
        ops.assert_eq(w, get_bit(zp, col));
    });
}

template <size_t LOG> size_t link_carries(const LinkChallenge& chal) {
    CountOps ops;
    PrefixWires<CountOps> in;
    in.x.resize(256);
    in.y.resize(256);
    in.rho.resize(RHO_BITS);
    std::array<uint8_t, Z_BYTES> zp{};
    link_sums<LOG>(ops, in, chal, zp, false);
    return ops.next;
}

template <size_t LOG, typename Ops>
void link_circuit(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
                  std::span<uint8_t, Z_BYTES> zp, bool record) {
    const size_t first = ops.next;
    link_sums<LOG>(ops, in, chal, zp, record);
    if (ops.next > first + LINK_BUDGET<LOG>) {
        throw std::runtime_error("ecdsa_pok: link carry budget exceeded");
    }
    while (ops.next < first + LINK_BUDGET<LOG>) {
        ops.assert_eq(ops.commit(false), false);
    }
}

template <Shape SH> size_t count_circuit_constraints() {
    CountOps ops;
    auto wires = prefix_circuit<SH.sha_log>(ops, nullptr);
    ops.next = 8 * PREFIX_BYTES;
    const LinkChallenge chal = derive_link_challenge(Digest{});
    std::array<uint8_t, Z_BYTES> zp{};
    link_circuit<SH.link_log>(ops, wires, chal, zp, false);
    return ops.constraints;
}
template <Shape SH> constexpr size_t CIRCUIT_CONSTRAINTS() {
    // x_Q, y_Q < p: one per carry and the top column, each. The link sum: one per column, and one
    // per carry in the budget.
    return 2 * (X_LT_P_BITS + 1) + Z_COLS + LINK_BUDGET<SH.link_log>;
}

constexpr faest::owf owf_for(BinPrg prg) {
    return static_cast<faest::owf>(((0xa0u + std::to_underlying(prg)) << 8) |
                                   faest::owf_flag_witness_bits_check);
}
constexpr bool is_rr_owf(faest::owf o) {
    const auto v = std::to_underlying(o);
    const auto hi = v >> 8;
    return (v & 0xff) == faest::owf_flag_witness_bits_check && hi >= 0xa0 && hi <= 0xa2;
}
constexpr BinPrg prg_of_owf(faest::owf o) {
    return static_cast<BinPrg>((std::to_underlying(o) >> 8) - 0xa0);
}

} // namespace vole_mole::ecdsa_pok::detail::rr

template <faest::owf O>
    requires(vole_mole::ecdsa_pok::detail::rr::is_rr_owf(O))
struct faest::OWF_CONSTANTS<faest::secpar::s128, O>
    : vole_mole::detail::RelationConstants<
          vole_mole::ecdsa_pok::detail::rr::witness_bits<vole_mole::ecdsa_pok::detail::SHAPE<
              vole_mole::ecdsa_pok::detail::rr::prg_of_owf(O)>>(),
          vole_mole::ecdsa_pok::detail::BIN_QS_DEGREE<vole_mole::ecdsa_pok::detail::rr::prg_of_owf(
              O)>,
          typename vole_mole::ecdsa_pok::detail::bin_prg<
              vole_mole::ecdsa_pok::detail::rr::prg_of_owf(O)>::type> {};

namespace vole_mole::ecdsa_pok::detail::rr {

template <bool SMALL, BinPrg PRG>
using BinParams =
    faest::parameter_set<faest::secpar::s128, SMALL ? 11 : 17, owf_for(PRG), faest::prg::aes_ctr,
                         faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, SMALL ? 7 : 8,
                         {faest::bavc::one_tree, SMALL ? 103u : 105u}, true, true>;

template <bool SMALL, BinPrg PRG> struct BinRelation {
    using params = BinParams<SMALL, PRG>;
    static constexpr Shape SH = SHAPE<PRG>;
    static constexpr bool DERIVED = PRG != BinPrg::none;

    struct instance {
        const Digest* mu;
        const LinkChallenge* chal;
        std::array<uint8_t, Z_BYTES> zp;
    };

    static constexpr size_t RELATION_WITNESS_BITS = witness_bits<SH>();
    static constexpr size_t WITNESS_PREFIX_BYTES = PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::ECDSA_RR_BINARY_DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST =
        vole_mole::detail::ECDSA_RR_BINARY_PRG_DST;

    static constexpr size_t NUM_CONSTRAINTS =
        (DERIVED ? 0 : RELATION_WITNESS_BITS) + CIRCUIT_CONSTRAINTS<SH>();

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(*x.mu);
        hasher.update(x.chal->digest);
        hasher.update(x.zp);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        static_assert(QS::max_degree == BIN_QS_DEGREE<PRG>);
        if constexpr (!DERIVED) {
            for (size_t i = 0; i < RELATION_WITNESS_BITS; ++i) {
                vole_mole::detail::qs_add_bit_constraint(qs, qs->get_witness_bit(i));
            }
        }
        QsOps<QS> ops{qs};
        const auto wires = prefix_circuit<SH.sha_log>(ops, nullptr);
        ops.next = 8 * WITNESS_PREFIX_BYTES;
        auto zp = x.zp;
        link_circuit<SH.link_log>(ops, wires, *x.chal, zp, false);
    }
};

} // namespace vole_mole::ecdsa_pok::detail::rr

#endif
