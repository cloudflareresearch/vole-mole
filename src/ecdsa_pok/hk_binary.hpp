// The binary part of the hidden-key ECDSA proof (see hk_relation.hpp), in FAEST's VOLEitH
// (src/voleith.hpp). It's binary.hpp without the message: e is public, so the binary proof only
// makes X = x(R) canonical and links it to F_n and F_p.
//
//   Instance: the statement digest, the link challenge, and the link values Z_n, Z_p
//   Witness:  X as 256 bits, the masks rho_n and rho_p, and carries
//   Constraints:
//     - X < p;
//     - Z_n = c_2 X + rho_n and Z_p = c_3 X + rho_p over the integers, for the sparse weights c_i
//       of the link challenge (link.hpp; its e_pos are unused).
//
// As in binary.hpp, the carries of the link sums are committed after the link challenge, with a
// budget.

#ifndef VOLE_MOLE_ECDSA_POK_HK_BINARY_HPP
#define VOLE_MOLE_ECDSA_POK_HK_BINARY_HPP

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

namespace vole_mole::ecdsa_pok::detail::hk {

// c_i < 2^256 and X < 2^256, so c_i X < 2^512; the masks are 128 bits wider.
constexpr size_t RHO_BITS = 512 + 128;
constexpr size_t Z_COLS = RHO_BITS + 1;
static_assert(8 * Z_BYTES >= Z_COLS);

constexpr size_t PREFIX_BITS = 256 + X_LT_P_BITS + 2 * RHO_BITS;
static_assert(PREFIX_BITS % 8 == 0);
constexpr size_t PREFIX_BYTES = PREFIX_BITS / 8;

// The budget of carries of the link sums, for counters of size LOG. Over 3000 random challenges
// (test_ecdsa_pok_hk.cpp), their number has mean ~4145 and standard deviation ~28 (max 4231) for
// LOG = 4, and mean ~8963 and standard deviation ~42 (max 9111) for LOG = 2. So the budget is about
// 10 standard deviations above the mean; the prover retries with a fresh seed if it's exceeded.
template <size_t LOG> constexpr size_t LINK_BUDGET = LOG == 4 ? 8 * 554 : 8 * 1175;

template <Shape SH> constexpr size_t witness_bits() {
    return 8 * PREFIX_BYTES + LINK_BUDGET<SH.link_log>;
}

template <typename Ops> struct PrefixWires {
    std::vector<typename Ops::Wire> x, rho_n, rho_p; // little endian
};

struct PrefixValues {
    std::array<uint8_t, 32> x;                 // X, little endian
    std::array<uint8_t, Z_BYTES> rho_n, rho_p; // little endian
};

template <size_t LOG, typename Ops>
PrefixWires<Ops> prefix_circuit(Ops& ops, const PrefixValues* vals) {
    using Wire = typename Ops::Wire;
    PrefixWires<Ops> out;
    // X < p, i.e., X + (2^256 - p) < 2^256 (as in binary.hpp).
    out.x.reserve(256);
    for (size_t i = 0; i < 256; ++i) {
        out.x.push_back(ops.commit(vals && get_bit(vals->x, i)));
    }
    {
        ColSum<Ops> sum(ops, 257);
        for (size_t i = 0; i < 256; ++i) {
            sum.add(out.x[i], i);
            if (get_bit(TWO256_MINUS_P, i)) {
                sum.add(ops.one(), i);
            }
        }
        sum.template reduce<LOG>([&](size_t col, const Wire& w) {
            if (col == 256) {
                ops.assert_eq(w, false);
            }
        });
    }
    for (size_t i = 0; i < RHO_BITS; ++i) {
        out.rho_n.push_back(ops.commit(vals && get_bit(vals->rho_n, i)));
    }
    for (size_t i = 0; i < RHO_BITS; ++i) {
        out.rho_p.push_back(ops.commit(vals && get_bit(vals->rho_p, i)));
    }
    return out;
}

// The link sums Z_n and Z_p. If `record`, then writes the sums to zn and zp (PlainOps);
// otherwise, constrains them to be zn and zp.
template <size_t LOG, typename Ops>
void link_sums(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
               std::span<uint8_t, Z_BYTES> zn, std::span<uint8_t, Z_BYTES> zp, bool record) {
    using Wire = typename Ops::Wire;
    if (record) {
        std::ranges::fill(zn, 0);
        std::ranges::fill(zp, 0);
    }
    auto sum = [&](std::span<const uint16_t, LINK_TERMS> pos, const std::vector<Wire>& rho,
                   std::span<uint8_t, Z_BYTES> z) {
        ColSum<Ops> s(ops, Z_COLS);
        for (const uint16_t j : pos) {
            for (size_t i = 0; i < 256; ++i) {
                s.add(in.x[i], j + i);
            }
        }
        for (size_t i = 0; i < RHO_BITS; ++i) {
            s.add(rho[i], i);
        }
        s.template reduce<LOG>([&ops, z, record](size_t col, const Wire& w) {
            if constexpr (std::is_same_v<Ops, PlainOps>) {
                if (record) {
                    set_bit(z, col, w != 0);
                }
            } else {
                (void)record;
            }
            ops.assert_eq(w, get_bit(z, col));
        });
    };
    sum(chal.xn_pos, in.rho_n, zn);
    sum(chal.xp_pos, in.rho_p, zp);
}

template <size_t LOG> size_t link_carries(const LinkChallenge& chal) {
    CountOps ops;
    PrefixWires<CountOps> in;
    in.x.resize(256);
    in.rho_n.resize(RHO_BITS);
    in.rho_p.resize(RHO_BITS);
    std::array<uint8_t, Z_BYTES> zn{}, zp{};
    link_sums<LOG>(ops, in, chal, zn, zp, false);
    return ops.next;
}

// The link sums, with carries in [first, first + LINK_BUDGET<LOG>), where the unused carries must
// be zero. Throws std::runtime_error if the budget is exceeded.
template <size_t LOG, typename Ops>
void link_circuit(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
                  std::span<uint8_t, Z_BYTES> zn, std::span<uint8_t, Z_BYTES> zp, bool record) {
    const size_t first = ops.next;
    link_sums<LOG>(ops, in, chal, zn, zp, record);
    if (ops.next > first + LINK_BUDGET<LOG>) {
        throw std::runtime_error("ecdsa_pok: link carry budget exceeded");
    }
    while (ops.next < first + LINK_BUDGET<LOG>) {
        ops.assert_eq(ops.commit(false), false);
    }
}

// The number of constraints of the circuit, besides the bit constraints: count_circuit_constraints
// computes it, and CIRCUIT_CONSTRAINTS is checked against it by test_ecdsa_pok_hk.cpp.
template <Shape SH> size_t count_circuit_constraints() {
    CountOps ops;
    auto wires = prefix_circuit<SH.small_log>(ops, nullptr);
    ops.next = 8 * PREFIX_BYTES;
    const LinkChallenge chal = derive_link_challenge(Digest{});
    std::array<uint8_t, Z_BYTES> zn{}, zp{};
    link_circuit<SH.link_log>(ops, wires, chal, zn, zp, false);
    return ops.constraints;
}
template <Shape SH> constexpr size_t CIRCUIT_CONSTRAINTS() {
    // X < p: one per carry, and the top column. The link sums: one per column, and one per carry
    // in the budget.
    return X_LT_P_BITS + 1 + 2 * Z_COLS + LINK_BUDGET<SH.link_log>;
}

constexpr faest::owf owf_for(BinPrg prg) {
    return static_cast<faest::owf>(((0x90u + std::to_underlying(prg)) << 8) |
                                   faest::owf_flag_witness_bits_check);
}
constexpr bool is_hk_owf(faest::owf o) {
    const auto v = std::to_underlying(o);
    const auto hi = v >> 8;
    return (v & 0xff) == faest::owf_flag_witness_bits_check && hi >= 0x90 && hi <= 0x92;
}
constexpr BinPrg prg_of_owf(faest::owf o) {
    return static_cast<BinPrg>((std::to_underlying(o) >> 8) - 0x90);
}

} // namespace vole_mole::ecdsa_pok::detail::hk

template <faest::owf O>
    requires(vole_mole::ecdsa_pok::detail::hk::is_hk_owf(O))
struct faest::OWF_CONSTANTS<faest::secpar::s128, O>
    : vole_mole::detail::RelationConstants<
          vole_mole::ecdsa_pok::detail::hk::witness_bits<vole_mole::ecdsa_pok::detail::SHAPE<
              vole_mole::ecdsa_pok::detail::hk::prg_of_owf(O)>>(),
          vole_mole::ecdsa_pok::detail::BIN_QS_DEGREE<vole_mole::ecdsa_pok::detail::hk::prg_of_owf(
              O)>,
          typename vole_mole::ecdsa_pok::detail::bin_prg<
              vole_mole::ecdsa_pok::detail::hk::prg_of_owf(O)>::type> {};

namespace vole_mole::ecdsa_pok::detail::hk {

// As binary.hpp's BinParams: faest::v3::faest_em_128_f or faest_em_128_s.
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
        std::array<uint8_t, Z_BYTES> zn, zp;
    };

    static constexpr size_t RELATION_WITNESS_BITS = witness_bits<SH>();
    static constexpr size_t WITNESS_PREFIX_BYTES = PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::ECDSA_HK_BINARY_DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST =
        vole_mole::detail::ECDSA_HK_BINARY_PRG_DST;

    static constexpr size_t NUM_CONSTRAINTS = vole_mole::detail::qs_batches(
        (DERIVED ? 0 : RELATION_WITNESS_BITS) + CIRCUIT_CONSTRAINTS<SH>());

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(*x.mu);
        hasher.update(x.chal->digest);
        hasher.update(x.zn);
        hasher.update(x.zp);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == BIN_QS_DEGREE<PRG>);
        QsOps<QS> ops(qs, chal2);
        if constexpr (!DERIVED) {
            for (size_t i = 0; i < RELATION_WITNESS_BITS; ++i) {
                ops.assert_bit(qs->get_witness_bit(i));
            }
        }
        const auto wires = prefix_circuit<SH.small_log>(ops, nullptr);
        ops.next = 8 * WITNESS_PREFIX_BYTES;
        auto zn = x.zn;
        auto zp = x.zp;
        link_circuit<SH.link_log>(ops, wires, *x.chal, zn, zp, false);
        ops.finish();
    }
};

} // namespace vole_mole::ecdsa_pok::detail::hk

#endif
