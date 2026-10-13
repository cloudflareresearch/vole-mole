// The binary part of the ECDSA proof of knowledge (see relation.hpp for the whole statement), in
// FAEST's VOLEitH (src/voleith.hpp).
//
//   Instance: the statement (public key, message length, context), the link challenge, and the
//             link values Z_n, Z_p
//   Witness:  the padded message, the SHA-256 intermediate values, X = x(R) as 256 bits, the masks
//             rho_n and rho_p, and carries
//   Constraints:
//     - the padding of the message is the public padding for its length;
//     - e = SHA-256(message) (sha256_circuit.hpp);
//     - X < p;
//     - Z_n = c_1 e + c_2 X + rho_n and Z_p = c_3 X + rho_p over the integers, for the sparse
//       weights c_i of the link challenge (link.hpp).
//
// The witness prefix (everything but the carries of the link sums) is committed in the VOLE
// generation step; the link challenge is derived from its correction (and from the commitment of
// the proof over F_p and F_n), and the carries of the link sums are committed in the second step.
// Their number depends on the weights, so we reserve a budget of carries (LINK_BUDGET), and the
// unused ones must be zero.

#ifndef VOLE_MOLE_ECDSA_POK_BINARY_HPP
#define VOLE_MOLE_ECDSA_POK_BINARY_HPP

#include "dst.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/sha256_circuit.hpp"
#include "p256/field.hpp"
#include "qs_bit.hpp"
#include "sha256/sha256.hpp"
#include "voleith.hpp"

#include "faest_sig.hpp"  // from faest-arch-opt
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

namespace vole_mole::ecdsa_pok::detail {

// Widths of the link sums: c_i < 2^256 and e, X < 2^256, so the weighted terms are less than
// 2^513 (Z_n) or 2^512 (Z_p). The masks are 128 bits wider, for statistical hiding.
constexpr size_t RHO_N_BITS = 513 + 128;
constexpr size_t RHO_P_BITS = 512 + 128;
constexpr size_t ZN_COLS = RHO_N_BITS + 1;
constexpr size_t ZP_COLS = RHO_P_BITS + 1;
constexpr size_t Z_BYTES = 81;
static_assert(8 * Z_BYTES >= ZN_COLS && 8 * Z_BYTES >= ZP_COLS);

// Committed bits per SHA-256 block (sha256_circuit.hpp, checked by tests), besides the message.
constexpr size_t SHA_FIRST_BLOCK_BITS = 20968;
constexpr size_t SHA_NEXT_BLOCK_BITS = 21080;
// The carries of the check X < p.
constexpr size_t X_LT_P_BITS = 256;
// The budget of carries of the link sums. Over random challenges their number has mean ~5376 and
// standard deviation ~31 (max 5518 over 50000 trials), so the budget is ~8 standard deviations
// above the mean; the prover retries with a fresh seed in the unlikely case it is exceeded.
constexpr size_t LINK_BUDGET = 8 * 704;

constexpr size_t sha_bits(size_t nb) {
    return 512 * nb + SHA_FIRST_BLOCK_BITS + (nb - 1) * SHA_NEXT_BLOCK_BITS;
}
constexpr size_t prefix_bits(size_t nb) {
    return sha_bits(nb) + 256 + X_LT_P_BITS + RHO_N_BITS + RHO_P_BITS;
}
constexpr size_t prefix_bytes(size_t nb) { return (prefix_bits(nb) + 7) / 8; }
constexpr size_t witness_bits(size_t nb) { return 8 * prefix_bytes(nb) + LINK_BUDGET; }

// 2^256 - p, so that X + (2^256 - p) < 2^256 iff X < p.
constexpr std::array<uint8_t, 32> TWO256_MINUS_P = [] {
    p256::Limbs k{};
    p256::detail::limbs_sub(k, p256::Limbs{0, 0, 0, 0}, p256::Fp::M);
    std::array<uint8_t, 32> out{};
    for (size_t i = 0; i < 32; ++i) {
        out[i] = static_cast<uint8_t>(k[i / 8] >> (8 * (i % 8)));
    }
    return out;
}();

// The wires of the prefix that the link sums use.
template <typename Ops> struct PrefixWires {
    std::vector<typename Ops::Wire> e, x, rho_n, rho_p; // little endian
};

// The values the prover commits to in the prefix (PlainOps only).
struct PrefixValues {
    std::vector<uint8_t> padded;              // the padded message
    std::vector<sha256::Trace> traces;        // SHA-256 traces
    std::array<uint8_t, 32> x;                // X, little endian
    std::array<uint8_t, Z_BYTES> rho_n, rho_p; // little endian
};

// The prefix circuit, for a message of msg_len bytes. vals is null except for PlainOps.
template <typename Ops>
PrefixWires<Ops> prefix_circuit(Ops& ops, size_t msg_len, const PrefixValues* vals) {
    using Wire = typename Ops::Wire;
    const size_t nb = sha256::num_blocks(msg_len);
    PrefixWires<Ops> out;

    // The padded message, with its public padding.
    const std::vector<uint8_t> pad = sha256::pad(std::vector<uint8_t>(msg_len, 0));
    std::vector<Wire> msg;
    msg.reserve(512 * nb);
    for (size_t i = 0; i < 512 * nb; ++i) {
        msg.push_back(ops.commit(vals && get_bit(vals->padded, i)));
        // One constraint per message bit, so that the number of constraints doesn't depend on the
        // message length: the padding is public, and the message bits are free.
        ops.assert_eq(i / 8 >= msg_len ? msg.back() : ops.zero(), i / 8 >= msg_len && get_bit(pad, i));
    }

    // e = SHA-256(msg) as an integer: digest word w holds bits 32 (7 - w), ..., 32 (7 - w) + 31.
    ShaCircuit<Ops> sha{ops};
    const auto h = sha.hash(msg, vals ? &vals->traces : nullptr);
    out.e.resize(256);
    for (size_t w = 0; w < 8; ++w) {
        for (size_t i = 0; i < 32; ++i) {
            out.e[32 * (7 - w) + i] = h[w].w[i];
        }
    }

    // X < p, i.e., X + (2^256 - p) < 2^256.
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
        sum.template reduce<SHA_COUNTER_LOG>([&](size_t col, const Wire& w) {
            if (col == 256) {
                ops.assert_eq(w, false);
            }
        });
    }

    for (size_t i = 0; i < RHO_N_BITS; ++i) {
        out.rho_n.push_back(ops.commit(vals && get_bit(vals->rho_n, i)));
    }
    for (size_t i = 0; i < RHO_P_BITS; ++i) {
        out.rho_p.push_back(ops.commit(vals && get_bit(vals->rho_p, i)));
    }
    return out;
}

// The link sums Z_n and Z_p. If `record`, then writes the sums to zn and zp (PlainOps);
// otherwise, constrains them to be zn and zp.
template <typename Ops>
void link_sums(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
               std::span<uint8_t, Z_BYTES> zn, std::span<uint8_t, Z_BYTES> zp, bool record) {
    using Wire = typename Ops::Wire;
    auto check = [&](std::span<uint8_t, Z_BYTES> z) {
        return [&ops, z, record](size_t col, const Wire& w) {
            if constexpr (std::is_same_v<Ops, PlainOps>) {
                if (record) {
                    set_bit(z, col, w != 0);
                }
            } else {
                (void)record;
            }
            ops.assert_eq(w, get_bit(z, col));
        };
    };
    if (record) {
        std::ranges::fill(zn, 0);
        std::ranges::fill(zp, 0);
    }
    {
        ColSum<Ops> sum(ops, ZN_COLS);
        for (const uint16_t j : chal.e_pos) {
            for (size_t i = 0; i < 256; ++i) {
                sum.add(in.e[i], j + i);
            }
        }
        for (const uint16_t j : chal.xn_pos) {
            for (size_t i = 0; i < 256; ++i) {
                sum.add(in.x[i], j + i);
            }
        }
        for (size_t i = 0; i < RHO_N_BITS; ++i) {
            sum.add(in.rho_n[i], i);
        }
        sum.template reduce<LINK_COUNTER_LOG>(check(zn));
    }
    {
        ColSum<Ops> sum(ops, ZP_COLS);
        for (const uint16_t j : chal.xp_pos) {
            for (size_t i = 0; i < 256; ++i) {
                sum.add(in.x[i], j + i);
            }
        }
        for (size_t i = 0; i < RHO_P_BITS; ++i) {
            sum.add(in.rho_p[i], i);
        }
        sum.template reduce<LINK_COUNTER_LOG>(check(zp));
    }
}

// The number of carries of the link sums for a challenge.
inline size_t link_carries(const LinkChallenge& chal) {
    CountOps ops;
    PrefixWires<CountOps> in;
    in.e.resize(256);
    in.x.resize(256);
    in.rho_n.resize(RHO_N_BITS);
    in.rho_p.resize(RHO_P_BITS);
    std::array<uint8_t, Z_BYTES> zn{}, zp{};
    link_sums(ops, in, chal, zn, zp, false);
    return ops.next;
}

// The link circuit: the link sums, with carries in [first, first + LINK_BUDGET), where the unused
// carries must be zero. Throws std::runtime_error if the budget is exceeded (which happens with
// negligible probability).
template <typename Ops>
void link_circuit(Ops& ops, const PrefixWires<Ops>& in, const LinkChallenge& chal,
                  std::span<uint8_t, Z_BYTES> zn, std::span<uint8_t, Z_BYTES> zp, bool record) {
    const size_t first = ops.next;
    link_sums(ops, in, chal, zn, zp, record);
    if (ops.next > first + LINK_BUDGET) {
        throw std::runtime_error("ecdsa_pok: link carry budget exceeded");
    }
    while (ops.next < first + LINK_BUDGET) {
        ops.assert_eq(ops.commit(false), false);
    }
}

// The number of constraints of the circuit, besides the bit constraints.
inline size_t count_circuit_constraints(size_t msg_len) {
    CountOps ops;
    auto wires = prefix_circuit(ops, msg_len, nullptr);
    ops.next = 8 * prefix_bytes(sha256::num_blocks(msg_len));
    const LinkChallenge chal = derive_link_challenge(Digest{});
    std::array<uint8_t, Z_BYTES> zn{}, zp{};
    link_circuit(ops, wires, chal, zn, zp, false);
    return ops.constraints;
}

// The QuickSilver degree: the counters of the link sums have degree 16.
constexpr size_t BIN_QS_DEGREE = COUNTER_DEGREE;

constexpr faest::owf owf_for_blocks(size_t nb) {
    return static_cast<faest::owf>(((0x60u + nb) << 8) | faest::owf_flag_witness_bits_check);
}
constexpr bool is_ecdsa_owf(faest::owf o) {
    const auto v = std::to_underlying(o);
    return (v & 0xff) == faest::owf_flag_witness_bits_check && (v >> 8) >= 0x61 &&
           (v >> 8) <= 0x6f;
}
constexpr size_t blocks_of_owf(faest::owf o) { return (std::to_underlying(o) >> 8) - 0x60; }

} // namespace vole_mole::ecdsa_pok::detail

template <faest::owf O>
    requires(vole_mole::ecdsa_pok::detail::is_ecdsa_owf(O))
struct faest::OWF_CONSTANTS<faest::secpar::s128, O> {
    constexpr static size_t WITNESS_BITS =
        vole_mole::ecdsa_pok::detail::witness_bits(vole_mole::ecdsa_pok::detail::blocks_of_owf(O));
    constexpr static size_t QS_DEGREE = vole_mole::ecdsa_pok::detail::BIN_QS_DEGREE;
    constexpr static bool valid = true;
};

namespace vole_mole::ecdsa_pok::detail {

// The binary VOLEitH parameters: as faest::v3::faest_em_128_f or faest_em_128_s.
template <size_t NB, bool SMALL>
using BinParams = faest::parameter_set<
    faest::secpar::s128, SMALL ? 11 : 17, owf_for_blocks(NB), faest::prg::aes_ctr,
    faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, SMALL ? 7 : 8,
    {faest::bavc::one_tree, SMALL ? 103u : 105u}, true, true>;

// The public statement shared by both proofs.
struct Statement {
    Digest mu; // binds the public key, message length, context, and parameters
    size_t msg_len;
};

template <size_t NB, bool SMALL> struct BinRelation {
    using params = BinParams<NB, SMALL>;

    struct instance {
        const Statement* stmt;
        const LinkChallenge* chal;
        std::array<uint8_t, Z_BYTES> zn, zp;
    };

    static constexpr size_t WITNESS_BITS = witness_bits(NB);
    static constexpr size_t WITNESS_PREFIX_BYTES = prefix_bytes(NB);
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::ECDSA_POK_BINARY_DST;

    // The bit constraints and the circuit's (which don't depend on the message length within NB
    // blocks).
    inline static const size_t NUM_CONSTRAINTS =
        WITNESS_BITS + count_circuit_constraints(64 * NB - 9);

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(x.stmt->mu);
        hasher.update(x.chal->digest);
        hasher.update(x.zn);
        hasher.update(x.zp);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        for (size_t i = 0; i < WITNESS_BITS; ++i) {
            vole_mole::detail::qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }
        QsOps<QS> ops{qs};
        const auto wires = prefix_circuit(ops, x.stmt->msg_len, nullptr);
        ops.next = 8 * WITNESS_PREFIX_BYTES;
        auto zn = x.zn;
        auto zp = x.zp;
        link_circuit(ops, wires, *x.chal, zn, zp, false);
    }
};

} // namespace vole_mole::ecdsa_pok::detail

#endif
