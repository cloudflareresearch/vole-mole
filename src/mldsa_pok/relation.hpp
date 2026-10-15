// The relation of the proof of knowledge of an ML-DSA-44 signature on a hidden message (see
// include/vole_mole/mldsa_pok.hpp), composed of the gadgets of verify_gadget.hpp.
//
// Statement. Public: pk. Secret: a message M of MESSAGE_BYTES bytes, and a signature on M with an
// empty context string, i.e., (c-tilde, z, h) that VerifyGadget accepts for
// mu = H(H(pk) || 0 || 0 || M, 64) (MuHash, one Keccak-f[1600] permutation).
//
// The proof is a single binary VOLEitH proof (FAEST, src/voleith.hpp), whose witness is derived
// from a short key with the local PRG (see "Derived witnesses" in voleith.hpp: each witness bit
// costs one bit of proof, and every witness bit is a bit). The witness is:
//
//   1. the witness prefix, committed by VOLE generation: MuHash's witness (M, and the state of the
//      hash), then VerifyGadget's;
//   2. the answer to the checks of VerifyGadget, whose seed binds the commitment to the prefix.

#ifndef VOLE_MOLE_MLDSA_POK_RELATION_HPP
#define VOLE_MOLE_MLDSA_POK_RELATION_HPP

#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include "dst.hpp"
#include "mldsa_pok/shake_relation.hpp"
#include "mldsa_pok/verify_gadget.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

// The statement.
struct Statement {
    const mldsa::PublicKey<P>* pk;
    VerifyKey key;
};
Statement make_statement(const mldsa::PublicKey<P>& pk);

using BinWitnessPrg = vole_mole::detail::LocalPrg<2>;
using Mu = MuHash<MESSAGE_BYTES>;
static_assert(Mu::NUM_PERMUTATIONS == 1);

// Witness layout (bytes).
constexpr Mu MU{0};
constexpr size_t B_PREFIX_BYTES = Mu::WITNESS_BYTES + VerifyGadget::WITNESS_BYTES;
constexpr VerifyGadget SIG{Mu::WITNESS_BYTES, /* answer */ B_PREFIX_BYTES};
constexpr size_t B_WITNESS_BITS = 8 * B_PREFIX_BYTES + MlDsaModQ::ANSWER_BITS;

constexpr size_t B_NUM_CONSTRAINTS = Mu::NUM_CONSTRAINTS + VerifyGadget::NUM_CONSTRAINTS;
constexpr size_t B_QS_DEGREE = VerifyGadget::QS_DEGREE;
static_assert(Mu::QS_DEGREE <= B_QS_DEGREE);

constexpr faest::owf OWF_MLDSA_POK = static_cast<faest::owf>((0x72u << 8) | 0b10'0000);

} // namespace vole_mole::mldsa_pok::detail

template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::mldsa_pok::detail::OWF_MLDSA_POK>
    : vole_mole::detail::RelationConstants<vole_mole::mldsa_pok::detail::B_WITNESS_BITS,
                                           vole_mole::mldsa_pok::detail::B_QS_DEGREE,
                                           vole_mole::mldsa_pok::detail::BinWitnessPrg> {};

namespace vole_mole::mldsa_pok::detail {

using CheckSeed = std::array<uint8_t, 32>;

struct BinRelation {
    using params = Params128f<OWF_MLDSA_POK>;
    struct instance {
        const Statement* stmt;
        CheckSeed seed;
        const Weights* weights; // derived from stmt and seed
    };
    static constexpr size_t NUM_CONSTRAINTS = B_NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = B_PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::MLDSA_POK_PROOF_DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST =
        vole_mole::detail::MLDSA_POK_PRG_DST;

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update(*x.stmt->pk);
        h.update(x.seed);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        using Bit = vole_mole::detail::qs_bit<QS, 1>;
        const auto mu = MU.constraints(qs, x.stmt->key.parsed.tr);
        SIG.constraints(qs, x.stmt->key,
                        std::span<const Bit, 8 * MU_BYTES>(mu.data(), 8 * MU_BYTES), *x.weights);
    }
};

constexpr size_t PROOF_BYTES_ = vole_mole::detail::PROOF_BYTES<BinRelation>;

// The seed of the checks, from the statement, chal1, and the part of the proof that commits to the
// witness prefix.
using Chal1 = std::array<uint8_t, BinRelation::params::CONSTS::VOLE_CHECK::CHALLENGE_BYTES>;
CheckSeed check_seed(const Statement& stmt, const Chal1& chal1,
                     std::span<const uint8_t, PROOF_BYTES_> proof);

} // namespace vole_mole::mldsa_pok::detail

#endif
