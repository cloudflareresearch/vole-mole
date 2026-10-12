// Tests for deriving the witness with the MQ PRG (see "Derived witnesses" in voleith.hpp). The same
// relation is proven with the witness committed directly (MQ_PRG_INSTANCES = 0) and derived with
// one or more instances of the MQ PRG.

#include "mq/split.hpp" // internal
#include "qs_bit.hpp"   // internal
#include "voleith.hpp"  // internal

#include "test.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "faest_sig.hpp"   // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <type_traits>
#include <utility>
#include <vector>

namespace toy {

// Witness: 64 bytes w. Instance: 32 bytes t. Constraints: t_i = w_{2i} w_{2i+1} for each bit i of
// t, and every bit of w is a bit. The witness prefix is the first 16 bytes.
constexpr size_t WITNESS_BYTES = 64;
constexpr size_t PREFIX_BYTES = 16;
constexpr size_t T_BYTES = WITNESS_BYTES / 2;
constexpr size_t QS_DEGREE = 2;
constexpr size_t NUM_CONSTRAINTS = 8 * WITNESS_BYTES + 8 * T_BYTES;

template <size_t c>
constexpr faest::owf OWF = static_cast<faest::owf>(((0x54u + c) << 8) | 0b10'0000);

} // namespace toy

// (A partial specialization for all c isn't allowed, since the type of OWF<c> isn't dependent.)
#define TOY_OWF_CONSTANTS(c)                                                                       \
    template <>                                                                                    \
    struct faest::OWF_CONSTANTS<faest::secpar::s128, toy::OWF<c>>                                  \
        : vole_mole::detail::RelationConstants<8 * toy::WITNESS_BYTES, toy::QS_DEGREE, c> {}
TOY_OWF_CONSTANTS(0);
TOY_OWF_CONSTANTS(1);
TOY_OWF_CONSTANTS(2);
TOY_OWF_CONSTANTS(3);
#undef TOY_OWF_CONSTANTS

namespace {

using namespace vole_mole::detail;

constexpr std::array<uint8_t, 4> TOY_DST = {'t', 'o', 'y', '0'};
constexpr std::array<uint8_t, 4> TOY_MQ_DST = {'t', 'o', 'y', 'q'};

using Witness = std::array<uint8_t, toy::WITNESS_BYTES>;
using Target = std::array<uint8_t, toy::T_BYTES>;

template <size_t c> struct ToyRelation {
    using params =
        faest::parameter_set<faest::secpar::s128, /* TAU */ 17, toy::OWF<c>, faest::prg::aes_ctr,
                             faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, /* W_GRIND */ 8,
                             {faest::bavc::one_tree, /* T_OPEN */ 105},
                             /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

    struct instance {
        Target t;
    };

    static constexpr size_t NUM_CONSTRAINTS = toy::NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = toy::PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = TOY_DST;
    static constexpr std::span<const uint8_t> MQ_PRG_DST = TOY_MQ_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) { hasher.update(x.t); }

    // The same constraints, whether or not the witness is derived.
    template <typename QS>
    static void
    constraints(QS* qs, const instance& x,
                std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> /* chal2 */) {
        static_assert(QS::max_degree == toy::QS_DEGREE);
        for (size_t i = 0; i < 8 * toy::WITNESS_BYTES; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }
        for (size_t i = 0; i < 8 * toy::T_BYTES; ++i) {
            const auto prod =
                qs_mul<QS, 1, 1>(qs->get_witness_bit(2 * i), qs->get_witness_bit(2 * i + 1));
            qs->add_constraint(qs_to_gfsecpar(prod + faest::poly1((x.t[i / 8] >> (i % 8)) & 1)));
        }
    }
};

Witness witness() { return vole_mole::test::filled<toy::WITNESS_BYTES>(0x37); }

Target target(const Witness& w) {
    Target t{};
    for (size_t i = 0; i < 8 * toy::T_BYTES; ++i) {
        const size_t a = 2 * i;
        const size_t b = 2 * i + 1;
        const uint8_t bit = ((w[a / 8] >> (a % 8)) & (w[b / 8] >> (b % 8))) & 1;
        t[i / 8] |= static_cast<uint8_t>(bit << (i % 8));
    }
    return t;
}

const ProveSeed<ToyRelation<0>> RHO = vole_mole::test::filled<16>(0x11);

template <size_t c> using Proof = std::array<uint8_t, PROOF_BYTES<ToyRelation<c>>>;

// Prove in two steps, with the instance bound in the first (delay_instance = false) or second.
template <size_t c>
Proof<c> prove(const Witness& w, const typename ToyRelation<c>::instance& x, bool delay_instance,
               const ProveSeed<ToyRelation<c>>& rho = RHO) {
    using R = ToyRelation<c>;
    Proof<c> proof{};
    auto pending = voleith_vole_gen<R>(proof, delay_instance ? nullptr : &x,
                                       std::span(w).template first<toy::PREFIX_BYTES>(), rho);
    voleith_prove_commit<R>(proof, x,
                            std::span(w).template last<toy::WITNESS_BYTES - toy::PREFIX_BYTES>(),
                            std::move(pending));
    return proof;
}

template <size_t c>
bool verify(const Proof<c>& proof, const typename ToyRelation<c>::instance& x,
            bool delay_instance) {
    using R = ToyRelation<c>;
    auto pending = voleith_vole_reconstruct<R>(proof, delay_instance ? nullptr : &x);
    return pending && voleith_verify_commit<R>(proof, x, std::move(*pending));
}

// The part of the proof that commits the prover to the witness prefix (see
// hash_witness_prefix_commitment).
template <size_t c> std::array<uint8_t, 32> prefix_commitment(const Proof<c>& proof) {
    faest::hash_state hasher;
    hasher.init(faest::secpar::s128);
    hash_witness_prefix_commitment<ToyRelation<c>>(hasher, proof);
    std::array<uint8_t, 32> out;
    hasher.finalize(out);
    return out;
}

template <typename T> class DerivedWitness : public testing::Test {};
template <size_t c> using Instances = std::integral_constant<size_t, c>;
using AllInstances = testing::Types<Instances<0>, Instances<1>, Instances<2>, Instances<3>>;
TYPED_TEST_SUITE(DerivedWitness, AllInstances);

} // namespace

// The proof is the FAEST proof, followed by e if the witness is derived; the VOLE witness is the
// key.
TEST(DerivedWitnessLayout, Sizes) {
    static_assert(!DERIVED_WITNESS<ToyRelation<0>>);
    static_assert(PROOF_BYTES<ToyRelation<0>> == FAEST_PROOF_BYTES<ToyRelation<0>>);
    static_assert(VOLE_WITNESS_BYTES<ToyRelation<0>> == toy::WITNESS_BYTES);
    static_assert(relation_params<ToyRelation<0>>::OWF_CONSTS::QS_DEGREE == toy::QS_DEGREE);

    static_assert(DERIVED_WITNESS<ToyRelation<2>>);
    static_assert(WITNESS_BYTES<ToyRelation<2>> == toy::WITNESS_BYTES);
    static_assert(PROOF_BYTES<ToyRelation<2>> ==
                  FAEST_PROOF_BYTES<ToyRelation<2>> + toy::WITNESS_BYTES);
    static_assert(VOLE_WITNESS_BYTES<ToyRelation<2>> ==
                  vole_mole::mq::detail::split_key_bits<8 * toy::WITNESS_BYTES, 2> / 8);
    static_assert(relation_params<ToyRelation<2>>::OWF_CONSTS::QS_DEGREE == 2 * toy::QS_DEGREE);
}

TYPED_TEST(DerivedWitness, Verifies) {
    constexpr size_t c = TypeParam::value;
    const Witness w = witness();
    const typename ToyRelation<c>::instance x{target(w)};
    for (const bool delay : {false, true}) {
        SCOPED_TRACE(delay ? "delayed instance" : "early instance");
        const auto proof = prove<c>(w, x, delay);
        EXPECT_TRUE(verify<c>(proof, x, delay));
        EXPECT_FALSE(verify<c>(proof, x, !delay));

        auto x2 = x;
        x2.t[3] ^= 0x10;
        EXPECT_FALSE(verify<c>(proof, x2, delay));
    }
}

// voleith_prove computes the same proof as the two steps.
TYPED_TEST(DerivedWitness, OneStepMatchesTwoSteps) {
    constexpr size_t c = TypeParam::value;
    const Witness w = witness();
    const typename ToyRelation<c>::instance x{target(w)};
    Proof<c> proof{};
    voleith_prove<ToyRelation<c>>(proof, w, x, RHO);
    EXPECT_EQ(proof, prove<c>(w, x, false));
    EXPECT_TRUE(voleith_verify<ToyRelation<c>>(proof, x));
}

// Every bit of the proof is bound, including e.
TYPED_TEST(DerivedWitness, RejectsTamperedProof) {
    constexpr size_t c = TypeParam::value;
    const Witness w = witness();
    const typename ToyRelation<c>::instance x{target(w)};
    auto proof = prove<c>(w, x, true);
    constexpr size_t FAEST_BYTES = FAEST_PROOF_BYTES<ToyRelation<c>>;
    for (size_t i = 0; i < proof.size(); i += (i >= FAEST_BYTES ? 1 : 89)) {
        proof[i] ^= 0x20;
        EXPECT_FALSE(verify<c>(proof, x, true)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x20;
    }
    EXPECT_TRUE(verify<c>(proof, x, true));
}

// VOLE generation commits the prover to the witness prefix: the prefix commitment depends on the
// prefix but neither on the suffix nor on a delayed instance.
TYPED_TEST(DerivedWitness, PrefixCommitment) {
    constexpr size_t c = TypeParam::value;
    const Witness w = witness();
    const typename ToyRelation<c>::instance x{target(w)};
    const auto commitment = prefix_commitment<c>(prove<c>(w, x, true));

    Witness w_suffix = w;
    w_suffix[toy::PREFIX_BYTES] ^= 1;
    const typename ToyRelation<c>::instance x_suffix{target(w_suffix)};
    const auto proof_suffix = prove<c>(w_suffix, x_suffix, true);
    EXPECT_EQ(commitment, prefix_commitment<c>(proof_suffix));
    EXPECT_TRUE(verify<c>(proof_suffix, x_suffix, true));

    Witness w_prefix = w;
    w_prefix[0] ^= 1;
    EXPECT_NE(commitment, prefix_commitment<c>(prove<c>(w_prefix, {target(w_prefix)}, true)));

    // It does depend on rho.
    auto rho2 = RHO;
    rho2[0] ^= 1;
    EXPECT_NE(commitment, prefix_commitment<c>(prove<c>(w, x, true, rho2)));
}
