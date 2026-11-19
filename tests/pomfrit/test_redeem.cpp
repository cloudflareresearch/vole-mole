// Tests for the PomFRIT redemption proof relation P(s) = h + r.

#include "vole_mole/uov.hpp"

#include "pomfrit/redeem.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::pomfrit::detail;
using vole_mole::test::filled;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

// RedeemRelation has degree 2.
using PlainQS = vole_mole::test::BasicPlainQS<REDEEM_QS_DEGREE>;
constexpr size_t CHALLENGE_BYTES = RedeemParams::CONSTS::QS::CHALLENGE_BYTES;
using Challenge = std::array<uint8_t, CHALLENGE_BYTES>;

const uov::Target H = filled<uov::M>(0x70);
const uov::Target R = filled<uov::M>(0xa0);

using Witness = std::array<uint8_t, REDEEM_WITNESS_BYTES>;

// The index of the constraint P(s) = h + r, after the bit constraints.
constexpr size_t OUTPUT_CONSTRAINT = REDEEM_WITNESS_BITS;

uov::Target add(const uov::Target& a, const uov::Target& b) {
    uov::Target out;
    for (size_t k = 0; k < uov::M; ++k) {
        out[k] = a[k] ^ b[k];
    }
    return out;
}

Witness encode_witness(const uov::Target& r, const uov::Preimage& s) {
    Witness w;
    std::ranges::copy(r, w.begin() + WIT_OFF_R);
    std::ranges::copy(s, w.begin() + WIT_OFF_S);
    return w;
}

// The witness for h under the fixed test key pair, i.e., with P(s) = h + r.
Witness honest_witness(const uov::Target& h = H, const uov::Target& r = R) {
    return encode_witness(r, uov_key_pair().sk.derive_preimage(add(h, r)));
}

RedeemRelation::instance make_instance(const uov::Target& h = H,
                                       const uov::PublicKey& pk = uov_key_pair().pk) {
    return {&pk, h};
}

// An arbitrary QuickSilver challenge, from which the random linear combination is derived.
const Challenge CHAL2 = filled<CHALLENGE_BYTES>(0x50);

std::vector<bool> evaluate(const Witness& w, const RedeemRelation::instance& x,
                           const Challenge& chal2 = CHAL2) {
    PlainQS qs{w.data(), {}};
    RedeemRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    return static_cast<size_t>(std::ranges::count(v, true));
}

} // namespace

TEST(PomfritRedeemRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto violated = evaluate(honest_witness(), make_instance());
    EXPECT_EQ(violated.size(), RedeemRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

// The relation holds for every combination, not just the one derived from CHAL2.
TEST(PomfritRedeemRelation, HonestWitnessSatisfiesAllConstraintsForAnyChallenge) {
    const auto w = honest_witness();
    const auto x = make_instance();
    for (const uint8_t start : {0x00, 0x01, 0xff}) {
        EXPECT_EQ(count_violated(evaluate(w, x, filled<CHALLENGE_BYTES>(start))), 0u)
            << "challenge starting at " << unsigned{start};
    }
}

TEST(PomfritRedeemRelation, HonestWitnessForOtherTargets) {
    const UovKeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    for (const uint8_t start : {0x00, 0x33}) {
        const uov::Target h = filled<uov::M>(start);
        const uov::Target r = filled<uov::M>(static_cast<uint8_t>(start + 0x80));
        const Witness w = encode_witness(r, other.sk.derive_preimage(add(h, r)));
        EXPECT_EQ(count_violated(evaluate(w, make_instance(h, other.pk))), 0u);
    }

    // The target mask may be zero.
    EXPECT_EQ(count_violated(evaluate(honest_witness(H, uov::Target{}), make_instance())), 0u);
}

// Every bit of the witness matters: r and s are related by P(s) = h + r, so flipping a single bit
// of either violates the output constraint. (The bit constraints still hold, since the witness is
// still a bit string.)
TEST(PomfritRedeemRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = honest_witness();
    const auto x = make_instance();
    for (size_t i = 0; i < REDEEM_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        const auto violated = evaluate(w, x);
        EXPECT_TRUE(violated[OUTPUT_CONSTRAINT])
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(PomfritRedeemRelation, WrongInstanceViolatesAConstraint) {
    const auto w = honest_witness();

    // Each component of h matters.
    for (size_t k = 0; k < uov::M; ++k) {
        uov::Target h = H;
        h[k] ^= 0x80;
        EXPECT_GT(count_violated(evaluate(w, make_instance(h))), 0u) << "component " << k;
    }

    // So does the public key.
    const UovKeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    EXPECT_GT(count_violated(evaluate(w, make_instance(H, other.pk))), 0u) << "public key";
}

// A witness whose preimage satisfies P(s) = h + r in all but one component, or in none, violates
// the output constraint.
TEST(PomfritRedeemRelation, RejectsWrongComponents) {
    const auto& [pk, sk] = uov_key_pair();
    const uov::Preimage s = sk.derive_preimage(add(H, R));
    for (size_t k = 0; k < uov::M; ++k) {
        uov::Target r = R;
        r[k] ^= 1;
        EXPECT_TRUE(evaluate(encode_witness(r, s), make_instance())[OUTPUT_CONSTRAINT])
            << "component " << k;
    }
    // A preimage of a different target, with the mask that matches neither.
    const uov::Preimage s2 = sk.derive_preimage(H);
    EXPECT_TRUE(evaluate(encode_witness(R, s2), make_instance())[OUTPUT_CONSTRAINT]);
    // But with r = 0, it's valid.
    EXPECT_EQ(count_violated(evaluate(encode_witness(uov::Target{}, s2), make_instance())), 0u);
}
