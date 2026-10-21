// Tests for the redemption proof relation of unbound tokens.

#include "vole_mole/ihat.hpp"
#include "vole_mole/keccak.hpp"
#include "vole_mole/uov.hpp"

#include "ihat/circuit.hpp"        // internal
#include "ihat/commit.hpp"         // internal
#include "ihat/unbound_redeem.hpp" // internal
#include "keccak/segmented.hpp"    // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::ihat;
using namespace vole_mole::ihat::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const ChallengeDigest CHALLENGE_DIGEST = filled<CHALLENGE_DIGEST_BYTES>(0x70);
const NfKey NF_KEY = filled<NF_KEY_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);

using Witness = std::array<uint8_t, UNBOUND_REDEEM_WITNESS_BYTES>;

// Three distinct Anchors. The issuing Anchor is the fixed test key pair, at index ISSUER.
struct Anchors {
    UovKeyPair a{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)}};
    UovKeyPair c{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x62)}};
    std::array<AnchorRef, 3> keys = {a.pk, uov_key_pair().pk, c.pk};
};
constexpr size_t ISSUER = 1;

const Anchors& anchors() {
    static const Anchors a;
    return a;
}

const uov::Preimage& signature() {
    static const uov::Preimage s =
        uov_key_pair().sk.derive_preimage(unbound_commit(NF_KEY, CTX_ISS, R));
    return s;
}

UnboundRedeemRelation::instance make_instance(AnchorSpan keys = anchors().keys,
                                              const Context& ctx_red = CTX_RED) {
    return {keys, derive(NF_KEY, ctx_red), CTX_ISS, ctx_red, CHALLENGE_DIGEST};
}

Witness honest_witness(size_t i = ISSUER, const Context& ctx_red = CTX_RED) {
    return encode_unbound_redeem_witness(NF_KEY, CTX_ISS, ctx_red, R, signature(), i);
}

std::vector<bool> evaluate(const Witness& w, const UnboundRedeemRelation::instance& x) {
    // An arbitrary QuickSilver challenge, from which the random linear combination is derived.
    static const auto chal2 = filled<UnboundRedeemParams::CONSTS::QS::CHALLENGE_BYTES>(0x50);
    PlainQS qs{w.data(), {}};
    UnboundRedeemRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    size_t n = 0;
    for (bool b : v) {
        n += b;
    }
    return n;
}

// Indices of the constraints.
constexpr size_t SELECTOR_OFF = 8 * UNBOUND_REDEEM_WIT_OFF_B; // b[u] is a bit, or zero if u >= N
constexpr size_t WEIGHT_OFF = SELECTOR_OFF + 2 * MAX_ANCHORS - 1;
constexpr size_t DERIVE_OUT_OFF =
    SELECTOR_OFF + SELECTOR_NUM_CONSTRAINTS + 2 * keccak::detail::NUM_SEGMENT_CONSTRAINTS;
constexpr size_t SIGNATURE_OFF = DERIVE_OUT_OFF + 8 * NF_BYTES;
static_assert(SIGNATURE_OFF + 1 == UNBOUND_REDEEM_NUM_CONSTRAINTS);

void set_selector(Witness& w, size_t u, bool value) {
    const size_t b = unbound_selector_bit(u);
    w[b / 8] = static_cast<uint8_t>((w[b / 8] & ~(1u << (b % 8))) | (unsigned{value} << (b % 8)));
}

} // namespace

TEST(UnboundRedeemRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto violated = evaluate(honest_witness(), make_instance());
    EXPECT_EQ(violated.size(), UnboundRedeemRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

// The issuing Anchor may be anywhere in the Anchor Set, including when it's the only Anchor.
TEST(UnboundRedeemRelation, HonestWitnessAtEveryPosition) {
    const uov::PublicKey& issuer = uov_key_pair().pk;
    const uov::PublicKey& other = anchors().keys[0];
    for (const size_t n : {size_t{1}, size_t{2}, size_t{5}}) {
        for (size_t i = 0; i < n; ++i) {
            std::vector<AnchorRef> keys(n, other);
            keys[i] = issuer;
            const auto violated = evaluate(honest_witness(i), make_instance(keys));
            EXPECT_EQ(violated.size(), UnboundRedeemRelation::NUM_CONSTRAINTS);
            EXPECT_EQ(count_violated(violated), 0u) << "n = " << n << ", i = " << i;
        }
    }
}

TEST(UnboundRedeemRelation, HonestWitnessForLargestAnchorSet) {
    std::vector<AnchorRef> keys(MAX_ANCHORS, anchors().keys[0]);
    keys.back() = uov_key_pair().pk;
    EXPECT_EQ(count_violated(evaluate(honest_witness(MAX_ANCHORS - 1), make_instance(keys))), 0u);
}

// The same token has an honest witness for every redemption context, with a different nullifier.
TEST(UnboundRedeemRelation, HonestWitnessForEveryRedemptionContext) {
    Context ctx_red = CTX_RED;
    ctx_red[0] ^= 1;
    const auto x = make_instance(anchors().keys, ctx_red);
    EXPECT_NE(x.nf, make_instance().nf);
    EXPECT_EQ(count_violated(evaluate(honest_witness(ISSUER, ctx_red), x)), 0u);

    // The witness for one redemption context doesn't satisfy the instance for another.
    const auto violated = evaluate(honest_witness(), x);
    EXPECT_GT(count_violated(violated), 0u);
}

// Every bit of the witness matters: r, nf_key, and the intermediate states determine the
// commitment and the nullifier, s determines the signature, and b determines the selected Anchor.
TEST(UnboundRedeemRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = honest_witness();
    const auto x = make_instance();
    for (size_t i = 0; i < UNBOUND_REDEEM_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, x)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(UnboundRedeemRelation, RejectsWrongSelector) {
    const auto x = make_instance();
    const auto honest = honest_witness();

    // No Anchor is selected.
    auto w = honest;
    set_selector(w, ISSUER, false);
    EXPECT_TRUE(evaluate(w, x)[WEIGHT_OFF]) << "empty selector";

    // Another Anchor is selected.
    for (size_t u = 0; u < x.anchors.size(); ++u) {
        if (u != ISSUER) {
            EXPECT_TRUE(evaluate(honest_witness(u), x)[SIGNATURE_OFF]) << "selected " << u;
        }
    }

    // Two Anchors are selected.
    w = honest;
    set_selector(w, 0, true);
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "also selected 0";

    // An index beyond the end of the Anchor Set is selected.
    w = honest;
    set_selector(w, ISSUER, false);
    set_selector(w, x.anchors.size(), true);
    EXPECT_TRUE(evaluate(w, x)[SELECTOR_OFF + x.anchors.size()]);
}

TEST(UnboundRedeemRelation, WrongInstanceViolatesAConstraint) {
    const auto w = honest_witness();

    // Each bit of nf is constrained.
    for (size_t i = 0; i < 8 * NF_BYTES; ++i) {
        auto x = make_instance();
        x.nf[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        const auto violated = evaluate(w, x);
        EXPECT_EQ(count_violated(violated), 1u) << "flipping bit " << i << " of nf";
        EXPECT_TRUE(violated[DERIVE_OUT_OFF + i]) << "flipping bit " << i << " of nf";
    }

    auto x = make_instance();
    x.ctx_iss[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_iss";

    // The redemption context is bound, even if the nullifier is adjusted to match it.
    x = make_instance();
    x.ctx_red[CTX_BYTES - 1] ^= 0x80;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_red";
    x.nf = derive(NF_KEY, x.ctx_red);
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_red and nf";

    // The issuing Anchor is moved or removed.
    auto keys = anchors().keys;
    std::swap(keys[0], keys[ISSUER]);
    EXPECT_GT(count_violated(evaluate(w, make_instance(keys))), 0u) << "moved";
    keys = anchors().keys;
    keys[ISSUER] = keys[0];
    EXPECT_GT(count_violated(evaluate(w, make_instance(keys))), 0u) << "removed";
    EXPECT_GT(count_violated(evaluate(w, make_instance(AnchorSpan(keys).first(ISSUER)))), 0u)
        << "truncated";
}

// The nullifier must be derived from the committed nullifier key: A witness for another key
// satisfies the constraints for the nullifier, but not the signature constraint.
TEST(UnboundRedeemRelation, NullifierKeyIsCommitted) {
    NfKey other = NF_KEY;
    other[0] ^= 1;
    const auto w = encode_unbound_redeem_witness(other, CTX_ISS, CTX_RED, R, signature(), ISSUER);
    auto x = make_instance();
    x.nf = derive(other, CTX_RED);
    const auto violated = evaluate(w, x);
    EXPECT_EQ(count_violated(violated), 1u);
    EXPECT_TRUE(violated[SIGNATURE_OFF]);
}

// The witness is consistent with the plaintext commitment and nullifier.
TEST(UnboundRedeemRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto w = honest_witness();
    const auto last_segment = [&w](size_t wit_off_states) {
        Kp800State state;
        std::copy_n(w.begin() + wit_off_states + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                    KP800_STATE_BYTES, state.begin());
        keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
        return state;
    };
    const auto com = last_segment(UNBOUND_REDEEM_WIT_OFF_COM_STATES);
    EXPECT_TRUE(
        std::equal(com.begin(), com.begin() + uov::M, unbound_commit(NF_KEY, CTX_ISS, R).begin()));
    const auto nf = last_segment(UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES);
    EXPECT_TRUE(std::equal(nf.begin(), nf.begin() + NF_BYTES, derive(NF_KEY, CTX_RED).begin()));
}
