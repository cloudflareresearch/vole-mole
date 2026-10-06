#include "vole_mole/pomfrit.hpp"
#include "vole_mole/uov.hpp"

#include "pomfrit/redeem.hpp" // internal
#include "pomfrit/seeded.hpp" // internal
#include "voleith.hpp"        // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::pomfrit;
using vole_mole::pomfrit::detail::issue_request_with_seed;
using vole_mole::pomfrit::detail::Seed;
using vole_mole::pomfrit::detail::SEED_BYTES;
using vole_mole::test::filled;
using vole_mole::test::to_hex;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

// The Client's state must not be copied; see PendingBlindSignature.
static_assert(!std::is_copy_constructible_v<PendingBlindSignature>);
static_assert(std::is_nothrow_move_constructible_v<PendingBlindSignature>);

namespace {

using pomfrit::detail::RedeemRelation;
using Proof = pomfrit::detail::ProofView;

// The proof has FAEST's layout.
static_assert(Proof::SIZE_CORRECTION == uov::M + uov::N);

// The signature is the proof, followed by refresher_com and refresher, 32 bytes each.
constexpr size_t REFRESHER_BYTES = 32;
constexpr size_t SIG_OFF_REFRESHER = SIGNATURE_BYTES - REFRESHER_BYTES;
constexpr size_t SIG_OFF_REFRESHER_COM = SIG_OFF_REFRESHER - REFRESHER_BYTES;
static_assert(SIG_OFF_REFRESHER_COM == vole_mole::detail::PROOF_BYTES<RedeemRelation>);

std::span<const uint8_t> sig_field(const BlindSignature& sig, size_t offset, size_t size) {
    return std::span(sig).subspan(offset, size);
}

const IssueRequest T = filled<uov::M>(0x70);
const Seed SEED = filled<SEED_BYTES>(0x80);

constexpr std::string_view MSG_STR = "the message to be signed";
const std::span<const uint8_t> MSG(reinterpret_cast<const uint8_t*>(MSG_STR.data()),
                                   MSG_STR.size());

BlindSignature issue(const uov::PublicKey& pk, const uov::SecretKey& sk,
                     std::span<const uint8_t> msg, const Seed& seed = SEED) {
    auto [pending, request] = issue_request_with_seed(pk, msg, seed);
    const IssueResponse response = issue_response(sk, request);
    auto sig = std::move(pending).finalize_issue(pk, response);
    EXPECT_TRUE(sig.has_value());
    return *sig;
}

} // namespace

TEST(IssueResponse, IsPreimageOfRequest) {
    const auto& [pk, sk] = uov_key_pair();
    const IssueResponse s = issue_response(sk, T);
    EXPECT_EQ(to_hex(pk.eval(s)), to_hex(T));
}

TEST(Pomfrit, Verifies) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig = issue(pk, sk, MSG);
    EXPECT_TRUE(verify(pk, MSG, sig));
}

TEST(Pomfrit, VerifiesEmptyMessage) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig = issue(pk, sk, {});
    EXPECT_TRUE(verify(pk, {}, sig));
    EXPECT_FALSE(verify(pk, MSG, sig));
}

TEST(Pomfrit, RandomSeed) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request(pk, MSG);
    auto sig = std::move(pending).finalize_issue(pk, issue_response(sk, request));
    ASSERT_TRUE(sig.has_value());
    EXPECT_TRUE(verify(pk, MSG, *sig));
}

TEST(Pomfrit, IssueRequestIsDeterministic) {
    const auto& [pk, sk] = uov_key_pair();
    const auto [pending1, request1] = issue_request_with_seed(pk, MSG, SEED);
    const auto [pending2, request2] = issue_request_with_seed(pk, MSG, SEED);
    EXPECT_EQ(to_hex(request1), to_hex(request2));

    // Another seed yields another request for the same message.
    const auto [pending3, request3] = issue_request_with_seed(pk, MSG, filled<SEED_BYTES>(0x81));
    EXPECT_NE(to_hex(request1), to_hex(request3));
}

TEST(Pomfrit, RejectsWrongMessage) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig = issue(pk, sk, MSG);
    auto msg = std::vector<uint8_t>(MSG.begin(), MSG.end());
    msg[0] ^= 1;
    EXPECT_FALSE(verify(pk, msg, sig));
}

TEST(Pomfrit, RejectsWrongKey) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig = issue(pk, sk, MSG);
    const UovKeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    EXPECT_FALSE(verify(other.pk, MSG, sig));
}

// Flipping a bit in any field of the signature invalidates it.
TEST(Pomfrit, RejectsTamperedSignature) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig = issue(pk, sk, MSG);
    const std::array<std::pair<const char*, size_t>, 12> fields = {{
        {"vole_commitment_corrections", Proof::OFFSET_VOLE_COMMITMENT_CORRECTIONS},
        {"vole_commitment_cmult", Proof::OFFSET_VOLE_COMMITMENT_CMULT},
        {"vole_check_proof", Proof::OFFSET_VOLE_CHECK_PROOF},
        {"correction of r", Proof::OFFSET_CORRECTION},
        {"correction of s", Proof::OFFSET_CORRECTION + uov::M},
        {"qs_proof", Proof::OFFSET_QS_PROOF},
        {"veccom_open", Proof::OFFSET_VECCOM_OPEN},
        {"delta", Proof::OFFSET_DELTA},
        {"iv_pre", Proof::OFFSET_IV_PRE},
        {"grinding_ctr", Proof::OFFSET_GRINDING_CTR},
        {"refresher_com", SIG_OFF_REFRESHER_COM},
        {"refresher", SIG_OFF_REFRESHER},
    }};
    for (const auto& [name, offset] : fields) {
        BlindSignature tampered = sig;
        tampered[offset] ^= 1;
        EXPECT_FALSE(verify(pk, MSG, tampered)) << name;
    }
    BlindSignature tampered = sig;
    tampered.back() ^= 0x80;
    EXPECT_FALSE(verify(pk, MSG, tampered)) << "last byte";
}

// The Client aborts if the Issuer's response isn't a preimage of the request.
TEST(Pomfrit, RejectsInvalidResponse) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request_with_seed(pk, MSG, SEED);
    IssueRequest other = request;
    other[0] ^= 1;
    EXPECT_FALSE(std::move(pending).finalize_issue(pk, issue_response(sk, other)).has_value());
}

TEST(Pomfrit, FinalizeIssueConsumesState) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request_with_seed(pk, MSG, SEED);
    auto moved = std::move(pending);
    EXPECT_THROW((void)std::move(pending).finalize_issue(pk, issue_response(sk, request)),
                 std::logic_error);
    EXPECT_TRUE(std::move(moved).finalize_issue(pk, issue_response(sk, request)).has_value());
}

// Finalizing with a different key than the request's is a caller error. It doesn't consume the
// state, so the caller can retry with the right key.
TEST(Pomfrit, FinalizeIssueRejectsWrongKey) {
    const auto& [pk, sk] = uov_key_pair();
    const UovKeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    auto [pending, request] = issue_request_with_seed(pk, MSG, SEED);
    const IssueResponse response = issue_response(sk, request);
    EXPECT_THROW((void)std::move(pending).finalize_issue(other.pk, response),
                 std::invalid_argument);
    auto sig = std::move(pending).finalize_issue(pk, response);
    ASSERT_TRUE(sig.has_value());
    EXPECT_TRUE(verify(pk, MSG, *sig));
}

// pi1 is fresh for each signature, even for the same message.
TEST(Pomfrit, FirstPartDependsOnSeed) {
    const auto& [pk, sk] = uov_key_pair();
    const BlindSignature sig1 = issue(pk, sk, MSG, SEED);
    const BlindSignature sig2 = issue(pk, sk, MSG, filled<SEED_BYTES>(0x81));
    const auto vole_commitment = [](const BlindSignature& sig) {
        return to_hex(sig_field(sig, Proof::OFFSET_VOLE_COMMITMENT, Proof::SIZE_VOLE_COMMITMENT));
    };
    const auto iv_pre = [](const BlindSignature& sig) {
        return to_hex(sig_field(sig, Proof::OFFSET_IV_PRE, Proof::SIZE_IV_PRE));
    };
    EXPECT_NE(vole_commitment(sig1), vole_commitment(sig2));
    EXPECT_NE(iv_pre(sig1), iv_pre(sig2));
    // The correction of r, which is part of pi_1 because it's hashed into h.
    EXPECT_NE(to_hex(sig_field(sig1, Proof::OFFSET_CORRECTION, uov::M)),
              to_hex(sig_field(sig2, Proof::OFFSET_CORRECTION, uov::M)));
    EXPECT_NE(to_hex(std::span(sig1).subspan(SIG_OFF_REFRESHER_COM, REFRESHER_BYTES)),
              to_hex(std::span(sig2).subspan(SIG_OFF_REFRESHER_COM, REFRESHER_BYTES)));
}
