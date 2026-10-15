#include "vole_mole/pomfrit.hpp"
#include "vole_mole/uov.hpp"

#include "pomfrit/redeem.hpp" // internal
#include "pomfrit/seeded.hpp" // internal
#include "voleith.hpp"        // internal

#include "test.hpp"

#include "block.hpp"       // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "util.hpp"        // from faest-arch-opt
#include "vector_com.inc"  // from faest-arch-opt
#include "vole_commit.hpp" // from faest-arch-opt
#include "vole_commit.inc" // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
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
    const std::array<std::pair<const char*, size_t>, 13> fields = {{
        {"vole_commitment_corrections", Proof::OFFSET_VOLE_COMMITMENT_CORRECTIONS},
        {"vole_commitment_corrections (label rows)",
         Proof::OFFSET_VOLE_COMMITMENT_CORRECTIONS + pomfrit::detail::REDEEM_WITNESS_BYTES},
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

namespace {

using RedeemParams = RedeemRelation::params;
using RedeemConsts = RedeemParams::CONSTS;
constexpr auto LAMBDA = RedeemParams::secpar_v;
constexpr size_t LAMBDA_BYTES = RedeemParams::secpar_bytes;
using Label = faest::block_secpar<LAMBDA>;

// The CRT VOLE masks use the lambda VOLE rows directly after the witness.
static_assert(!RedeemConsts::REUSE_CRT_WITNESS);
static_assert(RedeemConsts::CRT_LABEL_ROW_OFFSET == 8 * pomfrit::detail::REDEEM_WITNESS_BYTES);
static_assert(RedeemConsts::VOLE_CORRECTION_BYTES ==
              pomfrit::detail::REDEEM_WITNESS_BYTES + LAMBDA_BYTES);

bool label_eq(const Label& a, const Label& b) { return std::memcmp(&a, &b, sizeof(a)) == 0; }

} // namespace

// The verifier learns one of the two labels L0, L1 = L0 + offset of each gate of the CRT VOLE mask
// circuit. If the offset were u = d + r on the first witness rows, the Issuer, which can derive r,
// could compute the other label too, unmask the proof, and link it to its issuance.
TEST(Pomfrit, LabelOffsetIsNotDeterminedByCorrectionAndWitness) {
    using namespace faest;
    const uov::Target r = filled<uov::M>(0x90);

    // The prover's VOLE commitment (without the CRT lift, which overwrites V in place).
    auto sender = vole_commit_data<RedeemParams, false>::alloc().value();
    Label seed;
    block128 iv;
    const auto seed_bytes = filled<LAMBDA_BYTES>(0xa0);
    const auto iv_bytes = filled<sizeof(block128)>(0xb0);
    std::memcpy(&seed, seed_bytes.data(), sizeof(seed));
    std::memcpy(&iv, iv_bytes.data(), sizeof(iv));
    std::array<uint8_t, RedeemConsts::VOLE_COMMIT_CORRECTIONS_SIZE> corrections;
    std::array<uint8_t, RedeemConsts::VOLE_COMMIT_CHECK_SIZE> check;
    std::array<uint8_t, RedeemParams::delta_bits_v * RedeemConsts::VOLE_EXTRA_BYTES> u_extra;
    faest::detail::vole_commit_impl<RedeemParams>(
        seed, iv, sender.forest().data(), sender.hashed_leaves().data(), sender.u().data(),
        sender.v_columns().data(), corrections.data(), check.data(), u_extra.data());

    // Open at some Delta and reconstruct the verifier's VOLE keys.
    hash_state_x4 grinding_hasher;
    grinding_hasher.init(LAMBDA);
    grinding_hasher.update_1(r);
    std::array<uint8_t, LAMBDA_BYTES> delta{};
    std::array<uint8_t, RedeemParams::bavc_t::OPEN_SIZE> opening{};
    uint32_t counter = 0;
    ASSERT_TRUE(grind_and_open<RedeemParams::bavc_t>(sender.forest().data(),
                                                     sender.hashed_leaves().data(), delta.data(),
                                                     opening.data(), &grinding_hasher, &counter));
    std::array<uint8_t, RedeemParams::delta_bits_v> delta_bits{};
    expand_bits_to_bytes(delta_bits.data(), RedeemParams::delta_bits_v, delta.data());
    auto receiver = vole_commit_data<RedeemParams, true>::alloc().value();
    ASSERT_TRUE(vole_reconstruct<RedeemParams>(iv, receiver, delta_bits.data(), corrections,
                                               opening, check));

    constexpr size_t N_MULT = RedeemConsts::CRT_NUM_MULT;
    std::array<Label, N_MULT> l0;
    std::array<Label, N_MULT> l_verifier;
    faest::detail::crt_labels<RedeemParams>(l0.data(), sender.v_columns().data());
    faest::detail::crt_labels<RedeemParams>(l_verifier.data(), receiver.q_columns().data());
    const Label offset = faest::detail::crt_label_offset<RedeemParams>(sender.u().data());

    // The offset is u on the label rows.
    const auto u = sender.u_bytes();
    EXPECT_EQ(to_hex(std::span(reinterpret_cast<const uint8_t*>(&offset), LAMBDA_BYTES)),
              to_hex(u.subspan(pomfrit::detail::REDEEM_WITNESS_BYTES, LAMBDA_BYTES)));

    // The correction d[0..lambda) of r[0..lambda), as in the proof.
    std::array<uint8_t, LAMBDA_BYTES> d_plus_r;
    for (size_t i = 0; i < LAMBDA_BYTES; ++i) {
        const uint8_t d_i = u[i] ^ r[i];
        d_plus_r[i] = d_i ^ r[i];
    }
    const Label guess_offset = Label::load(d_plus_r.data());

    std::array<size_t, 2> num_gamma{};
    for (size_t e = 0; e < N_MULT; ++e) {
        const Label l1 = l0[e] ^ offset;
        const bool gamma0 = label_eq(l_verifier[e], l0[e]);
        const bool gamma1 = label_eq(l_verifier[e], l1);
        ASSERT_TRUE(gamma0 != gamma1) << e;
        ++num_gamma[gamma1 ? 1 : 0];

        const Label guess = l_verifier[e] ^ guess_offset;
        EXPECT_FALSE(label_eq(guess, l0[e]) || label_eq(guess, l1)) << e;
    }
    // Delta selects both labels for some gates.
    EXPECT_GT(num_gamma[0], 0U);
    EXPECT_GT(num_gamma[1], 0U);
}

// The same for an actual proof.
TEST(Pomfrit, ProofLabelOffsetIsNotCorrectionPlusR) {
    using vole_mole::detail::PROOF_BYTES;
    const uov::Target r = filled<uov::M>(0x90);
    std::array<uint8_t, PROOF_BYTES<RedeemRelation>> proof{};
    const auto pending = vole_mole::detail::voleith_vole_gen<RedeemRelation>(
        proof, nullptr, r, filled<vole_mole::detail::PROVE_SEED_BYTES<RedeemRelation>>(0xa0));

    const Proof view(proof.data());
    std::array<uint8_t, LAMBDA_BYTES> d_plus_r;
    for (size_t i = 0; i < LAMBDA_BYTES; ++i) {
        d_plus_r[i] = view.correction()[i] ^ r[i];
    }
    const Label offset =
        faest::detail::crt_label_offset<RedeemParams>(pending.vole_com_data.u().data());
    EXPECT_NE(to_hex(std::span(reinterpret_cast<const uint8_t*>(&offset), LAMBDA_BYTES)),
              to_hex(d_plus_r));
    // d has no entries for the label rows.
    static_assert(Proof::SIZE_CORRECTION == pomfrit::detail::REDEEM_WITNESS_BYTES);
}
