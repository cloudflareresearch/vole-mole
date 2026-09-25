#include "vole_mole/moussaka.hpp"

#include "moussaka/issue.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <span>

using namespace vole_mole;
using namespace vole_mole::moussaka;
using vole_mole::moussaka::detail::verify_issue_request;
using vole_mole::test::filled;
using vole_mole::test::to_hex;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);
const Seed SEED = filled<SEED_BYTES>(0x50);

IssueRequestResult make_request(const Seed& seed = SEED) {
    return issue_request_with_seed(CTX_ISS, CTX_RED, seed);
}

} // namespace

TEST(IssueRequest, WitnessIsConsistent) {
    using namespace moussaka::detail;
    const auto w = encode_issue_witness(NF, CTX_ISS, CTX_RED, R);

    // Re-run the last segment from the last committed state; it must yield the commitment.
    Kp800State state;
    std::copy_n(w.begin() + WIT_OFF_STATES + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, NUM_COMMITTED_STATES * ROUNDS_PER_SEGMENT, ROUNDS_PER_SEGMENT);
    const Commitment t = commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_EQ(to_hex(t), to_hex(std::span(state).first<UOV_M>()));
}

TEST(IssueRequest, Verifies) {
    const auto res = make_request();
    EXPECT_TRUE(verify_issue_request(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<UOV_M>()),
              to_hex(commit(res.pending_token.nf, CTX_ISS, CTX_RED, res.pending_token.r)));
}

TEST(IssueRequest, RandomizedVerifies) {
    const auto res = issue_request(CTX_ISS, CTX_RED);
    EXPECT_TRUE(verify_issue_request(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<UOV_M>()),
              to_hex(commit(res.pending_token.nf, CTX_ISS, CTX_RED, res.pending_token.r)));
}

TEST(IssueRequest, IsDeterministicGivenSeed) {
    const auto a = make_request();
    const auto b = make_request();
    EXPECT_EQ(to_hex(a.pending_token.nf), to_hex(b.pending_token.nf));
    EXPECT_EQ(to_hex(a.pending_token.r), to_hex(b.pending_token.r));
    EXPECT_EQ(to_hex(std::span(a.request).first<UOV_M>()),
              to_hex(std::span(b.request).first<UOV_M>()));
    EXPECT_TRUE(std::ranges::equal(std::span(a.request).last<ISSUE_PROOF_BYTES>(),
                                   std::span(b.request).last<ISSUE_PROOF_BYTES>()));

    // A different seed changes all of the randomness.
    const auto c = make_request(filled<SEED_BYTES>(0x99));
    EXPECT_NE(to_hex(a.pending_token.nf), to_hex(c.pending_token.nf));
    EXPECT_NE(to_hex(a.pending_token.r), to_hex(c.pending_token.r));
    EXPECT_NE(to_hex(std::span(a.request).first<UOV_M>()),
              to_hex(std::span(c.request).first<UOV_M>()));
    EXPECT_FALSE(std::ranges::equal(std::span(a.request).last<ISSUE_PROOF_BYTES>(),
                                    std::span(c.request).last<ISSUE_PROOF_BYTES>()));
    EXPECT_TRUE(verify_issue_request(c.request, CTX_ISS));
}

// Known answer for the seed expansion: nf || r are the first 40 bytes of
// SHAKE128("mous" || VERSION || "s0" || seed). Generated with Python:
//
//   hashlib.shake_128(b"mous" + bytes([0]) + b"s0" + bytes(range(0x50, 0x70))).digest(40)
TEST(IssueRequest, SeedExpansion) {
    const auto res = make_request(); // with SEED = 0x50, 0x51, ..., 0x6f
    EXPECT_EQ(to_hex(res.pending_token.nf), "5f45ce3c1d41bbcba4d2363195d69d965e5c5b60ab69d68f");
    EXPECT_EQ(to_hex(res.pending_token.r), "4ea25e5192a154af3c2c0f63f32cdd6a");
}

TEST(IssueRequest, RejectWrongCtxIss) {
    const auto res = make_request();
    Context ctx = CTX_ISS;
    ctx[5] ^= 1;
    EXPECT_FALSE(verify_issue_request(res.request, ctx));
}

TEST(IssueRequest, RejectWrongCommitment) {
    const auto res = make_request();
    IssueRequest req = res.request;
    req[0] ^= 0x80;
    EXPECT_FALSE(verify_issue_request(req, CTX_ISS));
}

// A commitment to different values (with a valid proof for those) doesn't transfer.
TEST(IssueRequest, RejectMismatchedProof) {
    const auto a = make_request();
    const auto b = issue_request(CTX_ISS, CTX_RED);
    IssueRequest req = a.request;
    std::ranges::copy(std::span(b.request).last<ISSUE_PROOF_BYTES>(),
                      std::span(req).last<ISSUE_PROOF_BYTES>().begin());
    EXPECT_FALSE(verify_issue_request(req, CTX_ISS));
}

TEST(IssueRequest, RejectTamperedProof) {
    const auto res = make_request();
    IssueRequest req = res.request;

    // Flip one bit in (at least) every field of the proof. See faest::faest_signature for the
    // layout.
    for (size_t i = 0; i < ISSUE_PROOF_BYTES; i += 97) {
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x04;
        EXPECT_FALSE(verify_issue_request(req, CTX_ISS)) << "flipped a bit of byte " << i;
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x04;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = ISSUE_PROOF_BYTES - 36; i < ISSUE_PROOF_BYTES; ++i) {
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x01;
        EXPECT_FALSE(verify_issue_request(req, CTX_ISS)) << "flipped a bit of byte " << i;
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x01;
    }
    EXPECT_TRUE(verify_issue_request(req, CTX_ISS));
}

// Every mask's row of the CRT VOLECommit's c_mult matrix is bound by the proof.
TEST(IssueRequest, RejectTamperedCMult) {
    using P = vole_mole::moussaka::detail::IssueParams;
    constexpr size_t N_MASK = P::CONSTS::CRT_NUM_MASK;
    constexpr size_t N_MULT_BYTES = P::CONSTS::CRT_NUM_MULT_BYTES;
    static_assert(N_MASK == vole_mole::moussaka::detail::ISSUE_QS_DEGREE - 1 + 4);

    const auto res = make_request();
    IssueRequest req = res.request;
    const auto c_mult =
        faest::mutable_faest_signature<P>(std::span(req).last<ISSUE_PROOF_BYTES>().data())
            .vole_commitment_cmult();
    for (size_t m = 0; m < N_MASK; ++m) {
        c_mult[m * N_MULT_BYTES] ^= 0x01;
        EXPECT_FALSE(verify_issue_request(req, CTX_ISS)) << "flipped a bit of row " << m;
        c_mult[m * N_MULT_BYTES] ^= 0x01;
    }
    EXPECT_TRUE(verify_issue_request(req, CTX_ISS));
}
