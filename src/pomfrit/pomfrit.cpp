#include "vole_mole/pomfrit.hpp"

#include "dst.hpp"
#include "pomfrit/redeem.hpp"
#include "uov/public_key.hpp"
#include "voleith.hpp"

#include "hash.hpp" // from faest-arch-opt

extern "C" {
#include "randomness.h" // from faest-arch-opt
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <utility>

namespace vole_mole::pomfrit {

using detail::ProofView;
using detail::RedeemRelation;
using detail::WIT_OFF_R;
using uov::detail::PublicKeyAccess;

namespace {

using namespace vole_mole::detail;

constexpr size_t REFRESHER_BYTES = 2 * RedeemRelation::params::secpar_bytes;
using Refresher = std::array<uint8_t, REFRESHER_BYTES>;

// The blind signature consists of the VOLEitH proof, the refresher_com (denoted rand_com in
// PomFRIT <https://ia.cr/2026/109>), and the refresher (rand).
constexpr size_t SIG_OFF_PROOF = 0;
constexpr size_t SIG_OFF_PROOF_CORRECTION = SIG_OFF_PROOF + ProofView::OFFSET_CORRECTION;
constexpr size_t SIG_OFF_REFRESHER_COM = SIG_OFF_PROOF + PROOF_BYTES<RedeemRelation>;
constexpr size_t SIG_OFF_REFRESHER = SIG_OFF_REFRESHER_COM + REFRESHER_BYTES;
static_assert(SIGNATURE_BYTES == SIG_OFF_REFRESHER + REFRESHER_BYTES);
static_assert(WIT_OFF_R == 0 && ProofView::SIZE_CORRECTION == WITNESS_BYTES<RedeemRelation>);

auto sig_proof(BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_PROOF, PROOF_BYTES<RedeemRelation>>();
}
auto sig_proof(const BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_PROOF, PROOF_BYTES<RedeemRelation>>();
}
auto sig_witness_prefix_correction(const BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_PROOF_CORRECTION, uov::M>();
}
auto sig_refresher_com(BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_REFRESHER_COM, REFRESHER_BYTES>();
}
auto sig_refresher_com(const BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_REFRESHER_COM, REFRESHER_BYTES>();
}
auto sig_refresher(BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_REFRESHER, REFRESHER_BYTES>();
}
auto sig_refresher(const BlindSignature& sig) {
    return std::span(sig).subspan<SIG_OFF_REFRESHER, REFRESHER_BYTES>();
}

// PomFRIT <https://ia.cr/2026/109>, Appendix D.3: rand_com = H(rand)
void commit_to_refresher(std::span<uint8_t, REFRESHER_BYTES> refresher_com,
                         std::span<const uint8_t, REFRESHER_BYTES> refresher) {
    constexpr auto S = relation_params<RedeemRelation>::secpar_v;
    faest::hash_state hasher;
    hasher.init(S);
    hasher.update(POMFRIT_REFRESHER_DST);
    hasher.update(refresher);
    hasher.finalize(refresher_com);
}

// PomFRIT <https://ia.cr/2026/109>, Algorithm 2: h <- H(pk, pi1, msg), where pi1 is the output of
// the VOLE generation step, including the corrections for the target mask.
//
// TODO(cjpatton) Unlike the paper, the Client samples r for the instance P(s) = h + r rather
// than borrowing it from the VOLE generator. This is intended to simplify PomFRIT by not
// treating the borrowed VOLEs as a special case. (The cost is sending an additional uov::M
// corrections in the proof.) On the other hand, it's now necessary to bind the additional
// corrections to h. Otherwise, the Client could easily forge many signatures for the same
// target. Discuss this change with the PomFRIT and FAEST authors and see what they might
// prefer.
uov::Target hash_to_target(const uov::PublicKey& pk, const BlindSignature& sig,
                           std::span<const uint8_t> chal1, std::span<const uint8_t> msg) {
    constexpr auto S = relation_params<RedeemRelation>::secpar_v;
    const ProofView proof = sig_proof(sig).data();
    uov::Target h;
    faest::hash_state hasher;
    hasher.init(S);
    hasher.update(POMFRIT_TARGET_DST);
    hasher.update(PublicKeyAccess::digest(pk));
    hasher.update(chal1);
    hasher.update(proof.vole_check_proof());
    hasher.update(sig_witness_prefix_correction(sig));
    hasher.update(msg);
    hasher.finalize(h);
    return h;
}

} // namespace

struct PendingBlindSignature::Impl {
    uov::detail::PublicKeyDigest pk_digest;
    IssueRequest t;
    uov::Target h;
    BlindSignature sig;
    PendingProof<RedeemRelation> pending;
};

PendingBlindSignature::PendingBlindSignature(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
PendingBlindSignature::PendingBlindSignature(PendingBlindSignature&&) noexcept = default;
PendingBlindSignature& PendingBlindSignature::operator=(PendingBlindSignature&&) noexcept = default;
PendingBlindSignature::~PendingBlindSignature() = default;

// PomFRIT <https://ia.cr/2026/109>: Algorithm 2, Sig1()
IssueRequestResult issue_request_with_seed(const uov::PublicKey& pk, std::span<const uint8_t> msg,
                                           const Seed& seed) {
    BlindSignature sig{};

    // Expand the seed into the prover seed (rho), the refresher, and the target mask (r).
    ProveSeed<RedeemRelation> rho;
    const auto refresher = sig_refresher(sig);
    uov::Target r;
    {
        faest::hash_state xof;
        xof.init(RedeemRelation::params::secpar_v);
        xof.update(POMFRIT_SEED_DST);
        xof.update(seed);
        Keccak_HashFinal(&xof.ctx, nullptr);
        Keccak_HashSqueeze(&xof.ctx, rho.data(), 8 * rho.size());
        Keccak_HashSqueeze(&xof.ctx, refresher.data(), 8 * refresher.size());
        Keccak_HashSqueeze(&xof.ctx, r.data(), 8 * r.size());
    }

    // Line 4: Step 1 of proof generation (pi1). The witness prefix (r) is known; the instance
    // depends on pi1, and the witness suffix (s) comes from the Issuer's response.
    const auto refresher_com = sig_refresher_com(sig);
    commit_to_refresher(refresher_com, refresher);
    auto pending = voleith_vole_gen<RedeemRelation>(sig_proof(sig), nullptr, r, rho, refresher_com);

    // Line 5: Compute the target (binding it to pi1).
    const uov::Target h = hash_to_target(pk, sig, pending.chal1, msg);

    // Line 6: Compute the masked target.
    IssueRequest t;
    for (size_t i = 0; i < t.size(); ++i) {
        t[i] = h[i] ^ r[i];
    }

    auto impl = std::unique_ptr<PendingBlindSignature::Impl>(new PendingBlindSignature::Impl{
        PublicKeyAccess::digest(pk), t, h, sig, std::move(pending)});
    return {PendingBlindSignature(std::move(impl)), t};
}

IssueRequestResult issue_request(const uov::PublicKey& pk, std::span<const uint8_t> msg) {
    Seed seed;
    if (rand_bytes(seed.data(), seed.size()) != 0) {
        throw std::runtime_error("failed to get randomness from the operating system");
    }

    return issue_request_with_seed(pk, msg, seed);
}

// PomFRIT <https://ia.cr/2026/109>: Algorithm 2, Sig2()
IssueResponse issue_response(const uov::SecretKey& sk, const IssueRequest& request) {
    return sk.derive_preimage(request); // Line 9
}

// PomFRIT <https://ia.cr/2026/109>: Algorithm 2, Sig3()
std::optional<BlindSignature>
PendingBlindSignature::finalize_issue(const uov::PublicKey& pk, const IssueResponse& response) && {
    if (!impl_) {
        throw std::logic_error("PomFRIT: pending blind signature was moved from");
    }

    if (PublicKeyAccess::digest(pk) != impl_->pk_digest) {
        throw std::invalid_argument(
            "PomFRIT: public key differs from the one in the issue request");
    }

    const std::unique_ptr<Impl> impl = std::move(impl_);

    // Line 12: Check that the signature (s) was produced by the Issuer.
    if (pk.eval(response) != impl->t) {
        return std::nullopt;
    }

    // Lines 13-14: Step 2 of proof generation (pi2). Bind the instance and the witness suffix (s);
    // the witness prefix (r) was committed in step 1.
    voleith_prove_commit<RedeemRelation>(sig_proof(impl->sig), {&pk, impl->h}, response,
                                         std::move(impl->pending), sig_refresher(impl->sig));
    return impl->sig;
}

// PomFRIT <https://ia.cr/2026/109>: Algorithm 2, Verify()
bool verify(const uov::PublicKey& pk, std::span<const uint8_t> msg, const BlindSignature& sig) {
    const auto proof = sig_proof(sig);
    const auto refresher_com = sig_refresher_com(sig);
    const auto refresher = sig_refresher(sig);

    Refresher expected_refresher_com;
    commit_to_refresher(expected_refresher_com, refresher);
    if (!std::ranges::equal(expected_refresher_com, refresher_com)) {
        return false;
    }
    auto pending = voleith_vole_reconstruct<RedeemRelation>(proof, nullptr, refresher_com);
    if (!pending) {
        return false;
    }

    const uov::Target h = hash_to_target(pk, sig, pending->chal1, msg);

    return voleith_verify_commit<RedeemRelation>(proof, {&pk, h}, std::move(*pending), refresher);
}

} // namespace vole_mole::pomfrit
