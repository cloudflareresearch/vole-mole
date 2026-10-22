// VOLE-IHAT, a post-quantum Issuer-Hiding Anonymous Token (IHAT).
//
// A Client obtains a token from an Anchor, then redeems it with a Moderator. The Moderator learns
// that the token was issued by some Anchor in its trusted Anchor Set, but not which one.

#include <vole_mole/ihat.hpp>
#include <vole_mole/uov.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <print>
#include <set>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

using namespace vole_mole;

namespace {

// Contexts are application-defined 16-byte values that the parties agree on out of band. Here we
// 10*-pad a short label. Another option would be to hash the label into the context string.
ihat::Context make_context(std::string_view label) {
    if (label.size() >= ihat::CTX_BYTES) {
        throw std::invalid_argument("context label is too long");
    }
    ihat::Context ctx{};
    std::ranges::copy(label, ctx.begin());
    ctx[label.size()] = 1;
    return ctx;
}

// A Moderator, identified by its redemption context.
struct Moderator {
    std::string_view name;
    std::set<ihat::Nullifier> spent;

    // Handle a redemption request. Returns true if the token is accepted.
    bool handle_redeem(const ihat::AnchorSet& anchors, const ihat::Context& ctx_iss,
                       const ihat::RedeemRequest& request,
                       const ihat::ChallengeDigest& challenge_digest) {
        const auto ctx_red = make_context(name);
        const auto nf = ihat::finalize_redeem(anchors, request, ctx_iss, ctx_red, challenge_digest);
        if (!nf) {
            std::println("Moderator {}: rejected an invalid token", name);
            return false;
        } else if (!spent.insert(*nf).second) {
            std::println("Moderator {}: rejected a token that was already redeemed", name);
            return false;
        }
        std::println("Moderator {}: accepted a token", name);
        return true;
    }
};

} // namespace

int main() {
    // The issuance context might be used to bound the epoch in which the token was issued. The
    // Moderator might accept tokens issued in the current epoch or the previous one. In this
    // example, the context indicates Tue Oct 06 2026 00:00:00 GMT+0000 (UNIX time 1791244800) as
    // the start of the epoch and 86400 as the duration of the epoch in seconds.
    const auto ctx_iss = std::bit_cast<ihat::Context>(std::array<uint64_t, 2>{1791244800, 86400});

    // Setup.
    //
    // Key generation: Each Anchor generates a secret key, then publishes the corresponding
    // public key where it can be accessed by Clients and Moderators.
    constexpr size_t NUM_ANCHORS = 3;
    std::vector<uov::SecretKey> anchor_sks;
    for (size_t u = 0; u < NUM_ANCHORS; ++u) {
        anchor_sks.emplace_back(uov::generate_secret_key_bytes());
    }
    std::vector<uov::PublicKey> anchor_pks;
    for (const uov::SecretKey& sk : anchor_sks) {
        anchor_pks.emplace_back(sk.public_key_bytes());
    }

    // The Anchor Set trusted by the Moderator. Clients redeem tokens against this set.
    const ihat::AnchorSet anchors(anchor_pks); // anchor_pks must outlive anchors

    // The redemption context might be used to bound the identity of the Moderator. This ensures the
    // token can only be redeemed by the Moderator the Client committed to during issuance.
    Moderator moderator{.name = "example.com", .spent = {}};

    // Issue.
    //
    // Client: Request a token from an Anchor.
    constexpr size_t ISSUER = 1;
    auto [pending_token, issue_request] =
        ihat::issue_request(ctx_iss, make_context(moderator.name));

    // Anchor: Issue a token to the Client.
    const auto issue_response = ihat::issue_response(anchor_sks[ISSUER], issue_request, ctx_iss);
    if (!issue_response) {
        std::println(stderr, "Anchor: the issue request is invalid");
        return EXIT_FAILURE;
    }

    // Client: Finalize issuance.
    auto token = std::move(pending_token).finalize_issue(anchor_pks[ISSUER], *issue_response);
    if (!token) {
        std::println(stderr, "Client: the Anchor's response is invalid");
        return EXIT_FAILURE;
    }

    // Redeem.
    //
    // Client and Moderator compute the digest of the challenge that triggered redemption. Use
    // an illustrative fixed digest here. This value is bound to the redemption proof.
    const ihat::ChallengeDigest challenge_digest{0x01};

    // Client: Request redemption.
    const auto redeem_request = std::move(*token).redeem_request(
        anchors, ctx_iss, make_context(moderator.name), challenge_digest);

    // Moderator: Finalize redemption.
    if (!moderator.handle_redeem(anchors, ctx_iss, redeem_request, challenge_digest)) {
        return EXIT_FAILURE;
    }

    // Malicious Client: Try to replay the redemption request.
    if (moderator.handle_redeem(anchors, ctx_iss, redeem_request, challenge_digest)) {
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
