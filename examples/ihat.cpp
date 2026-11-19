// VOLE-IHAT, a post-quantum Issuer-Hiding Anonymous Token (IHAT).
//
// A Client obtains a token from an Anchor, then redeems it with a Moderator. The Moderator learns
// that the token was issued by some Anchor in its trusted Anchor Set, but not which one.
//
// Each redemption also reports the issuing Anchor, split between the Moderator and a third party,
// the Aggregator. Neither learns which Anchor issued any one token, but together they can compute
// how many of the tokens the Moderator accepted each Anchor issued.

#include <vole_mole/ihat.hpp>
#include <vole_mole/uov.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstdio> // IWYU pragma: keep (for stderr)
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
    std::vector<ihat::Redemption> accepted;

    // Handle a redemption request. Returns true if the token is accepted.
    bool handle_redeem(const ihat::AnchorSet& anchors, const ihat::Context& ctx_iss,
                       const ihat::RedeemRequest& request,
                       const ihat::ChallengeDigest& challenge_digest) {
        const auto ctx_red = make_context(name);
        const auto redemption =
            ihat::finalize_redeem(anchors, request, ctx_iss, ctx_red, challenge_digest);
        if (!redemption) {
            std::println("Moderator {}: rejected an invalid token", name);
            return false;
        } else if (!spent.insert(redemption->nf).second) {
            std::println("Moderator {}: rejected a token that was already redeemed", name);
            return false;
        }
        std::println("Moderator {}: accepted a token", name);
        accepted.push_back(*redemption);
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
    Moderator moderator{.name = "example.com", .spent = {}, .accepted = {}};

    // The reports the Aggregator receives from Clients. In practice, each Client would encrypt its
    // report to the Aggregator, e.g., and send it via the Moderator, so that the Aggregator doesn't
    // learn who sent it.
    std::vector<ihat::Report> aggregator_reports;

    // Several Clients each obtain a token from an Anchor and redeem it.
    constexpr std::array<size_t, 5> ISSUERS = {1, 0, 1, 2, 1};
    for (const size_t issuer : ISSUERS) {
        // Issue.
        //
        // Client: Request a token from an Anchor.
        auto [pending_token, issue_request] =
            ihat::issue_request(ctx_iss, make_context(moderator.name));

        // Anchor: Issue a token to the Client.
        const auto issue_response =
            ihat::issue_response(anchor_sks[issuer], issue_request, ctx_iss);
        if (!issue_response) {
            std::println(stderr, "Anchor: the issue request is invalid");
            return EXIT_FAILURE;
        }

        // Client: Finalize issuance.
        auto token = std::move(pending_token).finalize_issue(anchor_pks[issuer], *issue_response);
        if (!token) {
            std::println(stderr, "Client: the Anchor's response is invalid");
            return EXIT_FAILURE;
        }

        // Redeem.
        //
        // Client and Moderator compute the digest of the challenge that triggered redemption. Use
        // an illustrative fixed digest here. This value is bound to the redemption proof.
        const ihat::ChallengeDigest challenge_digest{0x01};

        // Client: Request redemption, sending the request to the Moderator and the report to the
        // Aggregator.
        const auto [redeem_request, report] = std::move(*token).redeem_request(
            anchors, ctx_iss, make_context(moderator.name), challenge_digest);
        aggregator_reports.push_back(report);

        // Moderator: Finalize redemption.
        if (!moderator.handle_redeem(anchors, ctx_iss, redeem_request, challenge_digest)) {
            return EXIT_FAILURE;
        }

        // Malicious Client: Try to replay the redemption request.
        if (moderator.handle_redeem(anchors, ctx_iss, redeem_request, challenge_digest)) {
            return EXIT_FAILURE;
        }
    }

    // Aggregate.
    //
    // Moderator: Vouch for the tags of the redemptions it accepted.
    std::multiset<ihat::ReportTag> vouched;
    for (const ihat::Redemption& redemption : moderator.accepted) {
        vouched.insert(redemption.tag);
    }

    // Aggregator: Count the share of each report whose tag the Moderator vouched for, at most once
    // per vouched tag, and tell the Moderator which tags it counted.
    ihat::HistogramShare aggregator_agg{};
    std::multiset<ihat::ReportTag> counted;
    for (const ihat::Report& report : aggregator_reports) {
        const ihat::OpenedReport opened = ihat::open_report(report);
        const auto it = vouched.find(opened.tag);
        if (it == vouched.end()) {
            std::println("Aggregator: discarded a report the Moderator didn't vouch for");
            continue;
        }
        vouched.erase(it);
        counted.insert(opened.tag);
        ihat::aggregate(aggregator_agg, opened.share);
    }

    // Moderator: Count the share of each redemption whose tag the Aggregator counted.
    ihat::HistogramShare moderator_agg{};
    for (const ihat::Redemption& redemption : moderator.accepted) {
        const auto it = counted.find(redemption.tag);
        if (it != counted.end()) {
            counted.erase(it);
            ihat::aggregate(moderator_agg, redemption.share);
        }
    }

    // Moderator and Aggregator: Combine the aggregates into the histogram.
    ihat::HistogramShare histogram = moderator_agg;
    ihat::aggregate(histogram, aggregator_agg);
    for (size_t u = 0; u < anchors.size(); ++u) {
        std::println("Anchor {} issued {} of the accepted tokens", u, histogram[u]);
    }
    if (histogram[0] != 1 || histogram[1] != 3 || histogram[2] != 1) {
        std::println(stderr, "unexpected histogram");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
