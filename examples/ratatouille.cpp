// Ratatouille, a post-quantum Anonymous Credit Token (ACT).
//
// The Client requests a token with an initial state (i.e., number of credits) known to the Issuer.
// When the Client spends a token, it gets a token in return with an updated state. The Issuer knows
// the state change (i.e., how many credits were spent), but doesn't know the state.

#include <vole_mole/ratatouille.hpp>
#include <vole_mole/uov.hpp>

#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <print>
#include <set>
#include <utility>

using namespace vole_mole;
using ratatouille::Credits;

int main() {
    // The issuance context might be used to bound the epoch in which the token was issued. The
    // Issuer might accept tokens issued in the current epoch or the previous one. In this
    // example, the context indicates Tue Oct 06 2026 00:00:00 GMT+0000 (UNIX time 1791244800) as
    // the start of the epoch and 86400 as the duration of the epoch in seconds.
    const auto ctx_iss =
        std::bit_cast<ratatouille::Context>(std::array<uint64_t, 2>{1791244800, 86400});

    // Setup.
    //
    // Key generation.
    const uov::SecretKey sk(uov::generate_secret_key_bytes());
    const uov::PublicKey pk(sk.public_key());

    // The Issuer (in particular, a MOLE Moderator) remembers the nullifier of every token that's
    // spent, for as long as it accepts tokens for the given key and issuance context.
    std::set<ratatouille::Nullifier> spent;

    // Handle a spend request. Returns the response to send to the Client, or std::nullopt to reject
    // the request.
    const auto handle_spend = [&](const ratatouille::SpendRequest& request, Credits price,
                                  Credits refund) -> std::optional<ratatouille::SpendResponse> {
        const auto result = ratatouille::spend_response(sk, request, ctx_iss, refund);
        if (!result) {
            std::println("Issuer: rejected an invalid spend request");
            return std::nullopt;
        } else if (result->d != price) {
            std::println("Issuer: rejected a spend of {} credits (expected {})", result->d, price);
            return std::nullopt;
        } else if (!spent.insert(result->nf).second) {
            std::println("Issuer: rejected a token that was already spent");
            return std::nullopt;
        }
        std::println("Issuer: accepted a spend of {} credits, refunding {}", result->d, refund);
        return result->response;
    };

    // Issue.
    //
    // Client: Request a token with an initial balance of T_INIT.
    constexpr Credits T_INIT = 100;
    auto [pending_token, issue_request] = ratatouille::issue_request(T_INIT, ctx_iss);

    // Issuer: Verify the initial balance and issue a token to the Client.
    const auto issue_response = ratatouille::issue_response(sk, issue_request, T_INIT, ctx_iss);
    if (!issue_response) {
        std::println(stderr, "Issuer: the issue request is invalid");
        return EXIT_FAILURE;
    }

    // Client: Finalize the token.
    auto token = std::move(pending_token).finalize_issue(pk, *issue_response);
    if (!token) {
        std::println(stderr, "Client: the Issuer's response is invalid");
        return EXIT_FAILURE;
    }
    std::println("Client: balance is {}", token->credit() + token->refund());

    // Spend.
    struct Charge {
        Credits price;
        Credits refund;
    };
    for (auto [price, refund] : {Charge{30, 0}, Charge{40, 15}}) {
        // Client: Request to spend `price` credits.
        auto [pending_spend, spend_request] = std::move(*token).spend_request(pk, price, ctx_iss);

        // Issuer: Grant the spend, and refund `refund` credits.
        const auto spend_response = handle_spend(spend_request, price, refund);
        if (!spend_response) {
            return EXIT_FAILURE;
        }

        // Malicious Client: Try to replay the spend request.
        if (handle_spend(spend_request, price, refund)) {
            return EXIT_FAILURE;
        }

        // Client: Finalize the spend and keep the change token.
        token = std::move(pending_spend).finalize_spend(pk, *spend_response);
        if (!token) {
            std::println(stderr, "Client: the Issuer's response is invalid");
            return EXIT_FAILURE;
        }
        std::println("Client: balance is {}", token->credit() + token->refund());
    }

    return EXIT_SUCCESS;
}
