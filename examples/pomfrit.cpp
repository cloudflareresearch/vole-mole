// PomFRIT: a post-quantum blind signature.

#include <vole_mole/pomfrit.hpp>
#include <vole_mole/uov.hpp>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <print>
#include <span>
#include <string_view>
#include <utility>

using namespace vole_mole;

int main() {
    // Key generation.
    const uov::SecretKey sk(uov::generate_secret_key_bytes());
    const uov::PublicKey pk(sk.public_key());

    // Issue.
    //
    // Client: Request a signature. The message is hidden from the Issuer. When used in Privacy
    // Pass, it may include the nullifier that the Redeemer uses to check for double spending.
    constexpr std::string_view msg_str = "an example message";
    const std::span msg(reinterpret_cast<const uint8_t*>(msg_str.data()), msg_str.size());
    auto [pending, request] = pomfrit::issue_request(pk, msg);

    // Issuer: Issue a signature. The Issuer learns nothing about the message it's signing at this
    // point. In Privacy Pass, signatures are issued only to Clients that pass a challenge.
    const auto response = pomfrit::issue_response(sk, request);

    // Client: Finalize the signature.
    //
    // `pending` is consumed: each pending signature can be finalized only once.
    const auto sig = std::move(pending).finalize_issue(pk, response);
    if (!sig) {
        std::println(stderr, "Client: the Issuer's response is invalid");
        return EXIT_FAILURE;
    }

    // Verify: The relying party (perhaps the Issuer itself) verifies the blind signature against
    // the plaintext message. No party can link this presentation of the signature to its issuance.
    if (!pomfrit::verify(pk, msg, *sig)) {
        std::println(stderr, "Verifier: the signature is invalid");
        return EXIT_FAILURE;
    }
    std::println("Verifier: accepted a {}-byte signature", sig->size());

    return EXIT_SUCCESS;
}
