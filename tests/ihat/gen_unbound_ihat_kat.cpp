#include "vole_mole/ihat.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"                 // internal
#include "ihat/commit.hpp"         // internal
#include "ihat/seeded.hpp"         // internal
#include "ihat/token.hpp"          // internal
#include "ihat/unbound_issue.hpp"  // internal
#include "ihat/unbound_redeem.hpp" // internal
#include "keccak/segmented.hpp"    // internal

#include "test.hpp"

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <utility>
#include <vector>

using namespace vole_mole::ihat;
using vole_mole::ihat::detail::derive;
using vole_mole::ihat::detail::Seed;
using vole_mole::ihat::detail::SEED_BYTES;
using vole_mole::ihat::detail::unbound_commit;
using vole_mole::ihat::detail::unbound_issue_request_with_seed;
using vole_mole::ihat::detail::unbound_redeem_request_with_seed;
using vole_mole::test::filled;
using vole_mole::test::to_hex;

namespace {

// Each token is redeemed for this many redemption contexts.
constexpr size_t REDEMPTION_COUNT = 2;

} // namespace

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: gen_unbound_ihat_kat OUTPUT_FILE\n";
        return 1;
    }
    std::ofstream out(argv[1]);
    if (!out) {
        std::cerr << "Can't open " << argv[1] << '\n';
        return 1;
    }
    out << "# VOLE-IHAT v" << unsigned(detail::UNBOUND_VERSION)
        << " issuance and redemption KATs for unbound tokens.\n"
        << "# QuickSilver degrees: issuance " << detail::UNBOUND_ISSUE_QS_DEGREE << ", redemption "
        << detail::UNBOUND_REDEEM_QS_DEGREE << ".\n# Committed states:";
    for (size_t k = 1; k <= vole_mole::keccak::detail::NUM_COMMITTED_STATES; ++k) {
        out << " s" << vole_mole::keccak::detail::SEGMENT_START[k];
    }
    out << ".\n# Witness bytes: issuance " << detail::UNBOUND_ISSUE_WITNESS_BYTES << ", redemption "
        << detail::UNBOUND_REDEEM_WITNESS_BYTES << ".\n# Proof bytes: issuance "
        << UNBOUND_ISSUE_PROOF_BYTES << ", redemption " << UNBOUND_REDEEM_PROOF_BYTES
        << ".\n# Fields are hex bytes, except anchor_count, issuer (zero-based), and "
           "redemption_count, which are decimal.\n"
           "# anchor_sk repeats once per Anchor, in Anchor Set order; compact test-only UOV "
           "keys.\n"
           "# Each token is redeemed redemption_count times, each with redeem_seed through "
           "redeem_request.\n";
    for (size_t i = 0; i < 3; ++i) {
        Seed seed{}, redeem_seed{};
        Context ctx_iss{}, ctx_red{};
        ChallengeDigest challenge_digest{};
        if (i == 1) {
            seed = filled<SEED_BYTES>(0x50);
            redeem_seed = filled<SEED_BYTES>(0x90);
            ctx_iss = filled<CTX_BYTES>(0x10);
            ctx_red = filled<CTX_BYTES>(0x20);
            challenge_digest = filled<CHALLENGE_DIGEST_BYTES>(0x70);
        } else if (i == 2) {
            seed.fill(0xff);
            redeem_seed.fill(0xff);
            ctx_iss.fill(0xff);
            ctx_red.fill(0xff);
            challenge_digest.fill(0xff);
        }
        const size_t anchor_count = i == 0 ? 1 : i == 1 ? 3 : MAX_ANCHORS;
        const size_t issuer = i == 0 ? 0 : i == 1 ? 1 : anchor_count - 1;
        std::vector<vole_mole::uov::SecretKeyBytes> key_bytes;
        std::vector<vole_mole::test::UovKeyPair> key_pairs;
        key_pairs.reserve(anchor_count);
        for (size_t u = 0; u < anchor_count; ++u) {
            key_bytes.push_back(filled<vole_mole::uov::SECRET_KEY_BYTES>(
                static_cast<uint8_t>(u == issuer ? 0x60 : 0x61 + u)));
            key_pairs.emplace_back(vole_mole::uov::SecretKey{key_bytes.back()});
        }
        std::vector<AnchorRef> refs;
        for (const auto& kp : key_pairs) {
            refs.emplace_back(kp.pk);
        }
        const AnchorSet anchors(refs);

        auto res = unbound_issue_request_with_seed(ctx_iss, seed);
        const auto response = unbound_issue_response(key_pairs[issuer].sk, res.request, ctx_iss);
        if (!response) {
            std::cerr << "Generated proof failed verification for case " << i << '\n';
            return 1;
        }
        const auto nf_key = detail::TokenAccess::nf_key(res.pending_token);
        const auto r = detail::TokenAccess::r(res.pending_token);
        auto token = std::move(res.pending_token).finalize_issue(key_pairs[issuer].pk, *response);
        if (!token || detail::TokenAccess::nf_key(*token) != nf_key ||
            detail::TokenAccess::r(*token) != r || detail::TokenAccess::s(*token) != *response) {
            std::cerr << "Issuance finalization failed for case " << i << '\n';
            return 1;
        }

        out << "\nissue_seed " << to_hex(seed) << "\nctx_iss " << to_hex(ctx_iss)
            << "\nanchor_count " << anchor_count << "\nissuer " << issuer;
        for (const auto& sk : key_bytes) {
            out << "\nanchor_sk " << to_hex(sk);
        }
        out << "\nnf_key " << to_hex(nf_key) << "\nr " << to_hex(r) << "\ncommitment "
            << to_hex(unbound_commit(nf_key, ctx_iss, r)) << "\nissue_witness "
            << to_hex(detail::encode_unbound_issue_witness(nf_key, ctx_iss, r))
            << "\nissue_request " << to_hex(res.request) << "\nissue_response " << to_hex(*response)
            << "\nredemption_count " << REDEMPTION_COUNT;

        for (size_t j = 0; j < REDEMPTION_COUNT; ++j) {
            // Redeem the same token for another redemption context.
            if (j > 0) {
                ctx_red[0] ^= 0x80;
                redeem_seed[0] ^= 0x01;
            }
            const auto nf = derive(nf_key, ctx_red);
            const auto redeem_witness = detail::encode_unbound_redeem_witness(
                nf_key, ctx_iss, ctx_red, r, *response, issuer);
            const auto redeem_request = unbound_redeem_request_with_seed(
                *token, anchors, ctx_iss, ctx_red, challenge_digest, redeem_seed);
            const auto redeemed_nf = unbound_finalize_redeem(anchors, redeem_request, ctx_iss,
                                                             ctx_red, challenge_digest);
            if (!redeemed_nf || *redeemed_nf != nf) {
                std::cerr << "Redemption " << j << " failed verification for case " << i << '\n';
                return 1;
            }
            out << "\nredeem_seed " << to_hex(redeem_seed) << "\nctx_red " << to_hex(ctx_red)
                << "\nchallenge_digest " << to_hex(challenge_digest) << "\nnf " << to_hex(nf)
                << "\nredeem_witness " << to_hex(redeem_witness) << "\nredeem_request "
                << to_hex(redeem_request);
        }
        out << '\n';
    }
    out.close();
    if (!out) {
        std::cerr << "Failed to write " << argv[1] << '\n';
        return 1;
    }
}
