#include "vole_mole/act.hpp"
#include "vole_mole/uov.hpp"

#include "act/commit.hpp"       // internal
#include "act/issue.hpp"        // internal
#include "act/seeded.hpp"       // internal
#include "act/spend.hpp"        // internal
#include "act/token.hpp"        // internal
#include "keccak/segmented.hpp" // internal

#include "test.hpp"

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <set>
#include <utility>
#include <vector>

using namespace vole_mole::act;
using vole_mole::act::detail::commit;
using vole_mole::act::detail::issue_request_with_seed;
using vole_mole::act::detail::Seed;
using vole_mole::act::detail::SEED_BYTES;
using vole_mole::act::detail::spend_request_with_seed;
using vole_mole::act::detail::TokenAccess;
using vole_mole::test::filled;
using vole_mole::test::to_hex;

namespace {

constexpr Credits MAX_CREDITS = std::numeric_limits<Credits>::max();

struct Spend {
    Seed seed;
    Credits d;
    Credits refund;
};

struct Case {
    Seed issue_seed;
    Context ctx_iss;
    Credits t_init;
    vole_mole::uov::SecretKeyBytes issuer_sk;
    std::vector<Spend> spends;
};

Seed all(uint8_t b) {
    Seed s;
    s.fill(b);
    return s;
}

std::vector<Case> cases() {
    Context ctx_ff;
    ctx_ff.fill(0xff);
    return {
        // Spend nothing, then spend the only credit.
        {Seed{},
         Context{},
         1,
         filled<vole_mole::uov::SECRET_KEY_BYTES>(0x60),
         {{Seed{}, 0, 0}, {all(0x01), 1, 0}}},
        // Spend with a refund, then spend the whole balance, including the refund.
        {filled<SEED_BYTES>(0x50),
         filled<CTX_BYTES>(0x10),
         100,
         filled<vole_mole::uov::SECRET_KEY_BYTES>(0x61),
         {{filled<SEED_BYTES>(0x90), 30, 3}, {filled<SEED_BYTES>(0xa0), 73, 5}}},
        // Maximum credit values: t + x overflows 64 bits in the second spend.
        {all(0xff),
         ctx_ff,
         MAX_CREDITS,
         filled<vole_mole::uov::SECRET_KEY_BYTES>(0x62),
         {{all(0xff), 1, MAX_CREDITS}, {all(0xfe), MAX_CREDITS, MAX_CREDITS}}},
    };
}

} // namespace

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: gen_act_kat OUTPUT_FILE\n";
        return 1;
    }
    std::ofstream out(argv[1]);
    if (!out) {
        std::cerr << "Can't open " << argv[1] << '\n';
        return 1;
    }
    out << "# VOLE-ACT v" << unsigned(VERSION) << " issuance and spend KATs.\n"
        << "# QuickSilver degrees: issuance " << detail::ISSUE_QS_DEGREE << ", spend "
        << detail::SPEND_QS_DEGREE << ".\n# Committed states:";
    for (size_t k = 1; k <= vole_mole::keccak::detail::NUM_COMMITTED_STATES; ++k) {
        out << " s" << vole_mole::keccak::detail::SEGMENT_START[k];
    }
    out << ".\n# Witness bytes: issuance " << detail::ISSUE_WITNESS_BYTES << ", spend "
        << detail::SPEND_WITNESS_BYTES << ".\n# Proof bytes: issuance " << ISSUE_PROOF_BYTES
        << ", spend " << SPEND_PROOF_BYTES
        << ".\n# Fields are hex bytes, except t_init, spend_count, d, refund, and t_next "
           "(decimal).\n"
           "# issuer_sk is a compact test-only UOV key. Each token is spent spend_count times; "
           "each\n# spend after the first spends the change token of the previous one.\n";

    size_t i = 0;
    for (const auto& kat : cases()) {
        const vole_mole::test::UovKeyPair kp(vole_mole::uov::SecretKey{kat.issuer_sk});

        auto res = issue_request_with_seed(kat.t_init, kat.ctx_iss, kat.issue_seed);
        const auto issue_resp = issue_response(kp.sk, res.request, kat.t_init, kat.ctx_iss);
        if (!issue_resp) {
            std::cerr << "Generated issuance proof failed verification for case " << i << '\n';
            return 1;
        }
        const auto nf = TokenAccess::nf(res.pending_token);
        const auto r = TokenAccess::r(res.pending_token);
        auto token = std::move(res.pending_token).finalize_issue(kp.pk, *issue_resp);
        if (!token) {
            std::cerr << "Issuance finalization failed for case " << i << '\n';
            return 1;
        }

        out << "\nissue_seed " << to_hex(kat.issue_seed) << "\nctx_iss " << to_hex(kat.ctx_iss)
            << "\nt_init " << kat.t_init << "\nissuer_sk " << to_hex(kat.issuer_sk) << "\nnf "
            << to_hex(nf) << "\nr " << to_hex(r) << "\ncommitment "
            << to_hex(commit(nf, kat.ctx_iss, kat.t_init, r)) << "\nissue_witness "
            << to_hex(detail::encode_issue_witness(nf, kat.ctx_iss, kat.t_init, r))
            << "\nissue_request " << to_hex(res.request) << "\nissue_response "
            << to_hex(*issue_resp) << "\nspend_count " << kat.spends.size() << '\n';

        // Each spend must use a distinct seed, so that no nullifier repeats.
        std::set<Nullifier> nullifiers = {nf};

        for (const auto& spend : kat.spends) {
            const Credits t = token->credit(), x = token->refund();
            const auto spent_nf = TokenAccess::nf(*token);
            const auto spent_r = TokenAccess::r(*token);
            const auto s = TokenAccess::s(*token);
            auto [pending, request] =
                spend_request_with_seed(std::move(*token), kp.pk, spend.d, kat.ctx_iss, spend.seed);
            const auto nf_next = TokenAccess::nf(pending);
            if (!nullifiers.insert(nf_next).second) {
                std::cerr << "Repeated nullifier in case " << i << '\n';
                return 1;
            }
            const Credits t_next = TokenAccess::t(pending);
            const auto r_next = TokenAccess::r(pending);
            const auto witness = detail::encode_spend_witness(
                {spent_nf, t, spent_r, x, s, nf_next, t_next, r_next}, spend.d, kat.ctx_iss);

            const auto spend_resp = spend_response(kp.sk, request, kat.ctx_iss, spend.refund);
            if (!spend_resp || spend_resp->nf != spent_nf || spend_resp->d != spend.d) {
                std::cerr << "Generated spend proof failed verification for case " << i << '\n';
                return 1;
            }
            token = std::move(pending).finalize_spend(kp.pk, spend_resp->response);
            if (!token || token->credit() != t_next || token->refund() != spend.refund) {
                std::cerr << "Spend finalization failed for case " << i << '\n';
                return 1;
            }

            out << "\nspend_seed " << to_hex(spend.seed) << "\nd " << spend.d << "\nrefund "
                << spend.refund << "\nnf_next " << to_hex(nf_next) << "\nt_next " << t_next
                << "\nr_next " << to_hex(r_next) << "\nspend_witness " << to_hex(witness)
                << "\nspend_request " << to_hex(request) << "\nspend_response "
                << to_hex(spend_resp->response) << '\n';
        }
        ++i;
    }
    out.close();
    if (!out) {
        std::cerr << "Failed to write " << argv[1] << '\n';
        return 1;
    }
}
