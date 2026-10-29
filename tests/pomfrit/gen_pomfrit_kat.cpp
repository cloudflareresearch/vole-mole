// Generate PomFRIT known answers for the Lean protocol spec (lean/VoleMole/Spec/PomFRIT.lean, run
// by `lake exe spec_kats`). Unlike the VOLE-IHAT and VOLE-ACT known answers, no C++ test reads
// them.
//
// Every case uses the fixed test key pair (secret key filled(0x60)) and a fixed seed, through
// detail::issue_request_with_seed. Besides the protocol messages, the file has chal1 of each
// signature (the VOLEitH challenge that hash_to_target absorbs, recomputed from the signature as
// verify does), and the proof layout offsets that the Lean spec hard-codes.

#include "vole_mole/pomfrit.hpp"
#include "vole_mole/uov.hpp"

#include "pomfrit/redeem.hpp" // internal
#include "pomfrit/seeded.hpp" // internal
#include "uov/public_key.hpp" // internal
#include "voleith.hpp"        // internal

#include "test.hpp"

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <span>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::pomfrit;
using vole_mole::detail::PROOF_BYTES;
using vole_mole::detail::voleith_vole_reconstruct;
using vole_mole::pomfrit::detail::issue_request_with_seed;
using vole_mole::pomfrit::detail::ProofView;
using vole_mole::pomfrit::detail::RedeemRelation;
using vole_mole::pomfrit::detail::Seed;
using vole_mole::pomfrit::detail::SEED_BYTES;
using vole_mole::test::filled;
using vole_mole::test::to_hex;
using vole_mole::test::uov_key_pair;

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: gen_pomfrit_kat OUTPUT_FILE\n";
        return 1;
    }
    std::ofstream out(argv[1]);
    if (!out) {
        std::cerr << "Can't open " << argv[1] << '\n';
        return 1;
    }

    const auto& kp = uov_key_pair();
    constexpr size_t REFRESHER_BYTES = 2 * RedeemRelation::params::secpar_bytes;
    out << "# PomFRIT v" << unsigned(VERSION)
        << " known answers for lean/VoleMole/Spec/PomFRIT.lean.\n"
        << "# Written by tests/pomfrit/gen_pomfrit_kat.cpp. Fields are hex bytes, except the "
           "layout\n"
        << "# constants (decimal). Every case uses the test key pair (secret key filled(0x60)),\n"
        << "# whose compressed public key is pk; its expanded map is key `test` in\n"
        << "# lean/vectors/uov_keys.txt.\n"
        << "\nsignature_bytes " << SIGNATURE_BYTES << "\nproof_bytes "
        << PROOF_BYTES<RedeemRelation> << "\nrefresher_bytes " << REFRESHER_BYTES
        << "\nvole_check_proof_offset " << ProofView::OFFSET_VOLE_CHECK_PROOF
        << "\nvole_check_proof_bytes " << ProofView::SIZE_VOLE_CHECK_PROOF << "\ncorrection_offset "
        << ProofView::OFFSET_CORRECTION << "\ncorrection_bytes " << ProofView::SIZE_CORRECTION
        << "\nsk " << to_hex(test::UOV_SK_BYTES) << "\npk " << to_hex(kp.sk.public_key_bytes())
        << "\npk_digest " << to_hex(uov::detail::PublicKeyAccess::digest(kp.pk)) << '\n';

    for (size_t i = 0; i < 3; ++i) {
        Seed seed{};
        std::vector<uint8_t> msg;
        if (i == 1) {
            seed = filled<SEED_BYTES>(0x30);
            msg = {'h', 'e', 'l', 'l', 'o'};
        } else if (i == 2) {
            seed.fill(0xff);
            for (size_t j = 0; j < 300; ++j) {
                msg.push_back(static_cast<uint8_t>(j));
            }
        }

        auto res = issue_request_with_seed(kp.pk, msg, seed);
        const IssueResponse response = issue_response(kp.sk, res.request);
        const auto sig = std::move(res.pending).finalize_issue(kp.pk, response);
        if (!sig || !verify(kp.pk, msg, *sig)) {
            std::cerr << "Signature failed verification for case " << i << '\n';
            return 1;
        }

        // Recompute chal1 from the signature, as verify does.
        const auto proof = std::span(*sig).first<PROOF_BYTES<RedeemRelation>>();
        const auto refresher_com =
            std::span(*sig).subspan<PROOF_BYTES<RedeemRelation>, REFRESHER_BYTES>();
        const auto pending =
            voleith_vole_reconstruct<RedeemRelation>(proof, nullptr, refresher_com);
        if (!pending) {
            std::cerr << "VOLE reconstruction failed for case " << i << '\n';
            return 1;
        }

        out << "\nseed " << to_hex(seed) << "\nmsg " << to_hex(msg) << "\nrequest "
            << to_hex(res.request) << "\nresponse " << to_hex(response) << "\nchal1 "
            << to_hex(pending->chal1) << "\nsignature " << to_hex(*sig) << '\n';
    }
    out.close();
    if (!out) {
        std::cerr << "Failed to write " << argv[1] << '\n';
        return 1;
    }
}
