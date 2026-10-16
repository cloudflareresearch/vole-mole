// Domain separation tags (DSTs) for all protocols. They're kept in one place so that it's easy to
// check they're distinct.
//
// A DST is 7 bytes: a 4-byte protocol identifier, the protocol version, a purpose, and an index.

#ifndef VOLE_MOLE_DST_HPP
#define VOLE_MOLE_DST_HPP

#include "vole_mole/ecdsa_pok.hpp"
#include "vole_mole/moussaka.hpp"
#include "vole_mole/pomfrit.hpp"
#include "vole_mole/ratatouille.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::detail {

constexpr size_t DST_BYTES = 7;
using Dst = std::array<uint8_t, DST_BYTES>;

constexpr Dst make_dst(const char (&protocol)[5], uint8_t version, char purpose, char index) {
    return {static_cast<uint8_t>(protocol[0]),
            static_cast<uint8_t>(protocol[1]),
            static_cast<uint8_t>(protocol[2]),
            static_cast<uint8_t>(protocol[3]),
            version,
            static_cast<uint8_t>(purpose),
            static_cast<uint8_t>(index)};
}

// ECDSA proof of knowledge
constexpr Dst ECDSA_POK_BINARY_DST =
    make_dst("ecpk", ecdsa_pok::VERSION, 'b', '0'); // binary VOLEitH
constexpr Dst ECDSA_POK_BINDER_DST = make_dst("ecpk", ecdsa_pok::VERSION, 'f', '0'); // F_p, F_n QS
constexpr Dst ECDSA_POK_BINARY_PRG_DST = make_dst("ecpk", ecdsa_pok::VERSION, 'q', '0'); // wit PRG
constexpr Dst ECDSA_POK_LINK_DST = make_dst("ecpk", ecdsa_pok::VERSION, 'l', '0'); // link chal
constexpr Dst ECDSA_POK_SEED_DST = make_dst("ecpk", ecdsa_pok::VERSION, 's', '0'); // prover seed
constexpr Dst ECDSA_POK_STATEMENT_DST = make_dst("ecpk", ecdsa_pok::VERSION, 'x', '0'); // mu
// The batches of binary constraints (qs_batch.hpp), in all the binary proofs below.
constexpr Dst ECDSA_POK_BATCH_DST = make_dst("ecpk", ecdsa_pok::VERSION, 'k', '0');

// ECDSA proof with a hidden public key (experimental, src/ecdsa_pok/hk_relation.hpp)
constexpr Dst ECDSA_HK_BINARY_DST = make_dst("echk", ecdsa_pok::VERSION, 'b', '0');
constexpr Dst ECDSA_HK_BINDER_DST = make_dst("echk", ecdsa_pok::VERSION, 'f', '0');
constexpr Dst ECDSA_HK_BINARY_PRG_DST = make_dst("echk", ecdsa_pok::VERSION, 'q', '0');
constexpr Dst ECDSA_HK_LINK_DST = make_dst("echk", ecdsa_pok::VERSION, 'l', '0');
constexpr Dst ECDSA_HK_SEED_DST = make_dst("echk", ecdsa_pok::VERSION, 's', '0');
constexpr Dst ECDSA_HK_STATEMENT_DST = make_dst("echk", ecdsa_pok::VERSION, 'x', '0');

// ECDSA proof with a hidden public key and a revealed R (experimental, ecdsa_pok/rr_relation.hpp)
constexpr Dst ECDSA_RR_BINARY_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'b', '0');
constexpr Dst ECDSA_RR_BINDER_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'f', '0');
constexpr Dst ECDSA_RR_OFFSET_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'h', '0'); // comb offsets
constexpr Dst ECDSA_RR_BINARY_PRG_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'q', '0');
constexpr Dst ECDSA_RR_LINK_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'l', '0');
constexpr Dst ECDSA_RR_SEED_DST = make_dst("ecrr", ecdsa_pok::VERSION, 's', '0');
constexpr Dst ECDSA_RR_STATEMENT_DST = make_dst("ecrr", ecdsa_pok::VERSION, 'x', '0');

// mdoc proof (experimental, src/ecdsa_pok/mdoc_relation.hpp)
constexpr Dst ECDSA_MDOC_BINARY_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'b', '0');
constexpr Dst ECDSA_MDOC_SELECT_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'c', '0'); // coeffs
constexpr Dst ECDSA_MDOC_BINDER_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'f', '0');
// Unused (the comb offsets of an earlier version that revealed the device signature's R); reserved.
constexpr Dst ECDSA_MDOC_OFFSET_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'h', '0');
constexpr Dst ECDSA_MDOC_BINARY_PRG_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'q', '0');
constexpr Dst ECDSA_MDOC_LINK_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'l', '0');
constexpr Dst ECDSA_MDOC_SEED_DST = make_dst("ecmd", ecdsa_pok::VERSION, 's', '0');
constexpr Dst ECDSA_MDOC_STATEMENT_DST = make_dst("ecmd", ecdsa_pok::VERSION, 'x', '0');

// Moussaka
constexpr Dst MOUSSAKA_COM_DST = make_dst("mous", moussaka::VERSION, 'c', '0');
constexpr Dst MOUSSAKA_ISSUE_PRG_DST = make_dst("mous", moussaka::VERSION, 'q', '0'); // witness PRG
constexpr Dst MOUSSAKA_ISSUE_PROOF_DST = make_dst("mous", moussaka::VERSION, 'i', '0');
constexpr Dst MOUSSAKA_ISSUE_SEED_DST = make_dst("mous", moussaka::VERSION, 's', '0');
constexpr Dst MOUSSAKA_REDEEM_COMBINE_DST = make_dst("mous", moussaka::VERSION, 'l', '0');
constexpr Dst MOUSSAKA_REDEEM_PRG_DST =
    make_dst("mous", moussaka::VERSION, 'q', '1'); // witness PRG
constexpr Dst MOUSSAKA_REDEEM_PROOF_DST = make_dst("mous", moussaka::VERSION, 'r', '0');
constexpr Dst MOUSSAKA_REDEEM_SEED_DST = make_dst("mous", moussaka::VERSION, 's', '1');

// PomFRIT
constexpr Dst POMFRIT_COMBINE_DST = make_dst("pomf", pomfrit::VERSION, 'l', '0');
constexpr Dst POMFRIT_PRG_DST = make_dst("pomf", pomfrit::VERSION, 'q', '0');   // witness PRG
constexpr Dst POMFRIT_PROOF_DST = make_dst("pomf", pomfrit::VERSION, 'p', '0'); // VOLEitH relation
constexpr Dst POMFRIT_REFRESHER_DST = make_dst("pomf", pomfrit::VERSION, 'r', '0'); // refresher_com
constexpr Dst POMFRIT_SEED_DST = make_dst("pomf", pomfrit::VERSION, 's', '0');      // Client's seed
constexpr Dst POMFRIT_TARGET_DST = make_dst("pomf", pomfrit::VERSION, 'h', '0'); // H(pk, pi_1, msg)

// Ratatouille
constexpr Dst RATATOUILLE_COM_DST = make_dst("rata", ratatouille::VERSION, 'c', '0');
constexpr Dst RATATOUILLE_ISSUE_PRG_DST =
    make_dst("rata", ratatouille::VERSION, 'q', '0'); // witness PRG
constexpr Dst RATATOUILLE_ISSUE_PROOF_DST = make_dst("rata", ratatouille::VERSION, 'i', '0');
constexpr Dst RATATOUILLE_ISSUE_SEED_DST = make_dst("rata", ratatouille::VERSION, 's', '0');
constexpr Dst RATATOUILLE_SPEND_COMBINE_DST = make_dst("rata", ratatouille::VERSION, 'l', '0');
constexpr Dst RATATOUILLE_SPEND_PRG_DST =
    make_dst("rata", ratatouille::VERSION, 'q', '1'); // witness PRG
constexpr Dst RATATOUILLE_SPEND_PROOF_DST = make_dst("rata", ratatouille::VERSION, 'p', '0');
constexpr Dst RATATOUILLE_SPEND_SEED_DST = make_dst("rata", ratatouille::VERSION, 's', '1');
constexpr Dst RATATOUILLE_TAG_DST = make_dst("rata", ratatouille::VERSION, 't', '0');

constexpr bool dsts_are_distinct() {
    // Every DST must be distinct. Add new DSTs to this list.
    std::array all = {
        ECDSA_POK_BINARY_DST,
        ECDSA_POK_BINDER_DST,
        ECDSA_POK_BINARY_PRG_DST,
        ECDSA_POK_LINK_DST,
        ECDSA_POK_SEED_DST,
        ECDSA_POK_STATEMENT_DST,
        ECDSA_POK_BATCH_DST,
        ECDSA_HK_BINARY_DST,
        ECDSA_HK_BINDER_DST,
        ECDSA_HK_BINARY_PRG_DST,
        ECDSA_HK_LINK_DST,
        ECDSA_HK_SEED_DST,
        ECDSA_HK_STATEMENT_DST,
        ECDSA_RR_BINARY_DST,
        ECDSA_RR_BINDER_DST,
        ECDSA_RR_OFFSET_DST,
        ECDSA_RR_BINARY_PRG_DST,
        ECDSA_RR_LINK_DST,
        ECDSA_RR_SEED_DST,
        ECDSA_RR_STATEMENT_DST,
        ECDSA_MDOC_BINARY_DST,
        ECDSA_MDOC_SELECT_DST,
        ECDSA_MDOC_BINDER_DST,
        ECDSA_MDOC_OFFSET_DST,
        ECDSA_MDOC_BINARY_PRG_DST,
        ECDSA_MDOC_LINK_DST,
        ECDSA_MDOC_SEED_DST,
        ECDSA_MDOC_STATEMENT_DST,
        MOUSSAKA_COM_DST,
        MOUSSAKA_ISSUE_PRG_DST,
        MOUSSAKA_ISSUE_PROOF_DST,
        MOUSSAKA_ISSUE_SEED_DST,
        MOUSSAKA_REDEEM_COMBINE_DST,
        MOUSSAKA_REDEEM_PRG_DST,
        MOUSSAKA_REDEEM_PROOF_DST,
        MOUSSAKA_REDEEM_SEED_DST,
        POMFRIT_COMBINE_DST,
        POMFRIT_PRG_DST,
        POMFRIT_PROOF_DST,
        POMFRIT_REFRESHER_DST,
        POMFRIT_SEED_DST,
        POMFRIT_TARGET_DST,
        RATATOUILLE_COM_DST,
        RATATOUILLE_ISSUE_PRG_DST,
        RATATOUILLE_ISSUE_PROOF_DST,
        RATATOUILLE_ISSUE_SEED_DST,
        RATATOUILLE_SPEND_COMBINE_DST,
        RATATOUILLE_SPEND_PRG_DST,
        RATATOUILLE_SPEND_PROOF_DST,
        RATATOUILLE_SPEND_SEED_DST,
        RATATOUILLE_TAG_DST,
    };
    bool distinct = true;
    for (size_t i = 0; i < all.size(); ++i) {
        for (size_t j = 0; j < all.size(); ++j) {
            distinct = distinct && (i == j || all[i] != all[j]);
        }
    }
    return distinct;
}
static_assert(dsts_are_distinct());

} // namespace vole_mole::detail

#endif
