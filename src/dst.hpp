// Domain separation tags (DSTs) for all protocols. They're kept in one place so that it's easy to
// check they're distinct.
//
// A DST is 7 bytes: a 4-byte protocol identifier, the protocol version, a purpose, and an index.

#ifndef VOLE_MOLE_DST_HPP
#define VOLE_MOLE_DST_HPP

#include "vole_mole/mldsa_pok.hpp"
#include "vole_mole/mlkem_pop.hpp"
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

// ML-DSA proof of knowledge of a signature.
constexpr Dst MLDSA_POK_PROOF_DST = make_dst("mdpk", mldsa_pok::VERSION, 'b', '0');   // proof
constexpr Dst MLDSA_POK_SEED_DST = make_dst("mdpk", mldsa_pok::VERSION, 's', '0');    // check seed
constexpr Dst MLDSA_POK_WEIGHTS_DST = make_dst("mdpk", mldsa_pok::VERSION, 'w', '0'); // weights
constexpr Dst MLDSA_POK_RHO_DST = make_dst("mdpk", mldsa_pok::VERSION, 'r', '0');     // VOLE seeds
constexpr Dst MLDSA_POK_PRG_DST = make_dst("mdpk", mldsa_pok::VERSION, 'p', '0');     // witness PRG

// ML-KEM proof of possession: the VOLEitH relation for each parameter set, indexed by k.
constexpr Dst MLKEM_POP_PROOF_512_DST = make_dst("mpop", mlkem_pop::VERSION, 'p', '2');
constexpr Dst MLKEM_POP_PROOF_768_DST = make_dst("mpop", mlkem_pop::VERSION, 'p', '3');
constexpr Dst MLKEM_POP_PROOF_1024_DST = make_dst("mpop", mlkem_pop::VERSION, 'p', '4');

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
        MLDSA_POK_PROOF_DST,         MLDSA_POK_SEED_DST,          MLDSA_POK_WEIGHTS_DST,
        MLDSA_POK_RHO_DST,           MLDSA_POK_PRG_DST,           MLKEM_POP_PROOF_512_DST,
        MLKEM_POP_PROOF_768_DST,     MLKEM_POP_PROOF_1024_DST,    MOUSSAKA_COM_DST,
        MOUSSAKA_ISSUE_PRG_DST,      MOUSSAKA_ISSUE_PROOF_DST,    MOUSSAKA_ISSUE_SEED_DST,
        MOUSSAKA_REDEEM_COMBINE_DST, MOUSSAKA_REDEEM_PRG_DST,     MOUSSAKA_REDEEM_PROOF_DST,
        MOUSSAKA_REDEEM_SEED_DST,    POMFRIT_COMBINE_DST,         POMFRIT_PRG_DST,
        POMFRIT_PROOF_DST,           POMFRIT_REFRESHER_DST,       POMFRIT_SEED_DST,
        POMFRIT_TARGET_DST,          RATATOUILLE_COM_DST,         RATATOUILLE_ISSUE_PRG_DST,
        RATATOUILLE_ISSUE_PROOF_DST, RATATOUILLE_ISSUE_SEED_DST,  RATATOUILLE_SPEND_COMBINE_DST,
        RATATOUILLE_SPEND_PRG_DST,   RATATOUILLE_SPEND_PROOF_DST, RATATOUILLE_SPEND_SEED_DST,
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
