// Domain separation tags (DSTs) for all protocols. They're kept in one place so that it's easy to
// check they're distinct.
//
// A DST is 7 bytes: a 4-byte protocol identifier, the protocol version, a purpose, and an index.

#ifndef VOLE_MOLE_DST_HPP
#define VOLE_MOLE_DST_HPP

#include "vole_mole/moussaka.hpp"
#include "vole_mole/pomfrit.hpp"

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

// Moussaka
constexpr Dst MOUSSAKA_COM_DST = make_dst("mous", moussaka::VERSION, 'c', '0');
constexpr Dst MOUSSAKA_ISSUE_PROOF_DST = make_dst("mous", moussaka::VERSION, 'i', '0');
constexpr Dst MOUSSAKA_ISSUE_SEED_DST = make_dst("mous", moussaka::VERSION, 's', '0');
constexpr Dst MOUSSAKA_REDEEM_PROOF_DST = make_dst("mous", moussaka::VERSION, 'r', '0');
constexpr Dst MOUSSAKA_REDEEM_SEED_DST = make_dst("mous", moussaka::VERSION, 's', '1');
// Random linear combination of the components of Q(s) in the redemption proof
constexpr Dst MOUSSAKA_REDEEM_COMBINE_DST = make_dst("mous", moussaka::VERSION, 'l', '0');

// PomFRIT
constexpr Dst POMFRIT_PROOF_DST = make_dst("pomf", pomfrit::VERSION, 'p', '0'); // VOLEitH relation
constexpr Dst POMFRIT_REFRESHER_DST = make_dst("pomf", pomfrit::VERSION, 'r', '0'); // refresher_com
constexpr Dst POMFRIT_SEED_DST = make_dst("pomf", pomfrit::VERSION, 's', '0');      // Client's seed
constexpr Dst POMFRIT_TARGET_DST = make_dst("pomf", pomfrit::VERSION, 'h', '0'); // H(pk, pi_1, msg)
// Random linear combination of the components of P(s)
constexpr Dst POMFRIT_COMBINE_DST = make_dst("pomf", pomfrit::VERSION, 'l', '0');

constexpr bool dsts_are_distinct() {
    // Every DST must be distinct. Add new DSTs to this list.
    std::array all = {
        MOUSSAKA_COM_DST,           MOUSSAKA_ISSUE_PROOF_DST, MOUSSAKA_ISSUE_SEED_DST,
        MOUSSAKA_REDEEM_PROOF_DST,  MOUSSAKA_REDEEM_SEED_DST, MOUSSAKA_REDEEM_COMBINE_DST,
        POMFRIT_PROOF_DST,          POMFRIT_REFRESHER_DST,    POMFRIT_SEED_DST,
        POMFRIT_TARGET_DST,         POMFRIT_COMBINE_DST,
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
