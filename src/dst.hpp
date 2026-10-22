// Domain separation tags (DSTs) for all protocols. They're kept in one place so that it's easy to
// check they're distinct.
//
// A DST is 7 bytes: a 4-byte protocol identifier, the protocol version, a purpose, and an index.

#ifndef VOLE_MOLE_DST_HPP
#define VOLE_MOLE_DST_HPP

#include "vole_mole/act.hpp"
#include "vole_mole/ihat.hpp"
#include "vole_mole/pomfrit.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::ihat::detail {

// Version used for domain separation of unbound tokens. A future version of VOLE-IHAT may drop
// support for binding the redemption context at issuance.
constexpr uint8_t UNBOUND_VERSION = 1;

} // namespace vole_mole::ihat::detail

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

// VOLE-ACT
constexpr Dst ACT_COM_DST = make_dst("rata", act::VERSION, 'c', '0');
constexpr Dst ACT_ISSUE_PROOF_DST = make_dst("rata", act::VERSION, 'i', '0');
constexpr Dst ACT_ISSUE_SEED_DST = make_dst("rata", act::VERSION, 's', '0');
constexpr Dst ACT_SPEND_COMBINE_DST = make_dst("rata", act::VERSION, 'l', '0');
constexpr Dst ACT_SPEND_PROOF_DST = make_dst("rata", act::VERSION, 'p', '0');
constexpr Dst ACT_SPEND_SEED_DST = make_dst("rata", act::VERSION, 's', '1');
constexpr Dst ACT_TAG_DST = make_dst("rata", act::VERSION, 't', '0');

// VOLE-IHAT
constexpr Dst IHAT_COM_DST = make_dst("mous", ihat::VERSION, 'c', '0');
constexpr Dst IHAT_ISSUE_PROOF_DST = make_dst("mous", ihat::VERSION, 'i', '0');
constexpr Dst IHAT_ISSUE_SEED_DST = make_dst("mous", ihat::VERSION, 's', '0');
constexpr Dst IHAT_REDEEM_COMBINE_DST = make_dst("mous", ihat::VERSION, 'l', '0');
constexpr Dst IHAT_REDEEM_PROOF_DST = make_dst("mous", ihat::VERSION, 'r', '0');
constexpr Dst IHAT_REDEEM_SEED_DST = make_dst("mous", ihat::VERSION, 's', '1');

// VOLE-IHAT (unbound tokens)
constexpr Dst UNBOUND_IHAT_COM_DST = make_dst("mous", ihat::detail::UNBOUND_VERSION, 'c', '0');
constexpr Dst UNBOUND_IHAT_DERIVE_DST = make_dst("mous", ihat::detail::UNBOUND_VERSION, 'd', '0');
constexpr Dst UNBOUND_IHAT_ISSUE_PROOF_DST =
    make_dst("mous", ihat::detail::UNBOUND_VERSION, 'i', '0');
constexpr Dst UNBOUND_IHAT_ISSUE_SEED_DST =
    make_dst("mous", ihat::detail::UNBOUND_VERSION, 's', '0');
constexpr Dst UNBOUND_IHAT_REDEEM_COMBINE_DST =
    make_dst("mous", ihat::detail::UNBOUND_VERSION, 'l', '0');
constexpr Dst UNBOUND_IHAT_REDEEM_PROOF_DST =
    make_dst("mous", ihat::detail::UNBOUND_VERSION, 'r', '0');
constexpr Dst UNBOUND_IHAT_REDEEM_SEED_DST =
    make_dst("mous", ihat::detail::UNBOUND_VERSION, 's', '1');

// PomFRIT
constexpr Dst POMFRIT_COMBINE_DST = make_dst("pomf", pomfrit::VERSION, 'l', '0');
constexpr Dst POMFRIT_PROOF_DST = make_dst("pomf", pomfrit::VERSION, 'p', '0'); // VOLEitH relation
constexpr Dst POMFRIT_REFRESHER_DST = make_dst("pomf", pomfrit::VERSION, 'r', '0'); // refresher_com
constexpr Dst POMFRIT_SEED_DST = make_dst("pomf", pomfrit::VERSION, 's', '0');      // Client's seed
constexpr Dst POMFRIT_TARGET_DST = make_dst("pomf", pomfrit::VERSION, 'h', '0'); // H(pk, pi_1, msg)

constexpr bool dsts_are_distinct() {
    // Every DST must be distinct. Add new DSTs to this list.
    std::array all = {
        ACT_COM_DST,
        ACT_ISSUE_PROOF_DST,
        ACT_ISSUE_SEED_DST,
        ACT_SPEND_COMBINE_DST,
        ACT_SPEND_PROOF_DST,
        ACT_SPEND_SEED_DST,
        ACT_TAG_DST,
        IHAT_COM_DST,
        IHAT_ISSUE_PROOF_DST,
        IHAT_ISSUE_SEED_DST,
        IHAT_REDEEM_COMBINE_DST,
        IHAT_REDEEM_PROOF_DST,
        IHAT_REDEEM_SEED_DST,
        POMFRIT_COMBINE_DST,
        POMFRIT_PROOF_DST,
        POMFRIT_REFRESHER_DST,
        POMFRIT_SEED_DST,
        POMFRIT_TARGET_DST,
        UNBOUND_IHAT_COM_DST,
        UNBOUND_IHAT_DERIVE_DST,
        UNBOUND_IHAT_ISSUE_PROOF_DST,
        UNBOUND_IHAT_ISSUE_SEED_DST,
        UNBOUND_IHAT_REDEEM_COMBINE_DST,
        UNBOUND_IHAT_REDEEM_PROOF_DST,
        UNBOUND_IHAT_REDEEM_SEED_DST,
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
