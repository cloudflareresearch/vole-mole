// Domain separation tags (DSTs) for all protocols. They're kept in one place so that it's easy to
// check they're distinct.
//
// A DST is 7 bytes: a 4-byte protocol identifier, the protocol version, a purpose, and an index.

#ifndef VOLE_MOLE_DST_HPP
#define VOLE_MOLE_DST_HPP

#include "vole_mole/moussaka.hpp"

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

constexpr bool dsts_are_distinct() {
    // Every DST must be distinct. Add new DSTs to this list.
    std::array all = {
        MOUSSAKA_COM_DST,
        MOUSSAKA_ISSUE_PROOF_DST,
        MOUSSAKA_ISSUE_SEED_DST,
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
