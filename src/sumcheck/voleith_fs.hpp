// Multi-round Fiat-Shamir inside a VOLEitH proof (see docs/sumcheck-modq.md, section 3).
//
// A relation may fix later parts of its witness suffix after challenges derived from earlier
// parts. The proof carries, for each witness byte, a masked byte m = w + pad: for a derived witness
// (see "Derived witnesses" in voleith.hpp), m is the byte of e and pad that of G(K); otherwise m is
// the correction d and pad the VOLE's u. In both cases the pad is fixed before chal1 (by the VOLE
// commitment and the key's correction), so m fixes the committed value, and a challenge derived
// from m (and the seed, which binds the commitment) comes after the value is fixed.
//
// The prover knows the pads after VOLE generation, so it computes each masked message as it goes,
// and voleith_prove_commit later writes the same bytes to the proof. The verifier reads them from
// the proof before QuickSilver.

#ifndef VOLE_MOLE_SUMCHECK_VOLEITH_FS_HPP
#define VOLE_MOLE_SUMCHECK_VOLEITH_FS_HPP

#include "voleith.hpp"

#include "faest_sig.hpp" // from faest-arch-opt

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::sumcheck::detail {

// The prover's pad for witness byte i, which must be in the witness suffix.
template <typename Relation>
uint8_t prover_pad_byte(const vole_mole::detail::PendingProof<Relation>& pending, size_t i) {
    using namespace vole_mole::detail;
    assert(i >= WITNESS_PREFIX_BYTES<Relation> && i < WITNESS_BYTES<Relation>);
    if constexpr (DERIVED_WITNESS<Relation>) {
        uint8_t pad = 0;
        for (size_t j = 0; j < 8; ++j) {
            pad = static_cast<uint8_t>(pad | ((pending.derived[8 * i + j].value().data & 1) << j));
        }
        return pad;
    } else {
        return pending.vole_com_data.u_bytes()[i];
    }
}

// The masked witness bytes [off, off + len) in a proof.
template <typename Relation>
std::span<const uint8_t> masked_witness(vole_mole::detail::const_proof_span<Relation> proof,
                                        size_t off, size_t len) {
    using namespace vole_mole::detail;
    if constexpr (DERIVED_WITNESS<Relation>) {
        return std::span<const uint8_t>(derived_e<Relation>(proof)).subspan(off, len);
    } else {
        const faest::faest_signature<relation_params<Relation>> view(proof.data());
        return std::span<const uint8_t>(view.correction()).subspan(off, len);
    }
}

} // namespace vole_mole::sumcheck::detail

#endif
