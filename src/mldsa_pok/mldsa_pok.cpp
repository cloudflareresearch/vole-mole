#include "vole_mole/mldsa_pok.hpp"

#include "vole_mole/mldsa.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "mldsa/mldsa.hpp"
#include "mldsa_pok/prover.hpp"
#include "mldsa_pok/relation.hpp"
#include "mldsa_pok/verify_gadget.hpp"
#include "voleith.hpp"

#include "faest_sig.hpp" // from faest-arch-opt
#include "hash.hpp"      // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

namespace vole_mole::mldsa_pok {

namespace detail {

Statement make_statement(const mldsa::PublicKey<P>& pk) { return {&pk, make_verify_key(pk)}; }

CheckSeed check_seed(const Statement& stmt, const Chal1& chal1,
                     std::span<const uint8_t, PROOF_BYTES_> proof) {
    const faest::faest_signature<BinRelation::params> view(proof.data());
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::MLDSA_POK_SEED_DST);
    h.update(*stmt.pk);
    h.update(chal1);
    h.update(view.vole_check_proof());
    vole_mole::detail::hash_witness_prefix_commitment<BinRelation>(h, proof);
    CheckSeed seed;
    h.finalize(seed);
    return seed;
}

Witness make_witness(const Statement& stmt, const Message& msg,
                     const mldsa::detail::DecodedSignature<P>& sig) {
    Witness w{std::vector<uint8_t>(B_PREFIX_BYTES)};
    const auto mu = MU.encode_witness(w.prefix, stmt.key.parsed.tr, msg);
    SIG.encode_witness(w.prefix, stmt.key, mu, sig);
    return w;
}

Proof prove_witness(const Statement& stmt, const Witness& w, const Rho& rho) {
    using vole_mole::detail::ProveSeed;
    Proof proof(PROOF_BYTES_);
    const std::span<uint8_t, PROOF_BYTES_> bin(proof);
    const std::span<const uint8_t, B_PREFIX_BYTES> prefix(w.prefix);
    std::array<uint8_t, MlDsaModQ::ANSWER_BYTES> answer;
    for (uint8_t attempt = 0; attempt < 8; ++attempt) {
        ProveSeed<BinRelation> rho_bin;
        {
            const std::array<uint8_t, 1> a = {attempt};
            const std::array<std::span<const uint8_t>, 3> parts = {
                vole_mole::detail::MLDSA_POK_RHO_DST, rho, a};
            mldsa::detail::shake256(parts, rho_bin);
        }
        auto pending =
            vole_mole::detail::voleith_vole_gen<BinRelation>(bin, nullptr, prefix, rho_bin);
        BinRelation::instance inst{&stmt, check_seed(stmt, pending.chal1, bin), nullptr};
        const Weights weights = MlDsaModQ::make_weights(check_weights(stmt.key, inst.seed));
        if (!SIG.answer(w.prefix, weights, answer)) {
            continue; // the checks need more committed bits than the budget
        }
        inst.weights = &weights;
        vole_mole::detail::voleith_prove_commit<BinRelation>(
            bin, inst, std::span<const uint8_t, MlDsaModQ::ANSWER_BYTES>(answer),
            std::move(pending));
        return proof;
    }
    throw std::runtime_error("ML-DSA PoK: too many attempts");
}

bool verify_proof(const Statement& stmt, std::span<const uint8_t, PROOF_BYTES_> bin) {
    auto pending = vole_mole::detail::voleith_vole_reconstruct<BinRelation>(bin, nullptr);
    if (!pending) {
        return false;
    }
    BinRelation::instance inst{&stmt, check_seed(stmt, pending->chal1, bin), nullptr};
    const Weights weights = MlDsaModQ::make_weights(check_weights(stmt.key, inst.seed));
    if (MlDsaModQ::count_carries(weights) > MlDsaModQ::CARRY_BUDGET) {
        return false;
    }
    inst.weights = &weights;
    return vole_mole::detail::voleith_verify_commit<BinRelation>(bin, inst, std::move(*pending));
}

Proof prove_with_seed(const mldsa::PublicKey<P>& pk, const Message& msg,
                      const mldsa::Signature<P>& sig, const Rho& rho) {
    const auto decoded = mldsa::detail::decode_signature<P>(sig);
    if (!decoded) {
        throw std::invalid_argument("ML-DSA PoK: invalid signature");
    }
    const auto stmt = make_statement(pk);
    return prove_witness(stmt, make_witness(stmt, msg, *decoded), rho);
}

} // namespace detail

const size_t PROOF_BYTES = detail::PROOF_BYTES_;

Proof prove(const mldsa::PublicKey<mldsa::MlDsa44>& pk, const Message& msg,
            const mldsa::Signature<mldsa::MlDsa44>& sig) {
    return detail::prove_with_seed(pk, msg, sig, random_bytes<32>());
}

bool verify(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> proof) {
    if (proof.size() != PROOF_BYTES) {
        return false;
    }
    const auto stmt = detail::make_statement(pk);
    return detail::verify_proof(
        stmt, std::span<const uint8_t, detail::PROOF_BYTES_>(proof.data(), proof.size()));
}

} // namespace vole_mole::mldsa_pok
