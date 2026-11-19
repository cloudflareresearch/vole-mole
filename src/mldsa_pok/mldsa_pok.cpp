#include "vole_mole/mldsa_pok.hpp"

#include "vole_mole/mldsa.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "mldsa/mldsa.hpp"
#include "mldsa_pok/prover.hpp"
#include "mldsa_pok/relation.hpp"
#include "mldsa_pok/verify_gadget.hpp"
#include "sumcheck/tree_sumcheck.hpp"
#include "sumcheck/voleith_fs.hpp"
#include "voleith.hpp"

#include "faest_sig.hpp"  // from faest-arch-opt
#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

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

// The sumcheck's Fiat-Shamir chain, which starts from the check seed (see docs/sumcheck-modq.md).
sumcheck::detail::Chain sumcheck_chain(const CheckSeed& seed) {
    return {vole_mole::detail::MLDSA_POK_SUMCHECK_DST, seed};
}

Proof prove_witness(const Statement& stmt, const Witness& w, const Rho& rho) {
    using vole_mole::detail::ProveSeed;
    Proof proof(PROOF_BYTES_);
    const std::span<uint8_t, PROOF_BYTES_> bin(proof);
    const std::span<const uint8_t, B_PREFIX_BYTES> prefix(w.prefix);
    ProveSeed<BinRelation> rho_bin;
    {
        const std::array<std::span<const uint8_t>, 2> parts = {vole_mole::detail::MLDSA_POK_RHO_DST,
                                                               rho};
        mldsa::detail::shake256(parts, rho_bin);
    }
    auto pending = vole_mole::detail::voleith_vole_gen<BinRelation>(bin, nullptr, prefix, rho_bin);
    BinRelation::instance inst{&stmt, check_seed(stmt, pending.chal1, bin), nullptr};
    Checks checks;
    checks.enc = ModQChecks::encode(check_weights(stmt.key, inst.seed));
    // Each message's masked bytes, w + G(K), are known before voleith_prove_commit writes them to
    // the proof.
    auto chain = sumcheck_chain(inst.seed);
    std::array<uint8_t, VerifyGadget::ANSWER_BYTES> answer;
    std::array<uint8_t, ModQChecks::MESSAGE_BYTES> masked;
    SIG.answer(w.prefix, checks, answer, [&](size_t off, size_t len) {
        for (size_t i = 0; i < len; ++i) {
            masked[i] = answer[off + i] ^ sumcheck::detail::prover_pad_byte<BinRelation>(
                                              pending, B_PREFIX_BYTES + off + i);
        }
        return chain.next(std::span<const uint8_t>(masked).first(len));
    });
    inst.checks = &checks;
    vole_mole::detail::voleith_prove_commit<BinRelation>(
        bin, inst, std::span<const uint8_t, VerifyGadget::ANSWER_BYTES>(answer),
        std::move(pending));
    return proof;
}

bool verify_proof(const Statement& stmt, std::span<const uint8_t, PROOF_BYTES_> bin) {
    auto pending = vole_mole::detail::voleith_vole_reconstruct<BinRelation>(bin, nullptr);
    if (!pending) {
        return false;
    }
    BinRelation::instance inst{&stmt, check_seed(stmt, pending->chal1, bin), nullptr};
    Checks checks;
    checks.enc = ModQChecks::encode(check_weights(stmt.key, inst.seed));
    const auto masked = sumcheck::detail::masked_witness<BinRelation>(bin, B_PREFIX_BYTES,
                                                                      ModQChecks::ANSWER_BYTES);
    checks.challenges = ModQChecks::challenges(
        sumcheck_chain(inst.seed),
        std::span<const uint8_t, ModQChecks::ANSWER_BYTES>(masked.data(), masked.size()));
    inst.checks = &checks;
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
