// Generic VOLE-in-the-Head. The structure is close to FAEST v3, but replaces the one-way function
// constraints with an arbitrary relation consisting of an instance (analogous to the FAEST public
// key), a witness (FAEST secret key), and a set of constraints. The proof has the same structure as
// a FAEST signature.
//
// `voleith_prove` and `voleith_verify` are adapted from `faest_sign` and `faest_verify` in
// faest-arch-opt (faest.inc), which is distributed under the following license:
//
//   Copyright (c) 2023 FAEST Team
//
//   Permission is hereby granted, free of charge, to any person obtaining a copy of
//   this software and associated documentation files (the "Software"), to deal in
//   the Software without restriction, including without limitation the rights to
//   use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
//   of the Software, and to permit persons to whom the Software is furnished to do
//   so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in all
//   copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//   SOFTWARE.

#ifndef VOLE_MOLE_VOLEITH_HPP
#define VOLE_MOLE_VOLEITH_HPP

#include "faest_sig.hpp"
#include "hash.hpp"
#include "kos_vole_check.hpp"
#include "quicksilver.hpp"
#include "util.hpp"
// faest-arch-opt only instantiates these templates for its own parameter sets, so we include the
// implementations to instantiate them for ours.
#include "small_vole.inc"
#include "vole_commit.inc"

#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <new>
#include <span>
#include <stdexcept>

namespace vole_mole::detail {

template <typename Relation> using relation_params = typename Relation::params;

// Size of a proof in bytes.
template <typename Relation>
constexpr size_t PROOF_BYTES = faest::FAEST_SIGNATURE_BYTES<relation_params<Relation>>;

// Size of the witness in bytes.
template <typename Relation>
constexpr size_t WITNESS_BYTES = relation_params<Relation>::OWF_CONSTS::WITNESS_BITS / 8;

template <typename Relation> using proof_span = std::span<uint8_t, PROOF_BYTES<Relation>>;
template <typename Relation>
using const_proof_span = std::span<const uint8_t, PROOF_BYTES<Relation>>;
template <typename Relation> using witness_span = std::span<const uint8_t, WITNESS_BYTES<Relation>>;

// Size of the prefix of the witness provided to VOLE generation.
template <typename Relation> constexpr size_t WITNESS_PREFIX_BYTES = Relation::WITNESS_PREFIX_BYTES;

// mu <- H_2^0(instance || dst)
//
// This is analogous to mu <- H_2^0(pk || msg) in FAEST, with an added domain separator that
// identifies the relation being proven. Subsequent H invocations are bound to the domain separator
// via mu.
//
// TODO(cjpatton) Propose adding domain separation between FAEST and generic VOLEitH use cases.
template <typename Relation>
faest::block_2secpar<relation_params<Relation>::secpar_v>
hash_mu(const typename Relation::instance& instance) {
    constexpr auto S = relation_params<Relation>::secpar_v;
    faest::block_2secpar<S> mu;
    faest::hash_state hasher;
    hasher.init(S);
    Relation::hash_instance(hasher, instance);
    hasher.update(Relation::DST);
    hasher.update_byte(8 + 0); // domain separator for H_2^0
    hasher.finalize(&mu, sizeof(mu));
    return mu;
}

// Generate a proof that `witness` satisfies `Relation` for `instance`.
//
// `rho` is randomness for the prover. As in FAEST, it is hashed together with the witness and the
// instance to derive the seed of the VOLE commitment, so the proof remains sound and zero
// knowledge even if `rho` is empty (which makes proving deterministic), as long as the witness has
// enough entropy.
//
// Throws std::bad_alloc if memory allocation fails.
template <typename Relation>
void voleith_prove(proof_span<Relation> proof_bytes, witness_span<Relation> witness,
                   const typename Relation::instance& instance, std::span<const uint8_t> rho) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    using OC = P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;
    static_assert(P::use_crt_vole_masks && P::use_grinding && P::use_v3_hash_inputs,
                  "only the FAEST v3 code path is implemented");

    const mutable_faest_signature<P> proof = proof_bytes.data();

    hash_state hasher;

    const auto mu = hash_mu<Relation>(instance);

    // (r, iv^pre) <- H_3(witness_prefix || mu || rho)
    block_secpar<S> seed;
    block128 iv_pre;
    {
        std::array<uint8_t, sizeof(seed) + sizeof(iv_pre)> seed_iv_pre;
        hasher.init(S);
        static_assert(0 < WITNESS_PREFIX_BYTES<Relation> &&
                      WITNESS_PREFIX_BYTES<Relation> <= WITNESS_BYTES<Relation>);
        hasher.update(witness.template first<WITNESS_PREFIX_BYTES<Relation>>());
        hasher.update(&mu, sizeof(mu));
        hasher.update(rho);
        hasher.update_byte(3); // domain separator for H_3
        hasher.finalize(seed_iv_pre.data(), sizeof(seed_iv_pre));
        memcpy(&seed, seed_iv_pre.data(), sizeof(seed));
        memcpy(&iv_pre, &seed_iv_pre[sizeof(seed)], sizeof(iv_pre));
    }

    // iv <- H_4(iv^pre || mu)
    block128 iv;
    hasher.init(S);
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update(&mu, sizeof(mu));
    hasher.update_byte(4); // domain separator for H_4
    hasher.finalize(&iv, sizeof(iv));

    auto vole_com_data_e = vole_commit_data<P, false>::alloc();
    if (!vole_com_data_e) {
        throw std::bad_alloc();
    }
    const auto vole_com_data = std::move(*vole_com_data_e);

    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check;
    crt_vole_commit<P>(seed, iv, vole_com_data, proof.vole_commitment_corrections(),
                       vole_commit_check, proof.vole_commitment_cmult());

    // chall_1 <- H_2^1(mu || com || c_1 || ... || c_\tau-1 || c_mult || iv_pre)
    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update_byte(8 + 1); // domain separator for H_2^1
    hasher.finalize(chal1);

    // chall_2 <- H_2^2(chall_1 || \tilde{u} || h_V || d)
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1);
    kos_vole_check_sender<P>(
        vole_com_data.u_bytes().template subspan<0, CP::VOLE_CORRECTION_BYTES>(),
        vole_com_data.v().template subspan<0, CP::VOLE_CORRECTION_ROWS>(), vole_com_data.u_mask(),
        vole_com_data.v_mask(), chal1, proof.vole_check_proof(), hasher);

    // d = u + w: correct the random VOLE to a VOLE commitment to the witness.
    const auto correction = proof.correction();
    static_assert(correction.size() == witness.size());
    const auto u = vole_com_data.u_bytes();
    for (size_t i = 0; i < correction.size(); ++i) {
        correction[i] = u[i] ^ witness[i];
    }
    hasher.update(correction);
    hasher.update_byte(8 + 2); // domain separator for H_2^2
    hasher.finalize(chal2);

    // QuickSilver: With CRT VOLECommit, the VOLE tags v for the witness bits are the first
    // WITNESS_BITS entries of v, and the masks are separate.
    quicksilver_state<S, false, OC::QS_DEGREE> qs(witness.data(), vole_com_data.v().data(),
                                                  Relation::NUM_CONSTRAINTS, chal2.data());
    Relation::constraints(&qs, instance);

    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    qs.prove(vole_com_data.u_mask().data(), vole_com_data.v_mask().data(), proof.qs_proof().data(),
             qs_check.data());

    memcpy(proof.iv_pre().data(), &iv_pre, sizeof(iv_pre));

    // chall_3 <- H_2^3(chall_2 || \tilde{a}_0 || \tilde{a}_1 || ... || ctr), where ctr is chosen
    // such that the last w_grind bits of chall_3 are zero ("grinding").
    hash_state_x4 grinding_hasher;
    grinding_hasher.init(S);
    grinding_hasher.update_1(chal2);
    grinding_hasher.update_1(qs_check);
    grinding_hasher.update_1(proof.qs_proof());
    uint32_t counter;
    const bool open_success = grind_and_open<typename P::bavc_t>(
        vole_com_data.forest().data(), vole_com_data.hashed_leaves().data(), proof.delta().data(),
        proof.veccom_open().data(), &grinding_hasher, &counter);
    // The grinding loop only fails if the 32-bit counter overflows, which happens with
    // negligible probability.
    if (!open_success) {
        throw std::runtime_error("VOLEitH: grinding failed");
    }
    for (size_t i = 0; i < 4; ++i) {
        proof.grinding_ctr()[i] = static_cast<uint8_t>(counter >> (8 * i));
    }

    assert(proof.check_format());
}

// Verify a proof generated by `voleith_prove`.
//
// Returns false if the proof is invalid. Throws std::bad_alloc if memory allocation fails.
template <typename Relation>
bool voleith_verify(const_proof_span<Relation> proof_bytes,
                    const typename Relation::instance& instance) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    using OC = P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;

    const faest_signature<P> proof = proof_bytes.data();
    if (!proof.check_format()) {
        return false;
    }

    hash_state hasher;

    const auto mu = hash_mu<Relation>(instance);

    // iv <- H_4(iv^pre || mu)
    block128 iv;
    hasher.init(S);
    hasher.update(proof.iv_pre());
    hasher.update(&mu, sizeof(mu));
    hasher.update_byte(4); // domain separator for H_4
    hasher.finalize(&iv, sizeof(iv));

    block_secpar<S> delta;
    memcpy(&delta, proof.delta().data(), sizeof(delta));

    auto vole_com_data_e = vole_commit_data<P, true>::alloc();
    if (!vole_com_data_e) {
        throw std::bad_alloc();
    }
    const auto vole_com_data = std::move(*vole_com_data_e);

    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check;
    if (!crt_vole_reconstruct<P>(iv, vole_com_data, delta, proof.vole_commitment_corrections(),
                                 proof.veccom_open(), vole_commit_check,
                                 proof.vole_commitment_cmult())) {
        return false;
    }
    delta = crt_lift_delta<P>(delta);

    // chall_1 <- H_2^1(mu || com || c_1 || ... || c_\tau-1 || c_mult || iv_pre)
    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(proof.iv_pre());
    hasher.update_byte(8 + 1); // domain separator for H_2^1
    hasher.finalize(chal1);

    // chall_2 <- H_2^2(chall_1 || \tilde{u} || h_V || d)
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1);
    kos_vole_check_receiver<P>(delta,
                               vole_com_data.q().template subspan<0, CP::VOLE_CORRECTION_ROWS>(),
                               vole_com_data.q_mask(), chal1, proof.vole_check_proof(), hasher);
    hasher.update(proof.correction());
    hasher.update_byte(8 + 2); // domain separator for H_2^2
    hasher.finalize(chal2);

    // Apply the correction d to the verifier's VOLE keys: q_i += d_i * Delta.
    {
        const auto d = proof.correction();
        const auto q = vole_com_data.q();
        for (size_t i = 0; i < CP::VOLE_CORRECTION_ROWS; ++i) {
            if ((d[i / 8] >> (i % 8)) & 1) {
                q[i] = q[i] ^ delta;
            }
        }
    }

    quicksilver_state<S, true, OC::QS_DEGREE> qs(vole_com_data.q().data(),
                                                 Relation::NUM_CONSTRAINTS, delta, chal2.data());
    Relation::constraints(&qs, instance);

    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    qs.verify(vole_com_data.q_mask().data(), proof.qs_proof().data(), qs_check.data());

    // chall_3' <- H_2^3(chall_2 || \tilde{a}_0 || \tilde{a}_1 || ... || ctr)
    block_secpar<S> delta_check;
    hasher.init(S);
    hasher.update(chal2);
    hasher.update(qs_check);
    hasher.update(proof.qs_proof());
    hasher.update(proof.grinding_ctr());
    hasher.update_byte(8 + 3); // domain separator for H_2^3
    hasher.finalize(&delta_check, sizeof(delta_check));

    return memcmp(proof.delta().data(), &delta_check, sizeof(delta_check)) == 0;
}

} // namespace vole_mole::detail

#endif
