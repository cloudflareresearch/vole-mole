// The VOLE-in-the-Head proof system of FAEST v3. This implementation replaces the one-way function
// constraints with an arbitrary relation consisting of an instance (analogous to the FAEST public
// key), a witness (FAEST secret key), and a set of constraints. The proof itself is wire compatible
// with FAEST. Additional features:
//
// 1. Delayed instance binding: Proof generation has two steps: VOLE generation, followed by a
//    commit-and-prove step. In FAEST, the instance is bound at VOLE generation. In other
//    applications, like PomFRIT, the instance may not be known until the second step.
//
// 2. Partial witness binding: The prover provides a prefix of the witness to VOLE generation and
//    the rest to the commit-and-prove step. The prefix is hashed into the prover's seed, and its
//    correction is written to the proof, committing the prover to it.
//
// 3. Challenge binders: The application may provide additional data to bind at each step of proof
//    generation.
//
// 4. Challenge-dependent constraints: The relation's constraints are given the
//    challenge chal2, which is derived after the prover is committed to the entire witness. The
//    relation may use it to derive public randomness, e.g., to replace a set of constraints by a
//    random linear combination of them.
//
// Witness pad: Zero knowledge requires the first lambda = 8 * secpar_bytes rows of the VOLE
// witness to be uniform and secret from the verifier. FAEST v3 computes the CRT VOLE masks with a
// circuit of AND gates, garbled free-XOR style. The two labels of each gate differ by the prover's
// VOLE u on rows 0..lambda, and the proof reveals the correction d = u + w on those rows. A
// verifier who knows w[0..lambda) can therefore compute both labels of every gate, recover the
// masks, and unmask the VOLE check and QuickSilver responses, which leak information about the rest
// of the witness. FAEST meets the requirement because w[0..lambda) is its secret key. A generic
// relation may not: In PomFRIT, the witness starts with the target mask r, which the Issuer can
// recover from the signature and the issuance transcript. So by default, we prepend a pad of
// secpar_bytes bytes to the relation's witness. The pad is derived from the prover's randomness
// rho (see voleith_vole_gen) and is never revealed, except masked by u in its correction. So u on
// rows 0..lambda is uniform to the verifier, regardless of the relation's witness. The relation
// itself never sees the pad: its witness starts at VOLE row lambda, and QuickSilver is offset so
// that the relation indexes its witness from 0. A relation registers its witness length with
// PaddedOwfConstants, which adds the pad. A relation whose witness already starts with secpar_bytes
// uniformly random secret bytes may opt out by declaring `WITNESS_PAD = false`; we only do so to
// test wire compatibility with FAEST.
//
// This code was adapted from faest-arch-opt, which is distributed under the following license:
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

#include "qs_bit.hpp"

#include "block.hpp"          // from faest-arch-opt
#include "faest_sig.hpp"      // from faest-arch-opt
#include "hash.hpp"           // from faest-arch-opt
#include "kos_vole_check.hpp" // from faest-arch-opt
#include "parameters.hpp"     // from faest-arch-opt
#include "quicksilver.hpp"    // from faest-arch-opt
#include "vole_commit.hpp"    // from faest-arch-opt
// faest-arch-opt only instantiates these templates for its own parameter sets, so we include the
// implementations to instantiate them for ours.
#include "small_vole.inc"  // from faest-arch-opt; NOLINT(misc-include-cleaner)
#include "vole_commit.inc" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <new>
#include <optional>
#include <span>
#include <stdexcept>

namespace vole_mole::detail {

template <typename Relation> using relation_params = typename Relation::params;

// faest-arch-opt describes the statement being proven through `faest::OWF_CONSTANTS<S, owf>`, from
// which it derives the length of the VOLE witness and the QuickSilver degree. A relation registers
// itself as a new "one-way function" by deriving its specialization from this struct, which adds
// the witness pad (see above) to the relation's witness length.
template <faest::secpar S, size_t relation_witness_bits, size_t qs_degree>
struct PaddedOwfConstants {
    constexpr static size_t WITNESS_PAD_BITS = faest::secpar_to_bits(S);
    constexpr static size_t WITNESS_BITS = WITNESS_PAD_BITS + relation_witness_bits;
    constexpr static size_t QS_DEGREE = qs_degree;
    constexpr static bool valid = true;
};

// Size of the witness pad: secpar_bytes, unless the relation opts out by declaring
// `WITNESS_PAD = false`.
template <typename Relation> constexpr size_t witness_pad_bytes() {
    using OC = relation_params<Relation>::OWF_CONSTS;
    constexpr bool padded = [] {
        if constexpr (requires { Relation::WITNESS_PAD; }) {
            return Relation::WITNESS_PAD;
        } else {
            return true;
        }
    }();
    static_assert(
        padded == requires { OC::WITNESS_PAD_BITS; },
        "a padded relation must register its witness with PaddedOwfConstants");
    if constexpr (padded) {
        static_assert(OC::WITNESS_PAD_BITS == relation_params<Relation>::secpar_bits);
        return OC::WITNESS_PAD_BITS / 8;
    } else {
        return 0;
    }
}
template <typename Relation> constexpr size_t WITNESS_PAD_BYTES = witness_pad_bytes<Relation>();
template <typename Relation> constexpr size_t WITNESS_PAD_BITS = 8 * WITNESS_PAD_BYTES<Relation>;

// Size of the prover randomness.
template <typename Relation>
constexpr size_t PROVE_SEED_BYTES = relation_params<Relation>::secpar_bytes;
template <typename Relation> using ProveSeed = std::array<uint8_t, PROVE_SEED_BYTES<Relation>>;

// Size of a proof in bytes.
template <typename Relation>
constexpr size_t PROOF_BYTES = faest::FAEST_SIGNATURE_BYTES<relation_params<Relation>>;

// Size of the VOLE witness in bytes: the pad, followed by the relation's witness.
template <typename Relation>
constexpr size_t VOLE_WITNESS_BYTES = relation_params<Relation>::OWF_CONSTS::WITNESS_BITS / 8;

// Size of the relation's witness in bytes.
template <typename Relation>
constexpr size_t WITNESS_BYTES = VOLE_WITNESS_BYTES<Relation> - WITNESS_PAD_BYTES<Relation>;

template <typename Relation> using proof_span = std::span<uint8_t, PROOF_BYTES<Relation>>;
template <typename Relation>
using const_proof_span = std::span<const uint8_t, PROOF_BYTES<Relation>>;
template <typename Relation> using witness_span = std::span<const uint8_t, WITNESS_BYTES<Relation>>;

// Size of the prefix of the witness provided to VOLE generation.
template <typename Relation> constexpr size_t WITNESS_PREFIX_BYTES = Relation::WITNESS_PREFIX_BYTES;
template <typename Relation>
using witness_prefix_span = std::span<const uint8_t, WITNESS_PREFIX_BYTES<Relation>>;

// Size of the rest of the witness, provided to the commit-and-prove step.
template <typename Relation>
constexpr size_t WITNESS_SUFFIX_BYTES = WITNESS_BYTES<Relation> - WITNESS_PREFIX_BYTES<Relation>;
template <typename Relation>
using witness_suffix_span = std::span<const uint8_t, WITNESS_SUFFIX_BYTES<Relation>>;

// mu <- H_2^0(instance || dst)
//
// This is analogous to mu <- H_2^0(pk || msg) in FAEST, with an added domain separator that
// identifies the relation being proven. Subsequent H invocations are bound to the domain separator
// via mu.
//
// TODO(cjpatton) Propose adding domain separation between FAEST and generic VOLEitH use cases.
template <typename Relation>
faest::block_2secpar<relation_params<Relation>::secpar_v>
hash_mu(const typename Relation::instance* instance) {
    constexpr auto S = relation_params<Relation>::secpar_v;
    faest::block_2secpar<S> mu;
    faest::hash_state hasher;
    hasher.init(S);
    if (instance) {
        Relation::hash_instance(hasher, *instance);
    }
    hasher.update(Relation::DST);
    const uint8_t domain_separator = instance ? 0 : 4;
    hasher.update_byte(8 + domain_separator); // domain separator for H_2^0 or H_2^4
    hasher.finalize(&mu, sizeof(mu));
    return mu;
}

// Add bit constraints for the witness pad, which occupies the first pad_bits witness bits of qs,
// and then advance qs past the pad so that the relation sees its own witness from index 0.
//
// The pad is unused by the relation, so the relation's soundness does not depend on it. We
// constrain it anyway because it determines the label offset of the CRT VOLE mask circuit, just as
// FAEST's secret key does, and FAEST v3 bit-checks every witness row when CRT VOLE masks are used
// (see faest::parameter_set). This keeps us in the setting that FAEST v3 was analyzed in, rather
// than arguing that an unconstrained offset is harmless, at the cost of pad_bits degree-2
// constraints.
template <size_t pad_bits, typename QS> void qs_witness_pad_constraints(QS* qs) {
    for (size_t i = 0; i < pad_bits; ++i) {
        qs_add_bit_constraint(qs, qs->get_witness_bit(i));
    }
    qs->macs += pad_bits;
    if constexpr (!QS::is_verifier) {
        static_assert(pad_bits % 8 == 0);
        qs->witness += pad_bits / 8;
    }
}

template <typename Relation> struct PendingProof {
    std::array<uint8_t, relation_params<Relation>::CONSTS::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    faest::hash_state chal2_hasher;
    faest::vole_commit_data<relation_params<Relation>, false> vole_com_data;
    bool delayed_instance;
    // The VOLE witness: the pad and the prefix, then the suffix in step 2.
    std::array<uint8_t, VOLE_WITNESS_BYTES<Relation>> witness;
};

// The VOLE generation step. If instance is given, then it's bound to the proof at this step, as in
// FAEST. Otherwise, if instance == nullptr, then it's bound in the commit-and-prove step, as in
// PomFRIT. witness_prefix is the prefix of the witness; the suffix is passed to the second step.
// The caller also provides an optional chal1_binder, which is bound to the proof such that the
// verifier must agree on the value.
//
// The fields of the proof written by this step are the vole commitment, the VOLE check proof,
// iv_pre, and the corrections of the witness pad and the witness prefix.
//
// Returns the prover state to be consumed by the next step, voleith_prove_commit.
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by Relation::hash_instance
// are propagated.
//
// TODO(cjpatton) Propose adding the `chal1_binder` to the FAEST spec. It would probably make sense
// to length prefix it so it can have arbitrary length. (Likewise for `chal2_binder`).
template <typename Relation>
PendingProof<Relation>
voleith_vole_gen(proof_span<Relation> proof_bytes, const typename Relation::instance* instance,
                 witness_prefix_span<Relation> witness_prefix, const ProveSeed<Relation>& rho,
                 std::span<const uint8_t> chal1_binder = {}) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    constexpr auto S = P::secpar_v;
    static_assert(P::use_crt_vole_masks && P::use_grinding && P::use_v3_hash_inputs,
                  "only the FAEST v3 code path is implemented");

    const mutable_faest_signature<P> proof = proof_bytes.data();

    const bool delayed_instance = (instance == nullptr);

    hash_state hasher;

    const auto mu = hash_mu<Relation>(instance);

    // (r, iv^pre, pad) <- H_3(witness_prefix || mu || rho)
    //
    // FAEST outputs only (r, iv^pre). The pad, if any, is squeezed after them. It is as secret as
    // the seed r, and is never written to the proof, except masked by u in its correction.
    constexpr size_t PAD_BYTES = WITNESS_PAD_BYTES<Relation>;
    block_secpar<S> seed;
    block128 iv_pre;
    std::array<uint8_t, VOLE_WITNESS_BYTES<Relation>> witness{};
    {
        std::array<uint8_t, sizeof(seed) + sizeof(iv_pre) + PAD_BYTES> seed_iv_pre_pad;
        hasher.init(S);
        static_assert(0 < WITNESS_PREFIX_BYTES<Relation> &&
                      WITNESS_PREFIX_BYTES<Relation> <= WITNESS_BYTES<Relation>);
        hasher.update(witness_prefix);
        hasher.update(&mu, sizeof(mu));
        hasher.update(rho);
        hasher.update_byte(3); // domain separator for H_3
        hasher.finalize(seed_iv_pre_pad.data(), sizeof(seed_iv_pre_pad));
        memcpy(&seed, seed_iv_pre_pad.data(), sizeof(seed));
        memcpy(&iv_pre, &seed_iv_pre_pad[sizeof(seed)], sizeof(iv_pre));
        std::ranges::copy(std::span(seed_iv_pre_pad).template last<PAD_BYTES>(), witness.begin());
    }
    std::ranges::copy(witness_prefix, witness.begin() + PAD_BYTES);

    memcpy(proof.iv_pre().data(), &iv_pre, sizeof(iv_pre));

    // iv <- H_4(iv^pre || mu)
    block128 iv;
    hasher.init(S);
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update(&mu, sizeof(mu));
    hasher.update_byte(4); // domain separator for H_4
    hasher.finalize(&iv, sizeof(iv));

    auto allocated_vole_com_data = vole_commit_data<P, false>::alloc();
    if (!allocated_vole_com_data) {
        throw std::bad_alloc();
    }
    auto& vole_com_data = *allocated_vole_com_data;

    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check;
    crt_vole_commit<P>(seed, iv, vole_com_data, proof.vole_commitment_corrections(),
                       vole_commit_check, proof.vole_commitment_cmult());

    // chal1 <- H_2^1(mu || com || c_1 || ... || c_\tau-1 || c_mult || iv_pre || chal1_binder)
    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update(chal1_binder);
    hasher.update_byte(8 + 1); // domain separator for H_2^1
    hasher.finalize(chal1);

    // Begin chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || d).
    // The optional delayed-instance hash mu, chal2_binder, and d are hashed in the next step.
    hash_state chal2_hasher;
    chal2_hasher.init(S);
    chal2_hasher.update(chal1);
    kos_vole_check_sender<P>(
        vole_com_data.u_bytes().template subspan<0, CP::VOLE_CORRECTION_BYTES>(),
        vole_com_data.v().template subspan<0, CP::VOLE_CORRECTION_ROWS>(), vole_com_data.u_mask(),
        vole_com_data.v_mask(), chal1, proof.vole_check_proof(), chal2_hasher);

    // d = u + w: compute corrections for the witness pad and prefix.
    const auto u = vole_com_data.u_bytes();
    const auto correction = proof.correction();
    for (size_t i = 0; i < PAD_BYTES + WITNESS_PREFIX_BYTES<Relation>; ++i) {
        correction[i] = u[i] ^ witness[i];
    }

    return {chal1, chal2_hasher, std::move(vole_com_data), delayed_instance, witness};
}

// The commit-and-prove step. Writes the completed proof to the buffer. witness_suffix is the suffix
// of the witness; the prefix was passed in the first step. The caller also provides an optional
// chal2_binder, which is bound to the proof such that the verifier must agree on the value.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability). Exceptions thrown by Relation::hash_instance or
// Relation::constraints are propagated. If this throws, the contents of proof_bytes are
// unspecified.
template <typename Relation>
void voleith_prove_commit(proof_span<Relation> proof_bytes,
                          const typename Relation::instance& instance,
                          witness_suffix_span<Relation> witness_suffix,
                          PendingProof<Relation> pending,
                          std::span<const uint8_t> chal2_binder = {}) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    using OC = P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;
    static_assert(P::use_crt_vole_masks && P::use_grinding && P::use_v3_hash_inputs,
                  "only the FAEST v3 code path is implemented");

    auto& [chal1, hasher, vole_com_data, delayed_instance, witness] = pending;
    const mutable_faest_signature<P> proof = proof_bytes.data();
    constexpr size_t PAD_BYTES = WITNESS_PAD_BYTES<Relation>;
    constexpr size_t PAD_BITS = WITNESS_PAD_BITS<Relation>;
    std::ranges::copy(witness_suffix, witness.begin() + PAD_BYTES + WITNESS_PREFIX_BYTES<Relation>);

    // Finish chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || d),
    // where mu is included only for delayed instance binding.
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    if (delayed_instance) {
        const auto mu = hash_mu<Relation>(&instance);
        hasher.update(&mu, sizeof(mu));
    }
    hasher.update(chal2_binder);

    // d = u + w: compute corrections for the witness suffix.
    const auto u = vole_com_data.u_bytes();
    const auto correction = proof.correction();
    static_assert(correction.size() == VOLE_WITNESS_BYTES<Relation>);
    for (size_t i = PAD_BYTES + WITNESS_PREFIX_BYTES<Relation>; i < correction.size(); ++i) {
        correction[i] = u[i] ^ witness[i];
    }
    hasher.update(correction);
    hasher.update_byte(8 + 2); // domain separator for H_2^2
    hasher.finalize(chal2);

    // QuickSilver: With CRT VOLECommit, the VOLE tags v for the witness bits are the first
    // WITNESS_BITS entries of v, and the masks are separate.
    quicksilver_state<S, false, OC::QS_DEGREE> qs(witness.data(), vole_com_data.v().data(),
                                                  Relation::NUM_CONSTRAINTS + PAD_BITS,
                                                  chal2.data());
    qs_witness_pad_constraints<PAD_BITS>(&qs);
    Relation::constraints(&qs, instance, std::span<const uint8_t, CP::QS::CHALLENGE_BYTES>(chal2));

    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    qs.prove(vole_com_data.u_mask().data(), vole_com_data.v_mask().data(), proof.qs_proof().data(),
             qs_check.data());

    // chal3 <- H_2^3(chal2 || \tilde{a}_0 || \tilde{a}_1 || ... || ctr), where ctr is chosen
    // such that the last w_grind bits of chal3 are zero ("grinding").
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

// Generate a proof that witness satisfies Relation for instance. Write the completed proof to
// proof_bytes.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability). Exceptions thrown by Relation::hash_instance or
// Relation::constraints are propagated.
template <typename Relation>
void voleith_prove(proof_span<Relation> proof_bytes, witness_span<Relation> witness,
                   const typename Relation::instance& instance, const ProveSeed<Relation>& rho) {
    auto pending = voleith_vole_gen<Relation>(
        proof_bytes, &instance, witness.template first<WITNESS_PREFIX_BYTES<Relation>>(), rho);
    voleith_prove_commit<Relation>(proof_bytes, instance,
                                   witness.template last<WITNESS_SUFFIX_BYTES<Relation>>(),
                                   std::move(pending));
}

template <typename Relation> struct PendingVerification {
    std::array<uint8_t, relation_params<Relation>::CONSTS::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    faest::vole_commit_data<relation_params<Relation>, true> vole_com_data;
    faest::block_secpar<relation_params<Relation>::secpar_v> delta; // lifted
    bool delayed_instance;
};

// Reconstruct the verifier's VOLE keys from the proof. This is the verifier's counterpart to
// voleith_vole_gen: if instance is given, then bind it during this step; otherwise, delay
// binding to the next step. chal1_binder must match the value picked by the prover.
//
// Returns the verifier's state to be consumed by voleith_verify_commit, or nothing if the proof is
// deemed invalid at this point.
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by Relation::hash_instance
// are propagated. An invalid proof never causes an exception.
template <typename Relation>
std::optional<PendingVerification<Relation>>
voleith_vole_reconstruct(const_proof_span<Relation> proof_bytes,
                         const typename Relation::instance* instance,
                         std::span<const uint8_t> chal1_binder = {}) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    constexpr auto S = P::secpar_v;

    const faest_signature<P> proof = proof_bytes.data();
    if (!proof.check_format()) {
        return std::nullopt;
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

    auto allocated_vole_com_data = vole_commit_data<P, true>::alloc();
    if (!allocated_vole_com_data) {
        throw std::bad_alloc();
    }
    auto& vole_com_data = *allocated_vole_com_data;

    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check;
    if (!crt_vole_reconstruct<P>(iv, vole_com_data, delta, proof.vole_commitment_corrections(),
                                 proof.veccom_open(), vole_commit_check,
                                 proof.vole_commitment_cmult())) {
        return std::nullopt;
    }
    delta = crt_lift_delta<P>(delta);

    // chal1 <- H_2^1(mu || com || c_1 || ... || c_\tau-1 || c_mult || iv_pre || chal1_binder)
    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(proof.iv_pre());
    hasher.update(chal1_binder);
    hasher.update_byte(8 + 1); // domain separator for H_2^1
    hasher.finalize(chal1);

    return PendingVerification<Relation>{chal1, std::move(vole_com_data), delta,
                                         instance == nullptr};
}

// Finish verifying the proof for instance. This is the verifier's counterpart to
// voleith_prove_commit. chal2_binder must match the value picked by the prover.
//
// Returns false if the proof is invalid.
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by Relation::hash_instance or
// Relation::constraints are propagated. An invalid proof never causes an exception.
template <typename Relation>
bool voleith_verify_commit(const_proof_span<Relation> proof_bytes,
                           const typename Relation::instance& instance,
                           PendingVerification<Relation> pending,
                           std::span<const uint8_t> chal2_binder = {}) {
    using namespace faest;
    using P = relation_params<Relation>;
    using CP = P::CONSTS;
    using OC = P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;

    const auto& [chal1, vole_com_data, delta, delayed_instance] = pending;
    const faest_signature<P> proof = proof_bytes.data();

    hash_state hasher;

    // chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || d),
    // where mu is included only for delayed instance binding.
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1);
    kos_vole_check_receiver<P>(delta,
                               vole_com_data.q().template subspan<0, CP::VOLE_CORRECTION_ROWS>(),
                               vole_com_data.q_mask(), chal1, proof.vole_check_proof(), hasher);
    if (delayed_instance) {
        const auto mu = hash_mu<Relation>(&instance);
        hasher.update(&mu, sizeof(mu));
    }
    hasher.update(chal2_binder);
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

    quicksilver_state<S, true, OC::QS_DEGREE> qs(
        vole_com_data.q().data(), Relation::NUM_CONSTRAINTS + WITNESS_PAD_BITS<Relation>, delta,
        chal2.data());
    qs_witness_pad_constraints<WITNESS_PAD_BITS<Relation>>(&qs);
    Relation::constraints(&qs, instance, std::span<const uint8_t, CP::QS::CHALLENGE_BYTES>(chal2));

    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    qs.verify(vole_com_data.q_mask().data(), proof.qs_proof().data(), qs_check.data());

    // chal3 <- H_2^3(chal2 || \tilde{a}_0 || \tilde{a}_1 || ... || ctr)
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

// Verify a proof of knowledge of a witness that satisfies Relation for instance.
//
// Returns false if the proof is invalid.
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by Relation::hash_instance or
// Relation::constraints are propagated. An invalid proof never causes an exception.
template <typename Relation>
bool voleith_verify(const_proof_span<Relation> proof_bytes,
                    const typename Relation::instance& instance) {
    auto pending = voleith_vole_reconstruct<Relation>(proof_bytes, &instance);
    return pending && voleith_verify_commit<Relation>(proof_bytes, instance, std::move(*pending));
}

} // namespace vole_mole::detail

#endif
