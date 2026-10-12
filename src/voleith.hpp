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
//    correction is written to the proof, committing the prover to it. (With a derived witness, see
//    below, the commitment to the prefix also includes part of e; see
//    hash_witness_prefix_commitment.)
//
// 3. Challenge binders: The application may provide additional data to bind at each step of proof
//    generation.
//
// 4. Challenge-dependent constraints: The relation's constraints are given the
//    challenge chal2, which is derived after the prover is committed to the entire witness. The
//    relation may use it to derive public randomness, e.g., to replace a set of constraints by a
//    random linear combination of them.
//
// 5. Derived witnesses: Each witness bit costs tau bits of proof (its correction d and the VOLE
//    corrections c_1, ..., c_{tau-1}). With the WitnessPrg parameter (see RelationConstants), the
//    witness w is instead derived from a short key K with a PRG G of degree 2 (see
//    witness_prg.hpp): The VOLE witness is K, and the proof carries the public vector
//    e = w + G(K), one bit per witness bit.
//    The relation's constraints are evaluated unchanged on the committed values w = e + G(K) of
//    degree 2, through DerivedQS (see mq/derived_qs.hpp), so the QuickSilver degree doubles. Each
//    bit of K is constrained to be a bit, so each bit of w is a bit, too.
//
//    The prover derives K <- H_5(witness_prefix || mu || rho). VOLE generation writes the
//    correction of K and the part of e for the witness prefix; the commit-and-prove step writes
//    the rest of e. e is bound to chal2. Soundness is unaffected (K and e determine w); zero
//    knowledge additionally requires G to be a PRG. The public maps of G are derived from the
//    relation's WITNESS_PRG_DST. The proof is the FAEST proof followed by e.
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

#include "mq/derived_qs.hpp"
#include "mq/prg.hpp"
#include "qs_bit.hpp"
#include "witness_prg.hpp"

#include "block.hpp"          // from faest-arch-opt
#include "faest_sig.hpp"      // from faest-arch-opt
#include "hash.hpp"           // from faest-arch-opt
#include "kos_vole_check.hpp" // from faest-arch-opt
#include "polynomials.hpp"    // from faest-arch-opt
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
#include <vector>

namespace vole_mole::detail {

template <typename Relation> using relation_params = typename Relation::params;

// Size of the prover randomness.
template <typename Relation>
constexpr size_t PROVE_SEED_BYTES = relation_params<Relation>::secpar_bytes;
template <typename Relation> using ProveSeed = std::array<uint8_t, PROVE_SEED_BYTES<Relation>>;

// faest-arch-opt describes the statement being proven through `faest::OWF_CONSTANTS<S, owf>`, from
// which it derives the length of the VOLE witness and the QuickSilver degree. A relation registers
// a new "one-way function" whose OWF_CONSTANTS derive from RelationConstants, given the length of
// the relation's witness (in bits), the degree of its constraints, and the witness PRG, which
// determines whether and how the witness is derived (see "Derived witnesses" above): If it's
// NoPrg, then the VOLE witness is the witness. Otherwise, it's the key from which the witness is
// derived with the PRG (e.g., MqPrg<c>, see witness_prg.hpp), and the QuickSilver degree is
// mq::detail::DEGREE times the degree of the constraints. This is a VOLEitH parameter, like tau:
// it doesn't change the relation's constraints, only the proof size and the cost of proving and
// verifying.
template <size_t RELATION_WITNESS_BITS_, size_t RELATION_QS_DEGREE_, typename WitnessPrg_>
struct RelationConstants {
    static constexpr size_t RELATION_WITNESS_BITS = RELATION_WITNESS_BITS_;
    static constexpr size_t RELATION_QS_DEGREE = RELATION_QS_DEGREE_;
    using WitnessPrg = WitnessPrg_;
    static_assert(RELATION_WITNESS_BITS % 8 == 0);

    static constexpr size_t WITNESS_BITS = [] {
        if constexpr (derives_witness<WitnessPrg>) {
            return WitnessPrg::template Map<RELATION_WITNESS_BITS>::KEY_BITS;
        } else {
            return RELATION_WITNESS_BITS;
        }
    }();
    static constexpr size_t QS_DEGREE =
        derives_witness<WitnessPrg> ? mq::detail::DEGREE * RELATION_QS_DEGREE : RELATION_QS_DEGREE;
    // The CRT VOLE commitment needs QS_DEGREE - 1 masks for QuickSilver and 4 for the VOLE check.
    static_assert(QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

    static constexpr bool valid = true;
};

template <typename Relation> using owf_constants = typename relation_params<Relation>::OWF_CONSTS;

// The PRG from which the relation's witness is derived, or NoPrg. (FAEST's own OWF constants don't
// derive from RelationConstants.)
template <typename Relation> struct witness_prg_of {
    using type = NoPrg;
};
template <typename Relation>
    requires requires { typename owf_constants<Relation>::WitnessPrg; }
struct witness_prg_of<Relation> {
    using type = typename owf_constants<Relation>::WitnessPrg;
};
template <typename Relation> using WitnessPrg = typename witness_prg_of<Relation>::type;
template <typename Relation> constexpr bool DERIVED_WITNESS = derives_witness<WitnessPrg<Relation>>;

// Size of the VOLE witness in bytes: the witness, or the key from which it's derived.
template <typename Relation>
constexpr size_t VOLE_WITNESS_BYTES = owf_constants<Relation>::WITNESS_BITS / 8;

// Size of the witness in bytes.
template <typename Relation>
constexpr size_t WITNESS_BYTES = [] {
    if constexpr (requires { owf_constants<Relation>::RELATION_WITNESS_BITS; }) {
        return owf_constants<Relation>::RELATION_WITNESS_BITS / 8;
    } else {
        return VOLE_WITNESS_BYTES<Relation>;
    }
}();

// Size of e = w + G(K), or 0 if the witness isn't derived.
template <typename Relation>
constexpr size_t DERIVED_E_BYTES = DERIVED_WITNESS<Relation> ? WITNESS_BYTES<Relation> : 0;

// Size of the FAEST part of a proof in bytes.
template <typename Relation>
constexpr size_t FAEST_PROOF_BYTES = faest::FAEST_SIGNATURE_BYTES<relation_params<Relation>>;

// Size of a proof in bytes: the FAEST part, followed by e if the witness is derived.
template <typename Relation>
constexpr size_t PROOF_BYTES = FAEST_PROOF_BYTES<Relation> + DERIVED_E_BYTES<Relation>;

// Number of QuickSilver constraints: the relation's, and the bit constraints on the key if the
// witness is derived.
template <typename Relation>
constexpr size_t TOTAL_NUM_CONSTRAINTS =
    Relation::NUM_CONSTRAINTS + (DERIVED_WITNESS<Relation> ? 8 * VOLE_WITNESS_BYTES<Relation> : 0);

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

// The QuickSilver states of the prover and verifier.
template <typename Relation, bool verifier>
using quicksilver_for = faest::quicksilver_state<relation_params<Relation>::secpar_v, verifier,
                                                 owf_constants<Relation>::QS_DEGREE>;

// A committed bit of a derived witness.
template <typename QS> using derived_bit = qs_bit<QS, mq::detail::DEGREE>;

// The public map of the PRG from which the relation's witness is derived.
template <typename Relation>
    requires DERIVED_WITNESS<Relation>
using DerivedMap = typename WitnessPrg<Relation>::template Map<8 * WITNESS_BYTES<Relation>>;

template <typename Relation>
    requires DERIVED_WITNESS<Relation>
const DerivedMap<Relation>& derived_map() {
    static_assert(
        requires { Relation::WITNESS_PRG_DST; },
        "a relation whose witness is derived must define WITNESS_PRG_DST");
    static_assert(VOLE_WITNESS_BYTES<Relation> == DerivedMap<Relation>::KEY_BYTES);
    static const DerivedMap<Relation> map(Relation::WITNESS_PRG_DST);
    return map;
}

// The vector e = w + G(K) of a derived witness, at the end of the proof.
template <typename Relation>
std::span<uint8_t, DERIVED_E_BYTES<Relation>> derived_e(proof_span<Relation> proof) {
    return proof.template subspan<FAEST_PROOF_BYTES<Relation>, DERIVED_E_BYTES<Relation>>();
}
template <typename Relation>
std::span<const uint8_t, DERIVED_E_BYTES<Relation>> derived_e(const_proof_span<Relation> proof) {
    return proof.template subspan<FAEST_PROOF_BYTES<Relation>, DERIVED_E_BYTES<Relation>>();
}

// For a derived witness, the key K <- H_5(witness_prefix || mu || rho).
template <typename Relation>
std::array<uint8_t, VOLE_WITNESS_BYTES<Relation>>
derive_key(witness_prefix_span<Relation> witness_prefix,
           const faest::block_2secpar<relation_params<Relation>::secpar_v>& mu,
           const ProveSeed<Relation>& rho) {
    std::array<uint8_t, VOLE_WITNESS_BYTES<Relation>> key;
    faest::hash_state hasher;
    hasher.init(relation_params<Relation>::secpar_v);
    hasher.update(witness_prefix);
    hasher.update(&mu, sizeof(mu));
    hasher.update(rho);
    hasher.update_byte(5); // domain separator for H_5
    hasher.finalize(key);
    return key;
}

// The prover's committed G(K): Evaluate G on the committed key K, whose bits have the VOLE tags
// `macs`. The values of the outputs are G(K), so the prover doesn't need to evaluate G separately
// in the plain. This depends neither on the witness nor on chal2.
template <typename Relation, typename QS>
    requires(!QS::is_verifier)
std::vector<derived_bit<QS>>
prove_committed_prg(const faest::block_secpar<QS::secpar_v>* macs,
                    std::span<const uint8_t, VOLE_WITNESS_BYTES<Relation>> key) {
    constexpr size_t KEY_BITS = 8 * VOLE_WITNESS_BYTES<Relation>;
    // As quicksilver_state::get_witness_bit.
    std::vector<qs_bit<QS, 1>> committed_key;
    committed_key.reserve(KEY_BITS);
    for (size_t i = 0; i < KEY_BITS; ++i) {
        qs_bit<QS, 1> bit(static_cast<const QS*>(nullptr));
        bit.mac = faest::poly_secpar<QS::secpar_v>::load(&macs[i]);
        bit.value() = faest::poly1::load(key[i / 8], i % 8);
        committed_key.push_back(bit);
    }
    const std::array<uint8_t, WITNESS_BYTES<Relation>> zero{};
    return derived_map<Relation>().template qs_eval<QS>(
        std::span<const qs_bit<QS, 1>, KEY_BITS>(committed_key), zero);
}

// For the witness bytes w[off], ..., w[off + |w_part| - 1] = w_part, write e = w + G(K) to the
// same bytes of e and add it to the prover's committed G(K), so that these committed bits are
// e + G(K), of value w.
template <typename Relation, typename QS>
void prove_derived_e(std::span<uint8_t, DERIVED_E_BYTES<Relation>> e,
                     std::vector<derived_bit<QS>>& derived, std::span<const uint8_t> w_part,
                     size_t off) {
    for (size_t k = 0; k < w_part.size(); ++k) {
        uint8_t e_byte = w_part[k];
        for (size_t j = 0; j < 8; ++j) {
            e_byte ^= static_cast<uint8_t>((derived[8 * (off + k) + j].value().data & 1) << j);
        }
        e[off + k] = e_byte;
        for (size_t j = 0; j < 8; ++j) {
            derived[8 * (off + k) + j] += faest::poly1((e_byte >> j) & 1);
        }
    }
}

// For a derived witness, add the bit constraints on the key, and return its committed bits.
template <typename Relation, typename QS>
std::vector<qs_bit<QS, 1>> add_key_bit_constraints(QS* qs) {
    constexpr size_t KEY_BITS = 8 * VOLE_WITNESS_BYTES<Relation>;
    std::vector<qs_bit<QS, 1>> key;
    key.reserve(KEY_BITS);
    for (size_t i = 0; i < KEY_BITS; ++i) {
        key.emplace_back(qs->get_witness_bit(i));
        qs_add_bit_constraint(qs, key.back());
    }
    return key;
}

// Add the relation's constraints. If the witness is derived, then `derived` holds its committed
// bits (of degree 2), on which the constraints are evaluated through DerivedQS.
template <typename Relation, typename QS>
void add_relation_constraints(
    QS* qs, const typename Relation::instance& instance,
    std::span<const uint8_t, relation_params<Relation>::CONSTS::QS::CHALLENGE_BYTES> chal2,
    std::span<const derived_bit<QS>> derived) {
    if constexpr (DERIVED_WITNESS<Relation>) {
        DerivedQS<QS> derived_qs{qs, derived};
        Relation::constraints(&derived_qs, instance, chal2);
    } else {
        (void)derived;
        Relation::constraints(qs, instance, chal2);
    }
}

// Update `hasher` with the part of the proof, written by VOLE generation, that commits the prover
// to the witness prefix: the correction of the witness prefix, or, if the witness is derived, the
// correction of the key and the part of e for the witness prefix.
template <typename Relation>
void hash_witness_prefix_commitment(faest::hash_state& hasher, const_proof_span<Relation> proof) {
    const faest::faest_signature<relation_params<Relation>> view(proof.data());
    if constexpr (DERIVED_WITNESS<Relation>) {
        hasher.update(view.correction());
        hasher.update(derived_e<Relation>(proof).template first<WITNESS_PREFIX_BYTES<Relation>>());
    } else {
        hasher.update(view.correction().template first<WITNESS_PREFIX_BYTES<Relation>>());
    }
}

template <typename Relation> struct PendingProof {
    std::array<uint8_t, relation_params<Relation>::CONSTS::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    faest::hash_state chal2_hasher;
    faest::vole_commit_data<relation_params<Relation>, false> vole_com_data;
    bool delayed_instance;
    std::array<uint8_t, WITNESS_BYTES<Relation>> witness; // the prefix, then the suffix in step 2
    // If the witness is derived: the key, and the committed bits of G(K), to which e is added as
    // it's computed.
    std::array<uint8_t, DERIVED_WITNESS<Relation> ? VOLE_WITNESS_BYTES<Relation> : 0> key;
    std::vector<derived_bit<quicksilver_for<Relation, false>>> derived;
};

// The VOLE generation step. If instance is given, then it's bound to the proof at this step, as in
// FAEST. Otherwise, if instance == nullptr, then it's bound in the commit-and-prove step, as in
// PomFRIT. witness_prefix is the prefix of the witness; the suffix is passed to the second step.
// The caller also provides an optional chal1_binder, which is bound to the proof such that the
// verifier must agree on the value.
//
// The fields of the proof written by this step are the vole commitment, the VOLE check proof,
// iv_pre, and the correction of the witness prefix (or, if the witness is derived, the correction
// of the key and the part of e for the witness prefix).
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

    // (r, iv^pre) <- H_3(witness_prefix || mu || rho)
    block_secpar<S> seed;
    block128 iv_pre;
    {
        std::array<uint8_t, sizeof(seed) + sizeof(iv_pre)> seed_iv_pre;
        hasher.init(S);
        static_assert(0 < WITNESS_PREFIX_BYTES<Relation> &&
                      WITNESS_PREFIX_BYTES<Relation> <= WITNESS_BYTES<Relation>);
        hasher.update(witness_prefix);
        hasher.update(&mu, sizeof(mu));
        hasher.update(rho);
        hasher.update_byte(3); // domain separator for H_3
        hasher.finalize(seed_iv_pre.data(), sizeof(seed_iv_pre));
        memcpy(&seed, seed_iv_pre.data(), sizeof(seed));
        memcpy(&iv_pre, &seed_iv_pre[sizeof(seed)], sizeof(iv_pre));
    }

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

    // Begin chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || [e] || d).
    // The optional delayed-instance hash mu, chal2_binder, e, and d are hashed in the next step.
    hash_state chal2_hasher;
    chal2_hasher.init(S);
    chal2_hasher.update(chal1);
    kos_vole_check_sender<P>(
        vole_com_data.u_bytes().template subspan<0, CP::VOLE_CORRECTION_BYTES>(),
        vole_com_data.v().template subspan<0, CP::VOLE_CORRECTION_ROWS>(), vole_com_data.u_mask(),
        vole_com_data.v_mask(), chal1, proof.vole_check_proof(), chal2_hasher);

    PendingProof<Relation> pending{
        chal1, chal2_hasher, std::move(vole_com_data), delayed_instance, {}, {}, {}};
    std::ranges::copy(witness_prefix, pending.witness.begin());

    const auto u = pending.vole_com_data.u_bytes();
    const auto correction = proof.correction();
    if constexpr (DERIVED_WITNESS<Relation>) {
        // K <- H_5(witness_prefix || mu || rho), and d = u + K: compute the corrections for the
        // key.
        pending.key = derive_key<Relation>(witness_prefix, mu, rho);
        static_assert(correction.size() == VOLE_WITNESS_BYTES<Relation>);
        for (size_t i = 0; i < correction.size(); ++i) {
            correction[i] = u[i] ^ pending.key[i];
        }
        // e = w + G(K) for the witness prefix.
        pending.derived = prove_committed_prg<Relation, quicksilver_for<Relation, false>>(
            pending.vole_com_data.v().data(), pending.key);
        prove_derived_e<Relation>(derived_e<Relation>(proof_bytes), pending.derived, witness_prefix,
                                  0);
    } else {
        // d = u + w: compute corrections for the witness prefix.
        for (size_t i = 0; i < witness_prefix.size(); ++i) {
            correction[i] = u[i] ^ witness_prefix[i];
        }
    }
    return pending;
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
    constexpr auto S = P::secpar_v;
    static_assert(P::use_crt_vole_masks && P::use_grinding && P::use_v3_hash_inputs,
                  "only the FAEST v3 code path is implemented");

    auto& [chal1, hasher, vole_com_data, delayed_instance, witness, key, derived] = pending;
    const mutable_faest_signature<P> proof = proof_bytes.data();
    std::ranges::copy(witness_suffix, witness.begin() + WITNESS_PREFIX_BYTES<Relation>);

    // Finish chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || [e] || d),
    // where mu is included only for delayed instance binding and e only for a derived witness.
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    if (delayed_instance) {
        const auto mu = hash_mu<Relation>(&instance);
        hasher.update(&mu, sizeof(mu));
    }
    hasher.update(chal2_binder);

    const auto correction = proof.correction();
    static_assert(correction.size() == VOLE_WITNESS_BYTES<Relation>);
    if constexpr (DERIVED_WITNESS<Relation>) {
        // e = w + G(K) for the witness suffix. (The key's corrections were computed in the first
        // step.)
        prove_derived_e<Relation>(derived_e<Relation>(proof_bytes), derived, witness_suffix,
                                  WITNESS_PREFIX_BYTES<Relation>);
        hasher.update(derived_e<Relation>(proof_bytes));
    } else {
        // d = u + w: compute corrections for the witness suffix.
        const auto u = vole_com_data.u_bytes();
        for (size_t i = WITNESS_PREFIX_BYTES<Relation>; i < correction.size(); ++i) {
            correction[i] = u[i] ^ witness[i];
        }
    }
    hasher.update(correction);
    hasher.update_byte(8 + 2); // domain separator for H_2^2
    hasher.finalize(chal2);

    // QuickSilver: With CRT VOLECommit, the VOLE tags v for the bits of the VOLE witness are the
    // first WITNESS_BITS entries of v, and the masks are separate.
    using QS = quicksilver_for<Relation, false>;
    const uint8_t* vole_witness = DERIVED_WITNESS<Relation> ? key.data() : witness.data();
    QS qs(vole_witness, vole_com_data.v().data(), TOTAL_NUM_CONSTRAINTS<Relation>, chal2.data());
    if constexpr (DERIVED_WITNESS<Relation>) {
        add_key_bit_constraints<Relation>(&qs);
    }
    add_relation_constraints<Relation>(&qs, instance,
                                       std::span<const uint8_t, CP::QS::CHALLENGE_BYTES>(chal2),
                                       std::span<const derived_bit<QS>>(derived));

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
    constexpr auto S = P::secpar_v;

    const auto& [chal1, vole_com_data, delta, delayed_instance] = pending;
    const faest_signature<P> proof = proof_bytes.data();

    hash_state hasher;

    // chal2 <- H_2^2(chal1 || \tilde{u} || h_V || [mu] || chal2_binder || [e] || d),
    // where mu is included only for delayed instance binding and e only for a derived witness.
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
    if constexpr (DERIVED_WITNESS<Relation>) {
        hasher.update(derived_e<Relation>(proof_bytes));
    }
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

    using QS = quicksilver_for<Relation, true>;
    QS qs(vole_com_data.q().data(), TOTAL_NUM_CONSTRAINTS<Relation>, delta, chal2.data());
    // For a derived witness, w = e + G(K).
    std::vector<derived_bit<QS>> derived;
    if constexpr (DERIVED_WITNESS<Relation>) {
        constexpr size_t KEY_BITS = 8 * VOLE_WITNESS_BYTES<Relation>;
        const auto committed_key = add_key_bit_constraints<Relation>(&qs);
        derived = derived_map<Relation>().template qs_eval<QS>(
            std::span<const qs_bit<QS, 1>, KEY_BITS>(committed_key),
            derived_e<Relation>(proof_bytes));
    }
    add_relation_constraints<Relation>(&qs, instance,
                                       std::span<const uint8_t, CP::QS::CHALLENGE_BYTES>(chal2),
                                       std::span<const derived_bit<QS>>(derived));

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
