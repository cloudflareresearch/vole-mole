// A prototype of the ML-KEM proof of possession (see vole_mole/mlkem_pop.hpp) in binary VOLEitH,
// to compare with the proof over F_q (relation.hpp): the bits of the secret are committed, and the
// arithmetic modulo q is checked by random linear checks on them (see modq/modq.hpp). The statement
// is the same: knowledge of s and e with coefficients in [-eta_1, eta_1] such that t-hat = A-hat *
// NTT(s) + NTT(e).
//
// Write t = NTT^-1(t-hat) and a_ij = NTT^-1(a-hat_ij), so that t = A s + e in R_q^k. The witness
// is s + eta_1 and e + eta_1 as 3 bits per coefficient (2 eta_1 <= 6), with range checks x <= 2
// eta_1 (RangeLe, of degree 2 or 3). After the witness is committed, the verifier picks NUM_CHECKS
// random gamma in R_q^k, and the prover shows <gamma, A s + e> = <gamma, t> (mod q) for each, as
// linear checks on the committed bits (see modq/modq.hpp): the weight of coefficient m of s_j
// is (sum_i gamma_i sigma(a_ij))_m, for sigma(p)(X) = p(X^-1), and that of e_i is gamma_i. Each
// check has soundness error 1 / q, so 11 checks give q^-11 < 2^-128.
//
// The witness is derived from a short key with LocalPrg<2> (DERIVED), or committed directly.

#ifndef VOLE_MOLE_MLKEM_POP_BINARY_HPP
#define VOLE_MOLE_MLKEM_POP_BINARY_HPP

#include "vole_mole/mlkem.hpp"

#include "mlkem/mlkem.hpp"
#include "modq/modq.hpp"
#include "modq/range_le.hpp"
#include "qs_bit.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "faest_sig.hpp"  // from faest-arch-opt
#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <optional>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <vector>

namespace vole_mole::mlkem_pop::binary {

using mlkem::detail::N;
using mlkem::detail::Poly;
constexpr uint32_t Q = mlkem::detail::Q;

template <mlkem::ParamSet P> constexpr size_t param_index() {
    return std::is_same_v<P, mlkem::MlKem512> ? 0 : std::is_same_v<P, mlkem::MlKem768> ? 1 : 2;
}

// Sparse weights with exponents up to DIGIT_EXPS - 1 (see "Recoding" in modq.hpp).
constexpr size_t DIGIT_EXPS = 96;

// About the mean + 13 sd of the carries (see test_mlkem_pop_binary.cpp).
template <mlkem::ParamSet P>
constexpr size_t CARRY_BUDGET = std::array<size_t, 3>{20584, 29736, 38752}[param_index<P>()];

template <mlkem::ParamSet P> struct Spec {
    static constexpr uint32_t Q = binary::Q;
    static constexpr size_t K = P::K;
    static constexpr size_t ETA = P::ETA1;
    static constexpr size_t VALUE_BITS = 3; // x + eta in [0, 2 eta], 2 eta <= 6
    static_assert(2 * ETA < (size_t{1} << VALUE_BITS));
    // Values j < K N are s + eta (s_i at i N), then e + eta.
    static constexpr size_t NUM_VALUES = 2 * K * N;
    static constexpr size_t value_bits(size_t) { return VALUE_BITS; }
    static constexpr size_t bit_shift(size_t, size_t i) { return i; }
    static constexpr uint32_t offset(size_t) { return ETA; }
    // Soundness error q^-11 < 2^-128.
    static constexpr size_t NUM_CHECKS = 11;
    static constexpr size_t DIGIT_EXPS = binary::DIGIT_EXPS;
    static constexpr size_t COUNTER_LOG = 3;
    static constexpr size_t CARRY_BUDGET = binary::CARRY_BUDGET<P>;
};
template <mlkem::ParamSet P> using MQ = modq::detail::ModQ<Spec<P>>;
template <mlkem::ParamSet P>
using Range = modq::detail::RangeLe<2 * P::ETA1, Spec<P>::VALUE_BITS, Spec<P>::VALUE_BITS>;

// Witness layout: the values' bits (bit i of value j at VALUE_BITS j + i), then the answer to the
// checks, committed after the checks are known.
template <mlkem::ParamSet P> struct Layout {
    static constexpr size_t PREFIX_BITS = Spec<P>::VALUE_BITS * Spec<P>::NUM_VALUES;
    static_assert(PREFIX_BITS % 8 == 0);
    static constexpr size_t PREFIX_BYTES = PREFIX_BITS / 8;
    static constexpr size_t OFF_ANSWER = PREFIX_BITS;
    static constexpr size_t WITNESS_BITS = PREFIX_BITS + MQ<P>::ANSWER_BITS;
    static constexpr size_t value_bit(size_t j, size_t i) { return Spec<P>::VALUE_BITS * j + i; }
    // Counters of degree 8, range checks of degree at most 3.
    static constexpr size_t QS_DEGREE = size_t{1} << Spec<P>::COUNTER_LOG;
};

template <bool DERIVED>
using Prg = std::conditional_t<DERIVED, vole_mole::detail::LocalPrg<2>, vole_mole::detail::NoPrg>;

template <mlkem::ParamSet P, bool DERIVED> constexpr faest::owf owf_id() {
    return static_cast<faest::owf>(((0x80u + 3 * DERIVED + param_index<P>()) << 8) | 0b10'0000);
}

} // namespace vole_mole::mlkem_pop::binary

#define VOLE_MOLE_MLKEM_POP_BINARY_OWF(P, DERIVED)                                                 \
    template <>                                                                                    \
    struct faest::OWF_CONSTANTS<faest::secpar::s128,                                               \
                                vole_mole::mlkem_pop::binary::owf_id<P, DERIVED>()>                \
        : vole_mole::detail::RelationConstants<                                                    \
              vole_mole::mlkem_pop::binary::Layout<P>::WITNESS_BITS,                               \
              vole_mole::mlkem_pop::binary::Layout<P>::QS_DEGREE,                                  \
              vole_mole::mlkem_pop::binary::Prg<DERIVED>> {}
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem512, true);
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem768, true);
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem1024, true);
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem512, false);
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem768, false);
VOLE_MOLE_MLKEM_POP_BINARY_OWF(vole_mole::mlkem::MlKem1024, false);
#undef VOLE_MOLE_MLKEM_POP_BINARY_OWF

namespace vole_mole::mlkem_pop::binary {

// Test-only DSTs: this is a prototype.
template <mlkem::ParamSet P> constexpr std::array<uint8_t, 8> dst(char kind) {
    return {'m', 'p', 'o', 'b', 0, static_cast<uint8_t>(kind), static_cast<uint8_t>('0' + P::K),
            '0'};
}
template <mlkem::ParamSet P> inline constexpr auto PROOF_DST = dst<P>('b');
template <mlkem::ParamSet P> inline constexpr auto SEED_DST = dst<P>('s');
template <mlkem::ParamSet P> inline constexpr auto WEIGHTS_DST = dst<P>('w');
template <mlkem::ParamSet P> inline constexpr auto RHO_DST = dst<P>('r');
template <mlkem::ParamSet P> inline constexpr auto PRG_DST = dst<P>('p');

// H(dst || parts...) with output of any length.
inline void xof(std::span<const uint8_t> dst, std::initializer_list<std::span<const uint8_t>> parts,
                std::span<uint8_t> out) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(dst);
    for (const auto& p : parts) {
        h.update(p);
    }
    h.finalize(out.data(), out.size());
}

inline uint32_t fq_add(uint32_t a, uint32_t b) { return (a + b) % Q; }
inline uint32_t fq_sub(uint32_t a, uint32_t b) { return (a + Q - b) % Q; }
inline int32_t centered(uint32_t a) {
    return a > Q / 2 ? static_cast<int32_t>(a) - static_cast<int32_t>(Q) : static_cast<int32_t>(a);
}

// sigma(p)(X) = p(X^-1) in R_q: sigma(p)_0 = p_0 and sigma(p)_{N - n} = -p_n.
inline Poly sigma(const Poly& p) {
    Poly out;
    out[0] = p[0];
    for (size_t n = 1; n < N; ++n) {
        out[N - n] = static_cast<mlkem::detail::Fq>((Q - p[n]) % Q);
    }
    return out;
}

template <mlkem::ParamSet P> struct Statement {
    static constexpr size_t K = P::K;
    const mlkem::EncapsKey<P>* ek;
    std::span<const uint8_t> context;
    mlkem::detail::ParsedEncapsKey<P> parsed;
    std::array<Poly, K> t;               // NTT^-1(t-hat)
    std::array<Poly, K * K> sigma_a_hat; // NTT(sigma(a_ij)), row-major
};

// The statement for ek and context, or std::nullopt if ek fails the modulus check.
template <mlkem::ParamSet P>
std::optional<Statement<P>> make_statement(const mlkem::EncapsKey<P>& ek,
                                           std::span<const uint8_t> context) {
    auto parsed = mlkem::detail::parse_encaps_key<P>(ek);
    if (!parsed) {
        return std::nullopt;
    }
    Statement<P> s{&ek, context, std::move(*parsed), {}, {}};
    for (size_t i = 0; i < P::K; ++i) {
        s.t[i] = s.parsed.t_hat[i];
        mlkem::detail::inv_ntt(s.t[i]);
    }
    for (size_t i = 0; i < P::K * P::K; ++i) {
        Poly a = s.parsed.a_hat[i];
        mlkem::detail::inv_ntt(a);
        s.sigma_a_hat[i] = sigma(a);
        mlkem::detail::ntt(s.sigma_a_hat[i]);
    }
    return s;
}

using CheckSeed = std::array<uint8_t, 32>;

template <mlkem::ParamSet P> struct CheckWeights {
    std::vector<uint32_t> w; // W_{k,j} at k NUM_VALUES + j
    std::array<uint32_t, Spec<P>::NUM_CHECKS> a;
};

// The weights of the checks <gamma_k, A s + e> = <gamma_k, t>.
template <mlkem::ParamSet P>
CheckWeights<P> check_weights(const Statement<P>& stmt, const CheckSeed& seed) {
    constexpr size_t K = P::K;
    constexpr size_t T = Spec<P>::NUM_CHECKS;
    constexpr size_t NV = Spec<P>::NUM_VALUES;
    std::vector<uint8_t> stream(8 * T * K * N);
    xof(WEIGHTS_DST<P>, {seed}, stream);
    CheckWeights<P> cw{std::vector<uint32_t>(T * NV), {}};
    for (size_t k = 0; k < T; ++k) {
        std::array<Poly, K> gamma, gamma_hat;
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                uint64_t v = 0;
                for (size_t b = 0; b < 8; ++b) {
                    v |= uint64_t{stream[8 * ((k * K + i) * N + n) + b]} << (8 * b);
                }
                gamma[i][n] = static_cast<mlkem::detail::Fq>(v % Q);
            }
            gamma_hat[i] = gamma[i];
            mlkem::detail::ntt(gamma_hat[i]);
        }
        const std::span<uint32_t> wk = std::span(cw.w).subspan(k * NV, NV);
        // s_j: sum_i gamma_i sigma(a_ij).
        for (size_t j = 0; j < K; ++j) {
            Poly acc{};
            for (size_t i = 0; i < K; ++i) {
                mlkem::detail::multiply_ntts_acc(acc, gamma_hat[i], stmt.sigma_a_hat[i * K + j]);
            }
            mlkem::detail::inv_ntt(acc);
            std::ranges::copy(acc, wk.begin() + static_cast<ptrdiff_t>(j * N));
        }
        // e_i: gamma_i. The constant: <gamma, t>.
        uint64_t a = 0;
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                wk[K * N + i * N + n] = gamma[i][n];
                a += uint64_t{gamma[i][n]} * stmt.t[i][n];
            }
        }
        cw.a[k] = static_cast<uint32_t>(a % Q);
    }
    return cw;
}

template <mlkem::ParamSet P> typename MQ<P>::Weights make_weights(const CheckWeights<P>& cw) {
    return MQ<P>::make_weights(cw.w, cw.a);
}

template <mlkem::ParamSet P, bool DERIVED> struct BinRelation {
    using params =
        faest::parameter_set<faest::secpar::s128, /* TAU */ 17, owf_id<P, DERIVED>(),
                             faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                             /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                             /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;
    using L = Layout<P>;
    struct instance {
        const Statement<P>* stmt;
        CheckSeed seed;
        const typename MQ<P>::Weights* weights; // derived from stmt and seed
    };
    static constexpr size_t NUM_CONSTRAINTS = (DERIVED ? 0 : L::WITNESS_BITS) +
                                              Spec<P>::NUM_VALUES * Range<P>::NUM_CONSTRAINTS +
                                              MQ<P>::NUM_BINARY_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = L::PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = PROOF_DST<P>;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST = PRG_DST<P>;

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update(*x.stmt->ek);
        const uint64_t len = x.stmt->context.size();
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(len >> (8 * i)));
        }
        h.update(x.stmt->context);
        h.update(x.seed);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        if constexpr (!DERIVED) {
            for (size_t i = 0; i < L::WITNESS_BITS; ++i) {
                vole_mole::detail::qs_add_bit_constraint(qs, qs->get_witness_bit(i));
            }
        }
        for (size_t j = 0; j < Spec<P>::NUM_VALUES; ++j) {
            Range<P>::constraints(
                qs, [&](size_t i) { return qs->get_witness_bit(L::value_bit(j, i)); },
                [&] {
                    return qs->get_witness_bit(0); /* unused */
                });
        }
        MQ<P>::qs_constraints(qs, *x.weights, L::OFF_ANSWER, [&](size_t j, size_t i) {
            return qs->get_witness_bit(L::value_bit(j, i));
        });
    }
};

template <mlkem::ParamSet P, bool DERIVED>
constexpr size_t PROOF_BYTES = vole_mole::detail::PROOF_BYTES<BinRelation<P, DERIVED>>;

template <mlkem::ParamSet P, bool DERIVED>
CheckSeed check_seed(const Statement<P>& stmt, std::span<const uint8_t> chal1,
                     std::span<const uint8_t, PROOF_BYTES<P, DERIVED>> proof) {
    using R = BinRelation<P, DERIVED>;
    const faest::faest_signature<typename R::params> view(proof.data());
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(SEED_DST<P>);
    h.update(*stmt.ek);
    const uint64_t len = stmt.context.size();
    for (size_t i = 0; i < 8; ++i) {
        h.update_byte(static_cast<uint8_t>(len >> (8 * i)));
    }
    h.update(stmt.context);
    h.update(chal1);
    h.update(view.vole_check_proof());
    vole_mole::detail::hash_witness_prefix_commitment<R>(h, proof);
    CheckSeed seed;
    h.finalize(seed);
    return seed;
}

// The values s + eta, e + eta (as VALUE_BITS bits each), i.e., the witness prefix, for
// coefficients x (s, then e, centered). Values outside [-eta, 2^VALUE_BITS - 1 - eta] are
// truncated.
template <mlkem::ParamSet P> std::vector<uint8_t> encode_prefix(std::span<const int32_t> x) {
    std::vector<uint8_t> prefix(Layout<P>::PREFIX_BYTES);
    for (size_t j = 0; j < Spec<P>::NUM_VALUES; ++j) {
        const auto v = static_cast<uint32_t>(x[j] + static_cast<int32_t>(P::ETA1));
        for (size_t i = 0; i < Spec<P>::VALUE_BITS; ++i) {
            const size_t b = Layout<P>::value_bit(j, i);
            prefix[b / 8] = static_cast<uint8_t>(prefix[b / 8] | (((v >> i) & 1) << (b % 8)));
        }
    }
    return prefix;
}

inline bool get_bit(std::span<const uint8_t> b, size_t i) {
    return ((b[i / 8] >> (i % 8)) & 1) != 0;
}

using Rho = std::array<uint8_t, 32>;

// A proof for the witness prefix, which isn't checked.
template <mlkem::ParamSet P, bool DERIVED>
std::vector<uint8_t> prove_prefix(const Statement<P>& stmt, std::span<const uint8_t> prefix_bytes,
                                  const Rho& rho) {
    using R = BinRelation<P, DERIVED>;
    using M = MQ<P>;
    using vole_mole::detail::ProveSeed;
    std::vector<uint8_t> proof(PROOF_BYTES<P, DERIVED>);
    const std::span<uint8_t, PROOF_BYTES<P, DERIVED>> bin(proof);
    const std::span<const uint8_t, Layout<P>::PREFIX_BYTES> prefix(prefix_bytes.data(),
                                                                   Layout<P>::PREFIX_BYTES);
    const auto value_bit = [&](size_t j, size_t i) {
        return get_bit(prefix, Layout<P>::value_bit(j, i));
    };
    std::vector<uint8_t> answer(M::ANSWER_BYTES);
    for (uint8_t attempt = 0; attempt < 8; ++attempt) {
        ProveSeed<R> rho_bin;
        const std::array<uint8_t, 1> a = {attempt};
        xof(RHO_DST<P>, {rho, a}, rho_bin);
        auto pending = vole_mole::detail::voleith_vole_gen<R>(bin, nullptr, prefix, rho_bin);
        typename R::instance inst{&stmt, check_seed<P, DERIVED>(stmt, pending.chal1, bin), nullptr};
        const auto weights = make_weights<P>(check_weights<P>(stmt, inst.seed));
        if (!M::answer(weights, value_bit, std::span<uint8_t, M::ANSWER_BYTES>(answer))) {
            continue; // the checks need more committed bits than the budget
        }
        inst.weights = &weights;
        vole_mole::detail::voleith_prove_commit<R>(
            bin, inst, std::span<const uint8_t, M::ANSWER_BYTES>(answer), std::move(pending));
        return proof;
    }
    throw std::runtime_error("ML-KEM PoP (binary): too many attempts");
}

// The witness (s, then e, centered) of a decapsulation key, unchecked.
template <mlkem::ParamSet P>
std::vector<int32_t> witness_of(const Statement<P>& stmt, const mlkem::DecapsKey<P>& dk) {
    using Parts = mlkem::detail::DecapsKeyParts<P>;
    using mlkem::detail::POLY_BYTES;
    constexpr size_t K = P::K;
    std::array<Poly, K> s_hat;
    for (size_t i = 0; i < K; ++i) {
        if (!mlkem::detail::decode12(std::span(dk)
                                         .subspan(Parts::OFF_S_HAT + i * POLY_BYTES)
                                         .template first<POLY_BYTES>(),
                                     s_hat[i])) {
            throw std::invalid_argument("ML-KEM PoP: s-hat isn't reduced modulo q");
        }
    }
    std::vector<int32_t> x(2 * K * N);
    for (size_t i = 0; i < K; ++i) {
        Poly s = s_hat[i];
        mlkem::detail::inv_ntt(s);
        Poly acc{};
        for (size_t j = 0; j < K; ++j) {
            mlkem::detail::multiply_ntts_acc(acc, stmt.parsed.a_hat[i * K + j], s_hat[j]);
        }
        mlkem::detail::inv_ntt(acc);
        for (size_t n = 0; n < N; ++n) {
            x[i * N + n] = centered(s[n]);
            x[K * N + i * N + n] = centered(fq_sub(stmt.t[i][n], acc[n]));
        }
    }
    return x;
}

template <mlkem::ParamSet P, bool DERIVED>
std::vector<uint8_t> prove(const mlkem::DecapsKey<P>& dk, std::span<const uint8_t> context,
                           const Rho& rho) {
    using Parts = mlkem::detail::DecapsKeyParts<P>;
    mlkem::EncapsKey<P> ek;
    std::copy_n(dk.begin() + Parts::OFF_EK, ek.size(), ek.begin());
    const auto stmt = make_statement<P>(ek, context);
    if (!stmt) {
        throw std::invalid_argument("ML-KEM PoP: encapsulation key fails the modulus check");
    }
    const auto x = witness_of<P>(*stmt, dk);
    for (const int32_t v : x) {
        if (v < -static_cast<int32_t>(P::ETA1) || v > static_cast<int32_t>(P::ETA1)) {
            throw std::invalid_argument("ML-KEM PoP: the decapsulation key's secret isn't short");
        }
    }
    return prove_prefix<P, DERIVED>(*stmt, encode_prefix<P>(x), rho);
}

template <mlkem::ParamSet P, bool DERIVED>
bool verify(const mlkem::EncapsKey<P>& ek, std::span<const uint8_t> context,
            std::span<const uint8_t> proof) {
    using R = BinRelation<P, DERIVED>;
    if (proof.size() != PROOF_BYTES<P, DERIVED>) {
        return false;
    }
    const auto stmt = make_statement<P>(ek, context);
    if (!stmt) {
        return false;
    }
    const std::span<const uint8_t, PROOF_BYTES<P, DERIVED>> bin(proof.data(), proof.size());
    auto pending = vole_mole::detail::voleith_vole_reconstruct<R>(bin, nullptr);
    if (!pending) {
        return false;
    }
    typename R::instance inst{&*stmt, check_seed<P, DERIVED>(*stmt, pending->chal1, bin), nullptr};
    const auto weights = make_weights<P>(check_weights<P>(*stmt, inst.seed));
    if (MQ<P>::count_carries(weights) > MQ<P>::CARRY_BUDGET) {
        return false;
    }
    inst.weights = &weights;
    return vole_mole::detail::voleith_verify_commit<R>(bin, inst, std::move(*pending));
}

} // namespace vole_mole::mlkem_pop::binary

#endif
