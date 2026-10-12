#include "vole_mole/mldsa_pok.hpp"

#include "vole_mole/keccak.hpp"
#include "vole_mole/mldsa.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "keccak/segmented.hpp"
#include "mldsa/mldsa.hpp"
#include "mldsa_pok/prover.hpp"
#include "mldsa_pok/relation.hpp"
#include "mldsa_pok/shake_relation.hpp"
#include "modq/columns.hpp"
#include "modq/modq.hpp"
#include "qs_bit.hpp"
#include "voleith.hpp"

#include "faest_sig.hpp"   // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

namespace vole_mole::mldsa_pok {

namespace detail {

namespace {

using mldsa::detail::fq_add;
using mldsa::detail::fq_mul;
using mldsa::detail::fq_neg;
using mldsa::detail::fq_sub;

bool get_bit(std::span<const uint8_t> b, size_t i) { return ((b[i / 8] >> (i % 8)) & 1) != 0; }
void set_bit(std::span<uint8_t> b, size_t i, bool v) {
    b[i / 8] = static_cast<uint8_t>((b[i / 8] & ~(1u << (i % 8))) | (unsigned{v} << (i % 8)));
}

template <typename QS, size_t deg> void zero(QS* qs, const vole_mole::detail::qs_bit<QS, deg>& x) {
    qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(x));
}

// sigma(p)(X) = p(X^-1) in R_q: sigma(p)_0 = p_0 and sigma(p)_{N - n} = -p_n.
Poly sigma(const Poly& p) {
    Poly out;
    out[0] = p[0];
    for (size_t n = 1; n < N; ++n) {
        out[N - n] = mldsa::detail::fq_neg(p[n]);
    }
    return out;
}

} // namespace

Statement make_statement(const mldsa::PublicKey<P>& pk, std::span<const uint8_t, 64> mu) {
    Statement s{&pk, mldsa::detail::parse_public_key<P>(pk), {}, {}, {}};
    std::ranges::copy(mu, s.mu.begin());
    for (size_t i = 0; i < K * L; ++i) {
        Poly a = s.parsed.a_hat[i];
        mldsa::detail::inv_ntt(a);
        s.sigma_a_hat[i] = sigma(a);
        mldsa::detail::ntt(s.sigma_a_hat[i]);
    }
    for (size_t i = 0; i < K; ++i) {
        Poly t;
        for (size_t n = 0; n < N; ++n) {
            t[n] = fq_mul(s.parsed.t1[i][n], 1u << mldsa::detail::D);
        }
        s.sigma_t1_hat[i] = sigma(t);
        mldsa::detail::ntt(s.sigma_t1_hat[i]);
    }
    return s;
}

Statement statement_for(const mldsa::PublicKey<P>& pk, std::span<const uint8_t> msg,
                        std::span<const uint8_t> ctx) {
    if (ctx.size() > mldsa::MAX_CONTEXT_BYTES) {
        throw std::invalid_argument("ML-DSA PoK: context too long");
    }
    const auto parsed = mldsa::detail::parse_public_key<P>(pk);
    const auto mu = mldsa::detail::message_representative(parsed.tr, msg, ctx);
    return make_statement(pk, mu);
}

// ---------------------------------------------------------------------------------------------
// The checks

std::vector<Elem> check_weights(const Statement& stmt, const CheckSeed& seed) {
    constexpr size_t T = ModQSpec::NUM_CHECKS;
    // gamma_{k,i}: 8 bytes per coefficient, reduced modulo q (statistically close to uniform).
    std::vector<uint8_t> stream(8 * T * K * N);
    {
        const std::array<std::span<const uint8_t>, 2> parts = {
            vole_mole::detail::MLDSA_POK_WEIGHTS_DST, seed};
        mldsa::detail::shake256(parts, stream);
    }
    std::vector<Elem> w(T * NUM_VALUES);
    for (size_t k = 0; k < T; ++k) {
        std::array<Poly, K> gamma, gamma_hat;
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                uint64_t v = 0;
                for (size_t b = 0; b < 8; ++b) {
                    v |= uint64_t{stream[8 * ((k * K + i) * N + n) + b]} << (8 * b);
                }
                gamma[i][n] = static_cast<Elem>(v % Q);
            }
            gamma_hat[i] = gamma[i];
            mldsa::detail::ntt(gamma_hat[i]);
        }
        const std::span<Elem> wk = std::span(w).subspan(k * NUM_VALUES, NUM_VALUES);
        // z_l: sum_i gamma_i sigma(a_il).
        for (size_t l = 0; l < L; ++l) {
            Poly acc{};
            for (size_t i = 0; i < K; ++i) {
                mldsa::detail::multiply_ntts_acc(acc, gamma_hat[i], stmt.sigma_a_hat[i * L + l]);
            }
            mldsa::detail::inv_ntt(acc);
            std::ranges::copy(acc, wk.begin() + static_cast<ptrdiff_t>(V_OFF_Z + l * N));
        }
        // c: -sum_i gamma_i sigma(t1_i 2^d).
        {
            Poly acc{};
            for (size_t i = 0; i < K; ++i) {
                mldsa::detail::multiply_ntts_acc(acc, gamma_hat[i], stmt.sigma_t1_hat[i]);
            }
            mldsa::detail::inv_ntt(acc);
            for (size_t x = 0; x < N; ++x) {
                wk[V_OFF_C + x] = fq_neg(acc[x]);
            }
        }
        // psi and f: -gamma2 gamma and -gamma.
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                wk[V_OFF_PSI + i * N + n] = fq_neg(fq_mul(GAMMA2, gamma[i][n]));
                wk[V_OFF_F + i * N + n] = fq_neg(gamma[i][n]);
            }
        }
    }
    return w;
}

CheckSeed check_seed(const Statement& stmt, const Chal1& chal1,
                     std::span<const uint8_t, PROOF_BYTES_> proof) {
    const faest::faest_signature<BinRelation::params> view(proof.data());
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::MLDSA_POK_SEED_DST);
    h.update(*stmt.pk);
    h.update(stmt.mu);
    h.update(chal1);
    h.update(view.vole_check_proof());
    vole_mole::detail::hash_witness_prefix_commitment<BinRelation>(h, proof);
    CheckSeed seed;
    h.finalize(seed);
    return seed;
}

// ---------------------------------------------------------------------------------------------
// The binary relation

bool hint_weight_witness(std::span<uint8_t, B_PREFIX_BYTES> prefix) {
    HintCols::PlainOps ops{prefix, B_OFF_HINT_CARRIES, HINT_CARRIES};
    std::vector<std::vector<uint8_t>> cols;
    hint_weight_columns(
        ops, [&](size_t i) { return static_cast<uint8_t>(get_bit(prefix, i)); }, cols);
    bool ok = true;
    HintCols::reduce(ops, cols, [&](size_t col, uint8_t w) { ok &= w == ((OMEGA >> col) & 1); });
    return ops.finish() && ok;
}

template <typename QS>
void BinRelation::constraints(QS* qs, const instance& x,
                              std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
    using Bit = vole_mole::detail::qs_bit<QS, 1>;
    using faest::poly1;
    using vole_mole::detail::qs_mul;

    // The witness is derived, so it consists of bits by construction (see voleith.hpp).

    // c-tilde = H(mu || w1Encode(w1), 32), the first 256 bits of the state.
    const auto ct_state = Ctilde::qs_sponge(qs, std::span<const uint8_t, 64>(x.stmt->mu));

    // The SampleInBall stream: one permutation of c-tilde || 0x1f || 0^* || 0x80.
    keccak::detail::QsState<QS> sib_state(KF1600_STATE_BITS, Bit(poly1(0), qs));
    for (size_t i = 0; i < 8 * Ctilde::OUT_BYTES; ++i) {
        sib_state[i] = ct_state[i];
    }
    for (size_t k = 0; k < 8; ++k) {
        if ((0x1f >> k) & 1) {
            sib_state[8 * Ctilde::OUT_BYTES + k] = sib_state[8 * Ctilde::OUT_BYTES + k] + poly1(1);
        }
    }
    sib_state[8 * SHAKE256_RATE - 1] = sib_state[8 * SHAKE256_RATE - 1] + poly1(1);
    const auto stream = SibPerm::qs_keccak(qs, std::move(sib_state), B_OFF_SIB_STATES);
    static_assert(Sib::STREAM_BYTES <= SHAKE256_RATE);
    Sib::constraints(qs, std::span<const Bit>(stream).first(8 * Sib::STREAM_BYTES), B_OFF_SIB);

    // w1 < 44 = 0b101100: not b5 (b4 or b3 b2).
    for (size_t j = 0; j < NUM_R; ++j) {
        std::array<Bit, W1_BITS> b;
        for (size_t i = 0; i < W1_BITS; ++i) {
            b[i] = qs->get_witness_bit(w1_bit(j, i));
        }
        const auto b54 = qs_mul(b[5], b[4]);
        const auto b532 = qs_mul(qs_mul(b[5], b[3]), b[2]);
        const auto b5432 = qs_mul(qs_mul(b54, b[3]), b[2]);
        zero(qs, vole_mole::detail::qs_bit<QS, 4>(vole_mole::detail::qs_bit<QS, 3>(b54) + b532) +
                     b5432);
    }

    // b0 b1 = 0
    for (size_t j = 0; j < NUM_R; ++j) {
        zero(qs, qs_mul(qs->get_witness_bit(hint_bit(j, 0)), qs->get_witness_bit(hint_bit(j, 1))));
    }

    // sum_i (1 + b0_i) + slack = OMEGA
    {
        typename HintCols::template QsOps<QS> ops{qs, B_OFF_HINT_CARRIES, HINT_CARRIES};
        std::vector<std::vector<Bit>> cols;
        hint_weight_columns(ops, [&](size_t i) { return qs->get_witness_bit(i); }, cols);
        HintCols::reduce(ops, cols, [&](size_t col, const Bit& w) {
            ops.assert_equal(w, ((OMEGA >> col) & 1) != 0);
        });
        ops.finish();
    }

    // z + Z_BOUND <= 2 Z_BOUND and f + gamma2 - 1 <= alpha - 1.
    for (size_t j = 0; j < NUM_Z; ++j) {
        ZRange::constraints(
            qs, [&](size_t i) { return qs->get_witness_bit(z_bit(j, i)); },
            [&] { return qs->get_witness_bit(z_helper_bit(j)); });
    }
    for (size_t j = 0; j < NUM_R; ++j) {
        FRange::constraints(
            qs, [&](size_t i) { return qs->get_witness_bit(f_bit(j, i)); },
            [&] {
                return qs->get_witness_bit(0); /* unused */
            });
    }

    // r - gamma2 psi - f = 0, by random checks.
    MlDsaModQ::qs_constraints(qs, *x.weights, B_OFF_ANSWER, [&](size_t j, size_t i) {
        return qs->get_witness_bit(value_bit(j, i));
    });
}

// ---------------------------------------------------------------------------------------------
// The prover

Witness make_witness(const Statement& stmt, const mldsa::detail::DecodedSignature<P>& sig) {
    using mldsa::detail::fq_centered;
    Witness wit{std::vector<uint8_t>(B_PREFIX_BYTES)};
    auto& prefix = wit.prefix;

    const Poly c = mldsa::detail::sample_in_ball(sig.c_tilde, P::TAU);
    const auto r = mldsa::detail::w_approx<P>(stmt.parsed, sig.z, c);

    // w1, the hint classes, and f.
    std::array<Poly, K> w1;
    size_t weight = 0;
    for (size_t i = 0; i < K; ++i) {
        for (size_t n = 0; n < N; ++n) {
            const size_t j = i * N + n;
            w1[i][n] = mldsa::detail::use_hint(sig.h[i][n], r[i][n], GAMMA2);
            const int32_t e = fq_centered(fq_sub(r[i][n], fq_mul(ALPHA, w1[i][n])));
            const int32_t g2 = static_cast<int32_t>(GAMMA2);
            int32_t f;
            uint32_t u; // psi + 1 - 2 w1
            if (-g2 < e && e <= g2) {
                f = e, u = 1;
            } else if (g2 < e && e <= 2 * g2) {
                f = e - g2, u = 2;
            } else if (-2 * g2 < e && e <= -g2) {
                f = e + g2, u = 0;
            } else {
                throw std::runtime_error(
                    "ML-DSA PoK: the signature hits an uncovered boundary case");
            }
            weight += u != 1;
            set_bit(prefix, hint_bit(j, 0), u == 1);
            set_bit(prefix, hint_bit(j, 1), u == 2);
            const auto fv = static_cast<uint32_t>(f + g2 - 1);
            for (size_t b = 0; b < F_BITS; ++b) {
                set_bit(prefix, f_bit(j, b), ((fv >> b) & 1) != 0);
            }
        }
    }
    if (weight > OMEGA) {
        throw std::runtime_error("ML-DSA PoK: the signature hits an uncovered boundary case");
    }
    for (size_t i = 0; i < SLACK_BITS; ++i) {
        set_bit(prefix, B_OFF_SLACK + i, (((OMEGA - weight) >> i) & 1) != 0);
    }
    if (!hint_weight_witness(std::span<uint8_t, B_PREFIX_BYTES>(prefix))) {
        throw std::logic_error("ML-DSA PoK: hint weight");
    }

    // The c-tilde hash.
    const auto w1_enc = mldsa::detail::w1_encode(w1, GAMMA2);
    std::array<uint8_t, Ctilde::OUT_BYTES> c_tilde;
    const auto ct_wit =
        Ctilde::encode_witness(std::span<const uint8_t, 64>(stmt.mu),
                               std::span<const uint8_t, Ctilde::SECRET_BYTES>(w1_enc), c_tilde);
    std::ranges::copy(ct_wit, prefix.begin() + B_OFF_W1);
    if (c_tilde != sig.c_tilde) {
        throw std::logic_error("ML-DSA PoK: c-tilde mismatch");
    }

    // The SampleInBall hash.
    Kf1600State st{};
    std::ranges::copy(c_tilde, st.begin());
    st[Ctilde::OUT_BYTES] ^= 0x1f;
    st[SHAKE256_RATE - 1] ^= 0x80;
    const auto states = std::span(prefix)
                            .subspan(B_OFF_SIB_STATES)
                            .template first<SibPerm::COMMITTED_STATES_BYTES>();
    SibPerm::encode_committed_states(states, st);
    std::array<uint8_t, Sib::STREAM_BYTES> stream;
    std::copy_n(states.end() - KF1600_STATE_BYTES, stream.size(), stream.begin());

    // SampleInBall, and c + 1.
    const auto c_bits = Sib::encode_witness(stream, prefix, B_OFF_SIB);
    if (!c_bits) {
        throw std::runtime_error("ML-DSA PoK: the signature hits an uncovered boundary case");
    }
    for (size_t x = 0; x < N; ++x) {
        const int expect = c[x] == 0 ? 0 : (c[x] == 1 ? 1 : -1);
        if ((*c_bits)[x] != expect) {
            throw std::logic_error("ML-DSA PoK: SampleInBall mismatch");
        }
    }

    // z + Z_BOUND, and the range helper.
    for (size_t l = 0; l < L; ++l) {
        for (size_t n = 0; n < N; ++n) {
            const size_t j = l * N + n;
            const int32_t z = fq_centered(sig.z[l][n]);
            const auto zv = static_cast<uint32_t>(z + static_cast<int32_t>(Z_BOUND));
            for (size_t b = 0; b < Z_BITS; ++b) {
                set_bit(prefix, z_bit(j, b), ((zv >> b) & 1) != 0);
            }
            set_bit(prefix, z_helper_bit(j),
                    ZRange::helper([&](size_t b) { return ((zv >> b) & 1) != 0; }));
        }
    }
    return wit;
}

Proof prove_witness(const Statement& stmt, const Witness& w, const Rho& rho) {
    using vole_mole::detail::ProveSeed;
    Proof proof(PROOF_BYTES_);
    const std::span<uint8_t, PROOF_BYTES_> bin(proof);
    const std::span<const uint8_t, B_PREFIX_BYTES> prefix(w.prefix);
    std::vector<uint8_t> answer(MlDsaModQ::ANSWER_BYTES);
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
        const Weights weights = MlDsaModQ::make_weights(check_weights(stmt, inst.seed));
        if (!MlDsaModQ::answer(
                weights, [&](size_t j, size_t i) { return get_bit(prefix, value_bit(j, i)); },
                std::span<uint8_t, MlDsaModQ::ANSWER_BYTES>(answer))) {
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
    const Weights weights = MlDsaModQ::make_weights(check_weights(stmt, inst.seed));
    if (MlDsaModQ::count_carries(weights) > MlDsaModQ::CARRY_BUDGET) {
        return false;
    }
    inst.weights = &weights;
    return vole_mole::detail::voleith_verify_commit<BinRelation>(bin, inst, std::move(*pending));
}

Proof prove_with_seed(const mldsa::PublicKey<P>& pk, std::span<const uint8_t> msg,
                      std::span<const uint8_t> ctx, const mldsa::Signature<P>& sig,
                      const Rho& rho) {
    if (!mldsa::verify<P>(pk, msg, ctx, sig)) {
        throw std::invalid_argument("ML-DSA PoK: invalid signature");
    }
    const auto decoded = mldsa::detail::decode_signature<P>(sig);
    if (!decoded) {
        throw std::invalid_argument("ML-DSA PoK: invalid signature");
    }
    const auto stmt = statement_for(pk, msg, ctx);
    return prove_witness(stmt, make_witness(stmt, *decoded), rho);
}

} // namespace detail

const size_t PROOF_BYTES = detail::PROOF_BYTES_;

Proof prove(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> msg,
            std::span<const uint8_t> ctx, const mldsa::Signature<mldsa::MlDsa44>& sig) {
    return detail::prove_with_seed(pk, msg, ctx, sig, random_bytes<32>());
}

bool verify(const mldsa::PublicKey<mldsa::MlDsa44>& pk, std::span<const uint8_t> msg,
            std::span<const uint8_t> ctx, std::span<const uint8_t> proof) {
    if (ctx.size() > mldsa::MAX_CONTEXT_BYTES || proof.size() != PROOF_BYTES) {
        return false;
    }
    const auto stmt = detail::statement_for(pk, msg, ctx);
    return detail::verify_proof(
        stmt, std::span<const uint8_t, detail::PROOF_BYTES_>(proof.data(), proof.size()));
}

} // namespace vole_mole::mldsa_pok
