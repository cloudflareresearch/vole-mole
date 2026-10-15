// Circuit gadgets for ML-DSA-44 verification on a hidden message, in binary VOLEitH, for use in
// larger relations (see relation.hpp for a standalone one).
//
//   VerifyGadget: ML-DSA.Verify on a hidden message representative mu, given as committed bits by
//     the enclosing relation. The secret signature (c-tilde, z, h) is in the gadget's witness.
//   MuHash<MSG_BYTES>: mu = H(tr || 0 || 0 || M, 64), the message representative of FIPS 204
//     (Algorithm 3, with the external interface and an empty context string), for a hidden M of
//     MSG_BYTES bytes in the gadget's witness, where the enclosing relation may constrain it
//     further. Its output feeds VerifyGadget.
//
// Each gadget owns a byte-aligned region of the witness, at an offset chosen by the enclosing
// relation, and adds constraints of degree at most QS_DEGREE. They assume that every witness bit
// is a bit (as for a derived witness, see "Derived witnesses" in voleith.hpp); otherwise, the
// enclosing relation must add the bit constraints.
//
// The statement of VerifyGadget. Public: pk = (rho, t1). Secret: mu and the signature (c-tilde, z,
// h). ML-DSA.Verify accepts if and only if ||z||_inf < gamma1 - beta, h has at most omega ones,
// and c-tilde = H(mu || w1Encode(w1), 32) for
//
//   c = SampleInBall(c-tilde),  r = A z - c t1 2^d (mod q),  w1 = UseHint(h, r).
//
// The UseHint condition. Write alpha = 2 gamma2 (so q - 1 = 44 alpha) and e = r - alpha w1 (mod q,
// centered). Working through Decompose and UseHint (FIPS 204, Algorithms 36 and 40): for a given
// w1 in [0, 44),
//
//   UseHint(0, r) = w1 iff e in S0(w1) = (-gamma2, gamma2], plus e = -gamma2 if w1 = 0;
//   UseHint(1, r) = w1 iff e in S1(w1) = [-alpha + 1, -gamma2] u [gamma2 + 1, alpha], with
//     instead [-alpha, -gamma2 - 1] u [gamma2 + 1, alpha] if w1 = 0, plus e = alpha + 1 if
//     w1 = 43.
//
// (The exceptions come from the wrap-around at q - 1 = 44 alpha; test_mldsa_pok.cpp checks this
// against UseHint for every r.) We use a hint class u in {neg, none, pos}, write
//
//   e = gamma2 (hp - hn) + f,  f in (-gamma2, gamma2], or f = -gamma2 if w1 = 0, or
//                              f = gamma2 + 1 if w1 = 43 and u != none,
//
// where hp = [u = pos] and hn = [u = neg], and count the hints hp + hn. Then u = none implies
// e in S0(w1), and u in {pos, neg} implies e in S0(w1) u S1(w1) (e in (0, alpha] or (-alpha, 0],
// or one of the exceptions: e in {0, -alpha} for w1 = 0, e in {1, alpha + 1} for w1 = 43). So if
// the proof verifies, then setting h_i = 1 exactly where e_i is not in S0(w1_i) gives a signature
// with at most as many hints as the proof counts, and UseHint(h, r) = w1: the statement is sound.
// Conversely, an honest prover represents every e of a valid signature, with u = none wherever the
// signature has no hint, so every valid signature can be proven. The two guarded values of f
// handle the boundary cases e = -gamma2 or -alpha with w1 = 0 and e = alpha + 1 with w1 = 43, as
// Baum and Beckmann ("edaBits in the Exponent and Issuer-Hiding Blind Signatures from ML-DSA and
// VOLE-in-the-Head", Appendix G.2) handle the boundary case of Decompose with a guarded assertion.
// (Without them, about one in 2^16 signatures couldn't be proven, which matters when the
// signature, or its message, comes from elsewhere in the circuit.)
//
// The guarded values are encoded with two bits per coefficient, nb = [f != -gamma2] and
// yb = [f = gamma2 + 1], and 18 bits of f' + gamma2 - 1 in [0, alpha - 1] for f' in
// (-gamma2, gamma2], with f = f' - (1 - nb) + yb, i.e., f + gamma2 = (f' + gamma2 - 1) + nb + yb.
// The guards are the constraints (1 + nb) (1 + [w1 = 0]) = 0 and yb (1 + (1 + b0) [w1 = 43]) = 0,
// of degree 7 and 8.
//
// Note e = r - alpha w1 - gamma2 (hp - hn) = r - gamma2 psi for psi = 2 w1 + hp - hn in [-1, 87].
//
// The witness of VerifyGadget, all committed before the checks (below):
//
//   - w1Encode(w1), i.e., the 6 bits of each coefficient of w1, constrained to w1 < 44;
//   - the c-tilde hash (7 Keccak-f[1600] permutations, see shake_relation.hpp), which absorbs mu,
//     and whose output c-tilde feeds the SampleInBall hash (1 permutation) and the SampleInBall
//     circuit (see sample_in_ball.hpp), whose output is c + 1 in {0, 1, 2} as 2 bits per
//     coefficient;
//   - the hint class of each coefficient as 2 bits, b0 = [u = none] and b1 = [u = pos]
//     (b0 b1 = 0, and then psi + 1 = b0 + 2 b1 + 2 w1), and a 7-bit slack with
//     sum_i (1 + b0_i) + slack = omega (an integer sum, see modq/columns.hpp);
//   - z + B in [0, 2B] for B = gamma1 - beta - 1, and f' + gamma2 - 1 in [0, alpha - 1], as 18
//     bits per coefficient, with range checks (see `RangeLe`), and nb and yb.
//
// The checks. The equations r - gamma2 psi - f = 0 for r = A z - c t1 2^d are linear in the bits
// of z, c, psi, and f. After the witness above (and mu) is committed, the verifier picks
// NUM_CHECKS random combinations of the K N equations, and the prover shows each modulo q (see
// modq/modq.hpp), with soundness error 1 / q per check, with an answer of ANSWER_BITS bits that's
// committed after the checks are known. So the enclosing relation must commit to the gadget's
// witness before it derives the check seed, e.g., by putting it in the witness prefix (see
// voleith.hpp), and put the answer after it.
//
// For gamma in R_q^K (uniform, derived from the check seed), the combination is
// <gamma, A z - c t1 2^d - gamma2 psi - f>, with <u, v> = sum_n u_n v_n for polynomials
// (coefficient vectors). Write sigma(p)(X) = p(X^-1), an automorphism of R_q (so
// sigma(p)_0 = p_0 and sigma(p)_{N - n} = -p_n). Then <u, v> is the constant coefficient of
// sigma(u) v, and so <gamma_i, a z> = <gamma_i sigma(a), z>. So the weight of coefficient m of z_l
// is (sum_i gamma_i sigma(a_il))_m, that of c_x is -(sum_i gamma_i sigma(t1_i 2^d))_x, and those of
// psi and f are -gamma2 gamma and -gamma. The verifier computes these with NTTs, given
// NTT(sigma(a_il)) and NTT(sigma(t1_i 2^d)) (see VerifyKey).

#ifndef VOLE_MOLE_MLDSA_POK_VERIFY_GADGET_HPP
#define VOLE_MOLE_MLDSA_POK_VERIFY_GADGET_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/mldsa.hpp"

#include "keccak/segmented.hpp"
#include "mldsa/mldsa.hpp"
#include "mldsa_pok/sample_in_ball.hpp"
#include "mldsa_pok/shake_relation.hpp"
#include "modq/columns.hpp"
#include "modq/modq.hpp"
#include "modq/range_le.hpp"
#include "qs_bit.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

using P = mldsa::MlDsa44;
using mldsa::detail::Fq;
using mldsa::detail::N;
using mldsa::detail::Poly;
using Elem = Fq;
using modq::detail::Columns;
using modq::detail::ModQ;
using modq::detail::RangeLe;

constexpr size_t K = P::K;
constexpr size_t L = P::L;
constexpr uint32_t Q = mldsa::detail::Q;
constexpr uint32_t GAMMA2 = P::GAMMA2;
constexpr uint32_t ALPHA = 2 * GAMMA2;
constexpr uint32_t BETA = P::TAU * P::ETA;
constexpr uint32_t Z_BOUND = P::GAMMA1 - BETA - 1; // ||z||_inf <= Z_BOUND
constexpr size_t OMEGA = P::OMEGA;
constexpr size_t W1_BITS = 6;
static_assert(mldsa::detail::w1_bits(GAMMA2) == W1_BITS);
static_assert(Q - 1 == 44 * ALPHA);

constexpr size_t NUM_R = K * N; // coefficients of r (and w1, h)
constexpr size_t NUM_Z = L * N;
constexpr size_t Z_BITS = 18; // z + Z_BOUND in [0, 2 Z_BOUND]
constexpr size_t F_BITS = 18; // f' + gamma2 - 1 in [0, alpha - 1]
static_assert(2 * Z_BOUND < (1u << Z_BITS) && ALPHA - 1 < (1u << F_BITS));

constexpr size_t MU_BYTES = 64;
constexpr size_t TR_BYTES = 64;

// The parts of the circuit, all with degree at most 11 (twice that, plus one, is faest-arch-opt's
// limit of 29 for a derived witness, see voleith.hpp).
using Ctilde = ShakeShape<Kf1600Deg9, MU_BYTES, 32 * K * W1_BITS, 32>; // H(mu || w1Encode(w1), 32)
using SibPerm = Kf1600Deg9;
using Sib = SampleInBall<P::TAU, 80, /* COMMIT_EQ */ true>;
// Counters of degree 8, or 4 (COUNTER_LOG = 2): the latter needs about 1.8 times as many committed
// bits, so the proof is 1.6 times larger, but proving takes about a third of the time.
constexpr size_t COUNTER_LOG = 3;
static_assert(COUNTER_LOG == 2 || COUNTER_LOG == 3);
using HintCols = Columns<COUNTER_LOG>;

constexpr size_t HINT_COLUMNS = 11; // sum_i (1 + b0_i) + slack <= 1024 + 127 < 2^11
constexpr size_t SLACK_BITS = 7;
static_assert(OMEGA < (size_t{1} << SLACK_BITS));
constexpr size_t HINT_CARRIES = COUNTER_LOG == 3 ? 288 : 519; // see test_mldsa_pok.cpp

// 2 Z_BOUND = 0b111111111101100010: the helper covers bits 8..17, and the constraints have degree
// at most 10 (the helper's) and 5. alpha - 1 = 0b101110011111111111: degree at most 5.
using ZRange = RangeLe<2 * Z_BOUND, Z_BITS, 8>;
using FRange = RangeLe<ALPHA - 1, F_BITS, F_BITS>;

// The values of the checks (see modq/modq.hpp): value V_OFF_Z + j is z_j + Z_BOUND, V_OFF_C + x is
// c_x + 1 (bits z_x, p_x of sample_in_ball.hpp), V_OFF_PSI + j is psi_j + 1 (bits b0, b1,
// w1_0, ..., w1_5 with weights 1, 2, 2, 4, ..., 64), and V_OFF_F + j is f_j + gamma2 (the 18 bits
// of f'_j + gamma2 - 1, then nb_j and yb_j with weight 1).
constexpr size_t V_OFF_Z = 0;
constexpr size_t V_OFF_C = V_OFF_Z + NUM_Z;
constexpr size_t V_OFF_PSI = V_OFF_C + N;
constexpr size_t V_OFF_F = V_OFF_PSI + NUM_R;
constexpr size_t NUM_VALUES = V_OFF_F + NUM_R;

struct ModQSpec {
    static constexpr uint32_t Q = detail::Q;
    static constexpr size_t NUM_VALUES = detail::NUM_VALUES;
    static constexpr size_t value_bits(size_t j) {
        return j < V_OFF_C ? Z_BITS : j < V_OFF_PSI ? 2 : j < V_OFF_F ? 2 + W1_BITS : F_BITS + 2;
    }
    static constexpr size_t bit_shift(size_t j, size_t i) {
        if (j >= V_OFF_PSI && j < V_OFF_F) {
            return i == 0 ? 0 : i == 1 ? 1 : i - 1;
        }
        return j >= V_OFF_F && i >= F_BITS ? 0 : i;
    }
    static constexpr Elem offset(size_t j) {
        return j < V_OFF_C ? Z_BOUND : j < V_OFF_F ? 1 : GAMMA2;
    }
    // Soundness error q^-6 < 2^-137.
    static constexpr size_t NUM_CHECKS = 6;
    // Sparse weights with exponents up to 95 (see "Recoding" in modq/modq.hpp).
    static constexpr size_t DIGIT_EXPS = 96;
    static constexpr size_t COUNTER_LOG = detail::COUNTER_LOG;
    // About the mean + 13 sd (see test_mldsa_pok.cpp).
    static constexpr size_t CARRY_BUDGET = COUNTER_LOG == 3 ? 328048 : 575408;
};
using MlDsaModQ = ModQ<ModQSpec>;
using Weights = MlDsaModQ::Weights;

// The public key, prepared for the checks.
struct VerifyKey {
    mldsa::detail::ParsedPublicKey<P> parsed;
    std::array<Poly, K * L> sigma_a_hat; // NTT(sigma(a_il)), row-major
    std::array<Poly, K> sigma_t1_hat;    // NTT(sigma(t1_i 2^d))
};
VerifyKey make_verify_key(const mldsa::PublicKey<P>& pk);

// The check weights W_{k,j} (k NUM_VALUES + j), from a seed that binds the commitment to the
// gadget's witness and to mu. Feed them to MlDsaModQ::make_weights.
std::vector<Elem> check_weights(const VerifyKey& key, std::span<const uint8_t> seed);

namespace gadget_detail {
template <typename QS, size_t deg> void zero(QS* qs, const vole_mole::detail::qs_bit<QS, deg>& x) {
    qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(x));
}
} // namespace gadget_detail

// ML-DSA-44 Verify on a hidden mu: a gadget whose witness starts at byte `base` of the relation's
// witness, and whose answer to the checks starts at byte `answer_base`.
class VerifyGadget {
  public:
    // The layout, relative to the gadget's witness. Bytes:
    static constexpr size_t OFF_CTILDE = 0; // w1Encode(w1), then the states of the c-tilde hash
    static_assert(Ctilde::WIT_OFF_STATES == Ctilde::SECRET_BYTES);
    static constexpr size_t OFF_SIB_STATES = OFF_CTILDE + Ctilde::WITNESS_BYTES;
    // Bits:
    static constexpr size_t BOFF_SIB = 8 * (OFF_SIB_STATES + SibPerm::COMMITTED_STATES_BYTES);
    static constexpr size_t BOFF_HINT = BOFF_SIB + Sib::WITNESS_BITS; // b0, b1 per coefficient
    static constexpr size_t BOFF_SLACK = BOFF_HINT + 2 * NUM_R;
    static constexpr size_t BOFF_HINT_CARRIES = BOFF_SLACK + SLACK_BITS;
    static constexpr size_t BOFF_Z = BOFF_HINT_CARRIES + HINT_CARRIES; // Z_BITS per coefficient
    static constexpr size_t BOFF_Z_HELPER = BOFF_Z + Z_BITS * NUM_Z;   // one per coefficient
    static constexpr size_t BOFF_F = BOFF_Z_HELPER + NUM_Z;            // F_BITS per coefficient
    static constexpr size_t BOFF_GUARDED = BOFF_F + F_BITS * NUM_R;    // nb, yb per coefficient
    static constexpr size_t WITNESS_BITS = BOFF_GUARDED + 2 * NUM_R;
    static constexpr size_t WITNESS_BYTES = (WITNESS_BITS + 7) / 8;
    // The answer to the checks, committed after the checks are known.
    static constexpr size_t ANSWER_BYTES = MlDsaModQ::ANSWER_BYTES;

    static constexpr size_t QS_DEGREE = 11;
    static_assert(Kf1600Deg9::QS_DEGREE <= QS_DEGREE && Sib::DEGREE <= QS_DEGREE &&
                  (size_t{1} << COUNTER_LOG) <= QS_DEGREE);
    static constexpr size_t NUM_CONSTRAINTS = Ctilde::NUM_SPONGE_CONSTRAINTS       // c-tilde hash
                                              + SibPerm::NUM_SEGMENT_CONSTRAINTS   // SIB hash
                                              + Sib::NUM_CONSTRAINTS               // SampleInBall
                                              + NUM_R                              // w1 < 44
                                              + NUM_R                              // b0 b1 = 0
                                              + HINT_CARRIES + HINT_COLUMNS        // hint weight
                                              + NUM_Z * ZRange::NUM_CONSTRAINTS    // z range
                                              + NUM_R * FRange::NUM_CONSTRAINTS    // f range
                                              + 2 * NUM_R                          // nb, yb guards
                                              + MlDsaModQ::NUM_BINARY_CONSTRAINTS; // the checks

    constexpr VerifyGadget(size_t base, size_t answer_base)
        : base_(base), answer_base_(answer_base) {}

    constexpr size_t base() const { return base_; }
    constexpr size_t answer_base() const { return answer_base_; }

    // Witness bits (absolute).
    constexpr size_t bit(size_t rel) const { return 8 * base_ + rel; }
    constexpr size_t w1_bit(size_t j, size_t i) const {
        return bit(8 * OFF_CTILDE + W1_BITS * j + i);
    }
    constexpr size_t hint_bit(size_t j, size_t i) const { return bit(BOFF_HINT + 2 * j + i); }
    constexpr size_t slack_bit(size_t i) const { return bit(BOFF_SLACK + i); }
    constexpr size_t c_bit(size_t x, size_t i) const {
        return bit(BOFF_SIB + Sib::OFF_C + 2 * x + i);
    }
    constexpr size_t z_bit(size_t j, size_t i) const { return bit(BOFF_Z + Z_BITS * j + i); }
    constexpr size_t z_helper_bit(size_t j) const { return bit(BOFF_Z_HELPER + j); }
    constexpr size_t f_bit(size_t j, size_t i) const { return bit(BOFF_F + F_BITS * j + i); }
    constexpr size_t nb_bit(size_t j) const { return bit(BOFF_GUARDED + 2 * j); }
    constexpr size_t yb_bit(size_t j) const { return bit(BOFF_GUARDED + 2 * j + 1); }

    // The witness bit of bit i of check value j.
    constexpr size_t value_bit(size_t j, size_t i) const {
        if (j < V_OFF_C) {
            return z_bit(j - V_OFF_Z, i);
        }
        if (j < V_OFF_PSI) {
            return c_bit(j - V_OFF_C, i);
        }
        if (j < V_OFF_F) {
            const size_t r = j - V_OFF_PSI;
            return i < 2 ? hint_bit(r, i) : w1_bit(r, i - 2);
        }
        const size_t r = j - V_OFF_F;
        return i < F_BITS ? f_bit(r, i) : i == F_BITS ? nb_bit(r) : yb_bit(r);
    }

    // The hint-weight sum: sum_i (1 + b0_i) + slack, with the slack bits at columns 0..6.
    template <typename Ops, typename Bit>
    void hint_weight_columns(Ops& ops, Bit&& bit,
                             std::vector<std::vector<typename Ops::Wire>>& cols) const {
        cols.assign(HINT_COLUMNS, {});
        for (size_t j = 0; j < NUM_R; ++j) {
            cols[0].push_back(ops.flip(bit(hint_bit(j, 0))));
        }
        for (size_t i = 0; i < SLACK_BITS; ++i) {
            cols[i].push_back(bit(slack_bit(i)));
        }
    }

    // Writes the gadget's witness for mu and a decoded signature, which must be valid for mu, to
    // `witness` (the relation's witness, at least base() + WITNESS_BYTES bytes). Throws
    // std::invalid_argument if the signature isn't valid for mu, and std::runtime_error if
    // SampleInBall needs more than the scanned bytes (which happens with probability less than
    // 2^-77, see sample_in_ball.hpp).
    void encode_witness(std::span<uint8_t> witness, const VerifyKey& key,
                        std::span<const uint8_t, MU_BYTES> mu,
                        const mldsa::detail::DecodedSignature<P>& sig) const;

    // The answer to the checks, for the witness (the relation's witness, which must contain the
    // gadget's). Returns false if the checks need more committed bits than the budget (see
    // MlDsaModQ::CARRY_BUDGET); the verifier rejects such checks.
    bool answer(std::span<const uint8_t> witness, const Weights& weights,
                std::span<uint8_t, ANSWER_BYTES> out) const;

    // Whether the checks hold on the witness (in the clear).
    bool holds(std::span<const uint8_t> witness, const Weights& weights) const;

    // The constraints, for mu given by its committed bits (of degree 1).
    template <typename QS>
    void constraints(QS* qs, const VerifyKey& key,
                     std::span<const vole_mole::detail::qs_bit<QS, 1>, 8 * MU_BYTES> mu,
                     const Weights& weights) const;

  private:
    size_t base_;
    size_t answer_base_;
};

template <typename QS>
void VerifyGadget::constraints(QS* qs, const VerifyKey& /* key */,
                               std::span<const vole_mole::detail::qs_bit<QS, 1>, 8 * MU_BYTES> mu,
                               const Weights& weights) const {
    using Bit = vole_mole::detail::qs_bit<QS, 1>;
    using faest::poly1;
    using gadget_detail::zero;
    using vole_mole::detail::qs_mul;
    const auto wbit = [&](size_t i) { return qs->get_witness_bit(i); };

    // c-tilde = H(mu || w1Encode(w1), 32), the first 256 bits of the state.
    const auto ct_state = Ctilde::qs_sponge(qs, mu, base_ + OFF_CTILDE);

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
    const auto stream = SibPerm::qs_keccak(qs, std::move(sib_state), base_ + OFF_SIB_STATES);
    static_assert(Sib::STREAM_BYTES <= SHAKE256_RATE);
    Sib::constraints(qs, std::span<const Bit>(stream).first(8 * Sib::STREAM_BYTES), bit(BOFF_SIB));

    for (size_t j = 0; j < NUM_R; ++j) {
        std::array<Bit, W1_BITS> b;
        for (size_t i = 0; i < W1_BITS; ++i) {
            b[i] = wbit(w1_bit(j, i));
        }
        // w1 < 44 = 0b101100: not b5 (b4 or b3 b2).
        const auto b54 = qs_mul(b[5], b[4]);
        const auto b532 = qs_mul(qs_mul(b[5], b[3]), b[2]);
        const auto b5432 = qs_mul(qs_mul(b54, b[3]), b[2]);
        zero(qs, vole_mole::detail::qs_bit<QS, 4>(vole_mole::detail::qs_bit<QS, 3>(b54) + b532) +
                     b5432);

        // The guards of the boundary values of f: (1 + nb) (1 + [w1 = 0]) = 0 and
        // yb (1 + (1 + b0) [w1 = 43]) = 0.
        const auto eq = [&](uint32_t c) {
            const auto t = [&](size_t i) { return b[i] + poly1(1 ^ ((c >> i) & 1)); };
            return qs_mul(qs_mul(qs_mul(t(0), t(1)), qs_mul(t(2), t(3))), qs_mul(t(4), t(5)));
        };
        const Bit nb = wbit(nb_bit(j));
        const Bit yb = wbit(yb_bit(j));
        const Bit b0 = wbit(hint_bit(j, 0));
        zero(qs, qs_mul(nb + poly1(1), eq(0) + poly1(1)));
        zero(qs, qs_mul(yb, qs_mul(b0 + poly1(1), eq(43)) + poly1(1)));
    }

    // b0 b1 = 0
    for (size_t j = 0; j < NUM_R; ++j) {
        zero(qs, qs_mul(wbit(hint_bit(j, 0)), wbit(hint_bit(j, 1))));
    }

    // sum_i (1 + b0_i) + slack = OMEGA
    {
        typename HintCols::template QsOps<QS> ops{qs, bit(BOFF_HINT_CARRIES), HINT_CARRIES};
        std::vector<std::vector<Bit>> cols;
        hint_weight_columns(ops, wbit, cols);
        HintCols::reduce(ops, cols, [&](size_t col, const Bit& w) {
            ops.assert_equal(w, ((OMEGA >> col) & 1) != 0);
        });
        ops.finish();
    }

    // z + Z_BOUND <= 2 Z_BOUND and f' + gamma2 - 1 <= alpha - 1.
    for (size_t j = 0; j < NUM_Z; ++j) {
        ZRange::constraints(
            qs, [&](size_t i) { return wbit(z_bit(j, i)); }, [&] { return wbit(z_helper_bit(j)); });
    }
    for (size_t j = 0; j < NUM_R; ++j) {
        FRange::constraints(
            qs, [&](size_t i) { return wbit(f_bit(j, i)); },
            [&] {
                return wbit(0); /* unused */
            });
    }

    // r - gamma2 psi - f = 0, by random checks.
    MlDsaModQ::qs_constraints(qs, weights, 8 * answer_base_,
                              [&](size_t j, size_t i) { return wbit(value_bit(j, i)); });
}

// mu = H(tr || 0 || 0 || M, 64) for a hidden M of MSG_BYTES bytes, as a gadget whose witness (M,
// then the committed states of the hash) starts at byte `base` of the relation's witness.
template <size_t MSG_BYTES_> class MuHash {
  public:
    static constexpr size_t MSG_BYTES = MSG_BYTES_;
    // tr || 0 || |ctx| (= 0)
    static constexpr size_t PREFIX_BYTES = TR_BYTES + 2;
    using Shape = ShakeShape<Kf1600Deg9, PREFIX_BYTES, MSG_BYTES, MU_BYTES>;
    static_assert(Kf1600Deg9::OUTPUT_DEGREE == 1, "mu is absorbed by the c-tilde hash");

    static constexpr size_t NUM_PERMUTATIONS = Shape::NUM_BLOCKS;
    static constexpr size_t WITNESS_BYTES = Shape::WITNESS_BYTES;
    static constexpr size_t NUM_CONSTRAINTS = Shape::NUM_SPONGE_CONSTRAINTS;
    static constexpr size_t QS_DEGREE = Shape::QS_DEGREE;

    constexpr explicit MuHash(size_t base) : base_(base) {}

    constexpr size_t base() const { return base_; }
    // Bit i of M (absolute).
    constexpr size_t msg_bit(size_t i) const { return 8 * base_ + i; }

    static std::array<uint8_t, PREFIX_BYTES> prefix(std::span<const uint8_t, TR_BYTES> tr) {
        std::array<uint8_t, PREFIX_BYTES> p{};
        std::ranges::copy(tr, p.begin());
        return p;
    }

    // Writes the gadget's witness for M to `witness`, and returns mu.
    std::array<uint8_t, MU_BYTES> encode_witness(std::span<uint8_t> witness,
                                                 std::span<const uint8_t, TR_BYTES> tr,
                                                 std::span<const uint8_t, MSG_BYTES> msg) const {
        std::array<uint8_t, MU_BYTES> mu;
        const auto p = prefix(tr);
        const auto w = Shape::encode_witness(p, msg, mu);
        std::ranges::copy(w, witness.begin() + static_cast<std::ptrdiff_t>(base_));
        return mu;
    }

    // The constraints. Returns the state after the last permutation, whose first 8 MU_BYTES bits
    // (of degree 1) are mu.
    template <typename QS>
    keccak::detail::QsState<QS> constraints(QS* qs, std::span<const uint8_t, TR_BYTES> tr) const {
        const auto p = prefix(tr);
        return Shape::qs_sponge(qs, std::span<const uint8_t, PREFIX_BYTES>(p), base_);
    }

  private:
    size_t base_;
};

} // namespace vole_mole::mldsa_pok::detail

#endif
