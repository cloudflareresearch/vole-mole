// The relations of the proof of knowledge of an ML-DSA-44 signature (see
// include/vole_mole/mldsa_pok.hpp).
//
// Statement. Public: pk = (rho, t1), and mu = H(H(pk) || 0 || |ctx| || ctx || M). Secret: the
// signature (c-tilde, z, h). ML-DSA.Verify accepts if and only if ||z||_inf < gamma1 - beta, h has
// at most omega ones, and c-tilde = H(mu || w1Encode(w1), 32) for
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
//   e = gamma2 (hp - hn) + f,  f in (-gamma2, gamma2],
//
// where hp = [u = pos] and hn = [u = neg], and count the hints hp + hn. Then u = none implies
// e in S0(w1), and u in {pos, neg} implies e in (0, alpha] or (-alpha, 0], within S0(w1) u S1(w1).
// So if the proof verifies, then setting h_i = 1 exactly where e_i is not in S0(w1_i) gives a
// signature with at most as many hints as the proof counts, and UseHint(h, r) = w1: the statement
// is sound. For completeness, an honest prover represents e as above, with the hint class of the
// signature, except for three boundary cases, each hit with probability about 2^-23 per
// coefficient: e = -gamma2 with w1 = 0 and no hint (then u = neg, f = 0, which costs a hint and
// fails only if the signature already has omega hints), and e = -alpha with w1 = 0 or
// e = alpha + 1 with w1 = 43 (which the proof doesn't cover; prove() throws).
//
// Note e = r - alpha w1 - gamma2 (hp - hn) = r - gamma2 psi for psi = 2 w1 + hp - hn in [-1, 87].
//
// The proof is a single binary VOLEitH proof (FAEST, src/voleith.hpp), whose witness is derived
// from a short key with the local PRG (see "Derived witnesses" in voleith.hpp: each witness bit
// costs one bit of proof). That doubles the degree of the constraints, which faest-arch-opt limits
// to 29 (after doubling), so they have degree at most 11. The witness is:
//
//   - w1Encode(w1), i.e., the 6 bits of each coefficient of w1, constrained to w1 < 44;
//   - the c-tilde hash (7 Keccak-f[1600] permutations, see shake_relation.hpp), whose output
//     c-tilde feeds the SampleInBall hash (1 permutation) and the SampleInBall circuit (see
//     sample_in_ball.hpp), whose output is c + 1 in {0, 1, 2} as 2 bits per coefficient;
//   - the hint class of each coefficient as 2 bits, b0 = [u = none] and b1 = [u = pos]
//     (b0 b1 = 0, and then psi + 1 = b0 + 2 b1 + 2 w1), and a 7-bit slack with
//     sum_i (1 + b0_i) + slack = omega (an integer sum, see modq/columns.hpp);
//   - z + B in [0, 2B] for B = gamma1 - beta - 1, and f + gamma2 - 1 in [0, alpha - 1], as 18
//     bits per coefficient, with range checks (see `RangeLe`);
//   - the answer to the checks of r - gamma2 psi - f = 0 for r = A z - c t1 2^d, which is linear
//     in the bits of z, c, psi, and f: after the rest of the witness is committed, the verifier
//     picks NUM_CHECKS random combinations of the K N equations, and the prover shows each
//     modulo q (see modq/modq.hpp), with soundness error 1 / q per check.
//
// The checks. For gamma in R_q^K (uniform, derived from a seed that binds the commitment to the
// rest of the witness), the combination is <gamma, A z - c t1 2^d - gamma2 psi - f>, with
// <u, v> = sum_n u_n v_n for polynomials (coefficient vectors). Write sigma(p)(X) = p(X^-1), an
// automorphism of R_q (so sigma(p)_0 = p_0 and sigma(p)_{N - n} = -p_n). Then <u, v> is the
// constant coefficient of sigma(u) v, and so <gamma_i, a z> = <gamma_i sigma(a), z>. So the weight
// of coefficient m of z_l is (sum_i gamma_i sigma(a_il))_m, that of c_x is
// -(sum_i gamma_i sigma(t1_i 2^d))_x, and those of psi and f are -gamma2 gamma and -gamma. The
// verifier computes these with NTTs, given NTT(sigma(a_il)) and NTT(sigma(t1_i 2^d)).

#ifndef VOLE_MOLE_MLDSA_POK_RELATION_HPP
#define VOLE_MOLE_MLDSA_POK_RELATION_HPP

#include "vole_mole/mldsa.hpp"

#include "dst.hpp"
#include "mldsa/mldsa.hpp"
#include "mldsa_pok/sample_in_ball.hpp"
#include "mldsa_pok/shake_relation.hpp"
#include "modq/columns.hpp"
#include "modq/modq.hpp"
#include "modq/range_le.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
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
constexpr size_t F_BITS = 18; // f + gamma2 - 1 in [0, alpha - 1]
static_assert(2 * Z_BOUND < (1u << Z_BITS) && ALPHA - 1 < (1u << F_BITS));

// The statement.
struct Statement {
    const mldsa::PublicKey<P>* pk;
    mldsa::detail::ParsedPublicKey<P> parsed;
    std::array<uint8_t, 64> mu;
    std::array<Poly, K * L> sigma_a_hat; // NTT(sigma(a_il)), row-major
    std::array<Poly, K> sigma_t1_hat;    // NTT(sigma(t1_i 2^d))
};
Statement make_statement(const mldsa::PublicKey<P>& pk, std::span<const uint8_t, 64> mu);

// The witness PRG and the parts of the circuit, all with degree at most 11 (see above).
using BinWitnessPrg = vole_mole::detail::LocalPrg<2>;
using Ctilde = ShakeShape<Kf1600Deg9, 64, 32 * K * W1_BITS, 32>; // H(mu || w1Encode(w1), 32)
using SibPerm = Kf1600Deg9;
using Sib = SampleInBall<P::TAU, 80, /* COMMIT_EQ */ true>;
// Counters of degree 8, or 4 (COUNTER_LOG = 2): the latter needs about 1.8 times as many committed
// bits, so the proof is 1.6 times larger (160 KB instead of 98 KB), but proving takes about a third
// of the time (Apple M4 Pro: 205 ms instead of 556 ms).
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
// w1_0, ..., w1_5 with weights 1, 2, 2, 4, ..., 64), and V_OFF_F + j is f_j + gamma2 - 1.
constexpr size_t V_OFF_Z = 0;
constexpr size_t V_OFF_C = V_OFF_Z + NUM_Z;
constexpr size_t V_OFF_PSI = V_OFF_C + N;
constexpr size_t V_OFF_F = V_OFF_PSI + NUM_R;
constexpr size_t NUM_VALUES = V_OFF_F + NUM_R;

struct ModQSpec {
    static constexpr uint32_t Q = detail::Q;
    static constexpr size_t NUM_VALUES = detail::NUM_VALUES;
    static constexpr size_t value_bits(size_t j) {
        return j < V_OFF_C ? Z_BITS : j < V_OFF_PSI ? 2 : j < V_OFF_F ? 2 + W1_BITS : F_BITS;
    }
    static constexpr size_t bit_shift(size_t j, size_t i) {
        return j >= V_OFF_PSI && j < V_OFF_F ? (i == 0 ? 0 : i == 1 ? 1 : i - 1) : i;
    }
    static constexpr Elem offset(size_t j) {
        return j < V_OFF_C ? Z_BOUND : j < V_OFF_F ? 1 : GAMMA2 - 1;
    }
    // Soundness error q^-6 < 2^-137.
    static constexpr size_t NUM_CHECKS = 6;
    // Sparse weights with exponents up to 95 (see "Recoding" in modq/modq.hpp).
    static constexpr size_t DIGIT_EXPS = 96;
    static constexpr size_t COUNTER_LOG = detail::COUNTER_LOG;
    // About the mean + 13 sd (see test_mldsa_pok.cpp).
    static constexpr size_t CARRY_BUDGET = COUNTER_LOG == 3 ? 314280 : 575408;
};
using MlDsaModQ = ModQ<ModQSpec>;
using Weights = MlDsaModQ::Weights;

// Witness layout. Byte offsets:
constexpr size_t B_OFF_W1 = 0; // w1Encode(w1), the secret input of Ctilde
static_assert(Ctilde::WIT_OFF_STATES == Ctilde::SECRET_BYTES);
constexpr size_t B_OFF_SIB_STATES = Ctilde::WITNESS_BYTES;
// Bit offsets:
constexpr size_t B_OFF_SIB = 8 * (B_OFF_SIB_STATES + SibPerm::COMMITTED_STATES_BYTES);
constexpr size_t B_OFF_HINT = B_OFF_SIB + Sib::WITNESS_BITS; // b0, b1 for each coefficient
constexpr size_t B_OFF_SLACK = B_OFF_HINT + 2 * NUM_R;
constexpr size_t B_OFF_HINT_CARRIES = B_OFF_SLACK + SLACK_BITS;
constexpr size_t B_OFF_Z = B_OFF_HINT_CARRIES + HINT_CARRIES; // Z_BITS per coefficient
constexpr size_t B_OFF_Z_HELPER = B_OFF_Z + Z_BITS * NUM_Z;   // one per coefficient
constexpr size_t B_OFF_F = B_OFF_Z_HELPER + NUM_Z;            // F_BITS per coefficient
constexpr size_t B_PREFIX_BITS = B_OFF_F + F_BITS * NUM_R;
constexpr size_t B_PREFIX_BYTES = (B_PREFIX_BITS + 7) / 8;
// The answer to the checks (see modq/modq.hpp), committed after the checks are known.
constexpr size_t B_OFF_ANSWER = 8 * B_PREFIX_BYTES;
constexpr size_t B_WITNESS_BITS = B_OFF_ANSWER + MlDsaModQ::ANSWER_BITS;

constexpr size_t w1_bit(size_t j, size_t i) { return 8 * B_OFF_W1 + W1_BITS * j + i; }
constexpr size_t hint_bit(size_t j, size_t i) { return B_OFF_HINT + 2 * j + i; }
constexpr size_t c_bit(size_t x, size_t i) { return B_OFF_SIB + Sib::OFF_C + 2 * x + i; }
constexpr size_t z_bit(size_t j, size_t i) { return B_OFF_Z + Z_BITS * j + i; }
constexpr size_t z_helper_bit(size_t j) { return B_OFF_Z_HELPER + j; }
constexpr size_t f_bit(size_t j, size_t i) { return B_OFF_F + F_BITS * j + i; }

// The witness bit of bit i of check value j.
constexpr size_t value_bit(size_t j, size_t i) {
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
    return f_bit(j - V_OFF_F, i);
}

constexpr size_t B_NUM_CONSTRAINTS = Ctilde::NUM_SPONGE_CONSTRAINTS       // c-tilde hash
                                     + SibPerm::NUM_SEGMENT_CONSTRAINTS   // SampleInBall hash
                                     + Sib::NUM_CONSTRAINTS               // SampleInBall
                                     + NUM_R                              // w1 < 44
                                     + NUM_R                              // b0 b1 = 0
                                     + HINT_CARRIES + HINT_COLUMNS        // hint weight
                                     + NUM_Z * ZRange::NUM_CONSTRAINTS    // z range
                                     + NUM_R * FRange::NUM_CONSTRAINTS    // f range
                                     + MlDsaModQ::NUM_BINARY_CONSTRAINTS; // r - gamma2 psi - f
constexpr size_t B_QS_DEGREE = 11;
static_assert(Kf1600Deg9::QS_DEGREE <= B_QS_DEGREE && Sib::DEGREE <= B_QS_DEGREE &&
              (size_t{1} << COUNTER_LOG) <= B_QS_DEGREE);

constexpr faest::owf OWF_MLDSA_POK = static_cast<faest::owf>((0x72u << 8) | 0b10'0000);

} // namespace vole_mole::mldsa_pok::detail

template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::mldsa_pok::detail::OWF_MLDSA_POK>
    : vole_mole::detail::RelationConstants<vole_mole::mldsa_pok::detail::B_WITNESS_BITS,
                                           vole_mole::mldsa_pok::detail::B_QS_DEGREE,
                                           vole_mole::mldsa_pok::detail::BinWitnessPrg> {};

namespace vole_mole::mldsa_pok::detail {

// The hint-weight sum: sum_i (1 + b0_i) + slack, with the slack bits at columns 0..6.
template <typename Ops, typename Bit>
void hint_weight_columns(Ops& ops, Bit&& bit, std::vector<std::vector<typename Ops::Wire>>& cols) {
    cols.assign(HINT_COLUMNS, {});
    for (size_t j = 0; j < NUM_R; ++j) {
        cols[0].push_back(ops.flip(bit(hint_bit(j, 0))));
    }
    for (size_t i = 0; i < SLACK_BITS; ++i) {
        cols[i].push_back(bit(B_OFF_SLACK + i));
    }
}

using CheckSeed = std::array<uint8_t, 32>;

struct BinRelation {
    using params = Params128f<OWF_MLDSA_POK>;
    struct instance {
        const Statement* stmt;
        CheckSeed seed;
        const Weights* weights; // derived from stmt and seed
    };
    static constexpr size_t NUM_CONSTRAINTS = B_NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = B_PREFIX_BYTES;
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::MLDSA_POK_PROOF_DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST =
        vole_mole::detail::MLDSA_POK_PRG_DST;

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update(*x.stmt->pk);
        h.update(x.stmt->mu);
        h.update(x.seed);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>);
};

constexpr size_t PROOF_BYTES_ = vole_mole::detail::PROOF_BYTES<BinRelation>;

// The check weights W_{k,j} (k NUM_VALUES + j) for the statement and the seed.
std::vector<Elem> check_weights(const Statement& stmt, const CheckSeed& seed);

// The seed of the checks, from the statement, chal1, and the part of the proof that commits to the
// witness prefix (written by VOLE generation).
using Chal1 = std::array<uint8_t, BinRelation::params::CONSTS::VOLE_CHECK::CHALLENGE_BYTES>;
CheckSeed check_seed(const Statement& stmt, const Chal1& chal1,
                     std::span<const uint8_t, PROOF_BYTES_> proof);

// Writes the hint-weight carries to the prefix (in the clear). Returns false if the hint weight
// exceeds OMEGA.
bool hint_weight_witness(std::span<uint8_t, B_PREFIX_BYTES> prefix);

} // namespace vole_mole::mldsa_pok::detail

#endif
