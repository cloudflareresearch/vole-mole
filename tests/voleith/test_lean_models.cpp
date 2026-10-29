// Tests that check the models in the Lean proofs (lean/VoleMole/) against the code. Each Lean model
// was matched to the code by reading it. Here, each test computes the model's formula directly and
// compares it with the code's output on many inputs. The field arithmetic for the models (Gf below)
// is written from scratch, so the models don't share faest-arch-opt's arithmetic.

#include "vole_mole/ihat.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"               // internal
#include "ihat/commit.hpp"   // internal
#include "ihat/issue.hpp"    // internal
#include "ihat/redeem.hpp"   // internal
#include "ihat/unbound_issue.hpp"  // internal
#include "ihat/unbound_redeem.hpp" // internal
#include "pomfrit/redeem.hpp"    // internal
#include "act/issue.hpp" // internal
#include "act/spend.hpp" // internal
#include "uov/circuit.hpp"       // internal
#include "voleith.hpp"           // internal

#include "test.hpp"

#include "block.hpp"          // from faest-arch-opt
#include "faest_sig.hpp"      // from faest-arch-opt
#include "hash.hpp"           // from faest-arch-opt
#include "kos_vole_check.hpp" // from faest-arch-opt
#include "parameters.hpp"     // from faest-arch-opt
#include "polynomials.hpp"    // from faest-arch-opt
#include "quicksilver.hpp"    // from faest-arch-opt
#include "universal_hash.hpp" // from faest-arch-opt
#include "vector_com.hpp"     // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <random>
#include <span>
#include <vector>

namespace {

constexpr auto S = faest::secpar::s128;
using Poly = faest::poly_secpar<S>;
using Block = faest::block_secpar<S>;
using Digest = std::array<uint8_t, 32>;
namespace uov = vole_mole::uov;

// An element of GF(2^128) = GF(2)[X] / (X^128 + X^7 + X^2 + X + 1), as in the FAEST spec. Bit i of
// lo (i < 64) or of hi (i >= 64) is the coefficient of X^i. The byte encoding is little endian, as
// in faest-arch-opt's poly128::load.
struct Gf {
    uint64_t lo = 0;
    uint64_t hi = 0;

    static Gf one() { return {1, 0}; }

    static Gf load(const uint8_t* p) {
        Gf out;
        for (size_t i = 0; i < 8; ++i) {
            out.lo |= uint64_t{p[i]} << (8 * i);
            out.hi |= uint64_t{p[8 + i]} << (8 * i);
        }
        return out;
    }

    // A 64-bit polynomial (e.g., the short hash key t), as an element of degree < 64.
    static Gf load64(const uint8_t* p) {
        Gf out;
        for (size_t i = 0; i < 8; ++i) {
            out.lo |= uint64_t{p[i]} << (8 * i);
        }
        return out;
    }

    std::array<uint8_t, 16> bytes() const {
        std::array<uint8_t, 16> out;
        for (size_t i = 0; i < 8; ++i) {
            out[i] = static_cast<uint8_t>(lo >> (8 * i));
            out[8 + i] = static_cast<uint8_t>(hi >> (8 * i));
        }
        return out;
    }

    friend bool operator==(const Gf&, const Gf&) = default;

    friend Gf operator+(Gf a, Gf b) { return {a.lo ^ b.lo, a.hi ^ b.hi}; }
    Gf& operator+=(Gf b) { return *this = *this + b; }

    // Schoolbook multiplication: Horner's rule over the bits of b, from the top.
    friend Gf operator*(Gf a, Gf b) {
        Gf r;
        for (int i = 127; i >= 0; --i) {
            const uint64_t carry = r.hi >> 63;
            r.hi = (r.hi << 1) | (r.lo >> 63);
            r.lo = (r.lo << 1) ^ (carry != 0 ? 0x87 : 0); // X^128 = X^7 + X^2 + X + 1
            const uint64_t bit = i >= 64 ? (b.hi >> (i - 64)) & 1 : (b.lo >> i) & 1;
            if (bit != 0) {
                r += a;
            }
        }
        return r;
    }
    Gf& operator*=(Gf b) { return *this = *this * b; }
};

Gf pow(Gf a, size_t e) {
    Gf r = Gf::one();
    for (size_t i = 0; i < e; ++i) {
        r *= a;
    }
    return r;
}

// a^(2^128 - 2) = a^-1 for a != 0.
Gf inv(Gf a) {
    Gf r = Gf::one();
    for (int i = 1; i < 128; ++i) {
        a *= a;
        r *= a;
    }
    return r;
}

Poly to_poly(Gf a) {
    const auto b = a.bytes();
    return Poly::load(b.data());
}

Gf from_poly(const Poly& p) {
    std::array<uint8_t, 16> b;
    p.store1(b.data());
    return Gf::load(b.data());
}

Block to_block(Gf a) { return to_poly(a).to_block(); }

Gf random_gf(std::mt19937_64& rng) { return {rng(), rng()}; }

template <size_t N> std::array<uint8_t, N> random_bytes(std::mt19937_64& rng) {
    std::array<uint8_t, N> out;
    for (uint8_t& b : out) {
        b = static_cast<uint8_t>(rng());
    }
    return out;
}

// The leading coefficient of the polynomial of degree < xs.size() through the points (xs, ys),
// i.e., the divided difference sum_i ys[i] / prod_{j != i} (xs[i] - xs[j]). For xs.size() = d + 1
// points of a polynomial of degree <= d, this is its X^d coefficient. For d + 2 points, it's 0 iff
// the points lie on a polynomial of degree <= d.
Gf divided_difference(const std::vector<Gf>& xs, const std::vector<Gf>& ys) {
    Gf out;
    for (size_t i = 0; i < xs.size(); ++i) {
        Gf denom = Gf::one();
        for (size_t j = 0; j < xs.size(); ++j) {
            if (j != i) {
                denom *= xs[i] + xs[j];
            }
        }
        out += ys[i] * inv(denom);
    }
    return out;
}

Digest shake128(std::span<const uint8_t> input) {
    faest::hash_state h;
    h.init(S);
    h.update(input);
    Digest out;
    h.finalize(out);
    return out;
}

} // namespace

// Our Gf agrees with faest-arch-opt's GF(2^128) multiplication and encoding, so the models below,
// which use Gf, talk about the same field as the code.
TEST(LeanModels, FieldArithmeticMatchesFaest) {
    std::mt19937_64 rng(1);
    for (int i = 0; i < 1000; ++i) {
        const Gf a = random_gf(rng);
        const Gf b = random_gf(rng);
        EXPECT_EQ(from_poly((to_poly(a) * to_poly(b)).template reduce_to<128>()), a * b);
        EXPECT_EQ(from_poly(to_poly(a) + to_poly(b)), a + b);
        if (!(a == Gf{})) {
            EXPECT_EQ(a * inv(a), Gf::one());
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 1. KOS universal hash (lean/VoleMole/Seed/KOS.lean, lean/docs/extraction/L3-kos.md §2.1)
// ---------------------------------------------------------------------------------------------

namespace {

// chall_1 parsed as in KOS.lean's `Ch`: the matrix column r, the full keys s, and the short key t.
struct KosChallenge {
    std::array<Gf, 4> r;
    std::array<Gf, 4> s;
    Gf t;
};

constexpr size_t KOS_CHALLENGE_BYTES = faest::detail::kos_vole_check_challenge<S>::CHALLENGE_BYTES;
static_assert(KOS_CHALLENGE_BYTES == 136);

KosChallenge parse_kos_challenge(const std::array<uint8_t, KOS_CHALLENGE_BYTES>& c) {
    KosChallenge out;
    for (size_t i = 0; i < 4; ++i) {
        out.r[i] = Gf::load(&c[16 * i]);
        out.s[i] = Gf::load(&c[64 + 16 * i]);
    }
    out.t = Gf::load64(&c[128]);
    return out;
}

// hornerPoly x evaluated at a: P_x(a) = sum_k x_k a^(L-1-k) (`eval_hornerPoly`).
Gf eval_horner_poly(const std::vector<Gf>& x, Gf a) {
    Gf out;
    for (size_t k = 0; k < x.size(); ++k) {
        out += x[k] * pow(a, x.size() - 1 - k);
    }
    return out;
}

// `voleHashP (hornerPoly x) c + D`: h_j = r_j P_x(s_0) + y_{j+1} + D_j, with
// y = (P_x(s_1), P_x(s_2), P_x(s_3), P_x(t)) (`ys`), plus the direct masks D as in `kosValue`.
std::array<Gf, 4> vole_hash_model(const KosChallenge& c, const std::vector<Gf>& x,
                                  const std::array<Gf, 4>& d) {
    const Gf y0 = eval_horner_poly(x, c.s[0]);
    const std::array<Gf, 4> y = {eval_horner_poly(x, c.s[1]), eval_horner_poly(x, c.s[2]),
                                 eval_horner_poly(x, c.s[3]), eval_horner_poly(x, c.t)};
    std::array<Gf, 4> h;
    for (size_t j = 0; j < 4; ++j) {
        h[j] = c.r[j] * y0 + y[j] + d[j];
    }
    return h;
}

void append(std::vector<uint8_t>& out, Gf a) {
    const auto b = a.bytes();
    out.insert(out.end(), b.begin(), b.end());
}

} // namespace

// Validates KOS.lean's `voleHashP`, `hornerPoly` and `voleHashL` (and `kosValue` for the verifier)
// against kos_vole_check_both. The prover's VOLEHash of u (written to the proof), and the VOLEHash
// of V or Q (hashed into chall_2, with the verifier's Delta correction) must be the model's for
// every number of hashed rows L, in particular for every L mod 8 (uhasher_gfsecpar works in
// blocks of 8 key powers).
TEST(LeanModels, KosVoleHashMatchesModel) {
    std::mt19937_64 rng(2);
    for (const size_t n_hash : {0, 8, 16, 40, 128}) {
        for (size_t n_extra = 0; n_extra <= 9; ++n_extra) {
            const size_t l = n_hash + n_extra;
            if (l == 0) {
                continue; // the hashers need at least one input
            }
            SCOPED_TRACE(testing::Message() << "n_hash " << n_hash << ", n_hash_extra " << n_extra);

            const auto chall = random_bytes<KOS_CHALLENGE_BYTES>(rng);
            const KosChallenge c = parse_kos_challenge(chall);
            std::vector<uint8_t> u(n_hash / 8);
            for (uint8_t& b : u) {
                b = static_cast<uint8_t>(rng());
            }
            std::vector<Gf> vq(n_hash), u_mask(n_extra + 4), vq_mask(n_extra + 4);
            for (auto* vec : {&vq, &u_mask, &vq_mask}) {
                for (Gf& a : *vec) {
                    a = random_gf(rng);
                }
            }
            const auto to_blocks = [](const std::vector<Gf>& v) {
                std::vector<Block> out;
                for (const Gf& a : v) {
                    out.push_back(to_block(a));
                }
                return out;
            };
            const auto vq_blocks = to_blocks(vq);
            const auto u_mask_blocks = to_blocks(u_mask);
            const auto vq_mask_blocks = to_blocks(vq_mask);

            // The hashed rows x (L of them) and the direct masks D of the model.
            const auto rows = [&](const std::vector<Gf>& main, const std::vector<Gf>& mask) {
                std::vector<Gf> x = main;
                x.insert(x.end(), mask.begin(), mask.begin() + static_cast<ptrdiff_t>(n_extra));
                return x;
            };
            const auto direct = [&](const std::vector<Gf>& mask) {
                return std::array<Gf, 4>{mask[n_extra], mask[n_extra + 1], mask[n_extra + 2],
                                         mask[n_extra + 3]};
            };
            std::vector<Gf> u_rows; // the bits of u, as 0 or 1
            for (size_t i = 0; i < n_hash; ++i) {
                u_rows.push_back({uint64_t{(u[i / 8] >> (i % 8)) & 1u}, 0});
            }

            // Prover.
            std::array<uint8_t, 64> proof{};
            {
                faest::hash_state hasher;
                hasher.init(S);
                faest::detail::kos_vole_check_both<S>(false, n_hash, n_extra, u.data(),
                                                      vq_blocks.data(), u_mask_blocks.data(),
                                                      vq_mask_blocks.data(), Block::set_zero(),
                                                      chall.data(), proof.data(), nullptr, hasher);
                Digest got;
                hasher.finalize(got);

                const auto hu = vole_hash_model(c, rows(u_rows, u_mask), direct(u_mask));
                std::vector<uint8_t> want_proof;
                for (const Gf& h : hu) {
                    append(want_proof, h);
                }
                EXPECT_TRUE(std::ranges::equal(proof, want_proof));

                std::vector<uint8_t> want_input = want_proof;
                for (const Gf& h : vole_hash_model(c, rows(vq, vq_mask), direct(vq_mask))) {
                    append(want_input, h);
                }
                EXPECT_EQ(got, shake128(want_input));
            }

            // Verifier, with Q := vq, q_mask := vq_mask, and an arbitrary u_hash in the proof.
            {
                const auto proof_in = random_bytes<64>(rng);
                const Gf delta = random_gf(rng);
                faest::hash_state hasher;
                hasher.init(S);
                faest::detail::kos_vole_check_both<S>(
                    true, n_hash, n_extra, nullptr, vq_blocks.data(), nullptr,
                    vq_mask_blocks.data(), to_block(delta), chall.data(), nullptr, proof_in.data(),
                    hasher);
                Digest got;
                hasher.finalize(got);

                std::vector<uint8_t> want_input(proof_in.begin(), proof_in.end());
                const auto hq = vole_hash_model(c, rows(vq, vq_mask), direct(vq_mask));
                for (size_t j = 0; j < 4; ++j) {
                    append(want_input, hq[j] + delta * Gf::load(&proof_in[16 * j]));
                }
                EXPECT_EQ(got, shake128(want_input));
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 2. QuickSilver chi derivation and hashing (lean/VoleMole/Seed/QuickSilver.lean,
//    lean/docs/extraction/L4-quicksilver.md §2 and §4)
// ---------------------------------------------------------------------------------------------

// Validates QuickSilver.lean's `blockedStep` and `blockedHash_eq_sum` against uhasher_gfsecpar:
// after every update, the code's (state, pow + 1) is the model's, and the final hash is
// sum_k s^(n-1-k) x_k. Exhaustive over n = 1..64, which covers every n mod 8 several times, with a
// mix of field and bit inputs.
TEST(LeanModels, BlockedHornerMatchesModel) {
    std::mt19937_64 rng(3);
    using Hasher = faest::uhasher_gfsecpar<S>;
    for (size_t n = 1; n <= 64; ++n) {
        SCOPED_TRACE(testing::Message() << "n " << n);
        const Gf s = random_gf(rng);
        const auto key = Hasher::preprocess_key(to_poly(s));
        Hasher h;
        h.init(n);

        // The model's state: (state, pow + 1), initially (0, (n + 7) mod 8 + 1) (`blockedHash`).
        Gf st;
        size_t p = (n + 7) % 8 + 1;
        std::vector<Gf> xs;
        for (size_t k = 0; k < n; ++k) {
            Gf x;
            if (k % 3 == 0) {
                const bool bit = (rng() & 1) != 0;
                h.update(key, faest::poly1(bit));
                x = {uint64_t{bit}, 0};
            } else {
                x = random_gf(rng);
                h.update(key, to_poly(x));
            }
            xs.push_back(x);

            // `blockedStep`
            if (p == 0) {
                st = pow(s, 8) * st;
                p = 8;
            }
            st += pow(s, p - 1) * x;
            p -= 1;

            EXPECT_EQ(h.pow + 1, static_cast<int>(p)) << "after update " << k;
            EXPECT_EQ(from_poly(h.state.template reduce_to<128>()), st) << "after update " << k;
        }

        Gf sum;
        for (size_t k = 0; k < n; ++k) {
            sum += pow(s, n - 1 - k) * xs[k];
        }
        EXPECT_EQ(st, sum);
        EXPECT_EQ(from_poly(h.finalize()), sum);
    }
}

// Validates QuickSilver.lean's `horner` and `horner_eq_sum` against uhasher_gfsecpar_64, whose key
// is a 64-bit polynomial t.
TEST(LeanModels, ShortKeyHornerMatchesModel) {
    std::mt19937_64 rng(4);
    using Hasher = faest::uhasher_gfsecpar_64<S>;
    for (size_t n = 1; n <= 64; ++n) {
        SCOPED_TRACE(testing::Message() << "n " << n);
        const auto t_bytes = random_bytes<8>(rng);
        const Gf t = Gf::load64(t_bytes.data());
        const auto key = Hasher::preprocess_key(faest::poly64::load(t_bytes.data()));
        Hasher h;
        h.init(n);
        Gf horner;
        Gf sum;
        std::vector<Gf> xs;
        for (size_t k = 0; k < n; ++k) {
            const Gf x = random_gf(rng);
            h.update(key, to_poly(x));
            horner = t * horner + x; // `horner`
            xs.push_back(x);
        }
        for (size_t k = 0; k < n; ++k) {
            sum += pow(t, n - 1 - k) * xs[k];
        }
        EXPECT_EQ(horner, sum);
        EXPECT_EQ(from_poly(h.finalize()), sum);
    }
}

namespace {

constexpr size_t QS_CHALLENGE_BYTES = faest::QS_CONSTANTS<S, 1>::CHALLENGE_BYTES;
static_assert(QS_CHALLENGE_BYTES == 56);
using QsChallenge = std::array<uint8_t, QS_CHALLENGE_BYTES>;

// The ZKHash weights chi_k = r_0 s^(n-1-k) + r_1 t^(n-1-k) (`zkCoeff`), with chall_2 parsed as
// (r_0, r_1, s, t), where t is a 64-bit polynomial.
std::vector<Gf> zk_coeffs(const QsChallenge& chal2, size_t n) {
    const Gf r0 = Gf::load(&chal2[0]);
    const Gf r1 = Gf::load(&chal2[16]);
    const Gf s = Gf::load(&chal2[32]);
    const Gf t = Gf::load64(&chal2[48]);
    std::vector<Gf> chi(n);
    Gf s_pow = Gf::one();
    Gf t_pow = Gf::one();
    for (size_t i = 0; i < n; ++i) { // i = n - 1 - k
        chi[n - 1 - i] = r0 * s_pow + r1 * t_pow;
        s_pow *= s;
        t_pow *= t;
    }
    return chi;
}

} // namespace

// Validates QuickSilver.lean's `zkHash_eq_code` and `zkHash_eq_sum` (and so `zkCoeff`): the
// verifier's check value for constraint MACs m_0, ..., m_{n-1} (and no masks, at degree 1) is
// sum_k chi_k m_k. Exhaustive over n = 1..40, plus the five relations' n.
TEST(LeanModels, ZkHashMatchesModel) {
    std::mt19937_64 rng(5);
    using QS = faest::quicksilver_state<S, true, 1>;
    std::vector<size_t> ns;
    for (size_t n = 1; n <= 40; ++n) {
        ns.push_back(n);
    }
    for (const size_t n : {1313, 4008, 4409, 3776, 12282}) {
        ns.push_back(n);
    }
    for (const size_t n : ns) {
        SCOPED_TRACE(testing::Message() << "n " << n);
        const auto chal2 = random_bytes<QS_CHALLENGE_BYTES>(rng);
        const Gf delta = random_gf(rng);
        QS qs(nullptr, n, to_block(delta), chal2.data());
        const auto chi = zk_coeffs(chal2, n);
        Gf want;
        for (size_t k = 0; k < n; ++k) {
            // A public constant c at degree 1, whose MAC is c * Delta.
            const Gf c = random_gf(rng);
            qs.add_constraint(faest::quicksilver_gfsecpar<QS, 1>(to_poly(c), &qs));
            want += chi[k] * (c * delta);
        }
        std::array<uint8_t, 16> check;
        qs.verify(static_cast<const Block*>(nullptr), nullptr, check.data());
        EXPECT_EQ(Gf::load(check.data()), want);
    }
}

// ---------------------------------------------------------------------------------------------
// 3. QuickSilver check polynomial and its top coefficient (QuickSilver.lean `QSExpr.eval`,
//    `QSExpr.eval_natDegree_coeff`, `checkPoly_natDegree_coeff`, `maskPoly`)
// ---------------------------------------------------------------------------------------------

namespace {

// A small circuit of degree D = 4 that uses every operation of `QSExpr`: witness bits, constants
// (poly1 and poly_secpar) at several degrees, sums, products, combine_8_bits, explicit raising, and
// the raising to degree D in add_constraint. The constraints are written twice: with
// faest-arch-opt's QuickSilver operations here, and as formulas in small_circuit_model below.
constexpr size_t SMALL_DEGREE = 4;
constexpr size_t SMALL_CONSTRAINTS = 6;
constexpr size_t SMALL_WITNESS_BITS = 16;

struct SmallConsts {
    Gf c;  // multiplies combine_8_bits(b_8..b_15)
    Gf k;  // a constant at degree 3
    Gf c2; // a constant at degree 2
};

template <typename QS, typename Sink>
void small_circuit(const QS& qs, const SmallConsts& k, Sink&& sink) {
    using faest::poly1;
    using V1 = faest::quicksilver_gfsecpar<QS, 1>;
    using V2 = faest::quicksilver_gfsecpar<QS, 2>;
    using V4 = faest::quicksilver_gfsecpar<QS, 4>;
    const auto b = [&qs](size_t j) { return qs.get_witness_bit(j); };

    // C0 (degree 2): b_0 (b_0 + 1), as in add_bit_constraint.
    sink(V1(b(0)) * (V1(b(0)) + poly1(1)));
    // C1 (degree 3): b_0 b_1 b_2 + 1.
    sink(V1(b(0)) * V1(b(1)) * V1(b(2)) + poly1(1));
    // C2 (degree 3): (c * combine_8_bits(b_8..b_15) + b_3)^2 b_4 + k.
    const V1 y = to_poly(k.c) * qs.load_witness_8_bits_and_combine(8) + V1(b(3));
    sink(y * y * V1(b(4)) + to_poly(k.k));
    // C3 (degree 4): (b_0 + b_1)(b_2 + 1)(b_5 b_6).
    sink(V1(b(0) + b(1)) * V1(b(2) + poly1(1)) * (V1(b(5)) * V1(b(6))));
    // C4 (degree 2): the constant c2.
    sink(V2(to_poly(k.c2), &qs));
    // C5 (degree 4): b_7 raised from degree 1 to 4, plus 1.
    sink(V4(V1(b(7))) + poly1(1));
}

// `QSExpr.eval` of the constraints of small_circuit, raised to degree D, at X = delta, where
// witness bit j has MAC q(j). With q(j) = w_j and delta = 1, this is `QSExpr.value` at w.
std::array<Gf, SMALL_CONSTRAINTS> small_circuit_model(const std::function<Gf(size_t)>& q, Gf delta,
                                                      const SmallConsts& k) {
    // combine_8_bits weights beta_j: the embedding of the bit X^j of GF(256).
    Gf combined;
    for (size_t j = 0; j < 8; ++j) {
        combined += from_poly(Poly::from_8_byte(static_cast<uint8_t>(1u << j))) * q(8 + j);
    }
    const Gf y = k.c * combined + q(3);
    const Gf d2 = delta * delta;
    const Gf d3 = d2 * delta;
    return {
        q(0) * (q(0) + delta) * d2,
        (q(0) * q(1) * q(2) + d3) * delta,
        (y * y * q(4) + k.k * d3) * delta,
        (q(0) + q(1)) * (q(2) + delta) * (q(5) * q(6)),
        k.c2 * d2 * d2,
        q(7) * d3 + d2 * d2,
    };
}

// The verifier's view of one run of the small circuit at delta: the constraint MACs and the check
// value. Witness bit j has MAC v_j + w_j delta, and mask i has MAC a_i + b_i delta.
struct SmallRun {
    std::array<Gf, SMALL_CONSTRAINTS> macs;
    Gf check;
};

SmallRun run_small_verifier(const std::vector<Gf>& v, const std::vector<Gf>& w,
                            const std::vector<Gf>& a, const std::vector<Gf>& b,
                            const std::vector<Gf>& a_tilde, Gf delta, const SmallConsts& k,
                            const QsChallenge& chal2) {
    using QS = faest::quicksilver_state<S, true, SMALL_DEGREE>;
    std::vector<Block> macs;
    for (size_t j = 0; j < SMALL_WITNESS_BITS; ++j) {
        macs.push_back(to_block(v[j] + w[j] * delta));
    }
    std::vector<Block> q_mask;
    for (size_t i = 0; i + 1 < SMALL_DEGREE; ++i) {
        q_mask.push_back(to_block(a[i] + b[i] * delta));
    }
    std::vector<uint8_t> proof;
    for (size_t i = 1; i < SMALL_DEGREE; ++i) {
        append(proof, a_tilde[i]);
    }

    QS qs(macs.data(), SMALL_CONSTRAINTS, to_block(delta), chal2.data());
    SmallRun out;
    size_t i = 0;
    small_circuit(qs, k, [&](auto x) {
        const faest::quicksilver_gfsecpar<QS, SMALL_DEGREE> x_max = x;
        out.macs[i++] = from_poly(x_max.mac);
        qs.add_constraint(x);
    });
    std::array<uint8_t, 16> check;
    qs.verify(q_mask.data(), proof.data(), check.data());
    out.check = Gf::load(check.data());
    return out;
}

// `maskPoly` at delta, without the prover's check value z: sum_{i<d-1} (a_i + b_i X) X^i +
// sum_{1<=i<d} a~_i X^i.
Gf mask_poly(const std::vector<Gf>& a, const std::vector<Gf>& b, const std::vector<Gf>& a_tilde,
             Gf delta) {
    Gf out;
    for (size_t i = 0; i + 1 < SMALL_DEGREE; ++i) {
        out += (a[i] + b[i] * delta) * pow(delta, i);
    }
    for (size_t i = 1; i < SMALL_DEGREE; ++i) {
        out += a_tilde[i] * pow(delta, i);
    }
    return out;
}

std::vector<Gf> random_gfs(std::mt19937_64& rng, size_t n) {
    std::vector<Gf> out(n);
    for (Gf& a : out) {
        a = random_gf(rng);
    }
    return out;
}

} // namespace

// Validates `QSExpr.eval`, `maskPoly` and `checkPoly`: for random Delta, each of the verifier's
// constraint MACs is the circuit's eval polynomial at Delta, and its check value is
// sum_k chi_k eval_k(Delta) + maskPoly(Delta) (the check passes iff this equals the prover's z).
// Witness slopes w are arbitrary field elements, as in the Lean model.
TEST(LeanModels, QuickSilverVerifierMatchesEvalModel) {
    std::mt19937_64 rng(6);
    for (int trial = 0; trial < 20; ++trial) {
        const SmallConsts k = {random_gf(rng), random_gf(rng), random_gf(rng)};
        const auto v = random_gfs(rng, SMALL_WITNESS_BITS);
        const auto w = random_gfs(rng, SMALL_WITNESS_BITS);
        const auto a = random_gfs(rng, SMALL_DEGREE);
        const auto b = random_gfs(rng, SMALL_DEGREE);
        const auto a_tilde = random_gfs(rng, SMALL_DEGREE);
        const auto chal2 = random_bytes<QS_CHALLENGE_BYTES>(rng);
        const auto chi = zk_coeffs(chal2, SMALL_CONSTRAINTS);
        const Gf delta = random_gf(rng);

        const SmallRun run = run_small_verifier(v, w, a, b, a_tilde, delta, k, chal2);
        const auto model =
            small_circuit_model([&](size_t j) { return v[j] + w[j] * delta; }, delta, k);
        Gf want = mask_poly(a, b, a_tilde, delta);
        for (size_t i = 0; i < SMALL_CONSTRAINTS; ++i) {
            EXPECT_EQ(run.macs[i], model[i]) << "constraint " << i;
            want += chi[i] * model[i];
        }
        EXPECT_EQ(run.check, want);
    }
}

// Validates `checkPoly_natDegree_coeff` (and `QSExpr.eval_natDegree_coeff`,
// `maskPoly_natDegree_le`) on the small circuit: as a function of Delta, the verifier's check value
// is a polynomial of degree <= D whose X^D coefficient is sum_k chi_k f_k(w), where f_k =
// `QSExpr.value`. The masks and a~ are random, so they don't reach the top coefficient. Witness
// slopes are field elements in half the trials and bits in the other half, where C0 holds but the
// other constraints generally don't.
TEST(LeanModels, QuickSilverCheckPolynomialTopCoefficient) {
    std::mt19937_64 rng(7);
    for (int trial = 0; trial < 20; ++trial) {
        const SmallConsts k = {random_gf(rng), random_gf(rng), random_gf(rng)};
        const auto v = random_gfs(rng, SMALL_WITNESS_BITS);
        auto w = random_gfs(rng, SMALL_WITNESS_BITS);
        if (trial % 2 == 1) {
            for (Gf& wj : w) {
                wj = {wj.lo & 1, 0};
            }
        }
        const auto a = random_gfs(rng, SMALL_DEGREE);
        const auto b = random_gfs(rng, SMALL_DEGREE);
        const auto a_tilde = random_gfs(rng, SMALL_DEGREE);
        const auto chal2 = random_bytes<QS_CHALLENGE_BYTES>(rng);
        const auto chi = zk_coeffs(chal2, SMALL_CONSTRAINTS);

        std::vector<Gf> xs, ys;
        for (size_t i = 0; i < SMALL_DEGREE + 2; ++i) {
            xs.push_back(random_gf(rng));
            ys.push_back(run_small_verifier(v, w, a, b, a_tilde, xs.back(), k, chal2).check);
        }
        // Degree <= D: the (D+1)-th divided difference vanishes.
        EXPECT_EQ(divided_difference(xs, ys), Gf{});
        // The X^D coefficient.
        xs.pop_back();
        ys.pop_back();
        const auto values = small_circuit_model([&](size_t j) { return w[j]; }, Gf::one(), k);
        Gf want;
        for (size_t i = 0; i < SMALL_CONSTRAINTS; ++i) {
            want += chi[i] * values[i];
        }
        EXPECT_EQ(divided_difference(xs, ys), want);
    }
}

// Validates the prover side of `QSExpr.eval_natDegree_coeff`: on bit witnesses, the prover's MAC
// polynomial of each constraint (raised to degree D) evaluated at Delta is the verifier's MAC, its
// X^D coefficient is the prover's value, and that value is `QSExpr.value`.
TEST(LeanModels, QuickSilverProverPolynomialMatchesVerifier) {
    std::mt19937_64 rng(8);
    using PQS = faest::quicksilver_state<S, false, SMALL_DEGREE>;
    for (int trial = 0; trial < 20; ++trial) {
        const SmallConsts k = {random_gf(rng), random_gf(rng), random_gf(rng)};
        const auto v = random_gfs(rng, SMALL_WITNESS_BITS);
        const auto witness = random_bytes<SMALL_WITNESS_BITS / 8>(rng);
        std::vector<Gf> w;
        for (size_t j = 0; j < SMALL_WITNESS_BITS; ++j) {
            w.push_back({uint64_t{(witness[j / 8] >> (j % 8)) & 1u}, 0});
        }
        std::vector<Block> v_blocks;
        for (const Gf& vj : v) {
            v_blocks.push_back(to_block(vj));
        }
        const auto chal2 = random_bytes<QS_CHALLENGE_BYTES>(rng);

        // The prover's MAC polynomials, coefficient i of X^i. add_constraint isn't called, since
        // it requires satisfied constraints.
        const PQS pqs(witness.data(), v_blocks.data(), SMALL_CONSTRAINTS, chal2.data());
        std::vector<std::array<Gf, SMALL_DEGREE + 1>> polys;
        std::vector<Gf> prover_values;
        small_circuit(pqs, k, [&](auto x) {
            const faest::quicksilver_gfsecpar<PQS, SMALL_DEGREE> x_max = x;
            std::array<Gf, SMALL_DEGREE + 1> coeffs;
            for (size_t i = 0; i <= SMALL_DEGREE; ++i) {
                coeffs[i] = from_poly(x_max.mac.coeffs[i]);
            }
            polys.push_back(coeffs);
            prover_values.push_back(from_poly(x_max.value()));
        });
        ASSERT_EQ(polys.size(), SMALL_CONSTRAINTS);

        const auto values = small_circuit_model([&](size_t j) { return w[j]; }, Gf::one(), k);
        const std::vector<Gf> zeros(SMALL_DEGREE);
        const Gf delta = random_gf(rng);
        const SmallRun run = run_small_verifier(v, w, zeros, zeros, zeros, delta, k, chal2);
        for (size_t i = 0; i < SMALL_CONSTRAINTS; ++i) {
            SCOPED_TRACE(testing::Message() << "constraint " << i);
            Gf at_delta;
            for (size_t e = 0; e <= SMALL_DEGREE; ++e) {
                at_delta += polys[i][e] * pow(delta, e);
            }
            EXPECT_EQ(at_delta, run.macs[i]);
            EXPECT_EQ(polys[i][SMALL_DEGREE], prover_values[i]);
            EXPECT_EQ(prover_values[i], values[i]);
        }
    }
}

namespace {

namespace mo = vole_mole::ihat::detail;
namespace pf = vole_mole::pomfrit::detail;
namespace ra = vole_mole::act::detail;
using vole_mole::test::BasicPlainQS;

template <typename Relation> using Params = typename Relation::params;
template <typename Relation> constexpr size_t DEGREE = Params<Relation>::OWF_CONSTS::QS_DEGREE;
template <typename Relation>
constexpr size_t WITNESS_BYTES = vole_mole::detail::WITNESS_BYTES<Relation>;
template <typename Relation> constexpr size_t WITNESS_BITS = 8 * WITNESS_BYTES<Relation>;
template <typename Relation>
using Chal2 = std::array<uint8_t, Params<Relation>::CONSTS::QS::CHALLENGE_BYTES>;

// The verifier's QuickSilver check value for a relation at delta, with witness MACs q_j =
// v_j + w_j delta and mask MACs a_i + b_i delta.
template <typename Relation>
Gf relation_check(const typename Relation::instance& x, const Chal2<Relation>& chal2,
                  const std::vector<Gf>& v, const std::vector<Gf>& w, const std::vector<Gf>& a,
                  const std::vector<Gf>& b, const std::vector<Gf>& a_tilde, Gf delta) {
    constexpr size_t D = DEGREE<Relation>;
    using QS = faest::quicksilver_state<S, true, D>;
    std::vector<Block> macs;
    for (size_t j = 0; j < WITNESS_BITS<Relation>; ++j) {
        macs.push_back(to_block(v[j] + w[j] * delta));
    }
    std::vector<Block> q_mask;
    std::vector<uint8_t> proof;
    for (size_t i = 0; i + 1 < D; ++i) {
        q_mask.push_back(to_block(a[i] + b[i] * delta));
        append(proof, a_tilde[i + 1]);
    }
    QS qs(macs.data(), Relation::NUM_CONSTRAINTS, to_block(delta), chal2.data());
    Relation::constraints(&qs, x, chal2);
    std::array<uint8_t, 16> check;
    qs.verify(q_mask.data(), proof.data(), check.data());
    return Gf::load(check.data());
}

// Checks `checkPoly_natDegree_coeff` for a relation and a bit witness: the check value is a
// polynomial of degree <= d in Delta, and its X^d coefficient is sum_k chi_k f_k(w). Since the
// individual f_k aren't exposed, the latter is computed as the check value at Delta = 1 with
// q_j = w_j and zero masks, which is `QSExpr.value` (eval at X = 1 with no offsets). Returns the
// top coefficient.
template <typename Relation>
Gf check_relation_top_coefficient(const typename Relation::instance& x,
                                  std::span<const uint8_t, WITNESS_BYTES<Relation>> witness,
                                  std::mt19937_64& rng) {
    constexpr size_t D = DEGREE<Relation>;
    const auto chal2 = random_bytes<Params<Relation>::CONSTS::QS::CHALLENGE_BYTES>(rng);
    std::vector<Gf> w;
    for (size_t j = 0; j < WITNESS_BITS<Relation>; ++j) {
        w.push_back({uint64_t{(witness[j / 8] >> (j % 8)) & 1u}, 0});
    }
    const auto v = random_gfs(rng, w.size());
    const auto a = random_gfs(rng, D);
    const auto b = random_gfs(rng, D);
    const auto a_tilde = random_gfs(rng, D);

    std::vector<Gf> xs, ys;
    for (size_t i = 0; i < D + 2; ++i) {
        xs.push_back(random_gf(rng));
        ys.push_back(relation_check<Relation>(x, chal2, v, w, a, b, a_tilde, xs.back()));
    }
    EXPECT_EQ(divided_difference(xs, ys), Gf{}) << "degree > " << D;
    xs.pop_back();
    ys.pop_back();
    const Gf top = divided_difference(xs, ys);

    const std::vector<Gf> zeros(std::max(w.size(), D));
    EXPECT_EQ(top, relation_check<Relation>(x, chal2, zeros, w, zeros, zeros, zeros, Gf::one()));
    return top;
}

// The fixed test inputs of the relations.
const uov::Target POMFRIT_H = vole_mole::test::filled<uov::M>(0x70);
const uov::Target POMFRIT_R = vole_mole::test::filled<uov::M>(0xa0);

std::array<uint8_t, pf::REDEEM_WITNESS_BYTES> pomfrit_honest_witness() {
    uov::Target hr;
    for (size_t i = 0; i < uov::M; ++i) {
        hr[i] = POMFRIT_H[i] ^ POMFRIT_R[i];
    }
    const uov::Preimage s = vole_mole::test::uov_key_pair().sk.derive_preimage(hr);
    std::array<uint8_t, pf::REDEEM_WITNESS_BYTES> w{};
    std::ranges::copy(POMFRIT_R, w.begin() + pf::WIT_OFF_R);
    std::ranges::copy(s, w.begin() + pf::WIT_OFF_S);
    return w;
}

const vole_mole::ihat::Context IHAT_CTX_ISS = vole_mole::test::filled<16>(0x10);
const vole_mole::ihat::Context IHAT_CTX_RED = vole_mole::test::filled<16>(0x20);
const vole_mole::ihat::Nullifier IHAT_NF = vole_mole::test::filled<24>(0x30);
const mo::Opening IHAT_R = vole_mole::test::filled<16>(0x40);

template <typename Relation>
size_t count_violated(const typename Relation::instance& x,
                      std::span<const uint8_t, WITNESS_BYTES<Relation>> witness,
                      const Chal2<Relation>& chal2) {
    BasicPlainQS<DEGREE<Relation>> qs{witness.data(), {}};
    Relation::constraints(&qs, x, chal2);
    return static_cast<size_t>(std::ranges::count(qs.violated, true));
}

} // namespace

// Validates `checkPoly_natDegree_coeff` on PomFRIT redeem (d = 2): an honest witness gives top
// coefficient 0, and a witness with a flipped bit of s violates the combined constraint, which
// gives a nonzero top coefficient.
TEST(LeanModels, PomfritCheckPolynomialTopCoefficient) {
    std::mt19937_64 rng(9);
    const pf::RedeemRelation::instance x = {&vole_mole::test::uov_key_pair().pk, POMFRIT_H};
    auto w = pomfrit_honest_witness();
    EXPECT_EQ(check_relation_top_coefficient<pf::RedeemRelation>(x, w, rng), Gf{});

    w[pf::WIT_OFF_S] ^= 1;
    ASSERT_EQ(count_violated<pf::RedeemRelation>(x, w, {}), 1u);
    EXPECT_NE(check_relation_top_coefficient<pf::RedeemRelation>(x, w, rng), Gf{});
}

// As above, for VOLE-IHAT issue (d = 9, with the Keccak constraints).
TEST(LeanModels, IhatIssueCheckPolynomialTopCoefficient) {
    std::mt19937_64 rng(10);
    const mo::IssueRelation::instance x = {
        mo::commit(IHAT_NF, IHAT_CTX_ISS, IHAT_CTX_RED, IHAT_R), IHAT_CTX_ISS};
    auto w = mo::encode_issue_witness(IHAT_NF, IHAT_CTX_ISS, IHAT_CTX_RED, IHAT_R);
    EXPECT_EQ(check_relation_top_coefficient<mo::IssueRelation>(x, w, rng), Gf{});

    w[mo::WIT_OFF_STATES] ^= 1; // a bit of the first committed Keccak state
    ASSERT_GT(count_violated<mo::IssueRelation>(x, w, {}), 0u);
    EXPECT_NE(check_relation_top_coefficient<mo::IssueRelation>(x, w, rng), Gf{});
}

// ---------------------------------------------------------------------------------------------
// 4. Constraint counts (lean/docs/extraction/L4-quicksilver.md §7: n in `zkCoeff` is NUM_CONSTRAINTS)
// ---------------------------------------------------------------------------------------------

namespace {

// Counts the constraints that a relation's `constraints` adds (each add_constraint and
// add_bit_constraint call is one entry of BasicPlainQS::violated), and checks that faest-arch-opt's
// verifier, initialized with NUM_CONSTRAINTS, ends with the hasher state that finalize requires
// (pow == -1, i.e., the count is NUM_CONSTRAINTS mod 8).
template <typename Relation> void check_constraint_count(const typename Relation::instance& x) {
    const std::vector<uint8_t> witness(WITNESS_BYTES<Relation>);
    const Chal2<Relation> chal2{};
    BasicPlainQS<DEGREE<Relation>> plain{witness.data(), {}};
    Relation::constraints(&plain, x, chal2);
    EXPECT_EQ(plain.violated.size(), Relation::NUM_CONSTRAINTS);

    using QS = faest::quicksilver_state<S, true, DEGREE<Relation>>;
    const std::vector<Block> macs(WITNESS_BITS<Relation>, Block::set_zero());
    QS qs(macs.data(), Relation::NUM_CONSTRAINTS, to_block(Gf::one()), chal2.data());
    Relation::constraints(&qs, x, chal2);
    EXPECT_EQ(qs.state_secpar[0].pow, -1);
}

} // namespace

// The constraint counts n of L4 §7, for all five relations: PomFRIT redeem 1313, VOLE-IHAT issue
// 4008, VOLE-IHAT redeem 4409, VOLE-ACT issue 3776, VOLE-ACT spend 12282.
TEST(LeanModels, ConstraintCountsMatchNumConstraints) {
    const uov::PublicKey& pk = vole_mole::test::uov_key_pair().pk;
    {
        SCOPED_TRACE("PomFRIT redeem");
        static_assert(pf::RedeemRelation::NUM_CONSTRAINTS == 1313);
        check_constraint_count<pf::RedeemRelation>({&pk, {}});
    }
    {
        SCOPED_TRACE("VOLE-IHAT issue");
        static_assert(mo::IssueRelation::NUM_CONSTRAINTS == 4008);
        check_constraint_count<mo::IssueRelation>({});
    }
    {
        SCOPED_TRACE("VOLE-IHAT redeem");
        static_assert(mo::RedeemRelation::NUM_CONSTRAINTS == 4409);
        const std::array<vole_mole::ihat::AnchorRef, 1> anchors = {pk};
        check_constraint_count<mo::RedeemRelation>({anchors, {}, {}, {}, {}});
    }
    {
        SCOPED_TRACE("VOLE-ACT issue");
        static_assert(ra::IssueRelation::NUM_CONSTRAINTS == 3776);
        check_constraint_count<ra::IssueRelation>({});
    }
    {
        SCOPED_TRACE("VOLE-ACT spend");
        static_assert(ra::SpendRelation::NUM_CONSTRAINTS == 12282);
        check_constraint_count<ra::SpendRelation>({pk, {}, 0, {}, {}});
    }
}

// ---------------------------------------------------------------------------------------------
// 5. Grinding (lean/VoleMole/ZK/Grinding.lean)
// ---------------------------------------------------------------------------------------------

namespace {

using Bavc = pf::RedeemParams::bavc_t;
constexpr size_t W_GRIND = 128 - Bavc::delta_bits_v;
static_assert(W_GRIND == 8);
using Delta = std::array<uint8_t, 16>;

// The acceptance set A of Grinding.lean: the top w_grind bits of Delta are zero, and the BAVC
// opening at Delta succeeds. The opening is attempted on an all-zero tree, so that this tests that
// success depends on Delta alone.
bool in_acceptance_set(const Delta& delta) {
    if (delta[15] != 0) { // bits 120..127
        return false;
    }
    static const std::vector<Block> tree(Bavc::COMMIT_NODES, Block::set_zero());
    static const std::vector<unsigned char> hashed_leaves(Bavc::COMMIT_LEAVES *
                                                          Bavc::leaf_hash_t::hash_len);
    std::array<uint8_t, Bavc::delta_bits_v> delta_bits;
    for (size_t i = 0; i < delta_bits.size(); ++i) {
        delta_bits[i] = ((delta[i / 8] >> (i % 8)) & 1) != 0 ? 0xff : 0;
    }
    std::vector<unsigned char> opening(Bavc::OPEN_SIZE);
    return Bavc::open(tree.data(), hashed_leaves.data(), delta_bits.data(), opening.data());
}

// The H_2^3 output for counter ctr: SHAKE128(prefix || ctr (u32, little endian) || 0x0B).
Delta grinding_hash(std::span<const uint8_t> prefix, uint32_t ctr) {
    std::vector<uint8_t> input(prefix.begin(), prefix.end());
    for (size_t i = 0; i < 4; ++i) {
        input.push_back(static_cast<uint8_t>(ctr >> (8 * i)));
    }
    input.push_back(8 + 3);
    const Digest d = shake128(input);
    Delta out;
    std::copy_n(d.begin(), out.size(), out.begin());
    return out;
}

} // namespace

// Validates `IsFirstHit` (the first-success law): grind_and_open returns the first counter whose
// H_2^3 output lies in A, and that output as Delta. A is a fixed set: membership is computed from
// Delta alone (with a different tree than the prover's). Also checks, statistically and loosely,
// that the counter is geometric with success probability |A|/|Omega| (`card_isFirstHit`), where
// |A|/|Omega| is estimated from independent samples.
TEST(LeanModels, GrindingReturnsFirstHit) {
    std::mt19937_64 rng(11);

    // A random tree, distinct from the one used by in_acceptance_set.
    std::vector<Block> forest(Bavc::COMMIT_NODES);
    for (Block& blk : forest) {
        blk = to_block(random_gf(rng));
    }
    std::vector<unsigned char> hashed_leaves(Bavc::COMMIT_LEAVES * Bavc::leaf_hash_t::hash_len);
    for (unsigned char& c : hashed_leaves) {
        c = static_cast<unsigned char>(rng());
    }

    constexpr int RUNS = 128;
    double counter_sum = 0;
    for (int run = 0; run < RUNS; ++run) {
        const auto prefix = random_bytes<93 - 5>(rng); // chal2 || qs_check || qs_proof (PomFRIT)
        faest::hash_state_x4 hasher;
        hasher.init(S);
        hasher.update_1(prefix);
        Delta delta_out{};
        std::vector<unsigned char> opening(Bavc::OPEN_SIZE);
        uint32_t counter = 0;
        ASSERT_TRUE(faest::grind_and_open<Bavc>(forest.data(), hashed_leaves.data(),
                                                delta_out.data(), opening.data(), &hasher,
                                                &counter));
        for (uint32_t ctr = 0; ctr < counter; ++ctr) {
            EXPECT_FALSE(in_acceptance_set(grinding_hash(prefix, ctr))) << "counter " << ctr;
        }
        const Delta hit = grinding_hash(prefix, counter);
        EXPECT_TRUE(in_acceptance_set(hit));
        EXPECT_EQ(delta_out, hit);
        counter_sum += counter;
    }

    // Estimate Pr[open succeeds | top bits zero] from random Deltas.
    constexpr int SAMPLES = 4000;
    int opened = 0;
    for (int i = 0; i < SAMPLES; ++i) {
        Delta d = random_bytes<16>(rng);
        d[15] = 0;
        opened += in_acceptance_set(d) ? 1 : 0;
    }
    const double p = (static_cast<double>(opened) / SAMPLES) / (1u << W_GRIND);
    const double mean = (1 - p) / p; // of the geometric distribution
    const double stderr_mean = std::sqrt(1 - p) / p / std::sqrt(double{RUNS});
    EXPECT_NEAR(counter_sum / RUNS, mean, 5 * stderr_mean);
}

// Validates the verifier's half of the acceptance predicate: check_format accepts a Delta iff its
// top w_grind bits are zero. Exhaustive over the top byte, with random lower bytes.
TEST(LeanModels, CheckFormatMatchesGrindingPredicate) {
    std::mt19937_64 rng(12);
    using P = pf::RedeemParams;
    std::vector<uint8_t> proof(faest::FAEST_SIGNATURE_BYTES<P>); // c_mult padding is zero
    const faest::mutable_faest_signature<P> view(proof.data());
    for (unsigned top = 0; top < 256; ++top) {
        for (int i = 0; i < 4; ++i) {
            Delta d = random_bytes<16>(rng);
            d[15] = static_cast<uint8_t>(top);
            std::ranges::copy(d, view.delta().begin());
            EXPECT_EQ(view.check_format(), top == 0) << "top byte " << top;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 6. Domain separation (lean/VoleMole/Protocols/DomainSeparation.lean, `proofSystem`)
// ---------------------------------------------------------------------------------------------

namespace {

// The lengths of the H_2^1, H_2^2 and H_2^3 inputs of a relation, assembled from the code's field
// sizes in the order voleith.hpp hashes them:
// - H_2^1: mu || com || c_1..c_{tau-1} || c_mult || iv_pre || binder_1 || 09
// - H_2^2: chal_1 || u~ || h_V || [mu] || binder_2 || d || 0A
// - H_2^3: chal_2 || a~_0 || a~_1..a~_{d-1} || ctr || 0B
// delayed is whether mu is in H_2^2 (delayed instance binding), and binder_1, binder_2 the binder
// lengths the application passes.
struct ProofHashLengths {
    size_t h21, h22, h23;
};

template <typename Relation>
ProofHashLengths proof_hash_lengths(bool delayed, size_t binder1, size_t binder2) {
    using P = Params<Relation>;
    using CP = P::CONSTS;
    using View = faest::faest_signature<P>;
    constexpr size_t MU = sizeof(faest::block_2secpar<S>);
    return {
        MU + CP::VOLE_COMMIT_CHECK_SIZE + View::SIZE_VOLE_COMMITMENT + View::SIZE_IV_PRE + binder1 +
            1,
        CP::VOLE_CHECK::CHALLENGE_BYTES + View::SIZE_VOLE_CHECK_PROOF +
            CP::VOLE_CHECK::PROOF_BYTES + (delayed ? MU : 0) + binder2 + View::SIZE_CORRECTION + 1,
        CP::QS::CHALLENGE_BYTES + CP::QS::CHECK_BYTES + View::SIZE_QS_PROOF +
            View::SIZE_GRINDING_CTR + 1,
    };
}

} // namespace

// The `proofSystem` rows H2^1, H2^2 and H2^3 of DomainSeparation.lean: lengths per relation (in the
// order PomFRIT, VOLE-IHAT issue, VOLE-IHAT redeem, VOLE-ACT issue, VOLE-ACT spend, unbound
// VOLE-IHAT issue, unbound VOLE-IHAT redeem). PomFRIT
// binds the instance late and passes refresher_com (32 bytes) and the refresher (32 bytes) as
// binders (pomfrit.cpp); the others use voleith_prove, with no binders. The final tags 09, 0A and
// 0B are hard-coded in voleith.hpp; GrindingReturnsFirstHit checks the H_2^3 suffix ctr || 0B.
TEST(LeanModels, ProofHashLengthsMatchDomainTable) {
    const std::array<ProofHashLengths, 7> got = {
        proof_hash_lengths<pf::RedeemRelation>(true, 32, 32),
        proof_hash_lengths<mo::IssueRelation>(false, 0, 0),
        proof_hash_lengths<mo::RedeemRelation>(false, 0, 0),
        proof_hash_lengths<ra::IssueRelation>(false, 0, 0),
        proof_hash_lengths<ra::SpendRelation>(false, 0, 0),
        proof_hash_lengths<mo::UnboundIssueRelation>(false, 0, 0),
        proof_hash_lengths<mo::UnboundRedeemRelation>(false, 0, 0),
    };
    const std::array<size_t, 7> h21 = {3188, 4645, 6037, 4389, 14101, 4261, 9493};
    const std::array<size_t, 7> h22 = {493, 521, 608, 505, 1112, 497, 824};
    const std::array<size_t, 7> h23 = {93, 205, 205, 205, 205, 205, 205};
    for (size_t i = 0; i < got.size(); ++i) {
        SCOPED_TRACE(testing::Message() << "relation " << i);
        EXPECT_EQ(got[i].h21, h21[i]);
        EXPECT_EQ(got[i].h22, h22[i]);
        EXPECT_EQ(got[i].h23, h23[i]);
    }
}

namespace {

template <size_t deg>
void check_combination_domain(std::span<const uint8_t, vole_mole::detail::DST_BYTES> dst) {
    using QS = BasicPlainQS<deg>;
    using Combination = vole_mole::uov::detail::Combination<QS>;
    std::mt19937_64 rng(13);
    const auto chal2 = random_bytes<Combination::CHALLENGE_BYTES>(rng);
    const Combination l(chal2, dst);

    std::vector<uint8_t> input(chal2.begin(), chal2.end());
    input.insert(input.end(), dst.begin(), dst.end());
    EXPECT_EQ(input.size(), 63u);
    std::array<uint8_t, Combination::L_BYTES> l_bytes;
    faest::hash_state h;
    h.init(S);
    h.update(input);
    h.finalize(l_bytes);
    for (size_t k = 0; k < uov::M; ++k) {
        EXPECT_EQ(from_poly(l.coeff(k)), Gf::load(&l_bytes[16 * k])) << "coefficient " << k;
    }
}

} // namespace

// The `proofSystem` rows "UOV combination ...": the combination coefficients are
// SHAKE128(chal2 || DST), 63 bytes ending in the relation's combine DST.
TEST(LeanModels, CombinationHashMatchesDomainTable) {
    check_combination_domain<pf::REDEEM_QS_DEGREE>(vole_mole::detail::POMFRIT_COMBINE_DST);
    check_combination_domain<mo::REDEEM_QS_DEGREE>(vole_mole::detail::IHAT_REDEEM_COMBINE_DST);
    check_combination_domain<ra::SPEND_QS_DEGREE>(vole_mole::detail::ACT_SPEND_COMBINE_DST);
}
