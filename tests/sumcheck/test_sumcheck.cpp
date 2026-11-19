// Tests for the mod-q checks by product-tree sumcheck (src/sumcheck/, docs/sumcheck-modq.md):
// the exactness of the exponent check (exhaustively, for tiny instances), and complete VOLEitH
// proofs of small relations whose witness prefix is the value bits and whose suffix is the
// answer, with the witness committed directly or derived.

#include "sumcheck/exp_modq.hpp"      // internal
#include "sumcheck/gf128.hpp"         // internal
#include "sumcheck/tree_sumcheck.hpp" // internal
#include "sumcheck/voleith_fs.hpp"    // internal
#include "voleith.hpp"                // internal
#include "witness_prg.hpp"            // internal

#include "test.hpp"

#include "faest_sig.hpp"  // from faest-arch-opt
#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <random>
#include <span>
#include <utility>
#include <vector>

using namespace vole_mole::sumcheck::detail;

namespace sc_test {

constexpr uint32_t Q = 8380417;

// NV values with a mix of widths and shifts: consecutive shifts, a repeated shift (as for psi in
// the ML-DSA gadget), and a trailing bit of shift 0 (as for the guarded bits of f).
template <size_t NV> struct Spec {
    static constexpr uint32_t Q = sc_test::Q;
    static constexpr size_t NUM_VALUES = NV;
    static constexpr size_t value_bits(size_t j) { return NV == 1 ? 2 : 1 + (5 * j + 3) % 20; }
    static constexpr size_t bit_shift(size_t j, size_t i) {
        if (j % 4 == 2) {
            return i < 2 ? i : i - 1;
        }
        if (j % 4 == 3 && i + 1 == value_bits(j) && i > 0) {
            return 0;
        }
        return i;
    }
    static constexpr uint32_t offset(size_t j) { return static_cast<uint32_t>(j * 1000003 % Q); }
    static constexpr size_t NUM_CHECKS = 6;
};

// The variants: c = 0 commits to the witness directly, c = 1 derives it with the local PRG.
template <size_t c> struct prg {
    using type = vole_mole::detail::NoPrg;
};
template <> struct prg<1> {
    using type = vole_mole::detail::LocalPrg<2>;
};

template <size_t NV> using X = ExpModQ<Spec<NV>>;
template <size_t NV> constexpr size_t PREFIX_BYTES = (X<NV>::NUM_BITS + 7) / 8;
template <size_t NV> constexpr size_t WITNESS_BYTES = PREFIX_BYTES<NV> + X<NV>::ANSWER_BYTES;

template <size_t NV, size_t c>
constexpr faest::owf OWF = static_cast<faest::owf>(((0xB0u +
                                                     2 * (NV == 1   ? 0
                                                          : NV == 9 ? 1
                                                                    : 2) +
                                                     c)
                                                    << 8) |
                                                   0b10'0000);

} // namespace sc_test

#define SC_OWF_CONSTANTS(NV, c)                                                                    \
    template <>                                                                                    \
    struct faest::OWF_CONSTANTS<faest::secpar::s128, sc_test::OWF<NV, c>>                          \
        : vole_mole::detail::RelationConstants<8 * sc_test::WITNESS_BYTES<NV>, 2,                  \
                                               sc_test::prg<c>::type> {}
SC_OWF_CONSTANTS(1, 0);
SC_OWF_CONSTANTS(1, 1);
SC_OWF_CONSTANTS(9, 0);
SC_OWF_CONSTANTS(9, 1);
SC_OWF_CONSTANTS(40, 0);
SC_OWF_CONSTANTS(40, 1);
#undef SC_OWF_CONSTANTS

namespace {

using namespace vole_mole::detail;
using sc_test::Q;

constexpr std::array<uint8_t, 4> DST = {'s', 'c', 't', '0'};
constexpr std::array<uint8_t, 4> PRG_DST = {'s', 'c', 't', 'q'};
constexpr std::array<uint8_t, 4> CHAIN_DST = {'s', 'c', 't', 'c'};

template <size_t NV, size_t c> struct Relation {
    using Xq = sc_test::X<NV>;
    using params =
        faest::parameter_set<faest::secpar::s128, /* TAU */ 17, sc_test::OWF<NV, c>,
                             faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                             /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                             /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;
    struct instance {
        std::array<uint32_t, 6> constants; // A_k
        const typename Xq::Encoded* enc;
        const typename Xq::Challenges* challenges;
    };
    static constexpr size_t NUM_CONSTRAINTS = Xq::NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = sc_test::PREFIX_BYTES<NV>;
    static constexpr std::span<const uint8_t> DST = ::DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST = PRG_DST;

    static void hash_instance(faest::hash_state& h, const instance& x) {
        for (const uint32_t a : x.constants) {
            h.update_byte(static_cast<uint8_t>(a));
            h.update_byte(static_cast<uint8_t>(a >> 8));
            h.update_byte(static_cast<uint8_t>(a >> 16));
        }
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        Xq::qs_constraints(qs, *x.enc, *x.challenges, 8 * WITNESS_PREFIX_BYTES,
                           [&](size_t j, size_t i) { return qs->get_witness_bit(bit_of(j, i)); });
    }

    // The prefix bit of bit i of value j.
    static size_t bit_of(size_t j, size_t i) {
        size_t b = 0;
        for (size_t jj = 0; jj < j; ++jj) {
            b += sc_test::Spec<NV>::value_bits(jj);
        }
        return b + i;
    }
};

template <typename R> using Proof = std::array<uint8_t, PROOF_BYTES<R>>;

// The seed of the checks, from chal1 and the commitment to the witness prefix.
template <typename R>
std::array<uint8_t, 32> check_seed(std::span<const uint8_t> chal1, const_proof_span<R> proof) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(chal1);
    const faest::faest_signature<relation_params<R>> view(proof.data());
    h.update(view.vole_check_proof());
    hash_witness_prefix_commitment<R>(h, proof);
    std::array<uint8_t, 32> seed;
    h.finalize(seed);
    return seed;
}

// W_{k,j}, uniform in [0, q), from the seed.
template <size_t NV> std::vector<uint32_t> weights(const std::array<uint8_t, 32>& seed) {
    std::seed_seq seq(seed.begin(), seed.end());
    std::mt19937_64 rng(seq);
    std::vector<uint32_t> w(6 * NV);
    for (auto& x : w) {
        x = static_cast<uint32_t>(rng() % Q);
    }
    return w;
}

// A_k for the values in `prefix`: sum_j W_{k,j} (x_j - offset(j)) mod q.
template <size_t NV>
std::array<uint32_t, 6> true_constants(std::span<const uint8_t> prefix,
                                       std::span<const uint32_t> w) {
    using Sp = sc_test::Spec<NV>;
    std::array<uint32_t, 6> a{};
    size_t b = 0;
    for (size_t j = 0; j < NV; ++j) {
        uint64_t v = 0;
        for (size_t i = 0; i < Sp::value_bits(j); ++i, ++b) {
            if (((prefix[b / 8] >> (b % 8)) & 1) != 0) {
                v += uint64_t{1} << Sp::bit_shift(j, i);
            }
        }
        const uint64_t xv = (v % Q + Q - Sp::offset(j)) % Q;
        for (size_t k = 0; k < 6; ++k) {
            a[k] = static_cast<uint32_t>((a[k] + xv * w[k * NV + j]) % Q);
        }
    }
    return a;
}

// How the prover deviates.
struct Cheat {
    std::optional<std::array<uint32_t, 6>> quotients; // instead of the honest ones
    std::optional<size_t> flip_answer_bit;            // after the answer is computed
    std::optional<std::array<uint32_t, 6>> constants; // the claim the prover uses
};

template <size_t NV, size_t c> struct Harness {
    using R = Relation<NV, c>;
    using Xq = sc_test::X<NV>;

    // Proves the checks for constants A (which the verifier also uses), on the prefix's values.
    // A is a function of the weights (i.e., of the seed).
    template <typename ConstantsOf>
    static Proof<R> prove(std::span<const uint8_t, R::WITNESS_PREFIX_BYTES> prefix,
                          ConstantsOf&& constants_of, const Cheat& cheat = {}, uint8_t rho_s = 1) {
        Proof<R> proof{};
        const auto rho = vole_mole::test::filled<16>(rho_s);
        auto pending = voleith_vole_gen<R>(proof, nullptr, prefix, rho);
        const auto seed = check_seed<R>(pending.chal1, proof);
        const auto w = weights<NV>(seed);
        const auto a = constants_of(w);
        const auto enc = Xq::encode(w, cheat.constants ? *cheat.constants : a);
        std::array<uint8_t, Xq::ANSWER_BYTES> answer;
        typename Xq::Challenges ch;
        Chain chain(CHAIN_DST, seed);
        Xq::answer(
            enc,
            [&](size_t j, size_t i) {
                const size_t b = R::bit_of(j, i);
                return ((prefix[b / 8] >> (b % 8)) & 1) != 0;
            },
            std::span<uint8_t, Xq::ANSWER_BYTES>(answer),
            [&](size_t off, size_t len) {
                std::vector<uint8_t> m(len);
                for (size_t i = 0; i < len; ++i) {
                    m[i] =
                        answer[off + i] ^ sumcheck_pad(pending, R::WITNESS_PREFIX_BYTES + off + i);
                }
                return chain.next(m);
            },
            ch, cheat.quotients ? &*cheat.quotients : nullptr);
        if (cheat.flip_answer_bit) {
            answer[*cheat.flip_answer_bit / 8] ^=
                static_cast<uint8_t>(1u << (*cheat.flip_answer_bit % 8));
            // The challenges the verifier will derive.
            std::array<uint8_t, Xq::ANSWER_BYTES> masked;
            for (size_t i = 0; i < masked.size(); ++i) {
                masked[i] = answer[i] ^ sumcheck_pad(pending, R::WITNESS_PREFIX_BYTES + i);
            }
            ch = Xq::challenges(Chain(CHAIN_DST, seed),
                                std::span<const uint8_t, Xq::ANSWER_BYTES>(masked));
        }
        const typename R::instance inst{a, &enc, &ch};
        voleith_prove_commit<R>(
            proof, inst,
            std::span<const uint8_t, WITNESS_SUFFIX_BYTES<R>>(answer.data(), answer.size()),
            std::move(pending));
        return proof;
    }

    static uint8_t sumcheck_pad(const PendingProof<R>& p, size_t i) {
        return prover_pad_byte<R>(p, i);
    }

    template <typename ConstantsOf>
    static bool verify(const Proof<R>& proof, ConstantsOf&& constants_of) {
        auto pending = voleith_vole_reconstruct<R>(proof, nullptr);
        if (!pending) {
            return false;
        }
        const auto seed = check_seed<R>(pending->chal1, proof);
        const auto w = weights<NV>(seed);
        const auto a = constants_of(w);
        const auto enc = Xq::encode(w, a);
        const auto masked = masked_witness<R>(proof, R::WITNESS_PREFIX_BYTES, Xq::ANSWER_BYTES);
        const auto ch = Xq::challenges(Chain(CHAIN_DST, seed),
                                       std::span<const uint8_t, Xq::ANSWER_BYTES>(masked));
        const typename R::instance inst{a, &enc, &ch};
        return voleith_verify_commit<R>(proof, inst, std::move(*pending));
    }
};

template <size_t NV> std::array<uint8_t, sc_test::PREFIX_BYTES<NV>> random_prefix(uint64_t s) {
    std::mt19937_64 rng(s);
    std::array<uint8_t, sc_test::PREFIX_BYTES<NV>> p;
    for (auto& b : p) {
        b = static_cast<uint8_t>(rng());
    }
    return p;
}

template <typename T> class SumcheckProof : public testing::Test {};
template <size_t NV, size_t c> struct Params {
    static constexpr size_t nv = NV;
    static constexpr size_t prg = c;
};
using AllParams = testing::Types<Params<1, 0>, Params<1, 1>, Params<9, 0>, Params<9, 1>,
                                 Params<40, 0>, Params<40, 1>>;
TYPED_TEST_SUITE(SumcheckProof, AllParams);

} // namespace

// Product of the leaves of tree t, for data bits x and quotients k.
template <size_t NV>
Gf tree_product(const typename sc_test::X<NV>::Encoded& enc, size_t t, uint32_t x,
                const std::array<uint32_t, 3>& k) {
    using Xq = sc_test::X<NV>;
    Gf p = gf_one();
    for (size_t b = 0; b < Xq::NUM_BITS; ++b) {
        if (((x >> b) & 1) != 0) {
            p = gf_mul(p, enc.coef[(t << Xq::D) + b] + gf_one());
        }
    }
    for (size_t l = 0; l < 3; ++l) {
        for (size_t s = 0; s < Xq::KAPPA; ++s) {
            if (((k[l] >> s) & 1) != 0) {
                p = gf_mul(p, enc.coef[(t << Xq::D) + Xq::NUM_BITS + Xq::KAPPA * l + s] + gf_one());
            }
        }
    }
    return p;
}

TEST(SumcheckGf, Generator) {
    const Gf g = generator();
    EXPECT_FALSE(gf_eq(g, gf_one()));
    EXPECT_TRUE(gf_eq(gf_pow(g, GROUP_ORDER), gf_one()));
    for (const U128 p : GROUP_ORDER_FACTORS) {
        EXPECT_FALSE(gf_eq(gf_pow(g, GROUP_ORDER / p), gf_one()));
    }
    EXPECT_TRUE(gf_eq(gf_mul(gf_signed_pow(g, -12345), gf_pow(g, 12345)), gf_one()));
}

TEST(SumcheckGf, EqTable) {
    std::mt19937_64 rng(3);
    std::vector<Gf> z(4);
    for (auto& v : z) {
        v = gf_from_u128((U128{rng()} << 64) | rng());
    }
    const auto t = eq_table(z);
    Gf sum = gf_zero();
    for (size_t n = 0; n < t.size(); ++n) {
        Gf e = gf_one();
        for (size_t j = 0; j < z.size(); ++j) {
            e = gf_mul(e, ((n >> j) & 1) != 0 ? z[j] : z[j] + gf_one());
        }
        EXPECT_TRUE(gf_eq(e, t[n])) << n;
        sum += t[n];
    }
    EXPECT_TRUE(gf_eq(sum, gf_one()));
}

// Exactness: for every assignment of the data bits and the quotients of a tiny instance, the tree
// product equals the root iff the three integer equations S_k = B_k + q k_k hold. Weights random
// and extreme (q - 1, the largest sums).
TEST(SumcheckExactness, Exhaustive) {
    using Xq = sc_test::X<1>; // two bits, KAPPA = 1
    static_assert(Xq::NUM_BITS == 2 && Xq::KAPPA == 1);
    using Sp = sc_test::Spec<1>;
    std::mt19937_64 rng(5);
    for (size_t trial = 0; trial < 40; ++trial) {
        std::vector<uint32_t> w(6);
        for (auto& x : w) {
            x = trial < 4 ? Q - 1 - static_cast<uint32_t>(trial) : static_cast<uint32_t>(rng() % Q);
        }
        std::array<uint32_t, 6> a{};
        for (auto& x : a) {
            x = trial % 3 == 0 ? static_cast<uint32_t>(rng() % Q)
                               : static_cast<uint32_t>(rng() % 4);
        }
        const auto enc = Xq::encode(w, a);
        for (size_t t = 0; t < 2; ++t) {
            for (uint32_t x = 0; x < 4; ++x) {
                for (uint32_t kk = 0; kk < 8; ++kk) {
                    const std::array<uint32_t, 3> k = {kk & 1, (kk >> 1) & 1, (kk >> 2) & 1};
                    bool holds = true;
                    for (size_t l = 0; l < 3; ++l) {
                        const size_t chk = 3 * t + l;
                        int64_t s = 0;
                        for (size_t i = 0; i < 2; ++i) {
                            if (((x >> i) & 1) != 0) {
                                s += int64_t{w[chk]} * (int64_t{1} << Sp::bit_shift(0, i)) % Q;
                            }
                        }
                        holds &= s == int64_t{enc.b[chk]} + int64_t{Q} * k[l];
                    }
                    EXPECT_EQ(gf_eq(tree_product<1>(enc, t, x, k), enc.roots[t]), holds)
                        << trial << " " << t << " " << x << " " << kk;
                }
            }
        }
    }
}

// The same for 9 values (65 bits): random data bits, the honest quotients and nearby ones.
TEST(SumcheckExactness, Random) {
    using Xq = sc_test::X<9>;
    std::mt19937_64 rng(7);
    for (size_t trial = 0; trial < 20; ++trial) {
        std::vector<uint32_t> w(6 * 9);
        for (auto& x : w) {
            x = trial < 2 ? Q - 1 : static_cast<uint32_t>(rng() % Q);
        }
        std::array<uint32_t, 6> a{};
        for (auto& x : a) {
            x = static_cast<uint32_t>(rng() % Q);
        }
        const auto enc = Xq::encode(w, a);
        std::vector<uint8_t> bits(Xq::NUM_BITS);
        for (auto& b : bits) {
            b = static_cast<uint8_t>(rng() & 1);
        }
        const auto honest = Xq::quotients(enc, bits);
        // S_k - B_k, from the encoding's own definition.
        for (size_t t = 0; t < 2; ++t) {
            for (int dk = -1; dk <= 1; ++dk) {
                std::array<uint32_t, 3> k;
                for (size_t l = 0; l < 3; ++l) {
                    k[l] = static_cast<uint32_t>(
                        std::max<int64_t>(0, int64_t{honest[3 * t + l]} + (l == 1 ? dk : 0)));
                }
                // Product over data bits and quotients, compared with root: the proof's claim.
                Gf p = gf_one();
                for (size_t b = 0; b < Xq::NUM_BITS; ++b) {
                    if (bits[b] != 0) {
                        p = gf_mul(p, enc.coef[(t << Xq::D) + b] + gf_one());
                    }
                }
                for (size_t l = 0; l < 3; ++l) {
                    for (size_t s = 0; s < Xq::KAPPA; ++s) {
                        if (((k[l] >> s) & 1) != 0) {
                            p = gf_mul(p,
                                       enc.coef[(t << Xq::D) + Xq::NUM_BITS + Xq::KAPPA * l + s] +
                                           gf_one());
                        }
                    }
                }
                // Recompute the integer sums.
                bool holds = true;
                const auto& bv = Xq::bit_values();
                for (size_t l = 0; l < 3; ++l) {
                    const size_t chk = 3 * t + l;
                    int64_t s = 0;
                    for (size_t b = 0; b < Xq::NUM_BITS; ++b) {
                        if (bits[b] != 0) {
                            const auto [j, i] = bv[b];
                            s += int64_t{w[chk * 9 + j]} *
                                 (int64_t{1} << sc_test::Spec<9>::bit_shift(j, i)) % Q;
                        }
                    }
                    holds &= s == int64_t{enc.b[chk]} + int64_t{Q} * k[l];
                }
                EXPECT_EQ(gf_eq(p, enc.roots[t]), holds) << trial << " " << t << " " << dk;
            }
        }
    }
}

TYPED_TEST(SumcheckProof, HonestVerifies) {
    constexpr size_t NV = TypeParam::nv;
    using H = Harness<NV, TypeParam::prg>;
    for (uint64_t s = 0; s < 3; ++s) {
        const auto prefix = random_prefix<NV>(s);
        const auto truth = [&](std::span<const uint32_t> w) {
            return true_constants<NV>(prefix, w);
        };
        const auto proof = H::prove(prefix, truth, {}, static_cast<uint8_t>(s));
        EXPECT_TRUE(H::verify(proof, truth)) << s;
        // Another claim.
        EXPECT_FALSE(H::verify(proof, [&](std::span<const uint32_t> w) {
            auto a = truth(w);
            a[s % 6] = (a[s % 6] + 1) % Q;
            return a;
        }));
    }
}

// Every rejected deviation: a mutated data bit (the claim is then false), a wrong quotient, a
// wrong round message, and a false claim.
TYPED_TEST(SumcheckProof, RejectsCheating) {
#ifdef NDEBUG
    constexpr size_t NV = TypeParam::nv;
    using H = Harness<NV, TypeParam::prg>;
    using Xq = sc_test::X<NV>;
    const auto prefix = random_prefix<NV>(11);
    const auto truth = [&](std::span<const uint32_t> w) { return true_constants<NV>(prefix, w); };
    ASSERT_TRUE(H::verify(H::prove(prefix, truth), truth));

    // Mutated data bits, with the claims of the original values.
    for (const size_t b : {size_t{0}, Xq::NUM_BITS / 2, Xq::NUM_BITS - 1}) {
        auto bad = prefix;
        bad[b / 8] ^= static_cast<uint8_t>(1u << (b % 8));
        EXPECT_FALSE(H::verify(H::prove(bad, truth), truth)) << b;
    }

    // Wrong quotients, with the honest sumcheck for them.
    for (size_t k = 0; k < 6; ++k) {
        Cheat cheat;
        cheat.quotients = std::array<uint32_t, 6>{};
        // The honest ones, but one changed (computed inside via the same seed).
        bool done = false;
        H::prove(prefix, [&](std::span<const uint32_t> w) {
            const auto a = truth(w);
            if (!done) {
                std::vector<uint8_t> x(Xq::NUM_BITS);
                const auto& bv = Xq::bit_values();
                for (size_t b = 0; b < Xq::NUM_BITS; ++b) {
                    const size_t pb = Relation<NV, 0>::bit_of(bv[b].first, bv[b].second);
                    x[b] = (prefix[pb / 8] >> (pb % 8)) & 1;
                }
                *cheat.quotients = Xq::quotients(Xq::encode(w, a), x);
                done = true;
            }
            return a;
        });
        (*cheat.quotients)[k] ^= 1;
        EXPECT_FALSE(H::verify(H::prove(prefix, truth, cheat), truth)) << k;
    }

    // A wrong message: a flipped bit in the quotients, the first and last elements, and between.
    for (const size_t bit :
         {size_t{0}, 8 * Xq::Q_BYTES, 8 * Xq::Q_BYTES + 127, 8 * Xq::Q_BYTES + 128 * 5 + 3,
          8 * Xq::Q_BYTES + 128 * (Xq::Tree::NUM_ELEMS / 2) + 64, Xq::ANSWER_BITS - 1}) {
        Cheat cheat;
        cheat.flip_answer_bit = bit;
        EXPECT_FALSE(H::verify(H::prove(prefix, truth, cheat), truth)) << bit;
    }

    // A false claim, proven honestly for the prover's values.
    for (size_t k = 0; k < 6; ++k) {
        const auto wrong = [&](std::span<const uint32_t> w) {
            auto a = truth(w);
            a[k] = (a[k] + 1 + static_cast<uint32_t>(k)) % Q;
            return a;
        };
        EXPECT_FALSE(H::verify(H::prove(prefix, wrong), wrong)) << k;
        // The prover's encoding of the true claim, checked against the false one.
        EXPECT_FALSE(H::verify(H::prove(prefix, truth), wrong)) << k;
    }
#else
    GTEST_SKIP() << "the prover asserts its constraints in debug builds";
#endif
}

// The size formula of the design note.
TEST(SumcheckSize, Formula) {
    using Xq = sc_test::X<40>;
    constexpr size_t D = Xq::D;
    static_assert(Xq::Tree::NUM_ELEMS == D * (D + 1) + 2 * (D - 1));
    static_assert(Xq::ANSWER_BITS == 8 * ((6 * Xq::KAPPA + 7) / 8) + 128 * Xq::Tree::NUM_ELEMS);
    static_assert(Relation<40, 0>::NUM_CONSTRAINTS == D);
}
