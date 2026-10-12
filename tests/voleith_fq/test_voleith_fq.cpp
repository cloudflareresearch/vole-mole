#include "voleith_fq/field.hpp"   // internal
#include "voleith_fq/voleith.hpp" // internal

#include "test.hpp"

#include "hash.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

using namespace vole_mole::voleith_fq::detail;
using vole_mole::test::filled;

namespace {

// A deterministic stream of elements of F_q for tests.
struct TestRng {
    uint64_t state;
    Fq next() {
        state = state * 6364136223846793005u + 1442695040888963407u;
        return static_cast<Fq>((state >> 33) % Q);
    }
    Fq16 next16() {
        Fq16 out;
        for (auto& c : out.c) {
            c = next();
        }
        return out;
    }
};

Fq16 pow(Fq16 a, uint64_t e) {
    Fq16 out = Fq16::constant(1);
    while (e) {
        if (e & 1) {
            out *= a;
        }
        a *= a;
        e >>= 1;
    }
    return out;
}

} // namespace

TEST(Fq, Arithmetic) {
    EXPECT_EQ(fq_add(Q - 1, 1), 0);
    EXPECT_EQ(fq_sub(0, 1), Q - 1);
    EXPECT_EQ(fq_neg(0), 0);
    EXPECT_EQ(fq_mul(Q - 1, Q - 1), 1);
    EXPECT_EQ(fq_from_int(-1), Q - 1);
    EXPECT_EQ(fq_from_int(-3 * int32_t{Q} - 2), Q - 2);
    EXPECT_EQ(fq_centered(Q - 2), -2);
    EXPECT_EQ(fq_centered(Q / 2), int32_t{Q / 2});
    EXPECT_EQ(fq_centered(Q / 2 + 1), int32_t{Q / 2 + 1} - int32_t{Q});
}

TEST(Fq16, ReductionRule) {
    // X^15 * X = X^16 = 3.
    EXPECT_EQ(Fq16::monomial(15) * Fq16::monomial(1), Fq16::constant(3));
    TestRng rng{1};
    const Fq16 a = rng.next16();
    for (size_t k = 0; k < EXT_DEGREE; ++k) {
        EXPECT_EQ(a.mul_monomial(k), a * Fq16::monomial(k));
    }
}

TEST(Fq16, RingAxioms) {
    TestRng rng{2};
    for (int i = 0; i < 20; ++i) {
        const Fq16 a = rng.next16(), b = rng.next16(), c = rng.next16();
        EXPECT_EQ(a * b, b * a);
        EXPECT_EQ((a * b) * c, a * (b * c));
        EXPECT_EQ(a * (b + c), a * b + a * c);
        EXPECT_EQ((a - b) + b, a);
        const Fq s = rng.next();
        EXPECT_EQ(s * a, Fq16::constant(s) * a);
    }
}

// a^(q^16) = a, and a^(q^16 - 1) = 1 for a != 0, as in a field of q^16 elements.
TEST(Fq16, Frobenius) {
    TestRng rng{3};
    for (int i = 0; i < 4; ++i) {
        const Fq16 a = rng.next16();
        Fq16 b = a;
        for (size_t k = 0; k < EXT_DEGREE; ++k) {
            b = pow(b, Q); // Frobenius
            if (k + 1 < EXT_DEGREE) {
                // a is (with overwhelming probability) not in a proper subfield.
                EXPECT_NE(b, a) << k;
            }
        }
        EXPECT_EQ(b, a);
    }
}

TEST(Pack12, RoundTrip) {
    TestRng rng{4};
    std::vector<Fq> in(100);
    for (auto& x : in) {
        x = rng.next();
    }
    in[0] = Q - 1;
    in[1] = 0;
    std::vector<uint8_t> packed(packed12_bytes(in.size()));
    pack12(in, packed);
    std::vector<Fq> out(in.size());
    EXPECT_TRUE(unpack12(packed, out));
    EXPECT_EQ(in, out);

    // Non-canonical: q
    packed[0] = static_cast<uint8_t>(Q);
    packed[1] = static_cast<uint8_t>((packed[1] & 0xf0) | (Q >> 8));
    EXPECT_FALSE(unpack12(packed, out));
}

namespace {

// A toy relation: the witness is a vector of W elements in {-1, 0, 1} (or {0, 1} for degree 2),
// whose sum is the instance.
template <size_t W, size_t D> struct ToyRelation {
    static constexpr size_t WITNESS_LEN = W;
    static constexpr size_t DEGREE = D;
    static constexpr std::array<uint8_t, 3> DST_ARR = {'t', 'o', 'y'};
    static constexpr std::span<const uint8_t> DST = DST_ARR;

    struct instance {
        Fq sum;
    };

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update_byte(static_cast<uint8_t>(x.sum));
        h.update_byte(static_cast<uint8_t>(x.sum >> 8));
    }

    // Roots {0, 1} (degree 2) or {-1, 0, 1} (degree 3), padded to degree D.
    static constexpr std::array<Fq, D + 1> range_poly() {
        std::array<Fq, D + 1> f{};
        if constexpr (D == 2) {
            f[1] = Q - 1; // x^2 - x
            f[2] = 1;
        } else {
            f[1] = Q - 1; // x^3 - x
            f[3] = 1;
        }
        return f;
    }

    template <typename QS> static void constraints(QS& qs, const instance& x) {
        static constexpr auto F = range_poly();
        qs.constrain_roots(qs.witness(), std::span(F));

        auto sum = qs.apply_linear(qs.witness(), 1, [](std::span<const Fq> in, std::span<Fq> out) {
            Fq acc = 0;
            for (const Fq a : in) {
                acc = fq_add(acc, a);
            }
            out[0] = acc;
        });
        const std::array<Fq, 1> neg_sum = {fq_neg(x.sum)};
        qs.add_constant(sum, neg_sum);
        static constexpr std::array<Fq, D + 1> IDENTITY = [] {
            std::array<Fq, D + 1> f{};
            f[1] = 1; // f(x) = x, of degree < D
            return f;
        }();
        qs.constrain_roots(sum, std::span(IDENTITY));
    }
};

const ProveSeed RHO = filled<PROVE_SEED_BYTES>(0x42);

template <typename R> std::vector<Fq> toy_witness() {
    std::vector<Fq> w(R::WITNESS_LEN);
    for (size_t i = 0; i < w.size(); ++i) {
        w[i] = (i % 3 == 0) ? 1 : (R::DEGREE >= 3 && i % 5 == 0) ? Q - 1 : 0;
    }
    return w;
}

template <typename R> Fq sum_of(const std::vector<Fq>& w) {
    Fq acc = 0;
    for (const Fq a : w) {
        acc = fq_add(acc, a);
    }
    return acc;
}

template <typename R> std::vector<uint8_t> prove_toy(const std::vector<Fq>& w, Fq sum) {
    std::vector<uint8_t> proof(PROOF_BYTES<R>);
    prove<R>(std::span<uint8_t, PROOF_BYTES<R>>(proof), {sum},
             std::span<const Fq, R::WITNESS_LEN>(w), RHO);
    return proof;
}

template <typename R> bool verify_toy(const std::vector<uint8_t>& proof, Fq sum) {
    return verify<R>(std::span<const uint8_t, PROOF_BYTES<R>>(proof), {sum});
}

template <typename R> class ToyTest : public ::testing::Test {};
using ToyRelations = ::testing::Types<ToyRelation<64, 2>, ToyRelation<128, 3>, ToyRelation<32, 5>>;
TYPED_TEST_SUITE(ToyTest, ToyRelations);

} // namespace

TYPED_TEST(ToyTest, Verifies) {
    using R = TypeParam;
    const auto w = toy_witness<R>();
    const auto proof = prove_toy<R>(w, sum_of<R>(w));
    EXPECT_TRUE(verify_toy<R>(proof, sum_of<R>(w)));
    EXPECT_FALSE(verify_toy<R>(proof, fq_add(sum_of<R>(w), 1)));
}

TYPED_TEST(ToyTest, IsDeterministicInRho) {
    using R = TypeParam;
    const auto w = toy_witness<R>();
    EXPECT_EQ(prove_toy<R>(w, sum_of<R>(w)), prove_toy<R>(w, sum_of<R>(w)));
}

// A witness that violates the root constraints, or the linear constraint, doesn't verify.
TYPED_TEST(ToyTest, RejectsInvalidWitness) {
    using R = TypeParam;
    auto w = toy_witness<R>();
    w[1] = 2; // not a root
    EXPECT_FALSE(verify_toy<R>(prove_toy<R>(w, sum_of<R>(w)), sum_of<R>(w)));

    const auto w2 = toy_witness<R>();
    const Fq wrong_sum = fq_add(sum_of<R>(w2), 1);
    EXPECT_FALSE(verify_toy<R>(prove_toy<R>(w2, wrong_sum), wrong_sum));
}

TYPED_TEST(ToyTest, RejectsTampering) {
    using R = TypeParam;
    using Lay = Layout<R>;
    const auto w = toy_witness<R>();
    const Fq sum = sum_of<R>(w);
    const auto proof = prove_toy<R>(w, sum);
    const std::array<size_t, 9> offsets = {
        Lay::OFF_IV,     Lay::OFF_CORR, Lay::OFF_CORR + Lay::CORR_BYTES - 1,
        Lay::OFF_UTILDE, Lay::OFF_D,    Lay::OFF_QS,
        Lay::OFF_DELTA,  Lay::OFF_OPEN, Lay::PROOF_BYTES - 1,
    };
    for (const size_t off : offsets) {
        for (const uint8_t mask : {0x01, 0x80}) {
            auto bad = proof;
            bad[off] ^= mask;
            EXPECT_FALSE(verify_toy<R>(bad, sum)) << "offset " << off;
        }
    }
}
