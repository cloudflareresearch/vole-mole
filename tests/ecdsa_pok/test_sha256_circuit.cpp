#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/binary.hpp"
#include "ecdsa_pok/sha256_circuit.hpp"
#include "sha256/sha256.hpp"

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
#include <type_traits>
#include <vector>

namespace {

using namespace vole_mole::ecdsa_pok::detail;
namespace sha256 = vole_mole::sha256;

struct Result {
    std::vector<uint8_t> witness;
    sha256::Digest digest;
    size_t bits, constraints, failed;
};

// Run the circuit in the clear on msg, and return the witness, the digest it computes, and counts.
template <size_t LOG> Result run_plain(const std::vector<uint8_t>& msg) {
    const auto padded = sha256::pad(msg);
    const auto traces = sha256_traces(padded);
    Result r;
    r.witness.assign(1 << 16, 0);
    PlainOps ops{r.witness};
    std::vector<uint8_t> wires;
    for (size_t i = 0; i < 8 * padded.size(); ++i) {
        wires.push_back(ops.commit(((padded[i / 8] >> (i % 8)) & 1) != 0));
    }
    ShaCircuit<PlainOps, LOG> c{ops};
    const auto h = c.hash(wires, &traces);
    sha256::State s;
    for (size_t i = 0; i < 8; ++i) {
        uint32_t v = 0;
        for (size_t b = 0; b < 32; ++b) {
            v |= uint32_t{h[i].w[b]} << b;
        }
        s[i] = v;
    }
    r.digest = sha256::digest_of(s);
    r.bits = ops.next;
    r.constraints = ops.constraints;
    r.failed = ops.failed;
    return r;
}

// Checks the circuit on a modified trace: flipping a committed value must make a check fail.
template <size_t LOG>
size_t failures_with_bad_trace(const std::vector<uint8_t>& msg, size_t which) {
    const auto padded = sha256::pad(msg);
    auto traces = sha256_traces(padded);
    switch (which % 4) {
    case 0:
        traces[0].w[20 + which % 40] ^= 1u << (which % 32);
        break;
    case 1:
        traces[0].a[which % 64] ^= 1u << (which % 32);
        break;
    case 2:
        traces[0].e[which % 64] ^= 1u << (which % 32);
        break;
    default:
        traces.back().out[which % 8] ^= 1u << (which % 32);
        break;
    }
    std::vector<uint8_t> witness(1 << 16, 0);
    PlainOps ops{witness};
    std::vector<uint8_t> wires;
    for (size_t i = 0; i < 8 * padded.size(); ++i) {
        wires.push_back(ops.commit(((padded[i / 8] >> (i % 8)) & 1) != 0));
    }
    ShaCircuit<PlainOps, LOG> c{ops};
    c.hash(wires, &traces);
    return ops.failed;
}

template <size_t LOG> size_t count_bits(size_t blocks, size_t* constraints) {
    CountOps ops;
    std::vector<CountOps::Wire> wires(512 * blocks);
    ShaCircuit<CountOps, LOG> c{ops};
    c.hash(wires, nullptr);
    *constraints = ops.constraints;
    return ops.next;
}

template <typename LogT> struct Sha256Circuit : ::testing::Test {};
using Logs = ::testing::Types<std::integral_constant<size_t, 2>, std::integral_constant<size_t, 3>>;
TYPED_TEST_SUITE(Sha256Circuit, Logs);

TYPED_TEST(Sha256Circuit, MatchesReference) {
    constexpr size_t LOG = TypeParam::value;
    std::mt19937 rng(7);
    for (const size_t len : {0, 3, 55, 56, 64, 100, 200}) {
        std::vector<uint8_t> msg(len);
        for (auto& b : msg) {
            b = static_cast<uint8_t>(rng());
        }
        const auto r = run_plain<LOG>(msg);
        EXPECT_EQ(r.failed, 0u) << len;
        EXPECT_EQ(r.digest, sha256::hash(msg)) << len;
        size_t constraints;
        const size_t bits = count_bits<LOG>(sha256::num_blocks(len), &constraints);
        EXPECT_EQ(bits + 8 * 64 * sha256::num_blocks(len), r.bits);
        EXPECT_EQ(constraints, r.constraints);
    }
}

TYPED_TEST(Sha256Circuit, DetectsBadTrace) {
    constexpr size_t LOG = TypeParam::value;
    const std::vector<uint8_t> msg(70, 0x61);
    for (size_t which = 0; which < 64; ++which) {
        EXPECT_GT(failures_with_bad_trace<LOG>(msg, which), 0u) << which;
    }
}

TYPED_TEST(Sha256Circuit, Counts) {
    constexpr size_t LOG = TypeParam::value;
    size_t c1, c2;
    const size_t b1 = count_bits<LOG>(1, &c1);
    const size_t b2 = count_bits<LOG>(2, &c2);
    std::printf("SHA-256 (counters of size %zu): first block %zu bits, %zu constraints; next "
                "blocks %zu bits, %zu constraints\n",
                LOG, b1, c1, b2 - b1, c2 - c1);
    EXPECT_EQ(b1, sha_first_block_bits(LOG));
    EXPECT_EQ(b2 - b1, sha_next_block_bits(LOG));
}

} // namespace
