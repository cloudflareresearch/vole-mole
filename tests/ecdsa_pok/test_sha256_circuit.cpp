#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/binary.hpp"
#include "ecdsa_pok/sha256_circuit.hpp"
#include "sha256/sha256.hpp"

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
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
Result run_plain(const std::vector<uint8_t>& msg) {
    const auto padded = sha256::pad(msg);
    Result r;
    r.witness.assign(1 << 16, 0);
    PlainOps ops{r.witness};
    std::vector<uint8_t> wires;
    for (size_t i = 0; i < 8 * padded.size(); ++i) {
        wires.push_back(ops.commit(((padded[i / 8] >> (i % 8)) & 1) != 0));
    }
    ShaCircuit<PlainOps> c{ops};
    const auto h = c.hash(wires);
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

// The failed constraints when the circuit is run on `witness` (as committed by run_plain).
size_t replay(std::vector<uint8_t> witness, size_t blocks) {
    PlainOps ops{witness};
    ops.replay = true;
    std::vector<uint8_t> wires;
    for (size_t i = 0; i < 512 * blocks; ++i) {
        wires.push_back(ops.commit(false));
    }
    ShaCircuit<PlainOps> c{ops};
    c.hash(wires);
    return ops.failed;
}

size_t count_bits(size_t blocks, size_t* constraints) {
    CountOps ops;
    std::vector<CountOps::Wire> wires(512 * blocks);
    ShaCircuit<CountOps> c{ops};
    c.hash(wires);
    *constraints = ops.constraints;
    return ops.next;
}

TEST(Sha256Circuit, MatchesReference) {
    std::mt19937 rng(7);
    for (const size_t len : {0, 3, 55, 56, 64, 100, 200}) {
        std::vector<uint8_t> msg(len);
        for (auto& b : msg) {
            b = static_cast<uint8_t>(rng());
        }
        const auto r = run_plain(msg);
        EXPECT_EQ(r.failed, 0u) << len;
        EXPECT_EQ(r.digest, sha256::hash(msg)) << len;
        size_t constraints;
        const size_t bits = count_bits(sha256::num_blocks(len), &constraints);
        EXPECT_EQ(bits + 8 * 64 * sha256::num_blocks(len), r.bits);
        EXPECT_EQ(constraints, r.constraints);
        EXPECT_EQ(replay(r.witness, sha256::num_blocks(len)), 0u) << len;
    }
}

// Flipping any committed bit (besides the message) makes a constraint fail.
TEST(Sha256Circuit, DetectsBadWitness) {
    const std::vector<uint8_t> msg(70, 0x61);
    const auto r = run_plain(msg);
    const size_t first = 8 * 64 * 2;
    for (size_t b = first; b < r.bits; ++b) {
        auto bad = r.witness;
        bad[b / 8] ^= static_cast<uint8_t>(1u << (b % 8));
        ASSERT_GT(replay(bad, 2), 0u) << b;
    }
}

TEST(Sha256Circuit, Counts) {
    size_t c1, c2;
    const size_t b1 = count_bits(1, &c1);
    const size_t b2 = count_bits(2, &c2);
    std::printf("SHA-256: first block %zu bits, %zu constraints; next blocks %zu bits, %zu "
                "constraints\n",
                b1, c1, b2 - b1, c2 - c1);
    EXPECT_EQ(b1, sha_first_block_bits());
    EXPECT_EQ(b2 - b1, sha_next_block_bits());
}

} // namespace
