// Tests for randomness from the operating system.

#include "vole_mole/random.hpp"

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

using namespace vole_mole;
using vole_mole::test::to_hex;

TEST(Random, Distinct) {
    const std::array<uint8_t, 32> a = random_bytes<32>();
    const std::array<uint8_t, 32> b = random_bytes<32>();
    EXPECT_NE(to_hex(a), to_hex(b));
}

TEST(Random, Empty) {
    EXPECT_NO_THROW(random_bytes(std::span<uint8_t>{}));
    EXPECT_NO_THROW((void)random_bytes<0>());
}

// Long outputs are requested in chunks. Check that every chunk is filled, including a partial last
// one. (A chunk of random bytes is all zero with negligible probability.)
TEST(Random, FillsLongOutputs) {
    constexpr size_t CHUNK_BYTES = 256; // see random_bytes()
    std::vector<uint8_t> out(3 * CHUNK_BYTES + 100, 0);
    random_bytes(out);
    for (size_t off = 0; off < out.size(); off += CHUNK_BYTES) {
        const auto chunk = std::span(out).subspan(off, std::min(CHUNK_BYTES, out.size() - off));
        EXPECT_TRUE(std::ranges::any_of(chunk, [](uint8_t b) { return b != 0; }))
            << "chunk at offset " << off << " is all zero";
    }
}
