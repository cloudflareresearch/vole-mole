#include "vole_mole/keccak.hpp"

#include "keccak/tables.hpp"

#include <cassert>

namespace vole_mole {

namespace {

constexpr uint32_t rotl32(uint32_t v, unsigned r) { return r ? (v << r) | (v >> (32 - r)) : v; }

// One round of Keccak-p[800] on lanes a[x + 5*y].
void round800(std::array<uint32_t, 25>& a, uint32_t rc) {
    using detail::KECCAK_RHO;

    // theta
    uint32_t c[5], d[5];
    for (size_t x = 0; x < 5; ++x) {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    for (size_t x = 0; x < 5; ++x) {
        d[x] = c[(x + 4) % 5] ^ rotl32(c[(x + 1) % 5], 1);
    }
    for (size_t i = 0; i < 25; ++i) {
        a[i] ^= d[i % 5];
    }

    // rho and pi: B[x][y] = rot(A[(x + 3y) % 5][x], rho[(x + 3y) % 5][x])
    std::array<uint32_t, 25> b;
    for (size_t x = 0; x < 5; ++x) {
        for (size_t y = 0; y < 5; ++y) {
            const size_t sx = (x + 3 * y) % 5, sy = x;
            b[x + 5 * y] = rotl32(a[sx + 5 * sy], KECCAK_RHO[sx][sy]);
        }
    }

    // chi
    for (size_t y = 0; y < 5; ++y) {
        for (size_t x = 0; x < 5; ++x) {
            a[x + 5 * y] = b[x + 5 * y] ^ (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
        }
    }

    // iota
    a[0] ^= rc;
}

} // namespace

void keccak_p800_rounds(Kp800State& state, size_t first_round, size_t num_rounds) {
    assert(first_round + num_rounds <= KP800_ROUNDS);

    std::array<uint32_t, 25> lanes;
    for (size_t i = 0; i < 25; ++i) {
        lanes[i] = uint32_t{state[4 * i]} | (uint32_t{state[4 * i + 1]} << 8) |
                   (uint32_t{state[4 * i + 2]} << 16) | (uint32_t{state[4 * i + 3]} << 24);
    }

    for (size_t r = first_round; r < first_round + num_rounds; ++r) {
        round800(lanes, detail::KP800_RC[r]);
    }

    for (size_t i = 0; i < 25; ++i) {
        for (size_t j = 0; j < 4; ++j) {
            state[4 * i + j] = static_cast<uint8_t>(lanes[i] >> (8 * j));
        }
    }
}

} // namespace vole_mole
