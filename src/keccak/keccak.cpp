#include "vole_mole/keccak.hpp"

#include "keccak/tables.hpp"

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>

namespace vole_mole {

namespace {

template <typename Lane> constexpr Lane rotl(Lane v, unsigned r) {
    constexpr unsigned BITS = 8 * sizeof(Lane);
    return r ? static_cast<Lane>((v << r) | (v >> (BITS - r))) : v;
}

// One round of Keccak-p on lanes a[x + 5*y].
template <typename Spec, typename Lane> void keccak_round(std::array<Lane, 25>& a, Lane rc) {
    // theta
    Lane c[5], d[5];
    for (size_t x = 0; x < 5; ++x) {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    for (size_t x = 0; x < 5; ++x) {
        d[x] = c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
    }
    for (size_t i = 0; i < 25; ++i) {
        a[i] ^= d[i % 5];
    }

    // rho and pi: B[x][y] = rot(A[(x + 3y) % 5][x], rho[(x + 3y) % 5][x])
    std::array<Lane, 25> b;
    for (size_t x = 0; x < 5; ++x) {
        for (size_t y = 0; y < 5; ++y) {
            const size_t sx = (x + 3 * y) % 5, sy = x;
            b[x + 5 * y] = rotl(a[sx + 5 * sy], Spec::RHO[sx][sy]);
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

template <typename Spec, typename Lane>
void keccak_rounds(typename Spec::State& state, size_t first_round, size_t num_rounds) {
    static_assert(8 * sizeof(Lane) == Spec::W);
    assert(first_round + num_rounds <= Spec::ROUNDS);

    std::array<Lane, 25> lanes;
    for (size_t i = 0; i < 25; ++i) {
        Lane v = 0;
        for (size_t j = 0; j < sizeof(Lane); ++j) {
            v |= static_cast<Lane>(Lane{state[sizeof(Lane) * i + j]} << (8 * j));
        }
        lanes[i] = v;
    }

    for (size_t r = first_round; r < first_round + num_rounds; ++r) {
        keccak_round<Spec>(lanes, static_cast<Lane>(Spec::RC[r]));
    }

    for (size_t i = 0; i < 25; ++i) {
        for (size_t j = 0; j < sizeof(Lane); ++j) {
            state[sizeof(Lane) * i + j] = static_cast<uint8_t>(lanes[i] >> (8 * j));
        }
    }
}

} // namespace

void keccak_p800_rounds(Kp800State& state, size_t first_round, size_t num_rounds) {
    keccak_rounds<detail::Kp800, uint32_t>(state, first_round, num_rounds);
}

void keccak_f1600_rounds(Kf1600State& state, size_t first_round, size_t num_rounds) {
    keccak_rounds<detail::Kf1600, uint64_t>(state, first_round, num_rounds);
}

} // namespace vole_mole
