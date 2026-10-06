#include "vole_mole/random.hpp"

extern "C" {
#include "randomness.h" // from faest-arch-opt
}

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>

namespace vole_mole {

void random_bytes(std::span<uint8_t> out) {
    // On Linux, rand_bytes() is getrandom(), which only guarantees to fill requests of up to 256
    // bytes in one call; larger ones may be cut short by a signal, which rand_bytes() reports as a
    // failure. So request at most that much at a time.
    constexpr size_t CHUNK_BYTES = 256;
    for (size_t off = 0; off < out.size(); off += CHUNK_BYTES) {
        const size_t len = std::min(CHUNK_BYTES, out.size() - off);
        if (rand_bytes(out.data() + off, len) != 0) {
            throw std::runtime_error("failed to get randomness from the operating system");
        }
    }
}

} // namespace vole_mole
