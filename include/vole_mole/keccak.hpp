#ifndef VOLE_MOLE_KECCAK_HPP
#define VOLE_MOLE_KECCAK_HPP

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole {

// Keccak-p[800, 12] operates on a 100-byte state, or 25 "lanes" of 32 bits each.
constexpr size_t KP800_STATE_BYTES = 100;
constexpr size_t KP800_STATE_BITS = 8 * KP800_STATE_BYTES;
constexpr size_t KP800_ROUNDS = 12;

using Kp800State = std::array<uint8_t, KP800_STATE_BYTES>;

// Apply rounds [first_round, first_round + num_rounds) of Keccak-p[800, 12] to `state` in place,
// where round 0 is the first round of the permutation.
//
// Splitting the permutation up like this lets the prover compute the intermediate states that
// are committed to in the witness.
void keccak_p800_rounds(Kp800State& state, size_t first_round, size_t num_rounds);

// Apply Keccak-p[800, 12] to `state`.
inline Kp800State keccak_p800(Kp800State state) {
    keccak_p800_rounds(state, 0, KP800_ROUNDS);
    return state;
}

} // namespace vole_mole

#endif
