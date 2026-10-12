// Constant-time helpers.

#ifndef VOLE_MOLE_CT_HPP
#define VOLE_MOLE_CT_HPP

#include <cstdint>

namespace vole_mole::detail {

// Return x, hiding its value from the optimizer.
inline uint64_t value_barrier(uint64_t x) {
    __asm__("" : "+r"(x));
    return x;
}

// All ones if x == 0, otherwise zero.
inline uint64_t ct_is_zero_mask(uint64_t x) {
    x = value_barrier(x);
    return ((x | (0 - x)) >> 63) - 1;
}

// All ones if a == b, otherwise zero.
inline uint64_t ct_eq_mask(uint64_t a, uint64_t b) { return ct_is_zero_mask(a ^ b); }

} // namespace vole_mole::detail

#endif
