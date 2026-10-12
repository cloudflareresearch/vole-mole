// Range checks x <= MAX on integers given by committed bits, in binary VOLEitH.

#ifndef VOLE_MOLE_MODQ_RANGE_LE_HPP
#define VOLE_MOLE_MODQ_RANGE_LE_HPP

#include "qs_bit.hpp"

#include <bit>
#include <cstddef>
#include <cstdint>

namespace vole_mole::modq::detail {

// x <= MAX for an integer x of BITS committed bits (whose top bit is set in MAX): for each bit i
// that's 0 in MAX, x_i prod_{j > i, MAX_j = 1} x_j = 0. (If x > MAX, then this fails at the
// highest bit where they differ; if x <= MAX, then each product is 0, since otherwise x > MAX.) If
// CUT < BITS, a committed helper bit t = prod_{j >= CUT, MAX_j = 1} x_j replaces those factors, to
// lower the degree.
template <uint32_t MAX, size_t BITS, size_t CUT> struct RangeLe {
    static_assert(BITS < 32 && (MAX >> BITS) == 0 && ((MAX >> (BITS - 1)) & 1) != 0);
    static_assert(CUT <= BITS);
    static constexpr size_t NUM_BITS = BITS;
    static constexpr size_t CUT_BIT = CUT;
    static constexpr bool HELPER = CUT < BITS;
    static constexpr size_t NUM_ZEROS = BITS - static_cast<size_t>(std::popcount(MAX));
    static constexpr size_t NUM_CONSTRAINTS = NUM_ZEROS + (HELPER ? 1 : 0);

    // Whether bit i or a lower one is 0 in MAX.
    static constexpr bool zero_at_or_below(ptrdiff_t i) {
        const uint32_t mask = (uint32_t{2} << i) - 1;
        return (MAX & mask) != mask;
    }

    // The helper bit, for bits bit(i) (a bool).
    template <typename Bit> static bool helper(Bit&& bit) {
        bool t = true;
        for (size_t j = CUT; j < BITS; ++j) {
            if ((MAX >> j) & 1) {
                t = t && bit(j);
            }
        }
        return t;
    }

    template <typename QS, size_t deg>
    static void zero(QS* qs, const vole_mole::detail::qs_bit<QS, deg>& x) {
        qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(x));
    }

    // The constraints, for committed bits bit(i) and helper bit helper_bit() (if HELPER).
    template <typename QS, typename Bit, typename HelperBit>
    static void constraints(QS* qs, Bit&& bit, HelperBit&& helper_bit) {
        rec<QS, static_cast<ptrdiff_t>(BITS) - 2, 1, false>(qs, bit, helper_bit, bit(BITS - 1));
    }

  private:
    // prefix = prod_{j > I, MAX_j = 1} x_j (or the helper bit and the factors below CUT).
    template <typename QS, ptrdiff_t I, size_t D, bool CUT_DONE, typename Bit, typename HelperBit>
    static void rec(QS* qs, Bit& bit, HelperBit& helper_bit,
                    const vole_mole::detail::qs_bit<QS, D>& prefix) {
        using vole_mole::detail::qs_bit;
        if constexpr (I < 0) {
            return;
        } else if constexpr (HELPER && !CUT_DONE && I + 1 == static_cast<ptrdiff_t>(CUT)) {
            const qs_bit<QS, 1> t = helper_bit();
            if constexpr (D == 1) {
                zero(qs, t + prefix);
            } else {
                zero(qs, qs_bit<QS, D>(t) + prefix);
            }
            rec<QS, I, 1, true>(qs, bit, helper_bit, t);
        } else if constexpr (!zero_at_or_below(I)) {
            return;
        } else {
            const qs_bit<QS, 1> xi = bit(static_cast<size_t>(I));
            if constexpr (((MAX >> I) & 1) != 0) {
                rec<QS, I - 1, D + 1, CUT_DONE>(qs, bit, helper_bit,
                                                vole_mole::detail::qs_mul(prefix, xi));
            } else {
                zero(qs, vole_mole::detail::qs_mul(prefix, xi));
                rec<QS, I - 1, D, CUT_DONE>(qs, bit, helper_bit, prefix);
            }
        }
    }
};

} // namespace vole_mole::modq::detail

#endif
