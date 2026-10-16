// Arithmetic modulo a 256-bit prime, for the two prime fields of NIST P-256: the base field F_p and
// the scalar field F_n.
//
// Elements are kept in Montgomery form (x R mod m for R = 2^256) as four 64-bit limbs, least
// significant first. Addition, subtraction, and multiplication are constant time; inversion uses
// Fermat's little theorem with a public exponent, so it's constant time, too. Decoding (from_bytes)
// and the comparisons are not meant to be constant time in their result, only in the data they
// process.

#ifndef VOLE_MOLE_P256_FIELD_HPP
#define VOLE_MOLE_P256_FIELD_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

namespace vole_mole::p256 {

using u64 = uint64_t;
using u128 = unsigned __int128;
using Limbs = std::array<u64, 4>; // little endian

namespace detail {

constexpr bool limbs_ge(const Limbs& a, const Limbs& b) {
    for (size_t i = 4; i-- > 0;) {
        if (a[i] != b[i]) {
            return a[i] > b[i];
        }
    }
    return true;
}

// a - b, returning the borrow.
constexpr u64 limbs_sub(Limbs& out, const Limbs& a, const Limbs& b) {
    u64 borrow = 0;
    for (size_t i = 0; i < 4; ++i) {
        const u128 d = u128{a[i]} - b[i] - borrow;
        out[i] = static_cast<u64>(d);
        borrow = static_cast<u64>(d >> 64) & 1;
    }
    return borrow;
}

// a + b, returning the carry.
constexpr u64 limbs_add(Limbs& out, const Limbs& a, const Limbs& b) {
    u64 carry = 0;
    for (size_t i = 0; i < 4; ++i) {
        const u128 s = u128{a[i]} + b[i] + carry;
        out[i] = static_cast<u64>(s);
        carry = static_cast<u64>(s >> 64);
    }
    return carry;
}

constexpr Limbs limbs_from_hex(const char (&hex)[65]) {
    Limbs out{};
    for (size_t i = 0; i < 64; ++i) {
        const char c = hex[i];
        const u64 v = c >= '0' && c <= '9'   ? static_cast<u64>(c - '0')
                      : c >= 'a' && c <= 'f' ? static_cast<u64>(c - 'a' + 10)
                                             : static_cast<u64>(c - 'A' + 10);
        const size_t bit = 4 * (63 - i);
        out[bit / 64] |= v << (bit % 64);
    }
    return out;
}

} // namespace detail

// The parameters of a field: the modulus M (odd, with 2^255 < M < 2^256).
template <typename Params> class Field {
  public:
    static constexpr Limbs M = Params::MODULUS;
    static_assert((M[0] & 1) == 1 && (M[3] >> 63) == 1);

  private:
    // -M^-1 mod 2^64, by Newton's iteration.
    static constexpr u64 compute_m_inv() {
        u64 x = 1;
        for (int i = 0; i < 7; ++i) {
            x *= 2 - M[0] * x;
        }
        return ~x + 1;
    }
    // R mod M = 2^256 - M (since M > 2^255).
    static constexpr Limbs compute_r() {
        Limbs out{};
        detail::limbs_sub(out, Limbs{0, 0, 0, 0}, M);
        return out;
    }
    // x + y mod M for canonical x, y.
    static constexpr Limbs add_mod(const Limbs& x, const Limbs& y) {
        Limbs s{};
        const u64 carry = detail::limbs_add(s, x, y);
        Limbs d{};
        const u64 borrow = detail::limbs_sub(d, s, M);
        // Subtract M if s >= M, i.e., if there's a carry or no borrow.
        return (carry != 0 || borrow == 0) ? d : s;
    }
    // R^2 mod M, by doubling R mod M 256 times.
    static constexpr Limbs compute_r2() {
        Limbs x = compute_r();
        for (int i = 0; i < 256; ++i) {
            x = add_mod(x, x);
        }
        return x;
    }

  public:
    static constexpr u64 M_INV = compute_m_inv();
    static constexpr Limbs R1 = compute_r();
    static constexpr Limbs R2 = compute_r2();
    static_assert(M[0] * (~M_INV + 1) == 1);

    constexpr Field() : v_{} {}

    static constexpr Field zero() { return Field(); }
    static constexpr Field one() { return from_mont(R1); }

    // The element of canonical value x < M.
    static constexpr Field from_canonical(const Limbs& x) { return from_mont(x).mul_raw(R2); }
    static constexpr Field from_u64(u64 x) { return from_canonical(Limbs{x, 0, 0, 0}); }

    // Decode 32 big-endian bytes. Returns nothing if the value isn't canonical.
    static std::optional<Field> from_bytes(std::span<const uint8_t, 32> b) {
        const Limbs x = limbs_from_be(b);
        if (detail::limbs_ge(x, M)) {
            return std::nullopt;
        }
        return from_canonical(x);
    }

    // The value of a big-endian integer of any length, modulo M.
    static Field reduce_be(std::span<const uint8_t> b) {
        const Field b256 = from_u64(256);
        Field acc;
        for (const uint8_t byte : b) {
            acc = acc * b256 + from_u64(byte);
        }
        return acc;
    }

    // Reduce 32 big-endian bytes modulo M (the value may exceed M).
    static Field reduce_32(std::span<const uint8_t, 32> b) {
        Limbs x = limbs_from_be(b);
        Limbs d{};
        if (detail::limbs_sub(d, x, M) == 0) {
            x = d; // x < 2 M, so one subtraction suffices
        }
        return from_canonical(x);
    }

    static Limbs limbs_from_be(std::span<const uint8_t, 32> b) {
        Limbs x{};
        for (size_t i = 0; i < 32; ++i) {
            x[(31 - i) / 8] |= u64{b[i]} << (8 * ((31 - i) % 8));
        }
        return x;
    }

    // The canonical value.
    constexpr Limbs canonical() const { return mul_raw(Limbs{1, 0, 0, 0}).v_; }

    std::array<uint8_t, 32> to_bytes() const {
        const Limbs x = canonical();
        std::array<uint8_t, 32> out;
        for (size_t i = 0; i < 32; ++i) {
            out[i] = static_cast<uint8_t>(x[(31 - i) / 8] >> (8 * ((31 - i) % 8)));
        }
        return out;
    }

    // Bit i of the canonical value.
    bool bit(size_t i) const { return ((canonical()[i / 64] >> (i % 64)) & 1) != 0; }

    constexpr Field operator+(const Field& o) const { return from_mont(add_mod(v_, o.v_)); }
    constexpr Field operator-(const Field& o) const {
        Limbs d{};
        const u64 borrow = detail::limbs_sub(d, v_, o.v_);
        Limbs masked{};
        const u64 mask = ~borrow + 1; // all ones if borrow
        for (size_t i = 0; i < 4; ++i) {
            masked[i] = M[i] & mask;
        }
        Limbs out{};
        detail::limbs_add(out, d, masked);
        return from_mont(out);
    }
    constexpr Field operator-() const { return Field() - *this; }
    constexpr Field operator*(const Field& o) const { return mul_raw(o.v_); }
    constexpr Field& operator+=(const Field& o) { return *this = *this + o; }
    constexpr Field& operator-=(const Field& o) { return *this = *this - o; }
    constexpr Field& operator*=(const Field& o) { return *this = *this * o; }

    constexpr Field square() const { return *this * *this; }

    // x^e for a public exponent e.
    constexpr Field pow(const Limbs& e) const {
        Field acc = one();
        for (size_t i = 256; i-- > 0;) {
            acc = acc.square();
            if ((e[i / 64] >> (i % 64)) & 1) {
                acc *= *this;
            }
        }
        return acc;
    }

    // x^-1 (0^-1 = 0).
    constexpr Field inv() const {
        Limbs e{};
        detail::limbs_sub(e, M, Limbs{2, 0, 0, 0});
        return pow(e);
    }

    constexpr bool is_zero() const {
        return (v_[0] | v_[1] | v_[2] | v_[3]) == 0; // Montgomery form of 0 is 0
    }
    constexpr bool operator==(const Field& o) const { return v_ == o.v_; }

    const Limbs& mont() const { return v_; }
    static constexpr Field from_mont(const Limbs& x) {
        Field f;
        f.v_ = x;
        return f;
    }

    // Sums of products with lazy reduction: acc += a b, for the Montgomery representations as
    // integers, and reduce_wide(acc) is the element whose representation is acc R^-1 mod M, i.e.,
    // the sum of the products a b. acc must stay below 2^520 (e.g., at most 256 products, or 128
    // products doubled).
    using Wide = std::array<u64, 9>;
    static constexpr void mul_add_wide(Wide& acc, const Field& a, const Field& b) {
        u64 p[8] = {};
        for (size_t i = 0; i < 4; ++i) {
            u64 carry = 0;
            for (size_t j = 0; j < 4; ++j) {
                const u128 s = u128{a.v_[i]} * b.v_[j] + p[i + j] + carry;
                p[i + j] = static_cast<u64>(s);
                carry = static_cast<u64>(s >> 64);
            }
            p[i + 4] = carry;
        }
        u64 c = 0;
        for (size_t i = 0; i < 8; ++i) {
            const u128 s = u128{acc[i]} + p[i] + c;
            acc[i] = static_cast<u64>(s);
            c = static_cast<u64>(s >> 64);
        }
        acc[8] += c;
    }
    // acc *= 2.
    static constexpr void double_wide(Wide& acc) {
        for (size_t i = 9; i-- > 1;) {
            acc[i] = (acc[i] << 1) | (acc[i - 1] >> 63);
        }
        acc[0] <<= 1;
    }
    static constexpr Field reduce_wide(const Wide& acc) {
        // acc = hi 2^512 + lo. Montgomery reduction of lo (REDC, 4 rounds): t = (lo + m M) / R,
        // with t < 2^512 / R + M < 3 M.
        u64 t[9] = {acc[0], acc[1], acc[2], acc[3], acc[4], acc[5], acc[6], acc[7], 0};
        for (size_t i = 0; i < 4; ++i) {
            const u64 m = t[i] * M_INV;
            u64 carry = 0;
            for (size_t j = 0; j < 4; ++j) {
                const u128 s = u128{m} * M[j] + t[i + j] + carry;
                t[i + j] = static_cast<u64>(s);
                carry = static_cast<u64>(s >> 64);
            }
            for (size_t j = i + 4; j < 9; ++j) {
                const u128 s = u128{t[j]} + carry;
                t[j] = static_cast<u64>(s);
                carry = static_cast<u64>(s >> 64);
            }
        }
        // r = t[4..9) < 3 M < 2^258; subtract M while r >= M (at most twice, in constant time).
        u64 r[5] = {t[4], t[5], t[6], t[7], t[8]};
        for (int k = 0; k < 2; ++k) {
            u64 d[5];
            u64 borrow = 0;
            for (size_t i = 0; i < 5; ++i) {
                const u64 mi = i < 4 ? M[i] : 0;
                const u128 s = u128{r[i]} - mi - borrow;
                d[i] = static_cast<u64>(s);
                borrow = static_cast<u64>(s >> 64) & 1;
            }
            const u64 mask = borrow - 1; // all ones if r >= M
            for (size_t i = 0; i < 5; ++i) {
                r[i] = (d[i] & mask) | (r[i] & ~mask);
            }
        }
        // hi 2^512 R^-1 = hi R is the representation of the element hi, i.e., hi (R mod M), which
        // is less than M since hi < 2^8 and R mod M < 2^248.
        static_assert(R1[3] < (u64{1} << 56));
        Limbs h{};
        u64 carry = 0;
        for (size_t i = 0; i < 4; ++i) {
            const u128 v = u128{R1[i]} * acc[8] + carry;
            h[i] = static_cast<u64>(v);
            carry = static_cast<u64>(v >> 64);
        }
        return from_mont(Limbs{r[0], r[1], r[2], r[3]}) + from_mont(h);
    }

  private:
    // Montgomery multiplication (CIOS): v_ o R^-1 mod M.
    constexpr Field mul_raw(const Limbs& o) const {
        u64 t[6] = {};
        for (size_t i = 0; i < 4; ++i) {
            u64 carry = 0;
            for (size_t j = 0; j < 4; ++j) {
                const u128 s = u128{v_[j]} * o[i] + t[j] + carry;
                t[j] = static_cast<u64>(s);
                carry = static_cast<u64>(s >> 64);
            }
            u128 s = u128{t[4]} + carry;
            t[4] = static_cast<u64>(s);
            t[5] = static_cast<u64>(s >> 64);

            const u64 m = t[0] * M_INV;
            s = u128{m} * M[0] + t[0];
            carry = static_cast<u64>(s >> 64);
            for (size_t j = 1; j < 4; ++j) {
                s = u128{m} * M[j] + t[j] + carry;
                t[j - 1] = static_cast<u64>(s);
                carry = static_cast<u64>(s >> 64);
            }
            s = u128{t[4]} + carry;
            t[3] = static_cast<u64>(s);
            t[4] = t[5] + static_cast<u64>(s >> 64);
        }
        Limbs r = {t[0], t[1], t[2], t[3]};
        Limbs d{};
        const u64 borrow = detail::limbs_sub(d, r, M);
        // Subtract M if t >= M, i.e., if t[4] is set or there's no borrow.
        const u64 take_d = static_cast<u64>((t[4] != 0) | (borrow == 0));
        const u64 mask = ~take_d + 1;
        Limbs out{};
        for (size_t i = 0; i < 4; ++i) {
            out[i] = (d[i] & mask) | (r[i] & ~mask);
        }
        return from_mont(out);
    }

    Limbs v_;
};

struct FpParams {
    static constexpr Limbs MODULUS =
        detail::limbs_from_hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
};
struct FnParams {
    static constexpr Limbs MODULUS =
        detail::limbs_from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
};

// The base field of P-256.
using Fp = Field<FpParams>;
// The scalar field of P-256: the group order n.
using Fn = Field<FnParams>;

// A 256-bit unsigned integer, e.g., a scalar, as 32 big-endian bytes.
using Bytes32 = std::array<uint8_t, 32>;

} // namespace vole_mole::p256

#endif
