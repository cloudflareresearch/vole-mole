// Helpers shared by the tests and benchmarks, e.g., for building and comparing byte strings, a
// fixed UOV key pair, and evaluating constraint systems in the clear.

#ifndef VOLE_MOLE_TEST_HPP
#define VOLE_MOLE_TEST_HPP

#include "vole_mole/uov.hpp"

#include "keccak/segmented.hpp" // internal: keccak::detail::QS_DEGREE

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace vole_mole::test {

// An array of N bytes start, start + 1, start + 2, ... (mod 256).
template <size_t N> std::array<uint8_t, N> filled(uint8_t start) {
    std::array<uint8_t, N> out;
    for (size_t i = 0; i < N; ++i) {
        out[i] = static_cast<uint8_t>(start + i);
    }
    return out;
}

// The secret key of the fixed test key pair.
inline const uov::SecretKeyBytes UOV_SK_BYTES = filled<uov::SECRET_KEY_BYTES>(0x60);

// An expanded UOV key pair.
struct UovKeyPair {
    uov::PublicKey pk;
    uov::SecretKey sk;

    // Members are initialized in declaration order, so pk is expanded from sk_ before it's moved.
    explicit UovKeyPair(uov::SecretKey sk_) : pk(sk_.public_key()), sk(std::move(sk_)) {}
};

// The fixed test key pair, expanded once.
inline const UovKeyPair& uov_key_pair() {
    static const UovKeyPair kp(uov::SecretKey{UOV_SK_BYTES});
    return kp;
}

// The i-th of a family of distinct public keys, which are also distinct from the fixed test key
// pair's. Each is generated and expanded on first use. (E.g., for building Anchor Sets, which can't
// contain the same key twice.)
inline const uov::PublicKey& distinct_uov_public_key(size_t i) {
    static std::deque<uov::PublicKey> keys; // references to elements remain valid as it grows
    while (keys.size() <= i) {
        uov::SecretKeyBytes sk_bytes = filled<uov::SECRET_KEY_BYTES>(0x80);
        sk_bytes[0] = static_cast<uint8_t>(keys.size());
        sk_bytes[1] = static_cast<uint8_t>(keys.size() >> 8);
        keys.emplace_back(uov::SecretKey(sk_bytes).public_key());
    }
    return keys[i];
}

inline std::optional<std::vector<uint8_t>> hex_decode(std::string_view hex) {
    if (hex.size() % 2 != 0) {
        return std::nullopt;
    }
    std::vector<uint8_t> out(hex.size() / 2);
    for (size_t i = 0; i < out.size(); ++i) {
        const char* first = hex.data() + 2 * i;
        unsigned value = 0;
        const auto [end, err] = std::from_chars(first, first + 2, value, 16);
        if (err != std::errc{} || end != first + 2) {
            return std::nullopt;
        }
        out[i] = static_cast<uint8_t>(value);
    }
    return out;
}

inline std::string to_hex(std::span<const uint8_t> bytes) {
    static constexpr char digits[] = "0123456789abcdef";
    std::string out;
    out.reserve(2 * bytes.size());
    for (const uint8_t b : bytes) {
        out.push_back(digits[b >> 4]);
        out.push_back(digits[b & 0xf]);
    }
    return out;
}

// Plaintext stand-in for faest::quicksilver_state: evaluates each constraint of a relation on a
// plaintext witness and records whether the constraint is violated (i.e., evaluates to a non-zero
// value). Values are elements of GF(2^128) (witness bits are embedded as 0 or 1), so this can
// evaluate any relation of degree at most `max_degree` that is built from the operations below.
struct PlainQS {
    static constexpr faest::secpar secpar_v = faest::secpar::s128;
    static constexpr size_t secpar_bits = 128;
    static constexpr size_t max_degree = keccak::detail::QS_DEGREE;
    static constexpr bool is_verifier = false;

    const uint8_t* witness;
    std::vector<bool> violated; // one entry per constraint

    faest::quicksilver_gf2<PlainQS, 1> get_witness_bit(size_t i) const;
    // The 8 bits starting at bit i, which must be a multiple of 8, as an element of GF(256).
    faest::quicksilver_gfsecpar<PlainQS, 1> load_witness_8_bits_and_combine(size_t i) const;

    template <typename T> void add_constraint(const T& x) {
        violated.push_back(!(x.v == faest::poly_secpar<secpar_v>::set_zero()));
    }
    template <typename T> void add_bit_constraint(const T& x) {
        add_constraint(x * (x + faest::poly1(1)));
    }
};

} // namespace vole_mole::test

// Plaintext stand-in for a QuickSilver bit of degree `deg`. It's always just a bit. As for
// quicksilver_gfsecpar below, the degree is only tracked by the type.
template <size_t deg> struct faest::quicksilver_gf2<vole_mole::test::PlainQS, deg> {
    using PlainQS = vole_mole::test::PlainQS;

    bool v = false;

    quicksilver_gf2() = default;
    explicit quicksilver_gf2(bool b) : v(b) {}
    quicksilver_gf2(faest::poly1 c, const PlainQS*) : v(c.data != 0) {}
    template <size_t deg2>
        requires(deg2 < deg)
    quicksilver_gf2(const quicksilver_gf2<PlainQS, deg2>& lower) : v(lower.v) {}

    quicksilver_gf2 operator+(const quicksilver_gf2& o) const { return quicksilver_gf2(v != o.v); }
    quicksilver_gf2 operator+(faest::poly1 c) const { return quicksilver_gf2(v != (c.data != 0)); }
};

// Plaintext stand-in for a QuickSilver value of degree `deg`. The degree is only tracked by the
// type, so that the same relation code compiles for PlainQS and for faest::quicksilver_state.
template <size_t deg> struct faest::quicksilver_gfsecpar<vole_mole::test::PlainQS, deg> {
    using PlainQS = vole_mole::test::PlainQS;
    using poly = faest::poly_secpar<PlainQS::secpar_v>;

    poly v = poly::set_zero();

    quicksilver_gfsecpar() = default;
    explicit quicksilver_gfsecpar(poly x) : v(x) {}
    quicksilver_gfsecpar(faest::poly1 c, const PlainQS*) : v(poly::from_1(c)) {}
    quicksilver_gfsecpar(poly c, const PlainQS*) : v(c) {}
    template <size_t deg2>
    quicksilver_gfsecpar(faest::poly1 c, const quicksilver_gfsecpar<PlainQS, deg2>&)
        : v(poly::from_1(c)) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly c, const quicksilver_gfsecpar<PlainQS, deg2>&) : v(c) {}
    template <size_t deg2>
        requires(deg2 < deg)
    quicksilver_gfsecpar(const quicksilver_gfsecpar<PlainQS, deg2>& lower) : v(lower.v) {}
    // Embed a bit, as faest-arch-opt does.
    template <size_t deg2>
        requires(deg2 <= deg)
    quicksilver_gfsecpar(const quicksilver_gf2<PlainQS, deg2>& bit)
        : v(poly::from_1(faest::poly1(bit.v))) {}

    quicksilver_gfsecpar operator+(const quicksilver_gfsecpar& o) const {
        return quicksilver_gfsecpar(v + o.v);
    }
    quicksilver_gfsecpar operator+(faest::poly1 c) const {
        return quicksilver_gfsecpar(v + poly::from_1(c));
    }
    template <typename T> quicksilver_gfsecpar& operator+=(const T& o) {
        *this = *this + o;
        return *this;
    }
};

namespace vole_mole::test {

// Found by argument-dependent lookup, and more specialized than faest-arch-opt's generic product,
// so it's preferred for PlainQS.
template <size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<PlainQS, deg_a + deg_b>
operator*(const faest::quicksilver_gfsecpar<PlainQS, deg_a>& a,
          const faest::quicksilver_gfsecpar<PlainQS, deg_b>& b) {
    return faest::quicksilver_gfsecpar<PlainQS, deg_a + deg_b>(
        (a.v * b.v).template reduce_to<PlainQS::secpar_bits>());
}

// As above, for products of bits.
template <size_t deg_a, size_t deg_b>
faest::quicksilver_gf2<PlainQS, deg_a + deg_b>
operator*(const faest::quicksilver_gf2<PlainQS, deg_a>& a,
          const faest::quicksilver_gf2<PlainQS, deg_b>& b) {
    return faest::quicksilver_gf2<PlainQS, deg_a + deg_b>(a.v && b.v);
}

} // namespace vole_mole::test

inline faest::quicksilver_gf2<vole_mole::test::PlainQS, 1>
vole_mole::test::PlainQS::get_witness_bit(size_t i) const {
    return faest::quicksilver_gf2<PlainQS, 1>(((witness[i / 8] >> (i % 8)) & 1) != 0);
}

inline faest::quicksilver_gfsecpar<vole_mole::test::PlainQS, 1>
vole_mole::test::PlainQS::load_witness_8_bits_and_combine(size_t i) const {
    return faest::quicksilver_gfsecpar<PlainQS, 1>(
        faest::poly_secpar<secpar_v>::from_8_byte(witness[i / 8]));
}

#endif
