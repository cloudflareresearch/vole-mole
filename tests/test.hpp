// Helpers shared by the tests and benchmarks, e.g., for building and comparing byte strings, a
// fixed UOV key pair, and evaluating constraint systems in the clear.

#ifndef VOLE_MOLE_TEST_HPP
#define VOLE_MOLE_TEST_HPP

#include "vole_mole/uov.hpp"

#include "moussaka/issue.hpp" // internal: ISSUE_QS_DEGREE

#include "quicksilver.hpp" // from faest-arch-opt

#include <array>
#include <charconv>
#include <cstddef>
#include <cstdint>
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
// value). Constraints are over GF(2) and have degree at most `ISSUE_QS_DEGREE`.
struct PlainQS {
    static constexpr size_t max_degree = moussaka::detail::ISSUE_QS_DEGREE;

    const uint8_t* witness;
    std::vector<bool> violated; // one entry per constraint

    faest::quicksilver_gfsecpar<PlainQS, 1> get_witness_bit(size_t i) const;

    template <typename T> void add_constraint(const T& x) { violated.push_back(x.v); }
    template <typename T> void add_bit_constraint(const T&) {
        // Asserts that a witness value is 0 or 1. Plaintext witness values are always bits, so this
        // always holds. (So these tests can't check that the bit constraints are present, except
        // through the total number of constraints.)
        violated.push_back(false);
    }
};

} // namespace vole_mole::test

// Plaintext stand-in for a QuickSilver value of degree `deg`. It's always just a bit.
template <size_t deg> struct faest::quicksilver_gfsecpar<vole_mole::test::PlainQS, deg> {
    using PlainQS = vole_mole::test::PlainQS;

    bool v;

    explicit quicksilver_gfsecpar(bool b) : v(b) {}
    quicksilver_gfsecpar(faest::poly1 c, const PlainQS*) : v(c.data != 0) {}
    template <size_t deg2>
        requires(deg2 < deg)
    quicksilver_gfsecpar(const quicksilver_gfsecpar<PlainQS, deg2>& lower) : v(lower.v) {}

    quicksilver_gfsecpar operator+(const quicksilver_gfsecpar& o) const {
        return quicksilver_gfsecpar(v != o.v);
    }
    quicksilver_gfsecpar operator+(faest::poly1 c) const {
        return quicksilver_gfsecpar(v != (c.data != 0));
    }
    quicksilver_gfsecpar<PlainQS, 2 * deg> operator*(const quicksilver_gfsecpar& o) const {
        return quicksilver_gfsecpar<PlainQS, 2 * deg>(v && o.v);
    }
};

inline faest::quicksilver_gfsecpar<vole_mole::test::PlainQS, 1>
vole_mole::test::PlainQS::get_witness_bit(size_t i) const {
    return faest::quicksilver_gfsecpar<PlainQS, 1>(((witness[i / 8] >> (i % 8)) & 1) != 0);
}

#endif
