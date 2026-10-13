// The challenges that link the binary proof to the proof over F_p and F_n (see relation.hpp).

#ifndef VOLE_MOLE_ECDSA_POK_LINK_HPP
#define VOLE_MOLE_ECDSA_POK_LINK_HPP

#include "p256/field.hpp"

#include "hash.hpp" // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

using Digest = std::array<uint8_t, 32>;

// Each weight c of a link between the binary proof and a prime field is the sum of LINK_TERMS
// distinct powers 2^j, j < 256. There are C(256, 31) > 2^132 such weights, and each residue
// modulo n (or p) is hit by at most two of them.
constexpr size_t LINK_TERMS = 31;
constexpr size_t LINK_POSITIONS = 256;

// The weights of the checks between F_p and F_n are 64-bit integers, with two checks.
constexpr size_t NUM_Y_CHECKS = 2;
constexpr size_t NUM_LIMBS = 4; // 64-bit limbs of a scalar

struct LinkChallenge {
    Digest digest;
    // Z_n = sum_{j in e_pos} 2^j e + sum_{j in xn_pos} 2^j X + rho_n (binary and F_n),
    // Z_p = sum_{j in xp_pos} 2^j X + rho_p (binary and F_p).
    std::array<uint16_t, LINK_TERMS> e_pos, xn_pos, xp_pos;
    // Y_i = sum_l gamma[i][l] limb_l(u1) + gamma[i][4 + l] limb_l(u2) + sigma_i (F_p and F_n).
    std::array<std::array<uint64_t, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma;

    // The weight sum_{j in pos} 2^j in a field.
    template <typename F> static F weight(std::span<const uint16_t, LINK_TERMS> pos) {
        F out = F::zero();
        for (const uint16_t j : pos) {
            p256::Limbs l{};
            l[j / 64] = uint64_t{1} << (j % 64);
            out += F::from_canonical(l);
        }
        return out;
    }
};

inline LinkChallenge derive_link_challenge(const Digest& digest) {
    LinkChallenge out;
    out.digest = digest;
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(digest);
    Keccak_HashFinal(&h.ctx, nullptr);
    auto positions = [&](std::array<uint16_t, LINK_TERMS>& pos) {
        std::array<bool, LINK_POSITIONS> used{};
        for (size_t n = 0; n < LINK_TERMS;) {
            uint8_t b;
            Keccak_HashSqueeze(&h.ctx, &b, 8);
            if (!used[b]) {
                used[b] = true;
                pos[n++] = b;
            }
        }
        std::ranges::sort(pos);
    };
    positions(out.e_pos);
    positions(out.xn_pos);
    positions(out.xp_pos);
    for (auto& g : out.gamma) {
        for (auto& x : g) {
            std::array<uint8_t, 8> b;
            Keccak_HashSqueeze(&h.ctx, b.data(), 64);
            x = 0;
            for (size_t i = 0; i < 8; ++i) {
                x |= uint64_t{b[i]} << (8 * i);
            }
        }
    }
    return out;
}

// Little-endian bit vectors of integers.
inline bool get_bit(std::span<const uint8_t> b, size_t i) { return ((b[i / 8] >> (i % 8)) & 1) != 0; }
inline void set_bit(std::span<uint8_t> b, size_t i, bool v) {
    b[i / 8] = static_cast<uint8_t>((b[i / 8] & ~(1u << (i % 8))) | (unsigned{v} << (i % 8)));
}

// The value modulo F's modulus of a little-endian integer.
template <typename F> F reduce_le(std::span<const uint8_t> b) {
    const F b256 = F::from_u64(256);
    F acc = F::zero();
    for (size_t i = b.size(); i-- > 0;) {
        acc = acc * b256 + F::from_u64(b[i]);
    }
    return acc;
}

} // namespace vole_mole::ecdsa_pok::detail

#endif
