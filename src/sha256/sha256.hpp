// SHA-256 (FIPS 180-4).
//
// Besides the hash, this exposes the compression function and its intermediate values, which the
// ECDSA proof of knowledge commits to (see ecdsa_pok/sha256_circuit.hpp).

#ifndef VOLE_MOLE_SHA256_SHA256_HPP
#define VOLE_MOLE_SHA256_SHA256_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::sha256 {

using State = std::array<uint32_t, 8>;
using Block = std::array<uint8_t, 64>;
using Digest = std::array<uint8_t, 32>;

constexpr State IV = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};

constexpr std::array<uint32_t, 64> K = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
};

constexpr uint32_t rotr(uint32_t x, unsigned n) { return (x >> n) | (x << (32 - n)); }
constexpr uint32_t big_sigma0(uint32_t x) { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
constexpr uint32_t big_sigma1(uint32_t x) { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
constexpr uint32_t small_sigma0(uint32_t x) { return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3); }
constexpr uint32_t small_sigma1(uint32_t x) { return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10); }
constexpr uint32_t ch(uint32_t e, uint32_t f, uint32_t g) { return (e & f) ^ (~e & g); }
constexpr uint32_t maj(uint32_t a, uint32_t b, uint32_t c) { return (a & b) ^ (a & c) ^ (b & c); }

// The intermediate values of one compression: the message schedule W_0, ..., W_63, and the new
// words A_t, E_t computed by round t. The state before round t is
// (A_{t-1}, A_{t-2}, A_{t-3}, A_{t-4}, E_{t-1}, E_{t-2}, E_{t-3}, E_{t-4}), where A_{-1}, ...,
// A_{-4} and E_{-1}, ..., E_{-4} are the words of the input chaining value.
struct Trace {
    std::array<uint32_t, 64> w;
    std::array<uint32_t, 64> a;
    std::array<uint32_t, 64> e;
    State out; // the output chaining value
};

constexpr uint32_t load_be32(const uint8_t* p) {
    return (uint32_t{p[0]} << 24) | (uint32_t{p[1]} << 16) | (uint32_t{p[2]} << 8) | p[3];
}

inline Trace compress_trace(const State& h, const Block& block) {
    Trace tr{};
    for (size_t t = 0; t < 16; ++t) {
        tr.w[t] = load_be32(&block[4 * t]);
    }
    for (size_t t = 16; t < 64; ++t) {
        tr.w[t] = small_sigma1(tr.w[t - 2]) + tr.w[t - 7] + small_sigma0(tr.w[t - 15]) + tr.w[t - 16];
    }
    uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
    for (size_t t = 0; t < 64; ++t) {
        const uint32_t t1 = hh + big_sigma1(e) + ch(e, f, g) + K[t] + tr.w[t];
        const uint32_t t2 = big_sigma0(a) + maj(a, b, c);
        hh = g;
        g = f;
        f = e;
        e = d + t1;
        d = c;
        c = b;
        b = a;
        a = t1 + t2;
        tr.a[t] = a;
        tr.e[t] = e;
    }
    tr.out = {h[0] + a, h[1] + b, h[2] + c, h[3] + d, h[4] + e, h[5] + f, h[6] + g, h[7] + hh};
    return tr;
}

// The number of 64-byte blocks of a padded message of len bytes.
constexpr size_t num_blocks(size_t len) { return (len + 8) / 64 + 1; }

// The padded message.
inline std::vector<uint8_t> pad(std::span<const uint8_t> msg) {
    std::vector<uint8_t> out(64 * num_blocks(msg.size()), 0);
    std::copy(msg.begin(), msg.end(), out.begin());
    out[msg.size()] = 0x80;
    const uint64_t bits = uint64_t{msg.size()} * 8;
    for (size_t i = 0; i < 8; ++i) {
        out[out.size() - 1 - i] = static_cast<uint8_t>(bits >> (8 * i));
    }
    return out;
}

inline Digest digest_of(const State& s) {
    Digest out;
    for (size_t i = 0; i < 8; ++i) {
        for (size_t j = 0; j < 4; ++j) {
            out[4 * i + j] = static_cast<uint8_t>(s[i] >> (24 - 8 * j));
        }
    }
    return out;
}

inline Digest hash(std::span<const uint8_t> msg) {
    const auto padded = pad(msg);
    State s = IV;
    for (size_t off = 0; off < padded.size(); off += 64) {
        Block b;
        std::copy_n(padded.begin() + static_cast<ptrdiff_t>(off), 64, b.begin());
        s = compress_trace(s, b).out;
    }
    return digest_of(s);
}

} // namespace vole_mole::sha256

#endif
