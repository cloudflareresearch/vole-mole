// SHA-256 as a binary circuit (see bin_ops.hpp).
//
// For each block, the circuit commits to the message schedule W_16, ..., W_63, to the two new state
// words A_t, E_t of each round, and to the output chaining value, and checks each of these as an
// integer sum modulo 2^32 of (GF(2)-linear) wires, by column compression. The nonlinear functions
// Ch and Maj aren't linear, but twice them is an integer combination of linear wires:
//
//   2 Maj(a, b, c) = a + b + c - (a ^ b ^ c),
//   2 Ch(e, f, g)  = 2 (e & f) + 2 (~e & g) = f + g + 1 - (e ^ f) - ~(e ^ g),
//
// so round t checks, modulo 2^33,
//
//   2 (d + h + S1(e) + K_t + W_t - E_t) + 2 Ch(e, f, g)  = 0,
//   2 (E_t - d + S0(a) - A_t)           + 2 Maj(a, b, c) = 0,
//
// whose wires are all linear. (E_t = d + T1 and A_t = T1 + T2 = E_t - d + T2.) Each sum has about
// 10 wires per column, reduced by counters: one of size 3 (degree 8) that commits 3 carries, or
// a few of size 2 (degree 4).

#ifndef VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP
#define VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP

#include "ecdsa_pok/bin_ops.hpp"
#include "sha256/sha256.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

// LOG is the size of the counters (see bin_ops.hpp).
template <typename Ops, size_t LOG> struct ShaCircuit {
    using W = Word<Ops>;
    using Wire = typename Ops::Wire;

    Ops& ops;

    W commit_word(uint32_t v) {
        W out;
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = ops.commit(((v >> i) & 1) != 0);
        }
        return out;
    }
    W x(const W& a, const W& b) const {
        if (a.is_const && b.is_const) {
            return W::constant(a.c ^ b.c);
        }
        if (a.is_const) {
            return x(b, a);
        }
        W out = a;
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = b.is_const ? (((b.c >> i) & 1) ? ops.flip(a.w[i]) : a.w[i])
                                  : ops.add(a.w[i], b.w[i]);
        }
        return out;
    }
    W n(const W& a) const { return x(a, W::constant(0xffffffff)); }
    W rotr(const W& a, unsigned k) const {
        if (a.is_const) {
            return W::constant(sha256::rotr(a.c, k));
        }
        W out = a;
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = a.w[(i + k) % 32];
        }
        return out;
    }
    W shr(const W& a, unsigned k) const {
        if (a.is_const) {
            return W::constant(a.c >> k);
        }
        W out = a;
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = i + k < 32 ? a.w[i + k] : ops.zero();
        }
        return out;
    }
    W s0(const W& a) const { return x(x(rotr(a, 2), rotr(a, 13)), rotr(a, 22)); }
    W s1(const W& a) const { return x(x(rotr(a, 6), rotr(a, 11)), rotr(a, 25)); }
    W ss0(const W& a) const { return x(x(rotr(a, 7), rotr(a, 18)), shr(a, 3)); }
    W ss1(const W& a) const { return x(x(rotr(a, 17), rotr(a, 19)), shr(a, 10)); }

    // One compression of the message block whose bit (8 j + i) is wire msg[8 j + i] (byte j, bit
    // i), from chaining value h. trace holds the values to commit (PlainOps), or is null.
    std::array<W, 8> compress(const std::array<W, 8>& h, std::span<const Wire, 512> msg,
                              const sha256::Trace* trace) {
        std::array<W, 64> w;
        for (size_t t = 0; t < 16; ++t) {
            for (size_t i = 0; i < 32; ++i) {
                w[t].w[i] = msg[8 * (4 * t + 3 - i / 8) + i % 8];
            }
        }
        for (size_t t = 16; t < 64; ++t) {
            w[t] = commit_word(trace ? trace->w[t] : 0);
            ColSum<Ops> sum(ops, 32);
            sum.add_word(ss1(w[t - 2]), 0);
            sum.add_word(w[t - 7], 0);
            sum.add_word(ss0(w[t - 15]), 0);
            sum.add_word(w[t - 16], 0);
            sum.sub_word(w[t], 0);
            sum.template assert_zero<LOG>();
        }

        // a[t + 4] = A_t, so a[0..4) = A_{-4}, ..., A_{-1} = h[3], h[2], h[1], h[0].
        std::array<W, 68> a, e;
        for (size_t i = 0; i < 4; ++i) {
            a[i] = h[3 - i];
            e[i] = h[7 - i];
        }
        for (size_t t = 0; t < 64; ++t) {
            const W &aa = a[t + 3], &b = a[t + 2], &c = a[t + 1], &d = a[t];
            const W &ee = e[t + 3], &f = e[t + 2], &g = e[t + 1], &hh = e[t];
            const W an = commit_word(trace ? trace->a[t] : 0);
            const W en = commit_word(trace ? trace->e[t] : 0);
            {
                ColSum<Ops> sum(ops, 33);
                sum.add_word(d, 1);
                sum.add_word(hh, 1);
                sum.add_word(s1(ee), 1);
                sum.add_word(w[t], 1);
                sum.add_const(sha256::K[t], 1);
                sum.sub_word(en, 1);
                sum.add_word(f, 0);
                sum.add_word(g, 0);
                sum.add_const(0xffffffff, 0);
                sum.sub_word(x(ee, f), 0);
                sum.sub_word(n(x(ee, g)), 0);
                sum.template assert_zero<LOG>();
            }
            {
                ColSum<Ops> sum(ops, 33);
                sum.add_word(en, 1);
                sum.sub_word(d, 1);
                sum.add_word(s0(aa), 1);
                sum.sub_word(an, 1);
                sum.add_word(aa, 0);
                sum.add_word(b, 0);
                sum.add_word(c, 0);
                sum.sub_word(x(x(aa, b), c), 0);
                sum.template assert_zero<LOG>();
            }
            a[t + 4] = an;
            e[t + 4] = en;
        }

        const std::array<const W*, 8> s = {&a[67], &a[66], &a[65], &a[64],
                                           &e[67], &e[66], &e[65], &e[64]};
        std::array<W, 8> out;
        for (size_t i = 0; i < 8; ++i) {
            out[i] = commit_word(trace ? trace->out[i] : 0);
            ColSum<Ops> sum(ops, 32);
            sum.add_word(h[i], 0);
            sum.add_word(*s[i], 0);
            sum.sub_word(out[i], 0);
            sum.template assert_zero<LOG>();
        }
        return out;
    }

    // Hash the padded message msg (512 wires per block, in witness order), returning the digest
    // words. traces holds the compression traces (PlainOps), or is null.
    std::array<W, 8> hash(std::span<const Wire> msg, const std::vector<sha256::Trace>* traces) {
        std::array<W, 8> h;
        for (size_t i = 0; i < 8; ++i) {
            h[i] = W::constant(sha256::IV[i]);
        }
        for (size_t b = 0; b < msg.size() / 512; ++b) {
            h = compress(h, std::span<const Wire, 512>(msg.subspan(512 * b, 512)),
                         traces ? &(*traces)[b] : nullptr);
        }
        return h;
    }
};

// The compression traces of the padded message.
inline std::vector<sha256::Trace> sha256_traces(std::span<const uint8_t> padded) {
    std::vector<sha256::Trace> out;
    sha256::State s = sha256::IV;
    for (size_t off = 0; off < padded.size(); off += 64) {
        sha256::Block b;
        std::copy_n(padded.begin() + static_cast<ptrdiff_t>(off), 64, b.begin());
        out.push_back(sha256::compress_trace(s, b));
        s = out.back().out;
    }
    return out;
}

} // namespace vole_mole::ecdsa_pok::detail

#endif
