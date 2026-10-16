// SHA-256 as a binary circuit (see bin_ops.hpp).
//
// Every 32-bit word the circuit computes is a GF(2)-linear combination of committed bits (or a
// public constant), so the linear functions (the rotations, shifts, XORs and Sigmas) are free. Each
// addition modulo 2^32 is a ripple-carry addition:
//
//   - x + y, where x and y are linear: commit the carries c_1, ..., c_31 (c_0 = 0), constrained by
//     c_{i+1} = maj(x_i, y_i, c_i) (degree 2); the sum s_i = x_i + y_i + c_i is linear. If y is a
//     constant, the carries are known (and not committed) up to y's lowest set bit.
//   - x + y, where y = u + v w bitwise for linear u, v, w (y = Ch(e, f, g) = g + e (f + g), or
//     y = Maj(a, b, c) = b + (a + b)(b + c)): commit the sum s instead, so that s is linear. Then
//     the carries c_i = x_i + y_i + s_i are of degree 2, and c_{i+1} = maj(x_i, y_i, c_i) becomes
//     the constraint
//
//       c_{i+1} = x_i y_i + (x_i + y_i) c_i = y_i (x_i + s_i) + x_i + y_i + x_i s_i,
//
//     of degree 3.
//
// So a round, T1 = h + S1(e) + W_t + K_t + Ch(e, f, g), E = d + T1, and A = T1 + S0(a) + Maj(a, b,
// c), costs five additions of linear words and two with Ch and Maj, about 218 committed bits,
// and the message schedule costs three additions per word.

#ifndef VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP
#define VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP

#include "ecdsa_pok/bin_ops.hpp"
#include "sha256/sha256.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <span>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

// Words are 32 wires (for QsOps, about 1 KB), so the circuit writes its results into words
// provided by the caller, and reuses them, rather than returning temporaries.
template <typename Ops> struct ShaCircuit {
    using W = Word<Ops>;
    using Wire = typename Ops::Wire;

    Ops& ops;

    Wire bit(const W& a, size_t i) const {
        if (a.is_const) {
            return ((a.c >> i) & 1) != 0 ? ops.one() : ops.zero();
        }
        return a.w[i];
    }
    // a's value (PlainOps; 0 otherwise).
    uint32_t value(const W& a) const {
        if (a.is_const) {
            return a.c;
        }
        uint32_t v = 0;
        for (size_t i = 0; i < 32; ++i) {
            v |= uint32_t{ops.value(a.w[i])} << i;
        }
        return v;
    }
    static void set_const(W& out, uint32_t v) {
        out.is_const = true;
        out.c = v;
    }
    // out = a + b (XOR); out may be a or b.
    void x(W& out, const W& a, const W& b) const {
        if (a.is_const && b.is_const) {
            set_const(out, a.c ^ b.c);
            return;
        }
        if (a.is_const) {
            x(out, b, a);
            return;
        }
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = b.is_const ? (((b.c >> i) & 1) ? ops.flip(a.w[i]) : a.w[i])
                                  : ops.add(a.w[i], b.w[i]);
        }
        out.is_const = false;
    }
    // out = rotr(a, r1) + rotr(a, r2) + (rotr(a, r3) or, if shift, a >> r3); out isn't a.
    void sigma(W& out, const W& a, unsigned r1, unsigned r2, unsigned r3, bool shift) const {
        if (a.is_const) {
            set_const(out, sha256::rotr(a.c, r1) ^ sha256::rotr(a.c, r2) ^
                               (shift ? a.c >> r3 : sha256::rotr(a.c, r3)));
            return;
        }
        for (size_t i = 0; i < 32; ++i) {
            const Wire t = ops.add(a.w[(i + r1) % 32], a.w[(i + r2) % 32]);
            out.w[i] = !shift || i + r3 < 32 ? ops.add(t, a.w[(i + r3) % 32]) : t;
        }
        out.is_const = false;
    }
    void s0(W& out, const W& a) const { sigma(out, a, 2, 13, 22, false); }
    void s1(W& out, const W& a) const { sigma(out, a, 6, 11, 25, false); }
    void ss0(W& out, const W& a) const { sigma(out, a, 7, 18, 3, true); }
    void ss1(W& out, const W& a) const { sigma(out, a, 17, 19, 10, true); }

    // out = x + y modulo 2^32, for linear (or constant) x and y; out may be x or y.
    void add(W& out, const W& a, const W& b) {
        if (a.is_const && b.is_const) {
            set_const(out, a.c + b.c);
            return;
        }
        const W& xx = a.is_const ? b : a;
        const W& y = a.is_const ? a : b; // the constant, if any
        const bool y_const = y.is_const;
        const uint32_t yc = y.c;
        Wire c = ops.zero();
        bool c_zero = true; // c is known to be 0
        bool cv = false;    // c's value (PlainOps)
        for (size_t i = 0; i < 32; ++i) {
            // Read bit i of x and y before writing bit i of out.
            const Wire xi = xx.w[i];
            const Wire yi = y_const ? (((yc >> i) & 1) != 0 ? ops.one() : ops.zero()) : y.w[i];
            out.w[i] = c_zero ? ops.add(xi, yi) : ops.add(ops.add(xi, yi), c);
            if (i == 31) {
                break;
            }
            if (c_zero && y_const) {
                // c_{i+1} = x_i y_i is 0 or x_i.
                if (((yc >> i) & 1) != 0) {
                    c = xi;
                    cv = ops.value(c);
                    c_zero = false;
                }
                continue;
            }
            const bool xv = ops.value(xi), yv = ops.value(yi);
            cv = (xv && yv) || (cv && (xv != yv));
            const Wire cn = ops.commit(cv);
            ops.assert_maj(xi, yi, c, cn);
            c = cn;
            c_zero = false;
        }
        out.is_const = false;
    }
    // out = the sum of the terms and the constant k; out may be any of the terms.
    void add(W& out, std::initializer_list<const W*> terms, uint32_t k = 0) {
        std::array<const W*, 4> nc{};
        size_t n = 0;
        for (const W* t : terms) {
            if (t->is_const) {
                k += t->c;
            } else {
                nc.at(n++) = t;
            }
        }
        if (n == 0) {
            set_const(out, k);
            return;
        }
        // Add the terms in order (so that the committed carries don't depend on aliasing).
        if (n == 1) {
            if (&out != nc[0]) {
                out = *nc[0];
            }
        } else {
            add(out, *nc[0], *nc[1]);
            for (size_t j = 2; j < n; ++j) {
                add(out, out, *nc[j]);
            }
        }
        if (k != 0) {
            konst_.c = k;
            add(out, out, konst_);
        }
    }

    // out = x + (u + v w) modulo 2^32 (bitwise products), for linear (or constant) x, u, v, w;
    // out isn't any of them.
    void add_quad(W& out, const W& xw, const W& u, const W& v, const W& w) {
        if (v.is_const || w.is_const) {
            const W& lin = v.is_const ? w : v;
            const uint32_t k = v.is_const ? v.c : w.c;
            for (size_t i = 0; i < 32; ++i) {
                out.w[i] = ((k >> i) & 1) != 0 ? lin.w[i] : ops.zero();
            }
            out.is_const = false;
            if (lin.is_const) {
                set_const(out, lin.c & k);
            }
            x(out, u, out);
            add(out, xw, out);
            return;
        }
        const uint32_t sv = value(xw) + (value(u) ^ (value(v) & value(w)));
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = ops.commit(((sv >> i) & 1) != 0);
        }
        out.is_const = false;
        // l_i = x_i + u_i + s_i, so that c_i = l_i + v_i w_i.
        std::array<Wire, 32> l;
        for (size_t i = 0; i < 32; ++i) {
            l[i] = ops.add(ops.add(bit(xw, i), bit(u, i)), out.w[i]);
        }
        ops.assert_quad(l[0], v.w[0], w.w[0]); // c_0 = 0
        for (size_t i = 0; i < 31; ++i) {
            ops.assert_quad_carry(ops.add(ops.add(l[i + 1], bit(xw, i)), bit(u, i)), v.w[i + 1],
                                  w.w[i + 1], v.w[i], w.w[i], bit(u, i), bit(xw, i), out.w[i]);
        }
    }

    // One compression of the message block whose bit (8 j + i) is wire msg[8 j + i] (byte j, bit
    // i), from chaining value h, into h.
    void compress(std::array<W, 8>& h, std::span<const Wire, 512> msg) {
        std::array<W, 64> w;
        for (size_t t = 0; t < 16; ++t) {
            for (size_t i = 0; i < 32; ++i) {
                w[t].w[i] = msg[8 * (4 * t + 3 - i / 8) + i % 8];
            }
        }
        W t0, t1, t2, t3;
        for (size_t t = 16; t < 64; ++t) {
            ss1(t0, w[t - 2]);
            ss0(t1, w[t - 15]);
            add(w[t], {&t0, &w[t - 7], &t1, &w[t - 16]});
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
            // Ch(e, f, g) = g + e (f + g), Maj(a, b, c) = b + (a + b)(b + c).
            // T1 = (h + S1(e) + W_t + K_t) + Ch(e, f, g), in t1.
            s1(t0, ee);
            add(t0, {&hh, &t0, &w[t]}, sha256::K[t]);
            x(t2, f, g);
            add_quad(t1, t0, g, ee, t2);
            add(e[t + 4], d, t1);
            // A = (T1 + S0(a)) + Maj(a, b, c).
            s0(t0, aa);
            add(t0, t1, t0);
            x(t2, aa, b);
            x(t3, b, c);
            add_quad(a[t + 4], t0, b, t2, t3);
        }

        const std::array<const W*, 8> s = {&a[67], &a[66], &a[65], &a[64],
                                           &e[67], &e[66], &e[65], &e[64]};
        for (size_t i = 0; i < 8; ++i) {
            add(h[i], h[i], *s[i]);
        }
    }

    // Hash the padded message msg (512 wires per block, in witness order), returning the digest
    // words.
    std::array<W, 8> hash(std::span<const Wire> msg) {
        std::array<W, 8> h;
        for (size_t i = 0; i < 8; ++i) {
            set_const(h[i], sha256::IV[i]);
        }
        for (size_t b = 0; b < msg.size() / 512; ++b) {
            compress(h, std::span<const Wire, 512>(msg.subspan(512 * b, 512)));
        }
        return h;
    }

    W konst_ = W::constant(0); // scratch for constant addends (public, for aggregate init)
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
