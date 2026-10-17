// SHA-256 as a binary circuit (see bin_ops.hpp).
//
// Every 32-bit word the circuit keeps is a GF(2)-linear combination of committed bits (or a public
// constant), so the linear functions (the rotations, shifts, XORs and Sigmas) are free. Each
// addition modulo 2^32 is a ripple-carry addition, with constraints of degree at most 4 (the degree
// of the binary proof's counters with a derived witness):
//
//   - x + y, where x and y are linear: commit the carries c_1, ..., c_31 (c_0 = 0), constrained by
//     c_(i+1) = maj(x_i, y_i, c_i) (degree 2); the sum s_i = x_i + y_i + c_i is linear. If y is a
//     constant, the carries are known (and not committed) up to y's lowest set bit.
//   - half<D>: the same, but committing only every D-th carry (D = 2 or 3). The carries in between
//     are expressions of degree up to D, and so are the bits of the sum, which isn't kept: it's an
//     operand of a full addition. The constraint of a committed carry has degree D + 1.
//   - full: t + c, where bit i of t (or c) has degree k_i: commit the sum s, so that it's linear
//     (s_0 = t_0 + c_0 needn't be). Then the carries d_i = t_i + c_i + s_i are expressions, and
//     d_(i+1) = maj(t_i, c_i, d_i) = t_i c_i + (t_i + c_i) + s_i (t_i + c_i) on bits, of degree
//     max(k_t + k_c, max(k_t, k_c) + 1). So t can be a half<3> sum and c linear, or both half<2>.
//   - x + y, where y = u + v w bitwise for linear u, v, w (y = Ch(e, f, g) = g + e (f + g), or
//     y = Maj(a, b, c) = b + (a + b)(b + c)): commit the sum s, as for full; with x linear the
//     constraint has degree 3, and with x a half<2> sum, 4.
//
// A round, T1 = h + S1(e) + W_t + K_t + Ch(e, f, g), E = d + T1, and A = T1 + S0(a) + Maj(a, b,
// c), is computed as T1 = (full(half<3>(h, S1(e)), W_t) +_half<2> K_t) + Ch, E = d + T1, and
// A = half<2>(T1, S0(a)) + Maj: 10 + 31 + 15 + 32 + 31 + 15 + 32 = 166 committed bits (rather
// than 218 with only linear words). A word of the message schedule is
// full(half<2>(s1(W_(t-2)), W_(t-7)), half<2>(s0(W_(t-15)), W_(t-16))), 61 bits (rather than 93).

#ifndef VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP
#define VOLE_MOLE_ECDSA_POK_SHA256_CIRCUIT_HPP

#include "ecdsa_pok/bin_ops.hpp"
#include "sha256/sha256.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <numeric>
#include <span>
#include <utility>
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

    // Words of higher degree (see the top of this file). An XW<D> is a constant or 32 bits, where
    // bit i is an expression of degree 1 + (i mod D) (stored in w1, w2 or w3): the output of
    // half<D>, or for D = 1 a linear word.
    template <size_t d> using E = typename Ops::template Expr<d>;
    template <size_t D> struct XW {
        bool is_const = false;
        uint32_t c = 0;
        std::array<Wire, 32> w1{};
        std::array<E<2>, D >= 2 ? 32 : 0> w2{};
        std::array<E<3>, D >= 3 ? 32 : 0> w3{};
    };
    template <size_t d, size_t e> E<d> up(const E<e>& a) const {
        return ops.template lift<d, e>(a);
    }
    template <size_t a, size_t b> E<a + b> mul(const E<a>& x, const E<b>& y) const {
        return ops.template mul<a, b>(x, y);
    }
    template <size_t d> E<d> pl(const E<d>& x, const E<d>& y) const {
        return ops.template plus<d>(x, y);
    }
    // Bit i of a, of degree k = 1 + (i mod D).
    template <size_t k, size_t D> E<k> xb(const XW<D>& a, size_t i) const {
        if (a.is_const) {
            return up<k, 1>(((a.c >> i) & 1) != 0 ? ops.one() : ops.zero());
        }
        if constexpr (k == 1) {
            return a.w1[i];
        } else if constexpr (k == 2) {
            return a.w2[i];
        } else {
            return a.w3[i];
        }
    }
    template <size_t D> uint32_t xvalue(const XW<D>& a) const {
        if (a.is_const) {
            return a.c;
        }
        uint32_t v = 0;
        for (size_t i = 0; i < 32; ++i) {
            const size_t k = 1 + i % D;
            const bool b = k == 1 ? ops.value(a.w1[i])
                                  : (k == 2 ? ops.value(xb<D >= 2 ? 2 : 1>(a, i))
                                            : ops.value(xb<D >= 3 ? 3 : 1>(a, i)));
            v |= uint32_t{b} << i;
        }
        return v;
    }
    void lin_word(XW<1>& out, const W& a) const {
        out.is_const = a.is_const;
        out.c = a.c;
        if (!a.is_const) {
            out.w1 = a.w;
        }
    }
    // The carry maj(x, y, c) = x y + c (x + y), for linear x, y and c of degree k.
    template <size_t k> E<k + 1> carry(const Wire& x, const Wire& y, const E<k>& c) const {
        return pl<k + 1>(up<k + 1, 2>(mul<1, 1>(x, y)), mul<k, 1>(c, ops.add(x, y)));
    }
    // f.template operator()<r>(i0 + r) for r < L and i0 + r < n, for i0 = 0, L, 2 L, ...
    template <size_t L, typename F> static void unrolled(size_t n, F&& f) {
        for (size_t i0 = 0; i0 < n; i0 += L) {
            [&]<size_t... r>(std::index_sequence<r...>) {
                ((i0 + r < n ? (f.template operator()<r>(i0 + r), 0) : 0), ...);
            }(std::make_index_sequence<L>());
        }
    }

    // out = x + y modulo 2^32, for linear (or constant) x and y, committing only every D-th carry:
    // the carries in between, and the bits of the sum, have degree up to D, and the constraint of a
    // committed carry has degree D + 1.
    template <size_t D> void half(XW<D>& out, const W& a, const W& b) {
        static_assert(D == 2 || D == 3);
        if (a.is_const && b.is_const) {
            out.is_const = true;
            out.c = a.c + b.c;
            return;
        }
        out.is_const = false;
        const W& xx = a.is_const ? b : a;
        const W& y = a.is_const ? a : b; // the constant, if any
        const uint32_t xv = value(xx), yv = value(y);
        const uint32_t cv = (xv + yv) ^ xv ^ yv; // bit i: the carry into bit i (PlainOps)
        Wire c1 = ops.zero();                    // the committed carry into bit j
        for (size_t j = 0; j < 32; j += D) {
            const Wire xj = xx.w[j], yj = bit(y, j);
            out.w1[j] = ops.add(ops.add(xj, yj), c1);
            if (j + 1 == 32) {
                break;
            }
            const E<2> c2 = carry<1>(xj, yj, c1);
            const Wire x1 = xx.w[j + 1], y1 = bit(y, j + 1);
            out.w2[j + 1] = pl<2>(up<2, 1>(ops.add(x1, y1)), c2);
            if (j + 2 == 32) {
                break;
            }
            if constexpr (D == 2) {
                const Wire cn = ops.commit(((cv >> (j + 2)) & 1) != 0);
                ops.template assert_zero<3>(pl<3>(up<3, 1>(cn), carry<2>(x1, y1, c2)));
                c1 = cn;
            } else {
                const E<3> c3 = carry<2>(x1, y1, c2);
                const Wire x2 = xx.w[j + 2], y2 = bit(y, j + 2);
                out.w3[j + 2] = pl<3>(up<3, 1>(ops.add(x2, y2)), c3);
                if (j + 3 == 32) {
                    break;
                }
                const Wire cn = ops.commit(((cv >> (j + 3)) & 1) != 0);
                ops.template assert_zero<4>(pl<4>(up<4, 1>(cn), carry<3>(x2, y2, c3)));
                c1 = cn;
            }
        }
    }

    // out = t + c modulo 2^32, for t = XW<Dt> and c = XW<Dc>, committing the sum s, so that it's
    // linear (s_0 = t_0 + c_0 is). With the carries d_i = t_i + c_i + s_i,
    // d_(i+1) = maj(t_i, c_i, d_i) = t_i c_i + (t_i + c_i) + s_i (t_i + c_i) (on bits), of degree
    // at most max(Dt + Dc, max(Dt, Dc) + 1) <= 4.
    template <size_t Dt, size_t Dc> void full(W& out, const XW<Dt>& t, const XW<Dc>& c) {
        if (t.is_const && c.is_const) {
            set_const(out, t.c + c.c);
            return;
        }
        // With linear words, or a constant and a linear word, a plain addition (with the carries of
        // a constant known).
        if ((Dt == 1 && Dc == 1) || (Dt == 1 && c.is_const) || (Dc == 1 && t.is_const)) {
            W tw, cw;
            tw.is_const = t.is_const, tw.c = t.c, tw.w = t.w1;
            cw.is_const = c.is_const, cw.c = c.c, cw.w = c.w1;
            add(out, tw, cw);
            return;
        }
        const uint32_t sv = xvalue(t) + xvalue(c);
        out.w[0] = ops.add(xb<1>(t, 0), xb<1>(c, 0));
        for (size_t i = 1; i < 32; ++i) {
            out.w[i] = ops.commit(((sv >> i) & 1) != 0);
        }
        out.is_const = false;
        constexpr size_t L = Dt * Dc / std::gcd(Dt, Dc);
        unrolled<L>(31, [&]<size_t r>(size_t i) {
            constexpr size_t kt = 1 + r % Dt, kc = 1 + r % Dc;
            constexpr size_t kt1 = 1 + (r + 1) % Dt, kc1 = 1 + (r + 1) % Dc;
            constexpr size_t M = std::max(kt, kc);
            constexpr size_t ML = std::max({M, kt1, kc1});
            constexpr size_t P = std::max({kt + kc, M + 1, ML});
            static_assert(P <= 4);
            const E<kt> ti = xb<kt>(t, i);
            const E<kc> ci = xb<kc>(c, i);
            const E<M> tc = pl<M>(up<M, kt>(ti), up<M, kc>(ci));
            const E<ML> l =
                pl<ML>(pl<ML>(up<ML, kt1>(xb<kt1>(t, i + 1)), up<ML, kc1>(xb<kc1>(c, i + 1))),
                       pl<ML>(up<ML, 1>(out.w[i + 1]), up<ML, M>(tc)));
            ops.template assert_zero<P>(
                pl<P>(pl<P>(up<P, ML>(l), up<P, kt + kc>(mul<kt, kc>(ti, ci))),
                      up<P, M + 1>(mul<M, 1>(tc, out.w[i]))));
        });
    }

    // out = x + (u + v w) modulo 2^32 (as add_quad), for x = XW<2> (out isn't u, v or w): commit
    // the sum s; with y_i = u_i + v_i w_i and the carries d_i = x_i + y_i + s_i,
    // d_(i+1) = x_i y_i + (x_i + y_i) + s_i (x_i + y_i), of degree at most 4.
    void add_quad2(W& out, const XW<2>& xw, const W& u, const W& v, const W& w) {
        if (xw.is_const) {
            add_quad(out, W::constant(xw.c), u, v, w);
            return;
        }
        if (v.is_const || w.is_const) {
            const W& lin = v.is_const ? w : v;
            const uint32_t k = v.is_const ? v.c : w.c;
            W& y = out;
            for (size_t i = 0; i < 32; ++i) {
                y.w[i] = ((k >> i) & 1) != 0 ? lin.w[i] : ops.zero();
            }
            y.is_const = false;
            if (lin.is_const) {
                set_const(y, lin.c & k);
            }
            x(y, u, y);
            lin_word(lw_, y);
            full<2, 1>(out, xw, lw_);
            return;
        }
        const uint32_t sv = xvalue(xw) + (value(u) ^ (value(v) & value(w)));
        for (size_t i = 0; i < 32; ++i) {
            out.w[i] = ops.commit(((sv >> i) & 1) != 0);
        }
        out.is_const = false;
        for (size_t i = 0; i < 32; ++i) {
            yq_[i] = pl<2>(up<2, 1>(bit(u, i)), mul<1, 1>(v.w[i], w.w[i]));
        }
        auto yb = [&](size_t i) -> const E<2>& { return yq_[i]; };
        // d_0 = 0.
        ops.template assert_zero<2>(pl<2>(pl<2>(up<2, 1>(xw.w1[0]), yb(0)), up<2, 1>(out.w[0])));
        unrolled<2>(31, [&]<size_t r>(size_t i) {
            constexpr size_t kx = 1 + r, kx1 = 2 - r;
            constexpr size_t P = kx + 2;
            const E<kx> xi = xb<kx>(xw, i);
            const E<2>& yi = yb(i);
            const E<2> xy = pl<2>(up<2, kx>(xi), yi);
            const E<2> l = pl<2>(
                pl<2>(pl<2>(up<2, kx1>(xb<kx1>(xw, i + 1)), yb(i + 1)), up<2, 1>(out.w[i + 1])),
                xy);
            ops.template assert_zero<P>(
                pl<P>(pl<P>(up<P, 2>(l), mul<kx, 2>(xi, yi)), up<P, 3>(mul<2, 1>(xy, out.w[i]))));
        });
    }

    // Scratch words (public, for aggregate initialization).
    XW<1> lw_{};
    XW<2> ha_{}, hb_{};
    XW<3> hc_{};
    std::array<E<2>, 32> yq_{};

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
            half<2>(ha_, t0, w[t - 7]);
            half<2>(hb_, t1, w[t - 16]);
            full<2, 2>(w[t], ha_, hb_);
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
            half<3>(hc_, hh, t0);
            lin_word(lw_, w[t]);
            full<3, 1>(t0, hc_, lw_);
            konst_.c = sha256::K[t];
            half<2>(ha_, t0, konst_);
            x(t2, f, g);
            add_quad2(t1, ha_, g, ee, t2);
            add(e[t + 4], d, t1);
            // A = (T1 + S0(a)) + Maj(a, b, c).
            s0(t0, aa);
            x(t2, aa, b);
            x(t3, b, c);
            half<2>(ha_, t1, t0);
            add_quad2(a[t + 4], ha_, b, t2, t3);
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
