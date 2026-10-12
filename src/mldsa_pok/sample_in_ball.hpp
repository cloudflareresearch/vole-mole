// The binary arithmetization of ML-DSA's SampleInBall (FIPS 204, Algorithm 29) after the hash:
// given the SHAKE256 output stream (committed bits of degree 1), the challenge c with TAU
// coefficients +-1.
//
//   h <- the first 8 bytes of the stream, as bits (only h_0, ..., h_{TAU - 1} are used)
//   for i from 256 - TAU to 255:
//     j <- the next stream byte, until j <= i
//     c_i <- c_j;  c_j <- (-1)^(h_{i + TAU - 256})
//
// We scan SCAN_BYTES bytes of the stream (stream bytes 8, 9, ...). An honest prover fails if
// SampleInBall needs more, which happens with probability less than 2^-77 over c-tilde (for
// SCAN_BYTES = 80); see `scan_failure_log2` in test_sample_in_ball.cpp.
//
// Witness (all bits, committed):
//
// 1. The scan. For each byte p: a_p (accepted), v_{p+1} (6 bits), d_{p+1} (done). The step
//    being sampled at byte p is i_p = 192 + v_p (v_0 = 25, so i_0 = 217 = 256 - TAU), and d_p is
//    set once all TAU steps are done. Constraints:
//
//      a_p = (1 + d_p) [b_p <= i_p],  where [b <= 192 + v] = 1 + b_7 b_6 [v < b mod 64]
//      v_{p+1} = v_p + a_p (mod 64)
//      d_{p+1} = d_p + a_p [v_p = 63]
//      d_SCAN_BYTES = 1
//
// 2. The steps. For step l (i = 217 + l):
//
//      j_l (8 bits)           the accepted byte: j_l = sum_p a_p [v_p = 25 + l] b_p
//      Lv_l, L_l (1 + 6 bits) the last earlier step m < l with j_m = j_l, if any
//      last_l                 whether no later step m > l has j_m = j_l
//      sv_l, s_l (1 + 6 bits) the label (step) whose sign step l copies to position i, if any
//                             (src_l = A[j_l] before step l, in the notation below)
//      g_l                    h_{s_l}
//
//    Write A[x] for the label (the step whose sign it holds) at position x, or none. Step l sets
//    A[i] = A[j_l], then A[j_l] = l. So the final A[x] is l for the last step l with j_l = x, if
//    any; otherwise src_{x - 217} if x >= 217; otherwise none. And src_l, the content of j_l
//    before step l, is the label L_l if Lv_l (the last write to j_l was step L_l: step j_l, if
//    j_l >= 217, writes j_l before any step m > j_l with j_m = j_l), and otherwise src_{j_l - 217}
//    if 217 <= j_l < i, and none otherwise. Constraints:
//
//      Lv_l [L_l >= l] = 0,  (1 + Lv_l) L_l = 0                 (L_l = 0 if there's none)
//      Lv_l (j_{L_l} + j_l) = 0                                 (bitwise)
//      [j_m = j_l] (1 + Lv_l [L_l >= m]) = 0   for all m < l    (no occurrence after L_l)
//      last_l = 1 + sum_{m > l} Lv_m [L_m = l]                   (the next occurrence points to l)
//      sv_l = Lv_l + (1 + Lv_l) sum_{m < l} [j_l = 217 + m] sv_m
//      s_l = Lv_l L_l + (1 + Lv_l) sum_{m < l} [j_l = 217 + m] s_m
//      g_l = sum_n [s_l = n] h_n
//
//    The sums have at most one non-zero term, so they're the same in GF(2) and over the integers.
//
// 3. The challenge, as c_x + 1 in {0, 1, 2}: z_x = [c_x = 0] and p_x = [c_x = 1]. With
//    hit_x = sum_l last_l [j_l = x] and hp_x = sum_l last_l [j_l = x] (1 + h_l):
//
//      x < 217:        z_x = 1 + hit_x,              p_x = hp_x
//      x = 217 + l:    z_x = (1 + hit_x)(1 + sv_l),  p_x = hp_x + (1 + hit_x) sv_l (1 + g_l)
//
// All constraints have degree at most 16. If COMMIT_EQ is set, the witness also holds
// E_{l,m} = [j_m = j_l] for m < l, with the constraint E_{l,m} = [j_m = j_l], so that the
// no-occurrence constraint becomes E_{l,m} (1 + Lv_l [L_l >= m]) = 0, and the degree is at most 11.
// That costs TAU (TAU - 1) / 2 more witness bits, which is worthwhile if the witness is derived
// (which doubles the degree, see voleith.hpp).

#ifndef VOLE_MOLE_MLDSA_POK_SAMPLE_IN_BALL_HPP
#define VOLE_MOLE_MLDSA_POK_SAMPLE_IN_BALL_HPP

#include "qs_bit.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

template <size_t TAU_, size_t SCAN_BYTES_, bool COMMIT_EQ = false> struct SampleInBall {
    static constexpr size_t N = 256;
    static constexpr size_t TAU = TAU_;
    static constexpr size_t SCAN_BYTES = SCAN_BYTES_;
    static constexpr size_t FIRST = N - TAU; // the first step i
    static_assert(FIRST >= 192 && FIRST < 256);
    static constexpr size_t V0 = FIRST - 192;
    static_assert(TAU <= 64 && V0 + TAU == 64, "v counts to 64");
    static constexpr size_t SIGN_BYTES = 8;
    static constexpr size_t STREAM_BYTES = SIGN_BYTES + SCAN_BYTES;

    // Witness layout, in bits.
    static constexpr size_t SCAN_STRIDE = 8;  // a, v (6), d
    static constexpr size_t STEP_STRIDE = 24; // j (8), L (6), Lv, sv, s (6), last, g
    static constexpr size_t STEP_J = 0, STEP_L = 8, STEP_LV = 14, STEP_SV = 15, STEP_S = 16,
                            STEP_LAST = 22, STEP_G = 23;
    static constexpr size_t OFF_SCAN = 0;
    static constexpr size_t OFF_STEPS = OFF_SCAN + SCAN_STRIDE * SCAN_BYTES;
    static constexpr size_t OFF_C = OFF_STEPS + STEP_STRIDE * TAU; // z_x, p_x for each x
    static constexpr size_t OFF_EQ = OFF_C + 2 * N; // E_{l,m} for m < l, if COMMIT_EQ
    static constexpr size_t NUM_EQ = COMMIT_EQ ? TAU * (TAU - 1) / 2 : 0;
    static constexpr size_t eq_index(size_t l, size_t m) { return OFF_EQ + l * (l - 1) / 2 + m; }
    static constexpr size_t WITNESS_BITS = OFF_EQ + NUM_EQ;
    static constexpr size_t DEGREE = COMMIT_EQ ? 11 : 16;

    static constexpr size_t NUM_CONSTRAINTS = 8 * SCAN_BYTES + 1              // scan
                                              + TAU * (8 + 7 + 8 + 1 + 7 + 1) // steps, per l
                                              + TAU * (TAU - 1) / 2           // no occurrences
                                              + NUM_EQ                        // E_{l,m}
                                              + 2 * N;                        // c

    // The witness bits for the stream, written to `out` at bit offset `off`, and the challenge c
    // (coefficients in {-1, 0, 1}). Returns std::nullopt if the scan is too short.
    static std::optional<std::array<int8_t, N>>
    encode_witness(std::span<const uint8_t, STREAM_BYTES> stream, std::span<uint8_t> out,
                   size_t off) {
        const auto set = [&](size_t i, bool v) {
            const size_t b = off + i;
            out[b / 8] =
                static_cast<uint8_t>((out[b / 8] & ~(1u << (b % 8))) | (unsigned{v} << (b % 8)));
        };
        const auto h = [&](size_t n) { return ((stream[n / 8] >> (n % 8)) & 1) != 0; };

        // 1. The scan.
        std::array<size_t, TAU> j{};
        size_t v = V0;
        bool d = false;
        for (size_t p = 0; p < SCAN_BYTES; ++p) {
            const size_t b = stream[SIGN_BYTES + p];
            const bool a = !d && b <= 192 + v;
            if (a) {
                j[v - V0] = b;
            }
            const size_t v_next = (v + a) % 64;
            d = d || (a && v == 63);
            v = v_next;
            const size_t base = OFF_SCAN + SCAN_STRIDE * p;
            set(base, a);
            for (size_t k = 0; k < 6; ++k) {
                set(base + 1 + k, ((v >> k) & 1) != 0);
            }
            set(base + 7, d);
        }
        if (!d) {
            return std::nullopt;
        }

        // 2. The steps.
        std::array<bool, TAU> lv{}, last{}, sv{};
        std::array<size_t, TAU> l_idx{}, s{};
        for (size_t l = 0; l < TAU; ++l) {
            for (size_t m = 0; m < l; ++m) {
                if (j[m] == j[l]) {
                    lv[l] = true;
                    l_idx[l] = m;
                }
                if constexpr (COMMIT_EQ) {
                    set(eq_index(l, m), j[m] == j[l]);
                }
            }
            last[l] = true;
            for (size_t m = l + 1; m < TAU; ++m) {
                last[l] = last[l] && j[m] != j[l];
            }
            if (lv[l]) {
                sv[l] = true;
                s[l] = l_idx[l];
            } else if (j[l] >= FIRST && j[l] < FIRST + l) {
                sv[l] = sv[j[l] - FIRST];
                s[l] = s[j[l] - FIRST];
            }
            const size_t base = OFF_STEPS + STEP_STRIDE * l;
            for (size_t k = 0; k < 8; ++k) {
                set(base + STEP_J + k, ((j[l] >> k) & 1) != 0);
            }
            for (size_t k = 0; k < 6; ++k) {
                set(base + STEP_L + k, ((l_idx[l] >> k) & 1) != 0);
                set(base + STEP_S + k, ((s[l] >> k) & 1) != 0);
            }
            set(base + STEP_LV, lv[l]);
            set(base + STEP_SV, sv[l]);
            set(base + STEP_LAST, last[l]);
            set(base + STEP_G, h(s[l]));
        }

        // 3. The challenge.
        std::array<int8_t, N> c{};
        for (size_t x = 0; x < N; ++x) {
            int label = -1;
            for (size_t l = 0; l < TAU; ++l) {
                if (last[l] && j[l] == x) {
                    label = static_cast<int>(l);
                }
            }
            if (label < 0 && x >= FIRST && sv[x - FIRST]) {
                label = static_cast<int>(s[x - FIRST]);
            }
            c[x] = label < 0 ? 0 : (h(static_cast<size_t>(label)) ? -1 : 1);
            set(OFF_C + 2 * x, c[x] == 0);
            set(OFF_C + 2 * x + 1, c[x] == 1);
        }
        return c;
    }

    // ---------------------------------------------------------------------------------------------
    // Constraints

    template <typename QS, size_t deg> using Bit = vole_mole::detail::qs_bit<QS, deg>;

    // The product of N degree-1 terms.
    template <size_t M, typename QS> static Bit<QS, M> prod(std::span<const Bit<QS, 1>, M> t) {
        if constexpr (M == 1) {
            return t[0];
        } else {
            return vole_mole::detail::qs_mul(prod<M - 1, QS>(t.template first<M - 1>()), t[M - 1]);
        }
    }

    // [x = c] for M committed bits x and a constant c.
    template <size_t M, typename QS>
    static Bit<QS, M> eq_const(std::span<const Bit<QS, 1>, M> x, size_t c) {
        std::array<Bit<QS, 1>, M> t;
        for (size_t k = 0; k < M; ++k) {
            t[k] = x[k] + faest::poly1(1 ^ ((c >> k) & 1));
        }
        return prod<M, QS>(t);
    }

    // [x = y] for M committed bits x and y.
    template <size_t M, typename QS>
    static Bit<QS, M> eq_bits(std::span<const Bit<QS, 1>, M> x, std::span<const Bit<QS, 1>, M> y) {
        std::array<Bit<QS, 1>, M> t;
        for (size_t k = 0; k < M; ++k) {
            t[k] = x[k] + y[k] + faest::poly1(1);
        }
        return prod<M, QS>(t);
    }

    // [x < y] for the low K + 1 bits of x and y, of degree K + 2: lt_0 = (x_0 + 1) y_0, and
    // lt_k = (x_k + 1) y_k + (x_k + y_k + 1) lt_{k-1} (the terms are exclusive).
    template <size_t K, typename QS>
    static Bit<QS, K + 2> lt(std::span<const Bit<QS, 1>> x, std::span<const Bit<QS, 1>> y) {
        const Bit<QS, 2> top = vole_mole::detail::qs_mul(x[K] + faest::poly1(1), y[K]);
        if constexpr (K == 0) {
            return top;
        } else {
            return Bit<QS, K + 2>(top) +
                   vole_mole::detail::qs_mul(x[K] + y[K] + faest::poly1(1), lt<K - 1, QS>(x, y));
        }
    }

    // Constant bits.
    template <size_t M, typename QS>
    static std::array<Bit<QS, 1>, M> constant(const QS* qs, size_t c) {
        std::array<Bit<QS, 1>, M> out;
        for (size_t k = 0; k < M; ++k) {
            out[k] = Bit<QS, 1>(faest::poly1((c >> k) & 1), qs);
        }
        return out;
    }

    // [x = c] for c in [0, COUNT), for 6 committed bits x, via 3-bit halves (of degree 6).
    template <typename QS>
    static std::vector<Bit<QS, 6>> onehot6(std::span<const Bit<QS, 1>, 6> x, size_t count) {
        std::array<Bit<QS, 3>, 8> lo, hi;
        for (size_t c = 0; c < 8; ++c) {
            lo[c] = eq_const<3, QS>(x.template first<3>(), c);
            hi[c] = eq_const<3, QS>(x.template last<3>(), c);
        }
        std::vector<Bit<QS, 6>> out;
        out.reserve(count);
        for (size_t c = 0; c < count; ++c) {
            out.push_back(vole_mole::detail::qs_mul(lo[c % 8], hi[c / 8]));
        }
        return out;
    }

    // [x = c] for c in [0, 256), for 8 committed bits x, via 4-bit halves (of degree 8).
    template <typename QS>
    static std::vector<Bit<QS, 8>> onehot8(std::span<const Bit<QS, 1>, 8> x) {
        std::array<Bit<QS, 4>, 16> lo, hi;
        for (size_t c = 0; c < 16; ++c) {
            lo[c] = eq_const<4, QS>(x.template first<4>(), c);
            hi[c] = eq_const<4, QS>(x.template last<4>(), c);
        }
        std::vector<Bit<QS, 8>> out;
        out.reserve(N);
        for (size_t c = 0; c < N; ++c) {
            out.push_back(vole_mole::detail::qs_mul(lo[c % 16], hi[c / 16]));
        }
        return out;
    }

    template <typename QS, size_t deg> static void zero(QS* qs, const Bit<QS, deg>& x) {
        qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(x));
    }

    // The constraints, for the stream bits `stream` (at least 8 STREAM_BYTES of them, of degree 1)
    // and the witness at bit offset `off`.
    template <typename QS>
    static void constraints(QS* qs, std::span<const Bit<QS, 1>> stream, size_t off) {
        using B1 = Bit<QS, 1>;
        using faest::poly1;
        using vole_mole::detail::qs_mul;
        const auto w = [&](size_t i) { return qs->get_witness_bit(off + i); };
        const auto bits = [&]<size_t M>(size_t i) {
            std::array<B1, M> out;
            for (size_t k = 0; k < M; ++k) {
                out[k] = w(i + k);
            }
            return out;
        };
        const auto byte = [&](size_t p) {
            std::array<B1, 8> out;
            for (size_t k = 0; k < 8; ++k) {
                out[k] = stream[8 * (SIGN_BYTES + p) + k];
            }
            return out;
        };
        const auto h = [&](size_t n) { return stream[n]; };

        // 1. The scan. v_p and d_p for the current p, and the selectors a_p [v_p = V0 + l].
        std::array<B1, 6> v = constant<6, QS>(qs, V0);
        B1 d(poly1(0), qs);
        std::vector<std::array<Bit<QS, 7>, TAU>> sel(SCAN_BYTES);
        for (size_t p = 0; p < SCAN_BYTES; ++p) {
            const size_t base = OFF_SCAN + SCAN_STRIDE * p;
            const B1 a = w(base);
            const auto v_next = bits.template operator()<6>(base + 1);
            const B1 d_next = w(base + 7);
            const auto b = byte(p);

            // a = (1 + d) (1 + b_7 b_6 [v < b mod 64])
            const auto v_lt_b = lt<5, QS>(v, std::span<const B1>(b).first(6));
            const auto le = qs_mul(qs_mul(b[7], b[6]), v_lt_b) + poly1(1);
            zero(qs, Bit<QS, 10>(a) + qs_mul(d + poly1(1), le));

            // v_next = v + a (mod 64): bit k flips if a and the lower bits are all 1.
            zero(qs, v_next[0] + v[0] + a);
            {
                Bit<QS, 2> c2 = qs_mul(a, v[0]);
                zero(qs, Bit<QS, 2>(v_next[1] + v[1]) + c2);
                Bit<QS, 3> c3 = qs_mul(c2, v[1]);
                zero(qs, Bit<QS, 3>(v_next[2] + v[2]) + c3);
                Bit<QS, 4> c4 = qs_mul(c3, v[2]);
                zero(qs, Bit<QS, 4>(v_next[3] + v[3]) + c4);
                Bit<QS, 5> c5 = qs_mul(c4, v[3]);
                zero(qs, Bit<QS, 5>(v_next[4] + v[4]) + c5);
                Bit<QS, 6> c6 = qs_mul(c5, v[4]);
                zero(qs, Bit<QS, 6>(v_next[5] + v[5]) + c6);
                // d_next = d + a [v = 63]
                Bit<QS, 7> c7 = qs_mul(c6, v[5]);
                zero(qs, Bit<QS, 7>(d_next + d) + c7);
            }

            const auto onehot = onehot6<QS>(v, V0 + TAU);
            for (size_t l = 0; l < TAU; ++l) {
                sel[p][l] = qs_mul(a, onehot[V0 + l]);
            }
            v = v_next;
            d = d_next;
        }
        zero(qs, d + poly1(1));

        // 2. The steps.
        const auto step = [&](size_t l, size_t field) {
            return OFF_STEPS + STEP_STRIDE * l + field;
        };
        std::vector<std::array<B1, 8>> j(TAU);
        std::vector<std::array<B1, 6>> L(TAU), s(TAU);
        std::vector<B1> lv(TAU), sv(TAU), last(TAU), g(TAU);
        std::vector<std::vector<Bit<QS, 8>>> j_onehot(TAU);
        std::vector<std::vector<Bit<QS, 6>>> l_onehot(TAU);
        for (size_t l = 0; l < TAU; ++l) {
            j[l] = bits.template operator()<8>(step(l, STEP_J));
            L[l] = bits.template operator()<6>(step(l, STEP_L));
            s[l] = bits.template operator()<6>(step(l, STEP_S));
            lv[l] = w(step(l, STEP_LV));
            sv[l] = w(step(l, STEP_SV));
            last[l] = w(step(l, STEP_LAST));
            g[l] = w(step(l, STEP_G));
            j_onehot[l] = onehot8<QS>(j[l]);
            l_onehot[l] = onehot6<QS>(L[l], TAU);
        }
        for (size_t l = 0; l < TAU; ++l) {
            // j_l = sum_p a_p [v_p = V0 + l] b_p
            for (size_t k = 0; k < 8; ++k) {
                Bit<QS, 8> acc(j[l][k]);
                for (size_t p = l; p < SCAN_BYTES; ++p) {
                    acc = acc + qs_mul(sel[p][l], byte(p)[k]);
                }
                zero(qs, acc);
            }

            // Lv_l [L_l >= l] = 0
            const auto l_const = constant<6, QS>(qs, l);
            zero(qs, qs_mul(lv[l], lt<5, QS>(L[l], l_const) + poly1(1)));
            for (size_t k = 0; k < 6; ++k) {
                zero(qs, qs_mul(lv[l] + poly1(1), L[l][k]));
            }

            // Lv_l (j_{L_l} + j_l) = 0
            for (size_t k = 0; k < 8; ++k) {
                Bit<QS, 8> acc(B1(poly1(0), qs));
                for (size_t m = 0; m < l; ++m) {
                    acc = acc + qs_mul(qs_mul(lv[l], l_onehot[l][m]), j[m][k] + j[l][k]);
                }
                zero(qs, acc);
            }

            // [j_m = j_l] (1 + Lv_l [L_l >= m]) = 0 for m < l
            for (size_t m = 0; m < l; ++m) {
                const auto m_const = constant<6, QS>(qs, m);
                const auto after = qs_mul(lv[l], lt<5, QS>(L[l], m_const) + poly1(1)) + poly1(1);
                if constexpr (COMMIT_EQ) {
                    const B1 e = w(eq_index(l, m));
                    zero(qs, Bit<QS, 8>(e) + eq_bits<8, QS>(j[m], j[l]));
                    zero(qs, qs_mul(e, after));
                } else {
                    zero(qs, qs_mul(eq_bits<8, QS>(j[m], j[l]), after));
                }
            }

            // last_l = 1 + sum_{m > l} Lv_m [L_m = l]
            {
                Bit<QS, 7> acc(last[l] + poly1(1));
                for (size_t m = l + 1; m < TAU; ++m) {
                    acc = acc + qs_mul(lv[m], l_onehot[m][l]);
                }
                zero(qs, acc);
            }

            // sv_l = Lv_l + (1 + Lv_l) sum_{m < l} [j_l = FIRST + m] sv_m, and likewise for s_l.
            {
                std::array<Bit<QS, 9>, 7> sum;
                for (auto& x : sum) {
                    x = Bit<QS, 9>(B1(poly1(0), qs));
                }
                for (size_t m = 0; m < l; ++m) {
                    const auto& e = j_onehot[l][FIRST + m];
                    sum[0] = sum[0] + qs_mul(e, sv[m]);
                    for (size_t k = 0; k < 6; ++k) {
                        sum[1 + k] = sum[1 + k] + qs_mul(e, s[m][k]);
                    }
                }
                const B1 not_lv = lv[l] + poly1(1);
                zero(qs, Bit<QS, 10>(sv[l] + lv[l]) + qs_mul(not_lv, sum[0]));
                for (size_t k = 0; k < 6; ++k) {
                    zero(qs, Bit<QS, 10>(Bit<QS, 2>(s[l][k]) + qs_mul(lv[l], L[l][k])) +
                                 qs_mul(not_lv, sum[1 + k]));
                }
            }

            // g_l = sum_n [s_l = n] h_n
            {
                const auto onehot = onehot6<QS>(s[l], TAU);
                Bit<QS, 7> acc(g[l]);
                for (size_t n = 0; n < TAU; ++n) {
                    acc = acc + qs_mul(onehot[n], h(n));
                }
                zero(qs, acc);
            }
        }

        // 3. The challenge.
        for (size_t x = 0; x < N; ++x) {
            Bit<QS, 9> hit(B1(poly1(0), qs));
            Bit<QS, 10> hp(B1(poly1(0), qs));
            for (size_t l = 0; l < TAU; ++l) {
                const auto t = qs_mul(j_onehot[l][x], last[l]);
                hit = hit + t;
                hp = hp + qs_mul(t, h(l) + poly1(1));
            }
            const B1 z = w(OFF_C + 2 * x), pp = w(OFF_C + 2 * x + 1);
            const auto not_hit = hit + poly1(1);
            if (x < FIRST) {
                zero(qs, Bit<QS, 9>(z) + not_hit);
                zero(qs, Bit<QS, 10>(pp) + hp);
            } else {
                const size_t l = x - FIRST;
                zero(qs, Bit<QS, 10>(z) + qs_mul(not_hit, sv[l] + poly1(1)));
                zero(qs, Bit<QS, 11>(Bit<QS, 10>(pp) + hp) +
                             qs_mul(qs_mul(not_hit, sv[l]), g[l] + poly1(1)));
            }
        }
    }
};

} // namespace vole_mole::mldsa_pok::detail

#endif
