// The MQ PRG over F_q, q = 3329: a pseudorandom generator of degree 2, for deriving a witness in
// F_q^N from a short key (see "Derived witnesses" in voleith.hpp). This is the F_q analogue of
// mq/prg.hpp and mq/split.hpp. Experimental.
//
// The PRG stretches a key K in F_q^n into N outputs
//
//   G(K)_i = sum_{j <= k} m_{ijk} K_j K_k    (i in [N])
//
// with public coefficients m_{ijk} in F_q. Unlike over GF(2), K_j^2 != K_j, so there's no linear
// part; that doesn't matter for security (a linear part can be absorbed by a change of variables
// K -> K + c only up to constants, and the MQ estimate assumes a generic quadratic system).
// mq_key_len(N) is the smallest n for which solving the system is estimated to cost 2^128 (see
// mq_key_len.hpp).
//
// Split: As in mq/split.hpp, the N outputs may be split over c independent instances, each with
// its own key and coefficients, whose keys and outputs are concatenated. The committed evaluation
// of one instance costs about N n^2 / 2 multiplications per lane, and n grows like sqrt(N), so
// splitting divides the cost by about c, at the cost of a longer total key.
//
// Coefficients: For each instance t, the upper triangles of the n x n matrices M_i, row by row, are
// sampled by rejection sampling from AES-128-CTR (as the VOLE leaves, see expand_leaf in
// voleith.hpp) with key SHAKE128(dst || le32(n) || le32(N_t) || le32(t))[0..16]. They are
// expanded once and cached: for ML-KEM-768 with c = 1 that's 31 MB.
//
// Committed evaluation: If K is committed with MACs (degree 1 in Delta), then G(K)_i has degree 2:
// with K_j = V_j + k_j Delta,
//
//   G(K)_i = c0_i + c1_i Delta + c2_i Delta^2, where
//     c0_i = sum_j V_j L_ij(V),  c1_i = sum_j (V_j L_ij(k) + k_j L_ij(V)),  c2_i = G(k)_i,
//
// with the linear forms L_ij(x) = sum_{k >= j} m_{ijk} x_k. We compute L_ij on all 16 + 1 lanes
// (the coordinates of V, and the value k) at once, so each output costs n (n + 1) / 2 * 17
// multiply-adds plus n products in F_{q^16}. The verifier computes sum_j K_j L_ij(K) in the same
// way.

#ifndef VOLE_MOLE_VOLEITH_FQ_MQ_HPP
#define VOLE_MOLE_VOLEITH_FQ_MQ_HPP

#include "voleith_fq/field.hpp"
#include "voleith_fq/mq_key_len.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

#if defined(__aarch64__)
#include <arm_neon.h>
#endif

namespace vole_mole::voleith_fq::detail {

// The smallest key length for which the PRG with `num_outputs` outputs is estimated to be secure.
constexpr size_t mq_key_len(size_t num_outputs) {
    for (const MqKeyLenEntry& e : MQ_KEY_LEN_TABLE) {
        if (num_outputs <= e.max_outputs) {
            return e.key_len;
        }
    }
    throw std::invalid_argument("MQ PRG over F_q: too many outputs"); // not a constant expression
}

// The split layout: instance t has outputs [output_offset(t), output_offset(t + 1)) and key
// [key_offset(t), key_offset(t + 1)).
template <size_t NUM_OUTPUTS, size_t NUM_INSTANCES> struct MqLayout {
    static_assert(NUM_INSTANCES >= 1 && NUM_OUTPUTS >= NUM_INSTANCES);
    static constexpr size_t PART = (NUM_OUTPUTS + NUM_INSTANCES - 1) / NUM_INSTANCES;
    static_assert(PART * (NUM_INSTANCES - 1) < NUM_OUTPUTS, "too many instances");

    static constexpr size_t outputs(size_t t) {
        return t + 1 < NUM_INSTANCES ? PART : NUM_OUTPUTS - (NUM_INSTANCES - 1) * PART;
    }
    static constexpr size_t output_offset(size_t t) { return t * PART; }
    static constexpr size_t key_len(size_t t) { return mq_key_len(outputs(t)); }
    static constexpr size_t key_offset(size_t t) {
        size_t off = 0;
        for (size_t u = 0; u < t; ++u) {
            off += key_len(u);
        }
        return off;
    }
    static constexpr size_t KEY_LEN = key_offset(NUM_INSTANCES);
    static constexpr size_t max_key_len() {
        size_t m = 0;
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            m = key_len(t) > m ? key_len(t) : m;
        }
        return m;
    }
    // The 32-bit accumulators of the linear forms hold sums of up to n products < q^2.
    static_assert(uint64_t{max_key_len()} * (Q - 1) * (Q - 1) < (uint64_t{1} << 32));
};

// The coefficients of instance t (defined in voleith.hpp).
inline void mq_expand_coefficients(std::span<const uint8_t> dst, size_t n, size_t num_outputs,
                                   size_t t, std::span<Fq> out);

template <size_t NUM_OUTPUTS, size_t NUM_INSTANCES> class MqMap {
    using Lay = MqLayout<NUM_OUTPUTS, NUM_INSTANCES>;

  public:
    static constexpr size_t NUM_OUTPUTS_V = NUM_OUTPUTS;
    static constexpr size_t KEY_LEN = Lay::KEY_LEN;
    static_assert(KEY_LEN % 2 == 0);

    // Outputs are processed in blocks of BLOCK, whose coefficients are interleaved: for block b,
    // the stream holds m_{ijk} for i = BLOCK b + r at position ((j, k) index) * BLOCK + r, where
    // (j, k) runs over the upper triangle row by row.
    static constexpr size_t BLOCK = 4;
    static_assert([] {
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            if (Lay::outputs(t) % BLOCK != 0) {
                return false;
            }
        }
        return true;
    }());

    explicit MqMap(std::span<const uint8_t> dst) {
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            const size_t n = Lay::key_len(t);
            coeffs_[t].resize(Lay::outputs(t) * tri(n));
            mq_expand_coefficients(dst, n, Lay::outputs(t), t, coeffs_[t]);
        }
    }

    static constexpr size_t tri(size_t n) { return n * (n + 1) / 2; }

    // G(key).
    void eval(std::span<const Fq, KEY_LEN> key, std::span<Fq, NUM_OUTPUTS> out) const {
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            const size_t n = Lay::key_len(t);
            const Fq* k = key.data() + Lay::key_offset(t);
            const Fq* m = coeffs_[t].data();
            for (size_t b = 0; b < Lay::outputs(t) / BLOCK; ++b) {
                std::array<uint32_t, BLOCK> acc{};
                for (size_t j = 0; j < n; ++j) {
                    std::array<uint32_t, BLOCK> lin{};
                    for (size_t l = j; l < n; ++l) {
                        for (size_t r = 0; r < BLOCK; ++r) {
                            lin[r] += uint32_t{*m++} * k[l];
                        }
                    }
                    for (size_t r = 0; r < BLOCK; ++r) {
                        acc[r] = fq_reduce(acc[r] + uint32_t{k[j]} * fq_reduce(lin[r]));
                    }
                }
                for (size_t r = 0; r < BLOCK; ++r) {
                    out[Lay::output_offset(t) + BLOCK * b + r] = static_cast<Fq>(acc[r]);
                }
            }
        }
    }

    // Prover's committed evaluation. v[t] (t < 16) are the lanes of V for the key, key its value.
    // Writes, for each output i, c0_i to c0[.][i], c1_i to c1[.][i] (lane-major: coordinate t of
    // output i at [t * NUM_OUTPUTS + i]), and c2_i = G(key)_i to c2[i].
    void prove_eval(std::span<const std::span<const Fq>, EXT_DEGREE> v, std::span<const Fq> key,
                    std::span<Fq> c0, std::span<Fq> c1, std::span<Fq> c2) const {
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            const size_t n = Lay::key_len(t);
            const size_t ko = Lay::key_offset(t);
            // Element-major copy of the key's lanes.
            std::vector<Row> xv(n);
            std::vector<uint32_t> xk(n);
            for (size_t j = 0; j < n; ++j) {
                for (size_t c = 0; c < EXT_DEGREE; ++c) {
                    xv[j][c] = v[c][ko + j];
                }
                xk[j] = key[ko + j];
            }
            const Fq* m = coeffs_[t].data();
            for (size_t b = 0; b < Lay::outputs(t) / BLOCK; ++b) {
                // Lazily reduced: acc0 is the unreduced product sum_j V_j * L_ij(V).
                std::array<std::array<uint32_t, 2 * EXT_DEGREE>, BLOCK> acc0{};
                std::array<Lanes, BLOCK> acc1{};
                std::array<uint32_t, BLOCK> a2{};
                for (size_t j = 0; j < n; ++j) {
                    std::array<Lanes, BLOCK> lin;
                    std::array<uint32_t, BLOCK> linv;
                    lin_form(m, xv.data() + j, n - j, lin, xk.data() + j, &linv);
                    m += BLOCK * (n - j);
                    const uint32_t kj = xk[j];
                    for (size_t r = 0; r < BLOCK; ++r) {
                        for (size_t p = 0; p < EXT_DEGREE; ++p) {
                            lin[r][p] %= Q;
                        }
                        const uint32_t lval = linv[r] % Q;
                        mul_acc(acc0[r], xv[j], lin[r]);
                        for (size_t p = 0; p < EXT_DEGREE; ++p) {
                            acc1[r][p] += lval * uint32_t{xv[j][p]} + kj * lin[r][p];
                        }
                        a2[r] = (a2[r] + kj * lval) % Q;
                    }
                    if (j % REDUCE_EVERY == REDUCE_EVERY - 1) {
                        for (size_t r = 0; r < BLOCK; ++r) {
                            for (auto& x : acc0[r]) {
                                x %= Q;
                            }
                            for (auto& x : acc1[r]) {
                                x %= Q;
                            }
                        }
                    }
                }
                for (size_t r = 0; r < BLOCK; ++r) {
                    const size_t o = Lay::output_offset(t) + BLOCK * b + r;
                    for (size_t p = 0; p < EXT_DEGREE; ++p) {
                        c0[p * NUM_OUTPUTS + o] = fold(acc0[r], p);
                        c1[p * NUM_OUTPUTS + o] = fq_reduce(acc1[r][p]);
                    }
                    c2[o] = static_cast<Fq>(a2[r]);
                }
            }
        }
    }

    // Verifier's committed evaluation: out[t * NUM_OUTPUTS + i] = coordinate t of G(K)_i, where
    // k[t] are the lanes of the key's MACs K.
    void verify_eval(std::span<const std::span<const Fq>, EXT_DEGREE> k, const Fq16& /*delta*/,
                     std::span<Fq> out) const {
        for (size_t t = 0; t < NUM_INSTANCES; ++t) {
            const size_t n = Lay::key_len(t);
            const size_t ko = Lay::key_offset(t);
            std::vector<Row> x(n);
            for (size_t j = 0; j < n; ++j) {
                for (size_t c = 0; c < EXT_DEGREE; ++c) {
                    x[j][c] = k[c][ko + j];
                }
            }
            const Fq* m = coeffs_[t].data();
            for (size_t b = 0; b < Lay::outputs(t) / BLOCK; ++b) {
                std::array<std::array<uint32_t, 2 * EXT_DEGREE>, BLOCK> acc{};
                for (size_t j = 0; j < n; ++j) {
                    std::array<Lanes, BLOCK> lin;
                    lin_form(m, x.data() + j, n - j, lin, nullptr, nullptr);
                    m += BLOCK * (n - j);
                    for (size_t r = 0; r < BLOCK; ++r) {
                        for (size_t p = 0; p < EXT_DEGREE; ++p) {
                            lin[r][p] %= Q;
                        }
                        mul_acc(acc[r], x[j], lin[r]);
                    }
                    if (j % REDUCE_EVERY == REDUCE_EVERY - 1) {
                        for (auto& a : acc) {
                            for (auto& y : a) {
                                y %= Q;
                            }
                        }
                    }
                }
                for (size_t r = 0; r < BLOCK; ++r) {
                    const size_t o = Lay::output_offset(t) + BLOCK * b + r;
                    for (size_t p = 0; p < EXT_DEGREE; ++p) {
                        out[p * NUM_OUTPUTS + o] = fold(acc[r], p);
                    }
                }
            }
        }
    }

  private:
    using Lanes = std::array<uint32_t, EXT_DEGREE>;
    using Row = std::array<uint16_t, EXT_DEGREE>;

    // For each r < BLOCK: lin[r] = sum_l m[BLOCK l + r] x[l] (unreduced) over count rows, and, if
    // xk, (*linv)[r] = sum_l m[BLOCK l + r] xk[l].
    static void lin_form(const Fq* m, const Row* x, size_t count, std::array<Lanes, BLOCK>& lin,
                         const uint32_t* xk, std::array<uint32_t, BLOCK>* linv) {
#if defined(__aarch64__)
        static_assert(BLOCK == 4);
        uint32x4_t a[BLOCK][4];
        for (auto& set : a) {
            for (auto& r : set) {
                r = vdupq_n_u32(0);
            }
        }
        uint32x4_t v = vdupq_n_u32(0);
        for (size_t l = 0; l < count; ++l) {
            const uint16x4_t c = vld1_u16(m + BLOCK * l);
            const uint16x8_t lo = vld1q_u16(x[l].data());
            const uint16x8_t hi = vld1q_u16(x[l].data() + 8);
            const uint16x4_t lo0 = vget_low_u16(lo), hi0 = vget_low_u16(hi);
#define VOLE_MOLE_MQ_LANE(r)                                                                       \
    a[r][0] = vmlal_lane_u16(a[r][0], lo0, c, r);                                                  \
    a[r][1] = vmlal_high_lane_u16(a[r][1], lo, c, r);                                              \
    a[r][2] = vmlal_lane_u16(a[r][2], hi0, c, r);                                                  \
    a[r][3] = vmlal_high_lane_u16(a[r][3], hi, c, r);
            VOLE_MOLE_MQ_LANE(0)
            VOLE_MOLE_MQ_LANE(1)
            VOLE_MOLE_MQ_LANE(2)
            VOLE_MOLE_MQ_LANE(3)
#undef VOLE_MOLE_MQ_LANE
            if (xk) {
                v = vmlal_n_u16(v, c, static_cast<uint16_t>(xk[l]));
            }
        }
        for (size_t r = 0; r < BLOCK; ++r) {
            for (size_t q = 0; q < 4; ++q) {
                vst1q_u32(lin[r].data() + 4 * q, a[r][q]);
            }
        }
        if (linv) {
            vst1q_u32(linv->data(), v);
        }
#else
        for (auto& x : lin) {
            x = {};
        }
        std::array<uint32_t, BLOCK> v{};
        for (size_t l = 0; l < count; ++l) {
            for (size_t r = 0; r < BLOCK; ++r) {
                const uint32_t c = m[BLOCK * l + r];
                for (size_t p = 0; p < EXT_DEGREE; ++p) {
                    lin[r][p] += c * x[l][p];
                }
                if (xk) {
                    v[r] += c * xk[l];
                }
            }
        }
        if (linv) {
            *linv = v;
        }
#endif
    }

    // Accumulators are reduced every REDUCE_EVERY key elements: each adds at most 16 products
    // < q^2 per coefficient of acc0 (and 2 to acc1).
    static constexpr size_t REDUCE_EVERY = 16;
    static_assert(Q + uint64_t{REDUCE_EVERY} * EXT_DEGREE * (Q - 1) * (Q - 1) <
                  (uint64_t{1} << 32));

    // acc += a * b as polynomials (unreduced), for a, b with coefficients in [0, q).
    static void mul_acc(std::array<uint32_t, 2 * EXT_DEGREE>& acc, const Row& a, const Lanes& b) {
        for (size_t x = 0; x < EXT_DEGREE; ++x) {
            for (size_t y = 0; y < EXT_DEGREE; ++y) {
                acc[x + y] += uint32_t{a[x]} * b[y];
            }
        }
    }

    // Coefficient p of acc mod (X^16 - 3, q).
    static Fq fold(const std::array<uint32_t, 2 * EXT_DEGREE>& acc, size_t p) {
        return static_cast<Fq>(
            (uint64_t{acc[p]} + uint64_t{EXT_MODULUS_CONST} * acc[p + EXT_DEGREE]) % Q);
    }

    std::array<std::vector<Fq>, NUM_INSTANCES> coeffs_;
};

// Commit to the witness directly.
struct NoPrg {};

// Derive the witness with the MQ PRG over F_q, split into `instances` instances.
template <size_t instances> struct MqPrg {
    template <size_t N> using Map = MqMap<N, instances>;
};

} // namespace vole_mole::voleith_fq::detail

#endif
