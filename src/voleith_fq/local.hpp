// The local PRG over F_q, q = 3329: Goldreich's PRG with the predicate XOR_L-AND_2 over F_q, for
// deriving a witness from a short key (as an alternative to the dense MQ PRG of mq.hpp). This is
// the F_q analogue of mq/local.hpp. Experimental.
//
// The PRG stretches a key K in F_q^n into N outputs
//
//   G(K)_i = sum_{t < L} c_{i,t} K_{l_{i,t}} + K_{a_i} K_{b_i}
//
// where, for each output, the L + 2 indices are distinct and the coefficients c_{i,t} are nonzero;
// all are public and derived from a DST. (A coefficient on the product would be redundant: dividing
// by it only rescales the linear part.) Key lengths: see local_key_len.hpp. With the dense MQ
// estimate as a floor (DenseFloor = true), they're those of the dense MQ PRG.
//
// Indices and coefficients: read the elements of F_q sampled as in mq_expand_coefficients, in
// chunks of 4096 with t = 0x100, 0x101, ..., as a stream. For output i, in order:
// l_{i,0}, ..., l_{i,L-1}, a_i, b_i, each the next element w mod n, skipping elements
// w >= n floor(q / n) and indices already used by output i; then c_{i,0}, ..., c_{i,L-1}, each the
// next nonzero element.
//
// Committed evaluation: The linear part is a committed value of degree 1, lifted to degree 2 by
// multiplying it by Delta. With K_j = V_j + k_j Delta,
//
//   G(K)_i = V_a V_b + (V_a k_b + k_a V_b + sum_t c_t V_{l_t}) Delta + G(k)_i Delta^2,
//
// so each output costs one product in F_{q^16} and L + 2 scalar products for the prover, and the
// verifier computes Delta sum_t c_t K_{l_t} + K_a K_b.

#ifndef VOLE_MOLE_VOLEITH_FQ_LOCAL_HPP
#define VOLE_MOLE_VOLEITH_FQ_LOCAL_HPP

#include "voleith_fq/field.hpp"
#include "voleith_fq/local_key_len.hpp"
#include "voleith_fq/mq.hpp"
#include "voleith_fq/mq_key_len.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::voleith_fq::detail {

constexpr size_t LOCAL_LINEAR_TERMS = 16;

constexpr size_t local_key_len(size_t num_outputs, bool dense_floor) {
    const auto& table = dense_floor ? std::span<const MqKeyLenEntry>(LOCAL_KEY_LEN_TABLE_DENSE)
                                    : std::span<const MqKeyLenEntry>(LOCAL_KEY_LEN_TABLE_GD);
    for (const MqKeyLenEntry& e : table) {
        if (num_outputs <= e.max_outputs) {
            return e.key_len;
        }
    }
    throw std::invalid_argument("local PRG over F_q: too many outputs");
}

template <size_t NUM_OUTPUTS, size_t KEY_LEN_> class LocalMap {
  public:
    static constexpr size_t NUM_OUTPUTS_V = NUM_OUTPUTS;
    static constexpr size_t KEY_LEN = KEY_LEN_;
    static constexpr size_t L = LOCAL_LINEAR_TERMS;
    static_assert(KEY_LEN % 2 == 0 && KEY_LEN >= L + 2 && KEY_LEN < Q);

    explicit LocalMap(std::span<const uint8_t> dst) {
        // Generously sized stream; refilled if it runs out.
        std::vector<Fq> stream;
        size_t pos = 0, chunk = 0;
        auto next = [&]() -> Fq {
            if (pos == stream.size()) {
                stream.resize(4096);
                mq_expand_coefficients(dst, KEY_LEN, NUM_OUTPUTS, 0x100 + chunk++, stream);
                pos = 0;
            }
            return stream[pos++];
        };
        const uint32_t bound = KEY_LEN * (Q / KEY_LEN);
        for (auto& o : outputs_) {
            std::array<uint16_t, L + 2> idx;
            for (size_t t = 0; t < L + 2; ++t) {
                for (;;) {
                    const uint32_t w = next();
                    if (w >= bound) {
                        continue;
                    }
                    const auto j = static_cast<uint16_t>(w % KEY_LEN);
                    if (std::find(idx.begin(), idx.begin() + t, j) == idx.begin() + t) {
                        idx[t] = j;
                        break;
                    }
                }
            }
            std::copy_n(idx.begin(), L, o.lin.begin());
            o.a = idx[L];
            o.b = idx[L + 1];
            for (auto& c : o.coeff) {
                do {
                    c = next();
                } while (c == 0);
            }
        }
    }

    void eval(std::span<const Fq, KEY_LEN> key, std::span<Fq, NUM_OUTPUTS> out) const {
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            const Output& o = outputs_[i];
            uint32_t acc = uint32_t{key[o.a]} * key[o.b];
            for (size_t t = 0; t < L; ++t) {
                acc += uint32_t{o.coeff[t]} * key[o.lin[t]];
            }
            out[i] = fq_reduce(acc);
        }
    }

    void prove_eval(std::span<const std::span<const Fq>, EXT_DEGREE> v, std::span<const Fq> key,
                    std::span<Fq> c0, std::span<Fq> c1, std::span<Fq> c2) const {
        std::vector<Fq16> vm(KEY_LEN);
        for (size_t j = 0; j < KEY_LEN; ++j) {
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                vm[j].c[p] = v[p][j];
            }
        }
        static_assert(uint64_t{L + 2} * (Q - 1) * (Q - 1) < (uint64_t{1} << 32));
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            const Output& o = outputs_[i];
            const Fq16 a0 = vm[o.a] * vm[o.b];
            std::array<uint32_t, EXT_DEGREE> a1;
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                a1[p] = uint32_t{vm[o.a].c[p]} * key[o.b] + uint32_t{key[o.a]} * vm[o.b].c[p];
            }
            uint32_t a2 = uint32_t{key[o.a]} * key[o.b];
            for (size_t t = 0; t < L; ++t) {
                const uint32_t c = o.coeff[t];
                const Fq16& x = vm[o.lin[t]];
                for (size_t p = 0; p < EXT_DEGREE; ++p) {
                    a1[p] += c * x.c[p];
                }
                a2 += c * key[o.lin[t]];
            }
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                c0[p * NUM_OUTPUTS + i] = a0.c[p];
                c1[p * NUM_OUTPUTS + i] = fq_reduce(a1[p]);
            }
            c2[i] = fq_reduce(a2);
        }
    }

    void verify_eval(std::span<const std::span<const Fq>, EXT_DEGREE> k, const Fq16& delta,
                     std::span<Fq> out) const {
        std::vector<Fq16> km(KEY_LEN);
        for (size_t j = 0; j < KEY_LEN; ++j) {
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                km[j].c[p] = k[p][j];
            }
        }
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            const Output& o = outputs_[i];
            std::array<uint32_t, EXT_DEGREE> lin{};
            for (size_t t = 0; t < L; ++t) {
                const uint32_t c = o.coeff[t];
                for (size_t p = 0; p < EXT_DEGREE; ++p) {
                    lin[p] += c * km[o.lin[t]].c[p];
                }
            }
            Fq16 l;
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                l.c[p] = fq_reduce(lin[p]);
            }
            const Fq16 r = l * delta + km[o.a] * km[o.b];
            for (size_t p = 0; p < EXT_DEGREE; ++p) {
                out[p * NUM_OUTPUTS + i] = r.c[p];
            }
        }
    }

  private:
    struct Output {
        std::array<uint16_t, L> lin;
        std::array<Fq, L> coeff;
        uint16_t a, b;
    };
    std::array<Output, NUM_OUTPUTS> outputs_;
};

// Derive the witness with the local PRG over F_q. If DenseFloor, its key is as long as the dense MQ
// PRG's; otherwise it only accounts for guess and determine (NOT a security estimate).
template <bool DenseFloor = true> struct LocalPrg {
    template <size_t N> using Map = LocalMap<N, local_key_len(N, DenseFloor)>;
};

} // namespace vole_mole::voleith_fq::detail

#endif
