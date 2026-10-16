// EXPERIMENTAL: a local quadratic PRG over a 256-bit prime field (F_p or F_n of P-256), for
// deriving the witness of a VOLEitH proof over that field from a shorter key (see voleith.hpp), as
// src/mq/local.hpp does for FAEST's binary VOLEitH.
//
// The PRG stretches a key K in F^n into m outputs
//
//   G(K)_i = sum_{t < L} c_{i,t} K_{l_{i,t}} + sum_{s < Q} c'_{i,s} K_{a_{i,s}} K_{b_{i,s}}
//
// where, for each output, the L + 2 Q indices are distinct, and the coefficients are nonzero. The
// indices and coefficients are public and pseudorandom, derived from (tag, n, m): read the stream
// SHAKE128("vole-mole p256 local prg" || tag || le32(n) || le32(m) || le32(L) || le32(Q)); for each
// output, the indices l_{i,1}, ..., l_{i,L}, a_{i,1}, b_{i,1}, ..., a_{i,Q}, b_{i,Q} are the next
// le16 words w mod n, skipping words w >= n floor(2^16 / n) and indices already used by the output;
// then the coefficients c_{i,1}, ..., c_{i,L}, c'_{i,1}, ..., c'_{i,Q} are the next 32-byte strings
// that decode to nonzero field elements (F::from_bytes).
//
// Its security is a different and less studied assumption than that of the dense MQ PRG over
// GF(2); prg_key_len(m) is a rough estimate of the key length it needs (see prg_key_len.hpp and
// tools/fp_prg_key_len.py), NOT a security analysis.
//
// For QuickSilver (qs.hpp), each output of a committed key is an expression of degree 2. The
// prover's coefficients and the verifier's homogeneous evaluation are computed directly here, with
// about 6 Q + 2 L (prover) and 2 Q + L (verifier) multiplications per output.

#ifndef VOLE_MOLE_VOLEITH_P256_PRG_HPP
#define VOLE_MOLE_VOLEITH_P256_PRG_HPP

#include "voleith_p256/prg_key_len.hpp"

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace vole_mole::voleith_p256 {

// The smallest key length in PRG_KEY_LENS for m outputs (0 if there is none).
constexpr size_t prg_key_len(size_t m) {
    for (const auto& e : detail::PRG_KEY_LENS) {
        if (e.max_outputs >= m) {
            return e.key;
        }
    }
    return 0;
}

template <typename F> class LocalPrg {
  public:
    static constexpr size_t MAX_TERMS = 32; // L and Q, for keys of at least 4 MAX_TERMS elements

    LocalPrg(uint8_t tag, size_t n, size_t m)
        : n_(n), m_(m), l_(std::min(MAX_TERMS, n / 4)), q_(std::min(MAX_TERMS, n / 4)) {
        if (n < 8 || n >= 65536) {
            throw std::invalid_argument("LocalPrg: unsupported key length");
        }
        Keccak_HashInstance h;
        Keccak_HashInitialize_SHAKE128(&h);
        constexpr std::string_view DST = "vole-mole p256 local prg";
        Keccak_HashUpdate(&h, reinterpret_cast<const uint8_t*>(DST.data()), 8 * DST.size());
        Keccak_HashUpdate(&h, &tag, 8);
        for (const size_t v : {n, m, l_, q_}) {
            std::array<uint8_t, 4> le;
            for (size_t i = 0; i < 4; ++i) {
                le[i] = static_cast<uint8_t>(v >> (8 * i));
            }
            Keccak_HashUpdate(&h, le.data(), 8 * le.size());
        }
        Keccak_HashFinal(&h, nullptr);

        const size_t per = l_ + 2 * q_;
        const size_t limit = n * (65536 / n);
        idx_.reserve(m * per);
        coef_.reserve(m * (l_ + q_));
        std::vector<uint8_t> used(n, 0);
        for (size_t i = 0; i < m; ++i) {
            const size_t first = idx_.size();
            while (idx_.size() < first + per) {
                std::array<uint8_t, 2> b;
                Keccak_HashSqueeze(&h, b.data(), 16);
                const size_t w = b[0] | (size_t{b[1]} << 8);
                if (w >= limit || used[w % n]) {
                    continue;
                }
                used[w % n] = 1;
                idx_.push_back(static_cast<uint16_t>(w % n));
            }
            for (size_t j = first; j < idx_.size(); ++j) {
                used[idx_[j]] = 0;
            }
            for (size_t j = 0; j < l_ + q_;) {
                std::array<uint8_t, 32> b;
                Keccak_HashSqueeze(&h, b.data(), 8 * b.size());
                const auto c = F::from_bytes(b);
                if (c && !c->is_zero()) {
                    coef_.push_back(*c);
                    ++j;
                }
            }
        }
    }

    size_t key_len() const { return n_; }
    size_t outputs() const { return m_; }

    // G(K)_i.
    F eval(size_t i, std::span<const F> k) const {
        const uint16_t* ix = &idx_[i * (l_ + 2 * q_)];
        const F* c = &coef_[i * (l_ + q_)];
        F acc = F::zero();
        for (size_t t = 0; t < l_; ++t) {
            acc += c[t] * k[ix[t]];
        }
        for (size_t s = 0; s < q_; ++s) {
            acc += c[l_ + s] * k[ix[l_ + 2 * s]] * k[ix[l_ + 2 * s + 1]];
        }
        return acc;
    }

    // For the prover, with the MAC v_j and value k_j of each key element (degree 1): the
    // coefficients (c_0, c_1, c_2) of G(K)_i as an expression of degree 2 (the linear terms lifted
    // by Delta).
    std::array<F, 3> eval_prover(size_t i, std::span<const F> v, std::span<const F> k) const {
        const uint16_t* ix = &idx_[i * (l_ + 2 * q_)];
        const F* c = &coef_[i * (l_ + q_)];
        std::array<F, 3> out{};
        for (size_t t = 0; t < l_; ++t) {
            out[1] += c[t] * v[ix[t]];
            out[2] += c[t] * k[ix[t]];
        }
        for (size_t s = 0; s < q_; ++s) {
            const size_t a = ix[l_ + 2 * s], b = ix[l_ + 2 * s + 1];
            const F ck = c[l_ + s] * k[a], cv = c[l_ + s] * v[a];
            out[0] += cv * v[b];
            out[1] += ck * v[b] + cv * k[b];
            out[2] += ck * k[b];
        }
        return out;
    }

    // For the verifier, with the key MACs K_j = v_j + k_j Delta: Delta^2 G(K / Delta)_i.
    F eval_verifier(size_t i, std::span<const F> key_macs, const F& delta) const {
        const uint16_t* ix = &idx_[i * (l_ + 2 * q_)];
        const F* c = &coef_[i * (l_ + q_)];
        F lin = F::zero(), quad = F::zero();
        for (size_t t = 0; t < l_; ++t) {
            lin += c[t] * key_macs[ix[t]];
        }
        for (size_t s = 0; s < q_; ++s) {
            quad += c[l_ + s] * key_macs[ix[l_ + 2 * s]] * key_macs[ix[l_ + 2 * s + 1]];
        }
        return quad + lin * delta;
    }

  private:
    size_t n_, m_, l_, q_;
    std::vector<uint16_t> idx_;
    std::vector<F> coef_;
};

} // namespace vole_mole::voleith_p256

#endif
