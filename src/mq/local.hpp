// The local PRG: a pseudorandom generator of degree 2 over GF(2) in which each output depends on a
// constant number of key bits, for deriving witness bits from a short key (as an alternative to the
// dense MQ PRG of prg.hpp; see LocalPrg in witness_prg.hpp).
//
// The PRG stretches a key K of n bits into N output bits
//
//   G(K)_i = sum_{t <= L} K_{l_{i,t}} + sum_{s <= q} K_{a_{i,s}} K_{b_{i,s}}
//
// where, for each output, the L + 2q indices are distinct, public, and derived from a domain
// separation tag (DST). For q = 1, this is Goldreich's PRG with the predicate XOR_L-AND_2; for q >
// 1 it's a sparse random quadratic system. Its security is a different (and less studied)
// assumption than that of the dense MQ PRG; local_key_bits(N, q) is a rough estimate of the key
// length it needs (see local_key_bits.hpp and tools/local_key_bits.py), NOT a security analysis.
//
// Unlike the dense MQ PRG, whose committed evaluation costs about n^2 / 16 table lookups per output
// (and n grows with N), each output costs q products and L + q additions of committed bits.
//
// Indices: Let AES_KEY = SHAKE128(dst || "local" || le32(n) || le32(N) || le32(L) ||
// le32(q))[0..16], and read the key stream of AES4-CTR (see prg.hpp: block b is AES4(AES_KEY,
// le64(b) || 0^8)) as a sequence of le16 words. The indices are l_{0,1}, ..., l_{0,L}, a_{0,1},
// b_{0,1}, ..., a_{0,q}, b_{0,q}, l_{1,1}, ...: each is the next word w mod n, where words w >= n
// floor(2^16 / n) and indices already used by the same output are skipped.

#ifndef VOLE_MOLE_MQ_LOCAL_HPP
#define VOLE_MOLE_MQ_LOCAL_HPP

#include "mq/key_bits.hpp"
#include "mq/local_key_bits.hpp"
#include "mq/prg.hpp"

#include "aes.hpp"         // from faest-arch-opt
#include "aes_defs.hpp"    // from faest-arch-opt
#include "block.hpp"       // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <vector>

namespace vole_mole::mq::detail {

// The number of linear terms of each output of the local PRG.
constexpr size_t LOCAL_LINEAR_TERMS = 16;

// The smallest key length for which the local PRG with `num_outputs` outputs and `ands` products is
// estimated to be secure (see local_key_bits.hpp).
constexpr size_t local_key_bits(size_t num_outputs, size_t ands) {
    auto lookup = [&](const auto& table) {
        for (const KeyBitsEntry& e : table) {
            if (num_outputs <= e.max_outputs) {
                return e.key_bits;
            }
        }
        throw std::invalid_argument("local PRG: too many outputs"); // not a constant expression
    };
    switch (ands) {
    case 1:
        return lookup(LOCAL_KEY_BITS_TABLE_1);
    case 2:
        return lookup(LOCAL_KEY_BITS_TABLE_2);
    case 4:
        return lookup(LOCAL_KEY_BITS_TABLE_4);
    default:
        throw std::invalid_argument("local PRG: unsupported number of products");
    }
}

template <size_t KEY_BITS_, size_t NUM_OUTPUTS, size_t LINEAR, size_t ANDS> class LocalMap {
  public:
    static constexpr size_t KEY_BITS = KEY_BITS_;
    static constexpr size_t KEY_BYTES = KEY_BITS / 8;
    static constexpr size_t num_outputs_v = NUM_OUTPUTS;
    static constexpr size_t OUTPUT_BYTES = NUM_OUTPUTS / 8;
    static constexpr size_t TERMS = LINEAR + 2 * ANDS; // indices per output

    static_assert(KEY_BITS % 8 == 0 && KEY_BITS >= TERMS && KEY_BITS < (1u << 16));
    static_assert(NUM_OUTPUTS % 8 == 0 && NUM_OUTPUTS > 0);
    static_assert(LINEAR >= 2 && ANDS >= 1);

    explicit LocalMap(std::span<const uint8_t> dst) : idx_(TERMS * NUM_OUTPUTS) {
        faest::hash_state hasher;
        hasher.init(faest::secpar::s128);
        hasher.update(dst);
        const std::array<uint8_t, 5> label = {'l', 'o', 'c', 'a', 'l'};
        hasher.update(label);
        std::array<uint8_t, 16> sizes;
        const std::array<uint32_t, 4> vals = {KEY_BITS, NUM_OUTPUTS, LINEAR, ANDS};
        for (size_t v = 0; v < 4; ++v) {
            for (size_t i = 0; i < 4; ++i) {
                sizes[4 * v + i] = static_cast<uint8_t>(vals[v] >> (8 * i));
            }
        }
        hasher.update(sizes);
        std::array<uint8_t, 16> key;
        hasher.finalize(key);
        faest::aes_round_keys<faest::secpar::s128> aes;
        faest::aes_keygen<faest::secpar::s128>(&aes, faest::block128::load(key.data()));
        Aes4RoundKeys rk;
        std::copy_n(aes.keys, rk.size(), rk.begin());

        constexpr uint32_t LIMIT = KEY_BITS * ((uint32_t{1} << 16) / KEY_BITS);
        constexpr size_t BATCH = 8;
        std::array<uint8_t, 16 * BATCH> buf;
        size_t pos = buf.size();
        uint64_t block = 0;
        auto next_word = [&]() -> uint32_t {
            if (pos == buf.size()) {
                std::array<faest::block128, BATCH> blocks;
                for (size_t t = 0; t < BATCH; ++t) {
                    blocks[t] = faest::block128::set_64(block++, 0);
                }
                aes4_ecb<BATCH>(rk, blocks.data());
                for (size_t t = 0; t < BATCH; ++t) {
                    blocks[t].store(buf.data() + 16 * t);
                }
                pos = 0;
            }
            const uint32_t w = buf[pos] | (uint32_t{buf[pos + 1]} << 8);
            pos += 2;
            return w;
        };
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            uint16_t* out = idx_.data() + TERMS * i;
            for (size_t t = 0; t < TERMS;) {
                const uint32_t w = next_word();
                if (w >= LIMIT) {
                    continue;
                }
                const auto j = static_cast<uint16_t>(w % KEY_BITS);
                if (std::find(out, out + t, j) != out + t) {
                    continue;
                }
                out[t++] = j;
            }
        }
    }

    // The indices of output i: L linear terms, then q pairs.
    std::span<const uint16_t, TERMS> indices(size_t i) const {
        return std::span<const uint16_t, TERMS>(idx_.data() + TERMS * i, TERMS);
    }

    // Evaluate the PRG on a plaintext key.
    void eval(std::span<const uint8_t, KEY_BYTES> key, std::span<uint8_t, OUTPUT_BYTES> out) const {
        auto bit = [&](size_t j) { return (key[j / 8] >> (j % 8)) & 1; };
        std::ranges::fill(out, uint8_t{0});
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            const auto ix = indices(i);
            unsigned y = 0;
            for (size_t t = 0; t < LINEAR; ++t) {
                y ^= bit(ix[t]);
            }
            for (size_t s = 0; s < ANDS; ++s) {
                y ^= bit(ix[LINEAR + 2 * s]) & bit(ix[LINEAR + 2 * s + 1]);
            }
            out[i / 8] |= static_cast<uint8_t>(y << (i % 8));
        }
    }

    // Evaluate the PRG on a committed key and add the public vector `e` (as mq::detail::qs_eval).
    template <typename QS>
    std::vector<qs_bit<QS, DEGREE>> qs_eval(std::span<const qs_bit<QS, 1>, KEY_BITS> key,
                                            std::span<const uint8_t, OUTPUT_BYTES> e) const {
        using qs_1 = qs_bit<QS, 1>;
        using qs_2 = qs_bit<QS, DEGREE>;
        std::vector<qs_2> out;
        if constexpr (requires { key[0].value_; }) {
            // The prover. A committed bit of degree 1 is A + a_v X, with the MAC A and the value
            // a_v (a byte 0x00 or 0xff), and a b = A B + (b_v A + a_v B) X + a_v b_v X^2 (see
            // qs_mul), so the outputs' products A B are summed before a single reduction. The key
            // is copied into separate arrays of MACs and values, which are smaller than the
            // padded bits, for the random accesses.
            static_assert(DEGREE == 2);
            using mac_t = std::remove_cvref_t<decltype(key[0].mac.coeffs[0])>;
            std::vector<mac_t> km(KEY_BITS);
            std::vector<uint8_t> kv(KEY_BITS);
            for (size_t j = 0; j < KEY_BITS; ++j) {
                km[j] = key[j].mac.coeffs[0];
                kv[j] = key[j].value().data;
            }
            out.resize(NUM_OUTPUTS, qs_2(static_cast<const QS*>(nullptr)));
            for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
                const auto ix = indices(i);
                mac_t l0 = km[ix[0]], l1 = km[ix[1]];
                uint8_t lv = kv[ix[0]] ^ kv[ix[1]];
                size_t t = 2;
                for (; t + 2 <= LINEAR; t += 2) {
                    l0 = l0 + km[ix[t]];
                    l1 = l1 + km[ix[t + 1]];
                    lv ^= kv[ix[t]] ^ kv[ix[t + 1]];
                }
                for (; t < LINEAR; ++t) {
                    l0 = l0 + km[ix[t]];
                    lv ^= kv[ix[t]];
                }
                mac_t m1 = l0 + l1;
                auto prod = km[ix[LINEAR]] * km[ix[LINEAR + 1]];
                for (size_t s = 0; s < ANDS; ++s) {
                    const size_t a = ix[LINEAR + 2 * s], b = ix[LINEAR + 2 * s + 1];
                    if (s > 0) {
                        prod = prod + km[a] * km[b];
                    }
                    m1 = m1 + faest::poly1::set_all(kv[b]) * km[a] +
                         faest::poly1::set_all(kv[a]) * km[b];
                    lv ^= kv[a] & kv[b];
                }
                qs_2 y(static_cast<const QS*>(nullptr));
                y.mac.coeffs[0] = prod.template reduce_to<QS::secpar_bits>();
                y.mac.coeffs[1] = m1;
                y.value() = faest::poly1::set_all(lv) + faest::poly1((e[i / 8] >> (i % 8)) & 1);
                out[i] = y;
            }
            return out;
        }
        out.reserve(NUM_OUTPUTS);
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            const auto ix = indices(i);
            // Independent accumulators, so that the additions don't form a single chain.
            qs_1 l0 = key[ix[0]];
            qs_1 l1 = key[ix[1]];
            size_t t = 2;
            for (; t + 2 <= LINEAR; t += 2) {
                l0 += key[ix[t]];
                l1 += key[ix[t + 1]];
            }
            for (; t < LINEAR; ++t) {
                l0 += key[ix[t]];
            }
            qs_2 y = qs_2(l0 + l1); // raise the degree (for the verifier, a product with Delta)
            for (size_t s = 0; s < ANDS; ++s) {
                y += qs_mul<QS, 1, 1>(key[ix[LINEAR + 2 * s]], key[ix[LINEAR + 2 * s + 1]]);
            }
            out.push_back(y + faest::poly1((e[i / 8] >> (i % 8)) & 1));
        }
        return out;
    }

  private:
    std::vector<uint16_t> idx_;
};

} // namespace vole_mole::mq::detail

#endif
