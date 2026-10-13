// The MQ PRG: a pseudorandom generator of degree 2 over GF(2), for deriving witness bits from a
// short key.
//
// The PRG stretches a key K of n bits into N output bits
//
//   G(K)_i = sum_{j <= k} m_{ijk} K_j K_k    (i in [N])
//
// where the coefficients m_{ijk} are public and derived from a domain separation tag (DST). Since
// K_j^2 = K_j over GF(2), the diagonal coefficients m_{ijj} are the linear part of the quadratic
// form. G is a PRG if the N equations G(K) = y in n unknowns are hard to solve (and distinguish
// from random) for a random key, which is the MQ problem over GF(2) for an overdetermined system.
// key_bits(N) is the smallest n for which this is estimated to cost 2^128 (see key_bits.hpp).
//
// Coefficients: The coefficients of output i are the upper triangle of an n x n matrix of bits
// M_i, stored row by row: row j consists of the bytes j / 8, ..., n / 8 - 1 of the row, with
// m_{ijk} at bit k % 8 of byte k / 8, and the bits k < j of its first byte are ignored. (So each
// row starts at a byte boundary.) The packed matrices are MATRIX_BYTES long, i.e., padded to a
// whole number of 16-byte blocks, and M_0, M_1, ... are consecutive in the key stream of AES4-CTR
// with key AES_KEY = SHAKE128(dst || le32(n) || le32(N))[0..16]: block b of the key stream is
// AES4(AES_KEY, le64(b) || 0^8).
//
// AES4 is AES-128 reduced to 4 rounds, as UOV uses to expand the public key (its _4ROUND_AES_
// option): round keys 0, ..., 4 of the AES-128 key schedule, an initial AddRoundKey, three full
// rounds, and a final round without MixColumns. As in UOV, it only expands public inputs, so it
// only has to produce a random-looking (nothing up my sleeve) instance, not resist key recovery.
//
// Committed evaluation: If the bits of K are committed values of degree 1, then G(K)_i is a
// committed value of degree 2. We evaluate it as sum_j K_j * L_ij, where L_ij = sum_{k >= j}
// m_{ijk} K_k is linear in K, so it costs n products per output. The linear forms are computed
// with the method of four Russians: for each chunk of 8 bits of K, we tabulate the sums of all
// 256 subsets of the chunk, so that each L_ij is a sum of n / 8 table entries.

#ifndef VOLE_MOLE_MQ_PRG_HPP
#define VOLE_MOLE_MQ_PRG_HPP

#include "mq/key_bits.hpp"
#include "qs_bit.hpp"

#include "aes.hpp"         // from faest-arch-opt
#include "aes_defs.hpp"    // from faest-arch-opt
#include "block.hpp"       // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::mq::detail {

// The degree of the outputs of the PRG in the key.
constexpr size_t DEGREE = 2;

// The number of rounds of AES4 and its round keys.
constexpr size_t AES4_ROUNDS = 4;
using Aes4RoundKeys = std::array<faest::block128, AES4_ROUNDS + 1>;

// Encrypt the blocks in `data` with AES4 (see above).
template <size_t NUM_BLOCKS>
inline void aes4_ecb(const Aes4RoundKeys& rk, faest::block128* __restrict__ data) {
#if defined(__aarch64__)
    // aese is AddRoundKey, SubBytes, ShiftRows; aesmc is MixColumns.
    for (size_t r = 0; r + 1 < AES4_ROUNDS; ++r) {
        const uint8x16_t k = vreinterpretq_u8_u32(rk[r].data);
        for (size_t i = 0; i < NUM_BLOCKS; ++i) {
            data[i].data =
                vreinterpretq_u32_u8(vaesmcq_u8(vaeseq_u8(vreinterpretq_u8_u32(data[i].data), k)));
        }
    }
    const uint8x16_t k3 = vreinterpretq_u8_u32(rk[AES4_ROUNDS - 1].data);
    const uint8x16_t k4 = vreinterpretq_u8_u32(rk[AES4_ROUNDS].data);
    for (size_t i = 0; i < NUM_BLOCKS; ++i) {
        data[i].data =
            vreinterpretq_u32_u8(veorq_u8(vaeseq_u8(vreinterpretq_u8_u32(data[i].data), k3), k4));
    }
#elif defined(__AES__)
    // aesenc is SubBytes, ShiftRows, MixColumns, AddRoundKey; aesenclast omits MixColumns.
    for (size_t i = 0; i < NUM_BLOCKS; ++i) {
        data[i].data = _mm_xor_si128(data[i].data, rk[0].data);
    }
    for (size_t r = 1; r < AES4_ROUNDS; ++r) {
        for (size_t i = 0; i < NUM_BLOCKS; ++i) {
            data[i].data = _mm_aesenc_si128(data[i].data, rk[r].data);
        }
    }
    for (size_t i = 0; i < NUM_BLOCKS; ++i) {
        data[i].data = _mm_aesenclast_si128(data[i].data, rk[AES4_ROUNDS].data);
    }
#else
#error "AES4 needs AES instructions"
#endif
}

// The smallest key length (in bits) for which the PRG with `num_outputs` outputs is estimated to
// be secure. Fails to compile (in a constant expression) if no key length in the table suffices.
constexpr size_t key_bits(size_t num_outputs) {
    for (const KeyBitsEntry& e : KEY_BITS_TABLE) {
        if (num_outputs <= e.max_outputs) {
            return e.key_bits;
        }
    }
    throw std::invalid_argument("MQ PRG: too many outputs"); // not a constant expression
}

// The public map of the MQ PRG with `KEY_BITS` key bits and `NUM_OUTPUTS` output bits.
template <size_t KEY_BITS, size_t NUM_OUTPUTS> class PublicMap {
  public:
    static constexpr size_t key_bits_v = KEY_BITS;
    static constexpr size_t num_outputs_v = NUM_OUTPUTS;
    static constexpr size_t KEY_BYTES = KEY_BITS / 8;
    static constexpr size_t OUTPUT_BYTES = NUM_OUTPUTS / 8;
    static constexpr size_t ROW_BYTES = KEY_BITS / 8; // of a full row

    // Offset of row j in a packed matrix; ROW_OFFSET[KEY_BITS] is the packed length.
    static constexpr std::array<size_t, KEY_BITS + 1> ROW_OFFSET = [] {
        std::array<size_t, KEY_BITS + 1> out{};
        for (size_t j = 0; j < KEY_BITS; ++j) {
            out[j + 1] = out[j] + ROW_BYTES - j / 8;
        }
        return out;
    }();
    static constexpr size_t MATRIX_BLOCKS = (ROW_OFFSET[KEY_BITS] + 15) / 16;
    static constexpr size_t MATRIX_BYTES = 16 * MATRIX_BLOCKS;

    static_assert(KEY_BITS % 8 == 0 && KEY_BITS > 0);
    static_assert(NUM_OUTPUTS % 8 == 0 && NUM_OUTPUTS > 0);

    using Matrix = std::array<uint8_t, MATRIX_BYTES>;

    // Row j of a packed matrix, i.e., the bytes j / 8, ..., ROW_BYTES - 1 of the full row.
    static const uint8_t* row(const Matrix& m, size_t j) { return m.data() + ROW_OFFSET[j]; }

    // Derive the public map from a domain separation tag.
    explicit PublicMap(std::span<const uint8_t> dst) {
        faest::hash_state hasher;
        hasher.init(faest::secpar::s128);
        hasher.update(dst);
        const std::array<uint8_t, 8> sizes = {
            static_cast<uint8_t>(KEY_BITS),          static_cast<uint8_t>(KEY_BITS >> 8),
            static_cast<uint8_t>(KEY_BITS >> 16),    static_cast<uint8_t>(KEY_BITS >> 24),
            static_cast<uint8_t>(NUM_OUTPUTS),       static_cast<uint8_t>(NUM_OUTPUTS >> 8),
            static_cast<uint8_t>(NUM_OUTPUTS >> 16), static_cast<uint8_t>(NUM_OUTPUTS >> 24)};
        hasher.update(sizes);
        std::array<uint8_t, 16> key;
        hasher.finalize(key);
        // The round keys of AES4 are the first round keys of AES-128.
        faest::aes_round_keys<faest::secpar::s128> aes;
        faest::aes_keygen<faest::secpar::s128>(&aes, faest::block128::load(key.data()));
        std::copy_n(aes.keys, rk_.size(), rk_.begin());
    }

    // Write the (packed) coefficient matrix M_i of output i to `out`.
    void matrix(size_t i, Matrix& out) const {
        constexpr size_t BATCH = 8;
        std::array<faest::block128, BATCH> blocks;
        const uint64_t first = static_cast<uint64_t>(i) * MATRIX_BLOCKS;
        size_t b = 0;
        for (; b + BATCH <= MATRIX_BLOCKS; b += BATCH) {
            for (size_t t = 0; t < BATCH; ++t) {
                blocks[t] = faest::block128::set_64(first + b + t, 0); // le64(b) || 0^8
            }
            aes4_ecb<BATCH>(rk_, blocks.data());
            for (size_t t = 0; t < BATCH; ++t) {
                blocks[t].store(out.data() + 16 * (b + t));
            }
        }
        for (; b < MATRIX_BLOCKS; ++b) {
            blocks[0] = faest::block128::set_64(first + b, 0);
            aes4_ecb<1>(rk_, blocks.data());
            blocks[0].store(out.data() + 16 * b);
        }
    }

  private:
    Aes4RoundKeys rk_;
};

// Evaluate the PRG on a plaintext key, writing output bit i to bit i % 8 of byte i / 8 of `out`.
template <size_t KEY_BITS, size_t NUM_OUTPUTS>
void eval(const PublicMap<KEY_BITS, NUM_OUTPUTS>& map, std::span<const uint8_t, KEY_BITS / 8> key,
          std::span<uint8_t, NUM_OUTPUTS / 8> out) {
    using Map = PublicMap<KEY_BITS, NUM_OUTPUTS>;
    constexpr size_t WORDS = (KEY_BITS + 63) / 64;

    std::array<uint64_t, WORDS> k{};
    std::memcpy(k.data(), key.data(), KEY_BITS / 8); // little endian

    std::fill(out.begin(), out.end(), uint8_t{0});
    auto m = std::make_unique<typename Map::Matrix>();
    for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
        map.matrix(i, *m);
        uint64_t acc = 0;
        for (size_t j = 0; j < KEY_BITS; ++j) {
            if (((key[j / 8] >> (j % 8)) & 1) == 0) {
                continue;
            }
            // The full row, with the coefficients k < j zeroed.
            std::array<uint64_t, WORDS> row{};
            std::memcpy(reinterpret_cast<uint8_t*>(row.data()) + j / 8, Map::row(*m, j),
                        Map::ROW_BYTES - j / 8);
            row[j / 64] &= ~uint64_t{0} << (j % 64);
            for (size_t w = j / 64; w < WORDS; ++w) {
                acc ^= row[w] & k[w];
            }
        }
        out[i / 8] |= static_cast<uint8_t>((std::popcount(acc) & 1) << (i % 8));
    }
}

using vole_mole::detail::qs_bit;
using vole_mole::detail::qs_mul;

// Generic committed evaluation (see qs_eval), for any QuickSilver implementation.
template <typename QS, size_t KEY_BITS, size_t NUM_OUTPUTS>
std::vector<qs_bit<QS, DEGREE>> qs_eval_generic(const PublicMap<KEY_BITS, NUM_OUTPUTS>& map,
                                                std::span<const qs_bit<QS, 1>, KEY_BITS> key,
                                                std::span<const uint8_t, NUM_OUTPUTS / 8> e) {
    using Map = PublicMap<KEY_BITS, NUM_OUTPUTS>;
    using qs_1 = qs_bit<QS, 1>;
    using qs_2 = qs_bit<QS, 2>;
    constexpr size_t CHUNKS = KEY_BITS / 8;

    const qs_1 zero_1 = key[0] + key[0];
    const qs_2 zero_2 = qs_mul<QS, 1, 1>(zero_1, zero_1);

    // table[256 * c + b] is the sum of the bits 8c + t of the key for the bits t set in b.
    std::vector<qs_1> table(256 * CHUNKS, zero_1);
    for (size_t c = 0; c < CHUNKS; ++c) {
        for (size_t b = 1; b < 256; ++b) {
            const size_t low_bit = b & (~b + 1);
            table[256 * c + b] = table[256 * c + (b ^ low_bit)] +
                                 key[8 * c + static_cast<size_t>(std::countr_zero(low_bit))];
        }
    }

    std::vector<qs_2> out;
    out.reserve(NUM_OUTPUTS);
    auto m = std::make_unique<typename Map::Matrix>();
    for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
        map.matrix(i, *m);
        qs_2 y = zero_2;
        for (size_t j = 0; j < KEY_BITS; ++j) {
            const uint8_t* row = Map::row(*m, j); // bytes c0, ..., CHUNKS - 1 of the full row
            const size_t c0 = j / 8;
            // L_ij = sum_{k >= j} m_{ijk} K_k
            qs_1 l = table[256 * c0 + (row[0] & (0xffu << (j % 8)) & 0xffu)];
            for (size_t c = c0 + 1; c < CHUNKS; ++c) {
                l += table[256 * c + row[c - c0]];
            }
            y += qs_mul<QS, 1, 1>(key[j], l);
        }
        out.push_back(y + faest::poly1((e[i / 8] >> (i % 8)) & 1));
    }
    return out;
}

template <typename QS> constexpr bool is_faest_qs_128 = false;
template <bool verifier, size_t max_deg>
constexpr bool is_faest_qs_128<faest::quicksilver_state<faest::secpar::s128, verifier, max_deg>> =
    true;

// Committed evaluation for faest-arch-opt's QuickSilver, on the raw MACs.
//
// A committed bit of degree 1 is, for the prover, A + v X, where A in GF(2^128) is its MAC and v
// its value, and for the verifier, its MAC A + v Delta. The sum of bits is the sum of the MACs
// and values. For a key bit K_j = A_j + v_j X and L_ij = B + u X, the product is
// A_j B + (v_j B + u A_j) X + v_j u X^2 (as in qs_mul), and for the verifier, it's the product of
// the MACs. So both need the MAC parts B of L_ij, which we compute with the method of four Russians
// on tables of MACs only, and the products A_j B, which we sum before reducing them. The prover
// also needs the value u of L_ij, which it computes from the plaintext key.
template <typename QS, size_t KEY_BITS, size_t NUM_OUTPUTS>
std::vector<qs_bit<QS, DEGREE>> qs_eval_fast(const PublicMap<KEY_BITS, NUM_OUTPUTS>& map,
                                             std::span<const qs_bit<QS, 1>, KEY_BITS> key,
                                             std::span<const uint8_t, NUM_OUTPUTS / 8> e) {
    using Map = PublicMap<KEY_BITS, NUM_OUTPUTS>;
    using faest::poly128;
    using faest::poly256;
    constexpr bool prover = !QS::is_verifier;
    constexpr size_t CHUNKS = KEY_BITS / 8;
    constexpr size_t WORDS = (KEY_BITS + 63) / 64;

    // The MACs of the key bits, and (for the prover) the key, with zero padding so that a row can
    // be read 8 bytes at a time.
    std::vector<poly128> a(KEY_BITS);
    std::array<uint8_t, 8 * WORDS + 8> k{};
    for (size_t j = 0; j < KEY_BITS; ++j) {
        if constexpr (prover) {
            a[j] = key[j].mac.coeffs[0];
            k[j / 8] |= static_cast<uint8_t>((key[j].value().data & 1) << (j % 8));
        } else {
            a[j] = key[j].mac;
        }
    }

    // table[256 * c + b] is the sum of the MACs of the bits 8c + t of the key for the bits t in b.
    std::vector<poly128> table(256 * CHUNKS);
    for (size_t c = 0; c < CHUNKS; ++c) {
        table[256 * c] = poly128::set_zero();
        for (size_t b = 1; b < 256; ++b) {
            const size_t low_bit = b & (~b + 1);
            table[256 * c + b] = table[256 * c + (b ^ low_bit)] +
                                 a[8 * c + static_cast<size_t>(std::countr_zero(low_bit))];
        }
    }

    // A template for the outputs, with the right verifier state.
    const qs_bit<QS, 1> zero_1 = key[0] + key[0];
    const qs_bit<QS, DEGREE> zero_2 = qs_mul<QS, 1, 1>(zero_1, zero_1);

    std::vector<qs_bit<QS, DEGREE>> out;
    out.reserve(NUM_OUTPUTS);
    // The matrix, followed by 8 bytes of padding so that a row can be read 8 bytes at a time.
    struct PaddedMatrix {
        typename Map::Matrix m;
        std::array<uint8_t, 8> pad;
    };
    auto pm = std::make_unique<PaddedMatrix>();
    const poly128 zero = poly128::set_zero();
    for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
        map.matrix(i, pm->m);
        poly256 y0 = poly256::set_zero(); // sum of A_j B, unreduced
        poly128 y1 = zero;                // sum of v_j B + u A_j (prover only)
        uint64_t yv = 0;                  // sum of v_j u (prover only)
        for (size_t j = 0; j < KEY_BITS; ++j) {
            const uint8_t* row = Map::row(pm->m, j);
            const size_t c0 = j / 8;
            const size_t len = CHUNKS - c0;
            const uint8_t first = row[0] & static_cast<uint8_t>(0xffu << (j % 8));
            const poly128* t = table.data() + 256 * c0;

            // Independent accumulators, so that the additions don't form a single chain.
            poly128 l0 = t[first];
            poly128 l1 = zero;
            poly128 l2 = zero;
            poly128 l3 = zero;
            size_t c = 1;
            for (; c + 4 <= len; c += 4) {
                l0 += t[256 * c + row[c]];
                l1 += t[256 * (c + 1) + row[c + 1]];
                l2 += t[256 * (c + 2) + row[c + 2]];
                l3 += t[256 * (c + 3) + row[c + 3]];
            }
            for (; c < len; ++c) {
                l0 += t[256 * c + row[c]];
            }
            const poly128 l = (l0 + l1) + (l2 + l3);
            y0 += a[j] * l;

            if constexpr (prover) {
                // u = parity of the row (with the bits k < j of the first byte cleared) and the
                // key.
                uint64_t acc = static_cast<uint64_t>(first & k[c0]);
                for (size_t w = 1; w < len; w += 8) {
                    uint64_t rw;
                    uint64_t kw;
                    std::memcpy(&rw, row + w, 8);
                    std::memcpy(&kw, k.data() + c0 + w, 8);
                    if (len - w < 8) {
                        rw &= (uint64_t{1} << (8 * (len - w))) - 1;
                    }
                    acc ^= rw & kw;
                }
                const uint64_t u = static_cast<uint64_t>(std::popcount(acc) & 1);
                const uint64_t vj = (k[j / 8] >> (j % 8)) & 1;
                // Constant time: poly1 * poly128 is a mask.
                y1 += faest::poly1(vj) * l;
                y1 += faest::poly1(u) * a[j];
                yv ^= vj & u;
            }
        }

        qs_bit<QS, DEGREE> o = zero_2;
        if constexpr (prover) {
            o.mac.coeffs[0] = y0.template reduce_to<128>();
            o.mac.coeffs[1] = y1;
            o.value() = faest::poly1(yv);
        } else {
            o.mac = y0.template reduce_to<128>();
        }
        out.push_back(o + faest::poly1((e[i / 8] >> (i % 8)) & 1));
    }
    return out;
}

// Evaluate the PRG on a committed key and add the public vector `e`, i.e., compute the committed
// bits e_i + G(K)_i of degree 2. The key bits must be committed bits of degree 1 that are
// constrained to be bits (by the caller); then each output is a bit, too.
template <typename QS, size_t KEY_BITS, size_t NUM_OUTPUTS>
std::vector<qs_bit<QS, DEGREE>> qs_eval(const PublicMap<KEY_BITS, NUM_OUTPUTS>& map,
                                        std::span<const qs_bit<QS, 1>, KEY_BITS> key,
                                        std::span<const uint8_t, NUM_OUTPUTS / 8> e) {
    if constexpr (is_faest_qs_128<QS>) {
        return qs_eval_fast<QS>(map, key, e);
    } else {
        return qs_eval_generic<QS>(map, key, e);
    }
}

} // namespace vole_mole::mq::detail

#endif
