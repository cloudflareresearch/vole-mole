// Arithmetic in GF(256) = GF(2)[x] / (x^8 + x^4 + x^3 + x + 1), the field of UOV and AES.
//
// faest-arch-opt embeds this field into GF(2^128) (see `faest::poly_secpar<S>::from_8_byte`), so
// embed(a) embed(b) = embed(gf256_mul(a, b)).

#ifndef VOLE_MOLE_GF256_HPP
#define VOLE_MOLE_GF256_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

// As faest-arch-opt, we support x86-64 with AVX2 and AArch64.
#ifdef __AVX2__
#include <immintrin.h>
#elifdef __aarch64__
#include <arm_neon.h>
#else
#error "unsupported architecture"
#endif

namespace vole_mole::detail {

constexpr uint8_t gf256_mul(uint8_t a, uint8_t b) {
    uint8_t out = 0;
    for (size_t i = 0; i < 8; ++i) {
        out ^= static_cast<uint8_t>(-((b >> i) & 1) & a);
        a = static_cast<uint8_t>((a << 1) ^ ((a >> 7) * 0x1b));
    }
    return out;
}

// Multiplication by a fixed v, by table lookup in the low and high nibble:
// a v = lo[a & 0xf] + hi[a >> 4].
struct Gf256MulByConst {
    std::array<uint8_t, 16> lo, hi;

    explicit Gf256MulByConst(uint8_t v = 0) {
        for (size_t a = 0; a < 16; ++a) {
            lo[a] = gf256_mul(static_cast<uint8_t>(a), v);
            hi[a] = gf256_mul(static_cast<uint8_t>(a << 4), v);
        }
    }

    uint8_t operator()(uint8_t a) const { return lo[a & 0xf] ^ hi[a >> 4]; }
};

// `len` rounded up to a multiple of 16, the length of the accumulator of gf256_madd.
constexpr size_t gf256_padded(size_t len) { return (len + 15) / 16 * 16; }

// acc[k] += a[k] v for k in [len], where `mul` multiplies by v. (The last gf256_padded(len) - len
// bytes of acc are left unchanged.) This is vectorized with table lookups of 16 bytes at a time, as
// pqov's gf256v_madd.
template <size_t len>
void gf256_madd(std::array<uint8_t, gf256_padded(len)>& acc, std::span<const uint8_t, len> a,
                const Gf256MulByConst& mul) {
    static_assert(len >= 16);
    // The last len % 16 bytes are in a vector loaded from a + len - 16 (so as not to read beyond
    // a), shifted down by 16 - len % 16 bytes.
    constexpr int TAIL_SHIFT = (16 - len % 16) % 16;
#ifdef __AVX2__
    const auto load = [](const uint8_t* p) {
        return _mm_loadu_si128(reinterpret_cast<const __m128i*>(p));
    };
    const __m128i lo = load(mul.lo.data());
    const __m128i hi = load(mul.hi.data());
    const __m128i low_nibble = _mm_set1_epi8(0x0f);
    const auto mul16 = [&](__m128i x) {
        return _mm_xor_si128(_mm_shuffle_epi8(lo, _mm_and_si128(x, low_nibble)),
                             _mm_shuffle_epi8(hi, _mm_and_si128(_mm_srli_epi16(x, 4), low_nibble)));
    };
    const auto madd16 = [&](size_t offset, __m128i product) {
        _mm_storeu_si128(reinterpret_cast<__m128i*>(&acc[offset]),
                         _mm_xor_si128(load(&acc[offset]), product));
    };
    for (size_t offset = 0; offset + 16 <= len; offset += 16) {
        madd16(offset, mul16(load(&a[offset])));
    }
    if constexpr (TAIL_SHIFT != 0) {
        madd16(len / 16 * 16, _mm_srli_si128(mul16(load(&a[len - 16])), TAIL_SHIFT));
    }
#elifdef __aarch64__
    const uint8x16_t lo = vld1q_u8(mul.lo.data());
    const uint8x16_t hi = vld1q_u8(mul.hi.data());
    const uint8x16_t low_nibble = vdupq_n_u8(0x0f);
    const auto mul16 = [&](uint8x16_t x) {
        return veorq_u8(vqtbl1q_u8(lo, vandq_u8(x, low_nibble)), vqtbl1q_u8(hi, vshrq_n_u8(x, 4)));
    };
    const auto madd16 = [&](size_t offset, uint8x16_t product) {
        vst1q_u8(&acc[offset], veorq_u8(vld1q_u8(&acc[offset]), product));
    };
    for (size_t offset = 0; offset + 16 <= len; offset += 16) {
        madd16(offset, mul16(vld1q_u8(&a[offset])));
    }
    if constexpr (TAIL_SHIFT != 0) {
        madd16(len / 16 * 16, vextq_u8(mul16(vld1q_u8(&a[len - 16])), vdupq_n_u8(0), TAIL_SHIFT));
    }
#else
#error "unsupported architecture"
#endif
}

} // namespace vole_mole::detail

#endif
