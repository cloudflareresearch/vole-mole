#include "vole_mole/mlkem.hpp"

#include "vole_mole/random.hpp"

#include "mlkem/mlkem.hpp"
#include "voleith_fq/field.hpp"

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::mlkem::detail {

using voleith_fq::detail::fq_add;
using voleith_fq::detail::fq_from_int;
using voleith_fq::detail::fq_mul;
using voleith_fq::detail::fq_pow;
using voleith_fq::detail::fq_sub;

namespace {

constexpr Fq ZETA = 17; // a primitive 256-th root of unity modulo q

constexpr uint8_t bit_rev7(uint8_t i) {
    uint8_t out = 0;
    for (size_t b = 0; b < 7; ++b) {
        out |= static_cast<uint8_t>(((i >> b) & 1) << (6 - b));
    }
    return out;
}

// ZETAS[i] = zeta^BitRev7(i) (FIPS 203, Appendix A).
constexpr std::array<Fq, 128> ZETAS = [] {
    std::array<Fq, 128> out{};
    for (size_t i = 0; i < 128; ++i) {
        out[i] = fq_pow(ZETA, bit_rev7(static_cast<uint8_t>(i)));
    }
    return out;
}();

// GAMMAS[i] = zeta^(2 BitRev7(i) + 1) (FIPS 203, Appendix A).
constexpr std::array<Fq, 128> GAMMAS = [] {
    std::array<Fq, 128> out{};
    for (size_t i = 0; i < 128; ++i) {
        out[i] = fq_pow(ZETA, 2 * bit_rev7(static_cast<uint8_t>(i)) + 1);
    }
    return out;
}();

constexpr Fq INV_128 = 3303; // 128^-1 mod q
static_assert(fq_mul(INV_128, 128) == 1);
static_assert(ZETAS[1] == 1729 && GAMMAS[0] == 17 && GAMMAS[1] == Q - 17);

} // namespace

void ntt(std::span<Fq, N> f) {
    size_t i = 1;
    for (size_t len = 128; len >= 2; len /= 2) {
        for (size_t start = 0; start < N; start += 2 * len) {
            const Fq zeta = ZETAS[i++];
            for (size_t j = start; j < start + len; ++j) {
                const Fq t = fq_mul(zeta, f[j + len]);
                f[j + len] = fq_sub(f[j], t);
                f[j] = fq_add(f[j], t);
            }
        }
    }
}

void inv_ntt(std::span<Fq, N> f) {
    size_t i = 127;
    for (size_t len = 2; len <= 128; len *= 2) {
        for (size_t start = 0; start < N; start += 2 * len) {
            const Fq zeta = ZETAS[i--];
            for (size_t j = start; j < start + len; ++j) {
                const Fq t = f[j];
                f[j] = fq_add(t, f[j + len]);
                f[j + len] = fq_mul(zeta, fq_sub(f[j + len], t));
            }
        }
    }
    for (auto& x : f) {
        x = fq_mul(x, INV_128);
    }
}

void multiply_ntts_acc(std::span<Fq, N> h, std::span<const Fq, N> f, std::span<const Fq, N> g) {
    // BaseCaseMultiply (FIPS 203, Algorithm 12) on each of the 128 pairs of coefficients.
    for (size_t i = 0; i < N / 2; ++i) {
        const uint32_t a0 = f[2 * i], a1 = f[2 * i + 1];
        const uint32_t b0 = g[2 * i], b1 = g[2 * i + 1];
        const uint32_t a1b1 = fq_mul(static_cast<Fq>(a1), static_cast<Fq>(b1));
        const uint32_t c0 = a0 * b0 + a1b1 * GAMMAS[i] + h[2 * i];
        const uint32_t c1 = a0 * b1 + a1 * b0 + h[2 * i + 1];
        h[2 * i] = static_cast<Fq>(c0 % Q);
        h[2 * i + 1] = static_cast<Fq>(c1 % Q);
    }
}

Poly sample_ntt(std::span<const uint8_t, SYM_BYTES> rho, uint8_t j, uint8_t i) {
    Keccak_HashInstance xof;
    Keccak_HashInitialize_SHAKE128(&xof);
    Keccak_HashUpdate(&xof, rho.data(), 8 * rho.size());
    const std::array<uint8_t, 2> ji = {j, i};
    Keccak_HashUpdate(&xof, ji.data(), 8 * ji.size());
    Keccak_HashFinal(&xof, nullptr);

    Poly a{};
    size_t n = 0;
    std::array<uint8_t, 168> buf; // one SHAKE128 block, a multiple of 3 bytes
    while (n < N) {
        Keccak_HashSqueeze(&xof, buf.data(), 8 * buf.size());
        for (size_t off = 0; off < buf.size() && n < N; off += 3) {
            const uint16_t d1 = static_cast<uint16_t>(buf[off] | ((buf[off + 1] & 0xf) << 8));
            const uint16_t d2 = static_cast<uint16_t>((buf[off + 1] >> 4) | (buf[off + 2] << 4));
            if (d1 < Q) {
                a[n++] = d1;
            }
            if (d2 < Q && n < N) {
                a[n++] = d2;
            }
        }
    }
    return a;
}

std::vector<Poly> expand_a(std::span<const uint8_t, SYM_BYTES> rho, size_t k) {
    std::vector<Poly> a_hat(k * k);
    for (size_t i = 0; i < k; ++i) {
        for (size_t j = 0; j < k; ++j) {
            a_hat[i * k + j] = sample_ntt(rho, static_cast<uint8_t>(j), static_cast<uint8_t>(i));
        }
    }
    return a_hat;
}

Poly sample_cbd(std::span<const uint8_t, SYM_BYTES> sigma, uint8_t n, size_t eta) {
    // PRF_eta(sigma, n) = SHAKE256(sigma || n, 64 eta)
    std::array<uint8_t, 64 * 3> b{};
    Keccak_HashInstance prf;
    Keccak_HashInitialize_SHAKE256(&prf);
    Keccak_HashUpdate(&prf, sigma.data(), 8 * sigma.size());
    Keccak_HashUpdate(&prf, &n, 8);
    Keccak_HashFinal(&prf, nullptr);
    Keccak_HashSqueeze(&prf, b.data(), 8 * 64 * eta);

    const auto bit = [&](size_t i) { return static_cast<int32_t>((b[i / 8] >> (i % 8)) & 1); };
    Poly f{};
    for (size_t i = 0; i < N; ++i) {
        int32_t x = 0, y = 0;
        for (size_t j = 0; j < eta; ++j) {
            x += bit(2 * i * eta + j);
            y += bit(2 * i * eta + eta + j);
        }
        f[i] = fq_from_int(x - y);
    }
    return f;
}

void encode12(std::span<const Fq, N> f, std::span<uint8_t, POLY_BYTES> out) {
    voleith_fq::detail::pack12(f, out);
}

bool decode12(std::span<const uint8_t, POLY_BYTES> in, std::span<Fq, N> f) {
    return voleith_fq::detail::unpack12(in, f);
}

std::array<uint8_t, SYM_BYTES> hash_h(std::span<const uint8_t> m) {
    std::array<uint8_t, SYM_BYTES> out;
    Keccak_HashInstance h;
    Keccak_HashInitialize_SHA3_256(&h);
    Keccak_HashUpdate(&h, m.data(), 8 * m.size());
    Keccak_HashFinal(&h, out.data());
    return out;
}

template <ParamSet P> std::optional<ParsedEncapsKey<P>> parse_encaps_key(const EncapsKey<P>& ek) {
    ParsedEncapsKey<P> out;
    for (size_t i = 0; i < P::K; ++i) {
        if (!decode12(std::span(ek).subspan(POLY_BYTES * i).template first<POLY_BYTES>(),
                      out.t_hat[i])) {
            return std::nullopt;
        }
    }
    out.a_hat = expand_a(std::span(ek).template last<SYM_BYTES>(), P::K);
    return out;
}

template std::optional<ParsedEncapsKey<MlKem512>> parse_encaps_key(const EncapsKey<MlKem512>&);
template std::optional<ParsedEncapsKey<MlKem768>> parse_encaps_key(const EncapsKey<MlKem768>&);
template std::optional<ParsedEncapsKey<MlKem1024>> parse_encaps_key(const EncapsKey<MlKem1024>&);

} // namespace vole_mole::mlkem::detail

namespace vole_mole::mlkem {

using namespace detail;

template <ParamSet P> KeyPair<P> keygen(const Seed& seed) {
    constexpr size_t K = P::K;
    const auto d = std::span(seed).first<SYM_BYTES>();
    const auto z = std::span(seed).last<SYM_BYTES>();

    // K-PKE.KeyGen(d) (FIPS 203, Algorithm 13).
    //
    // (rho, sigma) <- G(d || k), where G = SHA3-512.
    std::array<uint8_t, 2 * SYM_BYTES> rho_sigma;
    {
        Keccak_HashInstance g;
        Keccak_HashInitialize_SHA3_512(&g);
        Keccak_HashUpdate(&g, d.data(), 8 * d.size());
        const uint8_t k = K;
        Keccak_HashUpdate(&g, &k, 8);
        Keccak_HashFinal(&g, rho_sigma.data());
    }
    const auto rho = std::span(rho_sigma).first<SYM_BYTES>();
    const auto sigma = std::span(rho_sigma).last<SYM_BYTES>();

    const std::vector<Poly> a_hat = expand_a(rho, K);
    std::array<Poly, K> s_hat, t_hat;
    uint8_t n = 0;
    for (auto& s : s_hat) {
        s = sample_cbd(sigma, n++, P::ETA1);
        ntt(s);
    }
    for (auto& t : t_hat) {
        t = sample_cbd(sigma, n++, P::ETA1); // e
        ntt(t);
    }
    // t-hat = A-hat * s-hat + e-hat
    for (size_t i = 0; i < K; ++i) {
        for (size_t j = 0; j < K; ++j) {
            multiply_ntts_acc(t_hat[i], a_hat[i * K + j], s_hat[j]);
        }
    }

    KeyPair<P> kp;
    for (size_t i = 0; i < K; ++i) {
        encode12(t_hat[i], std::span(kp.ek).subspan(POLY_BYTES * i).template first<POLY_BYTES>());
    }
    std::ranges::copy(rho, kp.ek.begin() + POLY_BYTES * K);

    // dk = dk_PKE || ek || H(ek) || z (FIPS 203, Algorithm 16).
    using Parts = DecapsKeyParts<P>;
    for (size_t i = 0; i < K; ++i) {
        encode12(s_hat[i], std::span(kp.dk)
                               .subspan(Parts::OFF_S_HAT + POLY_BYTES * i)
                               .template first<POLY_BYTES>());
    }
    std::ranges::copy(kp.ek, kp.dk.begin() + Parts::OFF_EK);
    std::ranges::copy(hash_h(kp.ek), kp.dk.begin() + Parts::OFF_H);
    std::ranges::copy(z, kp.dk.begin() + Parts::OFF_Z);
    return kp;
}

template <ParamSet P> KeyPair<P> keygen() { return keygen<P>(random_bytes<SEED_BYTES>()); }

template KeyPair<MlKem512> keygen<MlKem512>(const Seed&);
template KeyPair<MlKem768> keygen<MlKem768>(const Seed&);
template KeyPair<MlKem1024> keygen<MlKem1024>(const Seed&);
template KeyPair<MlKem512> keygen<MlKem512>();
template KeyPair<MlKem768> keygen<MlKem768>();
template KeyPair<MlKem1024> keygen<MlKem1024>();

} // namespace vole_mole::mlkem
