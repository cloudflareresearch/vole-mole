#include "vole_mole/mldsa.hpp"

#include "vole_mole/random.hpp"

#include "mldsa/mldsa.hpp"

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <vector>

namespace vole_mole::mldsa::detail {

namespace {

constexpr Fq ZETA = 1753; // a primitive 512th root of unity modulo q

constexpr Fq fq_pow(Fq a, uint32_t e) {
    Fq out = 1;
    while (e) {
        if (e & 1) {
            out = fq_mul(out, a);
        }
        a = fq_mul(a, a);
        e >>= 1;
    }
    return out;
}

constexpr uint32_t bitrev8(uint32_t x) {
    uint32_t out = 0;
    for (size_t i = 0; i < 8; ++i) {
        out |= ((x >> i) & 1) << (7 - i);
    }
    return out;
}

// zetas[m] = zeta^BitRev8(m) mod q.
constexpr std::array<Fq, N> ZETAS = [] {
    std::array<Fq, N> out{};
    for (uint32_t m = 0; m < N; ++m) {
        out[m] = fq_pow(ZETA, bitrev8(m));
    }
    return out;
}();
static_assert(ZETAS[1] == 4808194); // FIPS 204, Appendix B

constexpr Fq N_INV = 8347681; // 256^-1 mod q
static_assert(fq_mul(N_INV, 256) == 1);

// SHAKE128 or SHAKE256, absorbing then squeezing incrementally.
class Xof {
  public:
    explicit Xof(bool shake256) {
        if (shake256) {
            Keccak_HashInitialize_SHAKE256(&h_);
        } else {
            Keccak_HashInitialize_SHAKE128(&h_);
        }
    }
    Xof& absorb(std::span<const uint8_t> m) {
        Keccak_HashUpdate(&h_, m.data(), 8 * m.size());
        return *this;
    }
    void squeeze(std::span<uint8_t> out) {
        if (!finished_) {
            Keccak_HashFinal(&h_, nullptr);
            finished_ = true;
        }
        Keccak_HashSqueeze(&h_, out.data(), 8 * out.size());
    }
    uint8_t squeeze_byte() {
        uint8_t b;
        squeeze(std::span(&b, 1));
        return b;
    }

  private:
    Keccak_HashInstance h_;
    bool finished_ = false;
};

std::array<uint8_t, 2> le16(size_t x) {
    return {static_cast<uint8_t>(x), static_cast<uint8_t>(x >> 8)};
}

// Bits [off, off + bits) of `in`, little-endian.
uint32_t get_bits(std::span<const uint8_t> in, size_t off, size_t bits) {
    uint32_t v = 0;
    for (size_t i = 0; i < bits; ++i) {
        v |= uint32_t{(in[(off + i) / 8] >> ((off + i) % 8)) & 1u} << i;
    }
    return v;
}

void put_bits(std::span<uint8_t> out, size_t off, size_t bits, uint32_t v) {
    for (size_t i = 0; i < bits; ++i) {
        out[(off + i) / 8] |= static_cast<uint8_t>(((v >> i) & 1) << ((off + i) % 8));
    }
}

// SimpleBitPack(w, b) and BitPack(w, a, b) (FIPS 204, Algorithms 16 and 17) of one polynomial,
// written at the start of `out` (which must be zero-initialized). Returns the number of bytes.
size_t simple_bit_pack(const Poly& w, uint32_t b, std::span<uint8_t> out) {
    const size_t bits = bitlen(b);
    for (size_t i = 0; i < N; ++i) {
        put_bits(out, bits * i, bits, w[i]);
    }
    return bits * N / 8;
}
size_t bit_pack(const Poly& w, uint32_t a, uint32_t b, std::span<uint8_t> out) {
    const size_t bits = bitlen(a + b);
    for (size_t i = 0; i < N; ++i) {
        put_bits(out, bits * i, bits, fq_sub(fq_from_int(b), w[i]));
    }
    return bits * N / 8;
}
// BitUnpack(v, a, b) (FIPS 204, Algorithm 19).
Poly bit_unpack(std::span<const uint8_t> in, uint32_t a, uint32_t b) {
    const size_t bits = bitlen(a + b);
    Poly w;
    for (size_t i = 0; i < N; ++i) {
        w[i] = fq_from_int(int64_t{b} - get_bits(in, bits * i, bits));
    }
    return w;
}

// RejNTTPoly(rho) (FIPS 204, Algorithm 30).
Poly rej_ntt_poly(std::span<const uint8_t> rho) {
    Xof g(false);
    g.absorb(rho);
    Poly a;
    size_t j = 0;
    while (j < N) {
        std::array<uint8_t, 3> s;
        g.squeeze(s);
        const uint32_t z = uint32_t{s[0]} | (uint32_t{s[1]} << 8) | (uint32_t{s[2] & 0x7fu} << 16);
        if (z < Q) {
            a[j++] = z;
        }
    }
    return a;
}

// CoeffFromHalfByte(b) (FIPS 204, Algorithm 15).
std::optional<Fq> coeff_from_half_byte(uint32_t b, size_t eta) {
    if (eta == 2 && b < 15) {
        return fq_from_int(2 - int64_t{b % 5});
    }
    if (eta == 4 && b < 9) {
        return fq_from_int(4 - int64_t{b});
    }
    return std::nullopt;
}

// RejBoundedPoly(rho) (FIPS 204, Algorithm 31).
Poly rej_bounded_poly(std::span<const uint8_t> rho, size_t eta) {
    Xof h(true);
    h.absorb(rho);
    Poly a;
    size_t j = 0;
    while (j < N) {
        const uint8_t z = h.squeeze_byte();
        const auto z0 = coeff_from_half_byte(z & 0xf, eta);
        const auto z1 = coeff_from_half_byte(z >> 4, eta);
        if (z0) {
            a[j++] = *z0;
        }
        if (z1 && j < N) {
            a[j++] = *z1;
        }
    }
    return a;
}

// Power2Round(r) (FIPS 204, Algorithm 35).
std::pair<Fq, Fq> power2round(Fq r) {
    int32_t r0 = static_cast<int32_t>(r & ((1u << D) - 1));
    if (r0 > (1 << (D - 1))) {
        r0 -= 1 << D;
    }
    return {static_cast<Fq>((static_cast<int64_t>(r) - r0) >> D), fq_from_int(r0)};
}

uint32_t inf_norm(const Poly& w) {
    uint32_t m = 0;
    for (const Fq c : w) {
        const int32_t v = fq_centered(c);
        m = std::max(m, static_cast<uint32_t>(v < 0 ? -v : v));
    }
    return m;
}

template <ParamSet P> constexpr uint32_t BETA = static_cast<uint32_t>(P::TAU * P::ETA);
template <ParamSet P> constexpr size_t Z_BITS = 1 + bitlen(P::GAMMA1 - 1);
template <ParamSet P> constexpr size_t ETA_BITS = bitlen(2 * P::ETA);

template <ParamSet P> struct ParsedSecretKey {
    std::array<uint8_t, 32> rho, key;
    std::array<uint8_t, 64> tr;
    std::array<Poly, P::L> s1;
    std::array<Poly, P::K> s2, t0;
};

template <ParamSet P> ParsedSecretKey<P> sk_decode(const SecretKey<P>& sk) {
    ParsedSecretKey<P> out;
    std::copy_n(sk.begin(), 32, out.rho.begin());
    std::copy_n(sk.begin() + 32, 32, out.key.begin());
    std::copy_n(sk.begin() + 64, 64, out.tr.begin());
    size_t off = 128;
    for (auto& s : out.s1) {
        s = bit_unpack(std::span(sk).subspan(off), P::ETA, P::ETA);
        off += 32 * ETA_BITS<P>;
    }
    for (auto& s : out.s2) {
        s = bit_unpack(std::span(sk).subspan(off), P::ETA, P::ETA);
        off += 32 * ETA_BITS<P>;
    }
    for (auto& t : out.t0) {
        t = bit_unpack(std::span(sk).subspan(off), (1u << (D - 1)) - 1, 1u << (D - 1));
        off += 32 * D;
    }
    return out;
}

// NTT^-1(sum_j a_hat[i][j] * v_hat[j]) for each row i.
template <size_t K, size_t L>
std::array<Poly, K> mat_vec(const std::vector<Poly>& a_hat, const std::array<Poly, L>& v_hat) {
    std::array<Poly, K> out{};
    for (size_t i = 0; i < K; ++i) {
        for (size_t j = 0; j < L; ++j) {
            multiply_ntts_acc(out[i], a_hat[i * L + j], v_hat[j]);
        }
        inv_ntt(out[i]);
    }
    return out;
}

template <size_t M> std::array<Poly, M> ntt_all(std::array<Poly, M> v) {
    for (auto& p : v) {
        ntt(p);
    }
    return v;
}

Poly mul_ntt(const Poly& a_hat, const Poly& b_hat) {
    Poly out{};
    multiply_ntts_acc(out, a_hat, b_hat);
    inv_ntt(out);
    return out;
}

} // namespace

void ntt(std::span<Fq, N> w) {
    size_t m = 0;
    for (size_t len = 128; len >= 1; len /= 2) {
        for (size_t start = 0; start < N; start += 2 * len) {
            const Fq z = ZETAS[++m];
            for (size_t j = start; j < start + len; ++j) {
                const Fq t = fq_mul(z, w[j + len]);
                w[j + len] = fq_sub(w[j], t);
                w[j] = fq_add(w[j], t);
            }
        }
    }
}

void inv_ntt(std::span<Fq, N> w) {
    size_t m = N;
    for (size_t len = 1; len < N; len *= 2) {
        for (size_t start = 0; start < N; start += 2 * len) {
            const Fq z = fq_neg(ZETAS[--m]);
            for (size_t j = start; j < start + len; ++j) {
                const Fq t = w[j];
                w[j] = fq_add(t, w[j + len]);
                w[j + len] = fq_mul(z, fq_sub(t, w[j + len]));
            }
        }
    }
    for (auto& c : w) {
        c = fq_mul(N_INV, c);
    }
}

void multiply_ntts_acc(std::span<Fq, N> h, std::span<const Fq, N> f, std::span<const Fq, N> g) {
    for (size_t i = 0; i < N; ++i) {
        h[i] = fq_add(h[i], fq_mul(f[i], g[i]));
    }
}

std::vector<Poly> expand_a(std::span<const uint8_t, 32> rho, size_t k, size_t l) {
    std::vector<Poly> a(k * l);
    std::array<uint8_t, 34> seed;
    std::ranges::copy(rho, seed.begin());
    for (size_t r = 0; r < k; ++r) {
        for (size_t s = 0; s < l; ++s) {
            seed[32] = static_cast<uint8_t>(s);
            seed[33] = static_cast<uint8_t>(r);
            a[r * l + s] = rej_ntt_poly(seed);
        }
    }
    return a;
}

Poly sample_in_ball(std::span<const uint8_t> rho, size_t tau) {
    Xof h(true);
    h.absorb(rho);
    std::array<uint8_t, 8> s;
    h.squeeze(s);
    uint64_t signs = 0;
    for (size_t i = 0; i < 8; ++i) {
        signs |= uint64_t{s[i]} << (8 * i);
    }
    Poly c{};
    for (size_t i = N - tau; i < N; ++i) {
        size_t j;
        do {
            j = h.squeeze_byte();
        } while (j > i);
        c[i] = c[j];
        c[j] = ((signs >> (i + tau - N)) & 1) ? Q - 1 : 1;
    }
    return c;
}

size_t sample_in_ball_stream_bytes(std::span<const uint8_t> rho, size_t tau) {
    Xof h(true);
    h.absorb(rho);
    std::array<uint8_t, 8> s;
    h.squeeze(s);
    size_t bytes = 8;
    for (size_t i = N - tau; i < N; ++i) {
        size_t j;
        do {
            j = h.squeeze_byte();
            ++bytes;
        } while (j > i);
    }
    return bytes;
}

Decomposed decompose(Fq r, uint32_t gamma2) {
    int32_t r0 = static_cast<int32_t>(r % (2 * gamma2));
    if (r0 > static_cast<int32_t>(gamma2)) {
        r0 -= static_cast<int32_t>(2 * gamma2);
    }
    if (static_cast<int64_t>(r) - r0 == Q - 1) {
        return {0, r0 - 1};
    }
    return {static_cast<uint32_t>((static_cast<int64_t>(r) - r0) / (2 * gamma2)), r0};
}

bool make_hint(Fq z, Fq r, uint32_t gamma2) {
    return high_bits(r, gamma2) != high_bits(fq_add(r, z), gamma2);
}

uint32_t use_hint(bool h, Fq r, uint32_t gamma2) {
    const uint32_t m = (Q - 1) / (2 * gamma2);
    const auto [r1, r0] = decompose(r, gamma2);
    if (h && r0 > 0) {
        return (r1 + 1) % m;
    }
    if (h) {
        return (r1 + m - 1) % m;
    }
    return r1;
}

void shake256(std::span<const std::span<const uint8_t>> parts, std::span<uint8_t> out) {
    Xof h(true);
    for (const auto& p : parts) {
        h.absorb(p);
    }
    h.squeeze(out);
}

std::vector<uint8_t> w1_encode(std::span<const Poly> w1, uint32_t gamma2) {
    const size_t bits = w1_bits(gamma2);
    std::vector<uint8_t> out(w1.size() * N * bits / 8);
    for (size_t i = 0; i < w1.size(); ++i) {
        for (size_t j = 0; j < N; ++j) {
            put_bits(out, bits * (i * N + j), bits, w1[i][j]);
        }
    }
    return out;
}

template <ParamSet P> ParsedPublicKey<P> parse_public_key(const PublicKey<P>& pk) {
    ParsedPublicKey<P> out;
    std::copy_n(pk.begin(), 32, out.rho.begin());
    for (size_t i = 0; i < P::K; ++i) {
        for (size_t j = 0; j < N; ++j) {
            out.t1[i][j] = get_bits(std::span(pk).subspan(32), 10 * (i * N + j), 10);
        }
    }
    out.a_hat = expand_a(out.rho, P::K, P::L);
    shake256(std::array{std::span<const uint8_t>(pk)}, out.tr);
    return out;
}

template <ParamSet P> std::optional<DecodedSignature<P>> decode_signature(const Signature<P>& sig) {
    DecodedSignature<P> out;
    std::copy_n(sig.begin(), out.c_tilde.size(), out.c_tilde.begin());
    size_t off = out.c_tilde.size();
    for (auto& z : out.z) {
        z = bit_unpack(std::span(sig).subspan(off), P::GAMMA1 - 1, P::GAMMA1);
        off += 32 * Z_BITS<P>;
    }

    // HintBitUnpack (FIPS 204, Algorithm 21).
    const auto y = std::span(sig).subspan(off);
    for (auto& h : out.h) {
        h.fill(false);
    }
    size_t index = 0;
    for (size_t i = 0; i < P::K; ++i) {
        if (y[P::OMEGA + i] < index || y[P::OMEGA + i] > P::OMEGA) {
            return std::nullopt;
        }
        const size_t first = index;
        while (index < y[P::OMEGA + i]) {
            if (index > first && y[index - 1] >= y[index]) {
                return std::nullopt;
            }
            out.h[i][y[index]] = true;
            ++index;
        }
    }
    for (size_t i = index; i < P::OMEGA; ++i) {
        if (y[i] != 0) {
            return std::nullopt;
        }
    }
    return out;
}

std::array<uint8_t, 64> message_representative(std::span<const uint8_t, 64> tr,
                                               std::span<const uint8_t> msg,
                                               std::span<const uint8_t> ctx) {
    const std::array<uint8_t, 2> prefix = {0, static_cast<uint8_t>(ctx.size())};
    std::array<uint8_t, 64> mu;
    shake256(std::array{std::span<const uint8_t>(tr), std::span<const uint8_t>(prefix), ctx, msg},
             mu);
    return mu;
}

template <ParamSet P>
std::array<Poly, P::K> w_approx(const ParsedPublicKey<P>& pk, std::span<const Poly, P::L> z,
                                const Poly& c) {
    std::array<Poly, P::L> z_hat;
    std::ranges::copy(z, z_hat.begin());
    z_hat = ntt_all(z_hat);
    Poly c_hat = c;
    ntt(c_hat);
    std::array<Poly, P::K> out{};
    for (size_t i = 0; i < P::K; ++i) {
        for (size_t j = 0; j < P::L; ++j) {
            multiply_ntts_acc(out[i], pk.a_hat[i * P::L + j], z_hat[j]);
        }
        Poly t1_hat;
        for (size_t n = 0; n < N; ++n) {
            t1_hat[n] = fq_mul(pk.t1[i][n], 1u << D);
        }
        ntt(t1_hat);
        Poly ct1{};
        multiply_ntts_acc(ct1, c_hat, t1_hat);
        for (size_t n = 0; n < N; ++n) {
            out[i][n] = fq_sub(out[i][n], ct1[n]);
        }
        inv_ntt(out[i]);
    }
    return out;
}

#define VOLE_MOLE_INSTANTIATE(P)                                                                   \
    template ParsedPublicKey<P> parse_public_key<P>(const PublicKey<P>&);                          \
    template std::optional<DecodedSignature<P>> decode_signature<P>(const Signature<P>&);          \
    template std::array<Poly, P::K> w_approx<P>(const ParsedPublicKey<P>&,                         \
                                                std::span<const Poly, P::L>, const Poly&);
VOLE_MOLE_INSTANTIATE(MlDsa44)
VOLE_MOLE_INSTANTIATE(MlDsa65)
VOLE_MOLE_INSTANTIATE(MlDsa87)
#undef VOLE_MOLE_INSTANTIATE

} // namespace vole_mole::mldsa::detail

namespace vole_mole::mldsa {

using namespace detail;

template <ParamSet P> KeyPair<P> keygen(const Seed& xi) {
    const std::array<uint8_t, 2> kl = {static_cast<uint8_t>(P::K), static_cast<uint8_t>(P::L)};
    std::array<uint8_t, 128> seeds;
    shake256(std::array{std::span<const uint8_t>(xi), std::span<const uint8_t>(kl)}, seeds);
    const auto rho = std::span(seeds).template first<32>();
    const auto rho_prime = std::span(seeds).template subspan<32, 64>();
    const auto key = std::span(seeds).template subspan<96, 32>();

    // ExpandS (FIPS 204, Algorithm 33).
    std::array<Poly, P::L> s1;
    std::array<Poly, P::K> s2;
    std::array<uint8_t, 66> seed;
    std::ranges::copy(rho_prime, seed.begin());
    for (size_t r = 0; r < P::L + P::K; ++r) {
        const auto idx = le16(r);
        seed[64] = idx[0];
        seed[65] = idx[1];
        (r < P::L ? s1[r] : s2[r - P::L]) = rej_bounded_poly(seed, P::ETA);
    }

    const auto a_hat = expand_a(rho, P::K, P::L);
    auto t = mat_vec<P::K, P::L>(a_hat, ntt_all(s1));
    std::array<Poly, P::K> t1, t0;
    for (size_t i = 0; i < P::K; ++i) {
        for (size_t n = 0; n < N; ++n) {
            std::tie(t1[i][n], t0[i][n]) = power2round(fq_add(t[i][n], s2[i][n]));
        }
    }

    KeyPair<P> kp{};
    std::ranges::copy(rho, kp.pk.begin());
    for (size_t i = 0; i < P::K; ++i) {
        simple_bit_pack(t1[i], 1023, std::span(kp.pk).subspan(32 + 320 * i));
    }
    std::array<uint8_t, 64> tr;
    shake256(std::array{std::span<const uint8_t>(kp.pk)}, tr);

    std::ranges::copy(rho, kp.sk.begin());
    std::ranges::copy(key, kp.sk.begin() + 32);
    std::ranges::copy(tr, kp.sk.begin() + 64);
    size_t off = 128;
    for (const auto& s : s1) {
        off += bit_pack(s, P::ETA, P::ETA, std::span(kp.sk).subspan(off));
    }
    for (const auto& s : s2) {
        off += bit_pack(s, P::ETA, P::ETA, std::span(kp.sk).subspan(off));
    }
    for (const auto& t0i : t0) {
        off += bit_pack(t0i, (1u << (D - 1)) - 1, 1u << (D - 1), std::span(kp.sk).subspan(off));
    }
    return kp;
}

template <ParamSet P> KeyPair<P> keygen() { return keygen<P>(random_bytes<SEED_BYTES>()); }

template <ParamSet P>
Signature<P> sign(const SecretKey<P>& sk, std::span<const uint8_t> msg,
                  std::span<const uint8_t> ctx, const Rnd& rnd) {
    if (ctx.size() > MAX_CONTEXT_BYTES) {
        throw std::invalid_argument("ML-DSA: context string is too long");
    }
    const auto key = sk_decode<P>(sk);
    const auto s1_hat = ntt_all(key.s1);
    const auto s2_hat = ntt_all(key.s2);
    const auto t0_hat = ntt_all(key.t0);
    const auto a_hat = expand_a(key.rho, P::K, P::L);
    const auto mu = message_representative(key.tr, msg, ctx);
    std::array<uint8_t, 64> rho2;
    shake256(std::array{std::span<const uint8_t>(key.key), std::span<const uint8_t>(rnd),
                        std::span<const uint8_t>(mu)},
             rho2);

    for (size_t kappa = 0;; kappa += P::L) {
        // ExpandMask(rho'', kappa) (FIPS 204, Algorithm 34).
        std::array<Poly, P::L> y;
        for (size_t r = 0; r < P::L; ++r) {
            const auto idx = le16(kappa + r);
            std::array<uint8_t, 32 * Z_BITS<P>> v;
            shake256(std::array{std::span<const uint8_t>(rho2), std::span<const uint8_t>(idx)}, v);
            y[r] = bit_unpack(v, P::GAMMA1 - 1, P::GAMMA1);
        }
        const auto w = mat_vec<P::K, P::L>(a_hat, ntt_all(y));
        std::array<Poly, P::K> w1;
        for (size_t i = 0; i < P::K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                w1[i][n] = high_bits(w[i][n], P::GAMMA2);
            }
        }
        std::array<uint8_t, P::LAMBDA / 4> c_tilde;
        const auto w1_enc = w1_encode(w1, P::GAMMA2);
        shake256(std::array{std::span<const uint8_t>(mu), std::span<const uint8_t>(w1_enc)},
                 c_tilde);
        Poly c_hat = sample_in_ball(c_tilde, P::TAU);
        ntt(c_hat);

        std::array<Poly, P::L> z;
        bool reject = false;
        for (size_t j = 0; j < P::L; ++j) {
            const Poly cs1 = mul_ntt(c_hat, s1_hat[j]);
            for (size_t n = 0; n < N; ++n) {
                z[j][n] = fq_add(y[j][n], cs1[n]);
            }
            reject |= inf_norm(z[j]) >= P::GAMMA1 - BETA<P>;
        }
        std::array<std::array<bool, N>, P::K> h{};
        size_t ones = 0;
        for (size_t i = 0; i < P::K && !reject; ++i) {
            const Poly cs2 = mul_ntt(c_hat, s2_hat[i]);
            const Poly ct0 = mul_ntt(c_hat, t0_hat[i]);
            Poly r;
            for (size_t n = 0; n < N; ++n) {
                r[n] = fq_sub(w[i][n], cs2[n]);
            }
            for (size_t n = 0; n < N; ++n) {
                const int32_t r0 = low_bits(r[n], P::GAMMA2);
                reject |= static_cast<uint32_t>(r0 < 0 ? -r0 : r0) >= P::GAMMA2 - BETA<P>;
            }
            reject |= inf_norm(ct0) >= P::GAMMA2;
            for (size_t n = 0; n < N; ++n) {
                h[i][n] = make_hint(fq_neg(ct0[n]), fq_add(r[n], ct0[n]), P::GAMMA2);
                ones += h[i][n];
            }
        }
        if (reject || ones > P::OMEGA) {
            continue;
        }

        // sigEncode (FIPS 204, Algorithm 26).
        Signature<P> sig{};
        std::ranges::copy(c_tilde, sig.begin());
        size_t off = c_tilde.size();
        for (const auto& zj : z) {
            off += bit_pack(zj, P::GAMMA1 - 1, P::GAMMA1, std::span(sig).subspan(off));
        }
        size_t index = 0;
        for (size_t i = 0; i < P::K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                if (h[i][n]) {
                    sig[off + index++] = static_cast<uint8_t>(n);
                }
            }
            sig[off + P::OMEGA + i] = static_cast<uint8_t>(index);
        }
        return sig;
    }
}

template <ParamSet P>
Signature<P> sign(const SecretKey<P>& sk, std::span<const uint8_t> msg,
                  std::span<const uint8_t> ctx) {
    return sign<P>(sk, msg, ctx, random_bytes<RND_BYTES>());
}

template <ParamSet P>
bool verify(const PublicKey<P>& pk, std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
            const Signature<P>& sig) {
    if (ctx.size() > MAX_CONTEXT_BYTES) {
        return false;
    }
    const auto decoded = decode_signature<P>(sig);
    if (!decoded) {
        return false;
    }
    for (const auto& zj : decoded->z) {
        if (inf_norm(zj) >= P::GAMMA1 - BETA<P>) {
            return false;
        }
    }
    const auto parsed = parse_public_key<P>(pk);
    const auto mu = message_representative(parsed.tr, msg, ctx);
    const Poly c = sample_in_ball(decoded->c_tilde, P::TAU);
    const auto w = w_approx<P>(parsed, decoded->z, c);
    std::array<Poly, P::K> w1;
    for (size_t i = 0; i < P::K; ++i) {
        for (size_t n = 0; n < N; ++n) {
            w1[i][n] = use_hint(decoded->h[i][n], w[i][n], P::GAMMA2);
        }
    }
    std::array<uint8_t, P::LAMBDA / 4> c_tilde;
    const auto w1_enc = w1_encode(w1, P::GAMMA2);
    shake256(std::array{std::span<const uint8_t>(mu), std::span<const uint8_t>(w1_enc)}, c_tilde);
    return c_tilde == decoded->c_tilde;
}

#define VOLE_MOLE_INSTANTIATE(P)                                                                   \
    template KeyPair<P> keygen<P>(const Seed&);                                                    \
    template KeyPair<P> keygen<P>();                                                               \
    template Signature<P> sign<P>(const SecretKey<P>&, std::span<const uint8_t>,                   \
                                  std::span<const uint8_t>, const Rnd&);                           \
    template Signature<P> sign<P>(const SecretKey<P>&, std::span<const uint8_t>,                   \
                                  std::span<const uint8_t>);                                       \
    template bool verify<P>(const PublicKey<P>&, std::span<const uint8_t>,                         \
                            std::span<const uint8_t>, const Signature<P>&);
VOLE_MOLE_INSTANTIATE(MlDsa44)
VOLE_MOLE_INSTANTIATE(MlDsa65)
VOLE_MOLE_INSTANTIATE(MlDsa87)
#undef VOLE_MOLE_INSTANTIATE

} // namespace vole_mole::mldsa
