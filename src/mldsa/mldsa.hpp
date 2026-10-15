// Internals of ML-DSA (FIPS 204) shared by the signature scheme and the proof of knowledge of a
// signature: arithmetic modulo q, the NTT, sampling, rounding, and encodings.

#ifndef VOLE_MOLE_MLDSA_MLDSA_HPP
#define VOLE_MOLE_MLDSA_MLDSA_HPP

#include "vole_mole/mldsa.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::mldsa::detail {

constexpr uint32_t Q = 8380417;
constexpr size_t N = 256;
constexpr size_t D = 13; // dropped bits of t

// An element of Z_q in [0, q).
using Fq = uint32_t;

constexpr Fq fq_add(Fq a, Fq b) {
    const uint32_t t = a + b;
    return t >= Q ? t - Q : t;
}
constexpr Fq fq_sub(Fq a, Fq b) { return a >= b ? a - b : a + Q - b; }
constexpr Fq fq_neg(Fq a) { return a == 0 ? 0 : Q - a; }
constexpr Fq fq_mul(Fq a, Fq b) { return static_cast<Fq>(uint64_t{a} * b % Q); }
// x mod q for a signed x with |x| < 2^31.
constexpr Fq fq_from_int(int64_t x) {
    const int64_t r = x % int64_t{Q};
    return static_cast<Fq>(r < 0 ? r + Q : r);
}
// The representative of a in (-q/2, q/2] ("mod+-" in FIPS 204).
constexpr int32_t fq_centered(Fq a) {
    return a > Q / 2 ? static_cast<int32_t>(a) - static_cast<int32_t>(Q) : static_cast<int32_t>(a);
}

// An element of R_q = Z_q[X] / (X^256 + 1), or its NTT representation.
using Poly = std::array<Fq, N>;

// NTT and NTT^-1 in place (FIPS 204, Algorithms 41 and 42). These are linear over Z_q.
void ntt(std::span<Fq, N> w);
void inv_ntt(std::span<Fq, N> w);

// h += f * g in the NTT domain (FIPS 204, Algorithm 45, accumulated).
void multiply_ntts_acc(std::span<Fq, N> h, std::span<const Fq, N> f, std::span<const Fq, N> g);

// ExpandA(rho) (FIPS 204, Algorithm 32), row-major: a_hat[r * l + s].
std::vector<Poly> expand_a(std::span<const uint8_t, 32> rho, size_t k, size_t l);

// SampleInBall(rho) (FIPS 204, Algorithm 29), with coefficients in {0, 1, q - 1}.
Poly sample_in_ball(std::span<const uint8_t> rho, size_t tau);

// The bytes of the SampleInBall stream that are consumed for a given seed: the stream is
// SHAKE256(rho); SampleInBall reads 8 sign bytes and then index bytes until tau are accepted.
size_t sample_in_ball_stream_bytes(std::span<const uint8_t> rho, size_t tau);

// Decompose(r) (FIPS 204, Algorithm 36): r = r1 * 2 gamma2 + r0 (mod q).
struct Decomposed {
    uint32_t r1;
    int32_t r0;
};
Decomposed decompose(Fq r, uint32_t gamma2);
inline uint32_t high_bits(Fq r, uint32_t gamma2) { return decompose(r, gamma2).r1; }
inline int32_t low_bits(Fq r, uint32_t gamma2) { return decompose(r, gamma2).r0; }

// MakeHint(z, r) and UseHint(h, r) (FIPS 204, Algorithms 39 and 40).
bool make_hint(Fq z, Fq r, uint32_t gamma2);
uint32_t use_hint(bool h, Fq r, uint32_t gamma2);

// H(m, len) = SHAKE256(m)[0:len] for the concatenation m of `parts`.
void shake256(std::span<const std::span<const uint8_t>> parts, std::span<uint8_t> out);

// w1Encode(w1) (FIPS 204, Algorithm 28), for coefficients in [0, (q - 1) / (2 gamma2)).
std::vector<uint8_t> w1_encode(std::span<const Poly> w1, uint32_t gamma2);

// Bits per coefficient of w1Encode.
constexpr size_t w1_bits(uint32_t gamma2) { return bitlen((Q - 1) / (2 * gamma2) - 1); }

// A parsed public key pk = rho || t1.
template <ParamSet P> struct ParsedPublicKey {
    std::array<uint8_t, 32> rho;
    std::array<Poly, P::K> t1;
    std::vector<Poly> a_hat;    // ExpandA(rho)
    std::array<uint8_t, 64> tr; // H(pk, 64)
};
template <ParamSet P> ParsedPublicKey<P> parse_public_key(const PublicKey<P>& pk);

// A decoded signature sigma = c-tilde || z || h, with z in (-gamma1, gamma1] (as elements of Z_q)
// and h in {0, 1}. Returns std::nullopt if the hint encoding is malformed.
template <ParamSet P> struct DecodedSignature {
    std::array<uint8_t, P::LAMBDA / 4> c_tilde;
    std::array<Poly, P::L> z;
    std::array<std::array<bool, N>, P::K> h;
};
template <ParamSet P> std::optional<DecodedSignature<P>> decode_signature(const Signature<P>& sig);

// mu = H(H(pk, 64) || M', 64) for M' = 0 || |ctx| || ctx || M. Requires |ctx| <= 255.
std::array<uint8_t, 64> message_representative(std::span<const uint8_t, 64> tr,
                                               std::span<const uint8_t> msg,
                                               std::span<const uint8_t> ctx);

// The approximation w'_approx = NTT^-1(A-hat NTT(z) - NTT(c) NTT(t1 2^d)) computed by verification.
template <ParamSet P>
std::array<Poly, P::K> w_approx(const ParsedPublicKey<P>& pk, std::span<const Poly, P::L> z,
                                const Poly& c);

} // namespace vole_mole::mldsa::detail

#endif
