// Internals of ML-KEM (FIPS 203) shared by key generation and the proof of possession: the NTT,
// sampling, and encoding of keys.

#ifndef VOLE_MOLE_MLKEM_MLKEM_HPP
#define VOLE_MOLE_MLKEM_MLKEM_HPP

#include "vole_mole/mlkem.hpp"

#include "voleith_fq/field.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::mlkem::detail {

using voleith_fq::detail::Fq;
using voleith_fq::detail::Q;

constexpr size_t N = 256;
constexpr size_t POLY_BYTES = 384; // ByteEncode_12 of a polynomial
constexpr size_t SYM_BYTES = 32;   // the size of rho, sigma, d, z, and H(ek)

// An element of R_q = Z_q[X] / (X^256 + 1), or its NTT representation.
using Poly = std::array<Fq, N>;

// NTT and NTT^-1 in place (FIPS 203, Algorithms 9 and 10). These are linear over F_q.
void ntt(std::span<Fq, N> f);
void inv_ntt(std::span<Fq, N> f);

// h += f * g in the NTT domain (FIPS 203, Algorithm 11, accumulated).
void multiply_ntts_acc(std::span<Fq, N> h, std::span<const Fq, N> f, std::span<const Fq, N> g);

// SampleNTT(rho || j || i) (FIPS 203, Algorithm 7).
Poly sample_ntt(std::span<const uint8_t, SYM_BYTES> rho, uint8_t j, uint8_t i);

// The matrix A-hat, row-major: a_hat[i * k + j] = SampleNTT(rho || j || i).
std::vector<Poly> expand_a(std::span<const uint8_t, SYM_BYTES> rho, size_t k);

// SamplePolyCBD_eta(PRF_eta(sigma, n)) (FIPS 203, Algorithm 8 and Section 4.1).
Poly sample_cbd(std::span<const uint8_t, SYM_BYTES> sigma, uint8_t n, size_t eta);

// ByteEncode_12 and ByteDecode_12 (FIPS 203, Algorithms 5 and 6). Decoding fails if a coefficient
// isn't reduced modulo q, i.e., the input fails the modulus check (FIPS 203, Section 7.2).
void encode12(std::span<const Fq, N> f, std::span<uint8_t, POLY_BYTES> out);
bool decode12(std::span<const uint8_t, POLY_BYTES> in, std::span<Fq, N> f);

// H(m) = SHA3-256(m).
std::array<uint8_t, SYM_BYTES> hash_h(std::span<const uint8_t> m);

// A parsed encapsulation key ek = ByteEncode_12(t-hat) || rho.
template <ParamSet P> struct ParsedEncapsKey {
    std::array<Poly, P::K> t_hat;
    std::vector<Poly> a_hat; // expanded from rho, as for expand_a
};

// Parse and expand ek. Returns std::nullopt if ek fails the modulus check.
template <ParamSet P> std::optional<ParsedEncapsKey<P>> parse_encaps_key(const EncapsKey<P>& ek);

// The parts of a decapsulation key dk = ByteEncode_12(s-hat) || ek || H(ek) || z.
template <ParamSet P> struct DecapsKeyParts {
    static constexpr size_t OFF_S_HAT = 0;
    static constexpr size_t OFF_EK = POLY_BYTES * P::K;
    static constexpr size_t OFF_H = OFF_EK + ENCAPS_KEY_BYTES<P>;
    static constexpr size_t OFF_Z = OFF_H + SYM_BYTES;
    static_assert(OFF_Z + SYM_BYTES == DECAPS_KEY_BYTES<P>);
};

} // namespace vole_mole::mlkem::detail

#endif
