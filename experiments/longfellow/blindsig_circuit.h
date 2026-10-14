// Longfellow circuit for the blind signature relation of
// tests/blindsig/blindsig.hpp:
//
//   Public:  nf (nullifier)
//   Private: r (opening), s (UOV preimage), and optionally some intermediate
//   Keccak states Constraint: P(s) = Com(nf, r)
//
// where Com(nf, r) is the first M = 45 bytes of Keccak-p[800, 12] applied to
// DST || r || 0^9 || 0^32 || nf || 0^12, and P is the UOV public map (N = 119,
// M = 45) over GF(256), which is hardcoded into the circuit.
//
// The circuit is over GF(2^128). Keccak state bits are bits in GF(2^128), so
// XOR is addition and each round costs one layer of multiplications (chi).
// GF(256) (with the AES polynomial) is a subfield of GF(2^128): we embed byte b
// as sum_j b_j * alpha^j, where alpha is a root of the AES polynomial, which is
// a field homomorphism. The preimage s is input as bits and combined into
// GF(256) elements, so each component of P(s) is a quadratic form in these
// elements, and is compared to the corresponding output byte of the
// permutation, embedded the same way.
//
// To bound the depth of the circuit, the prover may commit to the state after
// some of the rounds, as in Longfellow's SHA-3 circuit; `slice_after[i]` says
// whether the state after round i is an input.

#ifndef VOLE_MOLE_EXPERIMENTS_LONGFELLOW_BLINDSIG_CIRCUIT_H_
#define VOLE_MOLE_EXPERIMENTS_LONGFELLOW_BLINDSIG_CIRCUIT_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace blindsig {

constexpr size_t N = 119;  // UOV preimage length
constexpr size_t M = 45;   // UOV target length
constexpr size_t NF_BYTES = 24;
constexpr size_t R_BYTES = 16;
constexpr size_t STATE_BYTES = 100;
constexpr size_t ROUNDS = 12;
constexpr size_t MONOMIALS = N * (N + 1) / 2;

// Commitment layout (see vole-mole's src/moussaka/commit.hpp).
constexpr uint8_t COM_DST[7] = {'m', 'o', 'u', 's', 0, 'c', '0'};
constexpr size_t COM_OFF_R = 7;
constexpr size_t COM_OFF_NF = COM_OFF_R + 25 + 2 * 16;

using Slicing = std::array<bool, ROUNDS>;

// FIPS 202, Algorithm 5.
inline uint32_t rc_bit(size_t t) {
  if (t % 255 == 0) return 1;
  uint32_t r = 1;
  for (size_t i = 1; i <= t % 255; ++i) {
    r <<= 1;
    const uint32_t r8 = (r >> 8) & 1;
    r ^= r8 | (r8 << 4) | (r8 << 5) | (r8 << 6);
    r &= 0xff;
  }
  return r & 1;
}

// Round constant of round i of Keccak-p[800, 12], i.e., of round index 10 + i
// of Keccak-f[800].
inline uint32_t round_constant(size_t i) {
  uint32_t rc = 0;
  for (size_t j = 0; j <= 5; ++j) {
    rc |= rc_bit(j + 7 * (10 + i)) << ((1u << j) - 1);
  }
  return rc;
}

template <class LogicCircuit>
class Circuit {
  using Field = typename LogicCircuit::Field;
  using Elt = typename Field::Elt;
  using EltW = typename LogicCircuit::EltW;
  using BitW = typename LogicCircuit::BitW;
  using v8 = typename LogicCircuit::v8;
  using v32 = typename LogicCircuit::v32;
  using State = std::array<std::array<v32, 5>, 5>;  // [x][y]

 public:
  // alpha_pow[j] = alpha^j for j < 8, where alpha is a root of the AES
  // polynomial in Field. pk[m * M + k] is the coefficient of the m-th monomial
  // in component k (see gen_blindsig_vectors).
  Circuit(const LogicCircuit& lc, const Field& f,
          const std::array<Elt, 8>& alpha_pow, const std::vector<uint8_t>& pk)
      : lc_(lc), f_(f), alpha_pow_(alpha_pow), pk_(pk) {
    // gf256[b] is the embedding of byte b.
    for (size_t b = 0; b < 256; ++b) {
      Elt e = f_.zero();
      for (size_t j = 0; j < 8; ++j) {
        if ((b >> j) & 1) e = f_.addf(e, alpha_pow_[j]);
      }
      gf256_[b] = e;
    }
  }

  struct Inputs {
    std::array<v8, NF_BYTES> nf;
    std::array<v8, R_BYTES> r;
    std::array<v8, N> s;
    std::vector<State> slices;  // one per sliced round
  };

  // Declare the inputs: nf is public, the rest is private. Every private input
  // is a bit, so it's in the subfield.
  template <class QuadCircuit>
  void input(QuadCircuit& q, Inputs& in, const Slicing& slicing) const {
    for (auto& b : in.nf) b = lc_.template vinput<8>();
    q.private_input();
    for (auto& b : in.r) b = lc_.template vinput<8>();
    for (auto& b : in.s) b = lc_.template vinput<8>();
    for (size_t i = 0; i < ROUNDS; ++i) {
      if (slicing[i]) {
        State st;
        for (size_t lane = 0; lane < 25; ++lane) {
          st[lane % 5][lane / 5] = lc_.template vinput<32>();
        }
        in.slices.push_back(st);
      }
    }
    q.begin_full_field();
  }

  void assert_valid(const Inputs& in, const Slicing& slicing) const {
    // Commitment input.
    std::array<v8, STATE_BYTES> bytes;
    for (size_t i = 0; i < STATE_BYTES; ++i) bytes[i] = lc_.template vbit<8>(0);
    for (size_t i = 0; i < 7; ++i) bytes[i] = lc_.template vbit<8>(COM_DST[i]);
    for (size_t i = 0; i < R_BYTES; ++i) bytes[COM_OFF_R + i] = in.r[i];
    for (size_t i = 0; i < NF_BYTES; ++i) bytes[COM_OFF_NF + i] = in.nf[i];

    State a;
    for (size_t lane = 0; lane < 25; ++lane) {
      for (size_t z = 0; z < 32; ++z) {
        a[lane % 5][lane / 5][z] = bytes[4 * lane + z / 8][z % 8];
      }
    }

    size_t slice = 0;
    for (size_t i = 0; i < ROUNDS; ++i) {
      round(a, i);
      if (slicing[i]) {
        const State& next = in.slices[slice++];
        for (size_t x = 0; x < 5; ++x) {
          for (size_t y = 0; y < 5; ++y) {
            assert_eq_packed(a[x][y], next[x][y]);
            a[x][y] = next[x][y];
          }
        }
      }
    }

    // Embed the preimage in GF(256) and evaluate the public map.
    std::array<EltW, N> s;
    for (size_t i = 0; i < N; ++i) s[i] = embed(in.s[i]);
    std::array<EltW, M> p;
    for (size_t k = 0; k < M; ++k) p[k] = lc_.konst(f_.zero());
    size_t m = 0;
    for (size_t i = 0; i < N; ++i) {
      for (size_t j = i; j < N; ++j, ++m) {
        const EltW sij = lc_.mul(s[i], s[j]);
        for (size_t k = 0; k < M; ++k) {
          const uint8_t c = pk_[m * M + k];
          if (c != 0) p[k] = lc_.axpy(p[k], gf256_[c], sij);
        }
      }
    }

    // Compare with the first M output bytes.
    for (size_t k = 0; k < M; ++k) {
      const size_t lane = k / 4;
      v8 out;
      for (size_t j = 0; j < 8; ++j)
        out[j] = a[lane % 5][lane / 5][8 * (k % 4) + j];
      lc_.assert_eq(p[k], embed(out));
    }
  }

 private:
  EltW embed(const v8& b) const {
    EltW e = lc_.konst(f_.zero());
    for (size_t j = 0; j < 8; ++j)
      e = lc_.axpy(e, alpha_pow_[j], lc_.eval(b[j]));
    return e;
  }

  // Assert x = y with one assertion per 16 bits, by packing the bits into the
  // subfield.
  void assert_eq_packed(const v32& x, const v32& y) const {
    lc_.assert_eq(lc_.as_scalar(lc_.template slice<0, 16>(x)),
                  lc_.as_scalar(lc_.template slice<0, 16>(y)));
    lc_.assert_eq(lc_.as_scalar(lc_.template slice<16, 32>(x)),
                  lc_.as_scalar(lc_.template slice<16, 32>(y)));
  }

  void round(State& a, size_t i) const {
    // theta
    std::array<v32, 5> c, d;
    for (size_t x = 0; x < 5; ++x) {
      c[x] = lc_.vxor(
          lc_.vxor(lc_.vxor(a[x][0], a[x][1]), lc_.vxor(a[x][2], a[x][3])),
          a[x][4]);
    }
    for (size_t x = 0; x < 5; ++x) {
      d[x] = lc_.vxor(c[(x + 4) % 5], lc_.vrotl(c[(x + 1) % 5], 1));
    }
    for (size_t x = 0; x < 5; ++x) {
      for (size_t y = 0; y < 5; ++y) a[x][y] = lc_.vxor(a[x][y], d[x]);
    }
    // rho
    {
      size_t x = 1, y = 0;
      for (size_t t = 0; t < 24; ++t) {
        a[x][y] = lc_.vrotl(a[x][y], ((t + 1) * (t + 2) / 2) % 32);
        const size_t nx = y, ny = (2 * x + 3 * y) % 5;
        x = nx;
        y = ny;
      }
    }
    // pi
    State b;
    for (size_t x = 0; x < 5; ++x) {
      for (size_t y = 0; y < 5; ++y) b[x][y] = a[(x + 3 * y) % 5][x];
    }
    // chi
    for (size_t x = 0; x < 5; ++x) {
      for (size_t y = 0; y < 5; ++y) {
        a[x][y] = lc_.vxor(
            b[x][y], lc_.vand(lc_.vnot(b[(x + 1) % 5][y]), b[(x + 2) % 5][y]));
      }
    }
    // iota
    a[0][0] = lc_.vxor(a[0][0], lc_.template vbit<32>(round_constant(i)));
  }

  const LogicCircuit& lc_;
  const Field& f_;
  const std::array<Elt, 8> alpha_pow_;
  const std::vector<uint8_t>& pk_;
  std::array<Elt, 256> gf256_;
};

}  // namespace blindsig

#endif  // VOLE_MOLE_EXPERIMENTS_LONGFELLOW_BLINDSIG_CIRCUIT_H_
