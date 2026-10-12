// VOLE-in-the-Head (VOLEitH) over the prime field F_q, q = 3329.
//
// FAEST's VOLEitH (src/voleith.hpp) commits to bits and authenticates them with MACs in
// GF(2^128). That's a good fit for Boolean circuits and for UOV over GF(256), but a poor fit for
// lattice relations over Z_q: every addition modulo q would cost a binary adder. This is a
// VOLEitH proof system that commits to elements of F_q instead, with MACs in F_{q^16}. Linear
// relations over F_q are then free.
//
// Relations. A relation consists of a witness w in F_q^WITNESS_LEN, and constraints built from
// the following operations on committed vectors:
//
//   - affine maps over F_q: y = L(x) + c, where L is a public linear map and c a public vector;
//   - root constraints: f(x_i) = 0 for each entry x_i of a committed vector x, where f is a public
//     polynomial of degree at most DEGREE.
//
// This suffices for, e.g., Module-LWE: knowledge of a short s with b - A s short. See
// mlkem_pop/relation.hpp.
//
// Protocol. The structure follows FAEST v1 <https://faest.info> and the VOLEitH paper of Baum et
// al. <https://ia.cr/2023/996>, with the binary subfield VOLE replaced by one over F_q:
//
// 1. VOLE commitment. The prover expands TAU = 16 GGM trees of depth 8. For tree t, each leaf
//    x in [0, 256) yields a commitment com_{t,x} and a vector r_{t,x} in F_q^LHAT. Viewing x as an
//    element of F_q (x < 256 < q), the prover computes
//
//      u_t = sum_x r_{t,x},  v_t = -sum_x x r_{t,x},
//
//    so for any Delta_t in [0, 256), q_t := sum_x (Delta_t - x) r_{t,x} = v_t + Delta_t u_t, and
//    q_t is computable without r_{t,Delta_t}. The prover sends corrections c_t = u_0 - u_t for
//    t > 0, after which the verifier can compute q_t = v_t + Delta_t u for u = u_0. Stacking the
//    TAU repetitions as coordinates of F_{q^16} = F_q[X] / (X^16 - 3) yields a VOLE correlation
//
//      Q_j = V_j + u_j Delta,  where Q_j = sum_t q_{t,j} X^t, V_j = sum_t v_{t,j} X^t, and
//                                    Delta = sum_t Delta_t X^t,
//
//    i.e., a MAC Q_j of each u_j in F_q under the global key Delta in F_{q^16}. Delta is uniform
//    in a set of 2^128 elements.
//
// 2. VOLE consistency check (as in FAEST, Section 5.3 of the spec). The verifier's challenge
//    determines an F_q-linear universal hash H: F_q^LHAT -> F_{q^16}; the prover sends
//    u-tilde = H(u) (masked by the last 16 entries of u) and binds h_t = H(v_t) for each t to the
//    next challenge. The verifier recomputes h_t = H(q_t) - Delta_t u-tilde. This ensures that the
//    corrections c_t are consistent, i.e., that the prover is committed to a single u.
//
// 3. Witness commitment. The prover sends d = w - u[0..WITNESS_LEN), so the verifier gets MACs
//    K_j = Q_j + d_j Delta = V_j + w_j Delta of the witness.
//
// 4. QuickSilver <https://ia.cr/2021/076> for constraints of degree DEGREE. The constraints are
//    combined with powers of a random chi in F_{q^16}. For a root constraint f(x) = 0 on a
//    committed value with MAC K = V + x Delta, the homogenization
//
//      g(K, Delta) = Delta^DEGREE f(K / Delta) = sum_m (f^(m)(x) / m!) V^m Delta^(DEGREE - m)
//
//    is a polynomial in Delta whose leading coefficient f(x) is zero if the constraint holds. The
//    prover sends the masked middle coefficients A_1, ..., A_{DEGREE - 1} of the combined
//    polynomial, and the verifier, who knows Delta and K, recomputes the constant coefficient A_0.
//
// 5. Fiat-Shamir. Delta = H(chal2 || A_0 || A_1 || ...), with A_0 recomputed by the verifier, as
//    in FAEST. The prover opens all leaves of tree t but leaf Delta_t.
//
// Soundness. The QuickSilver check fails with probability at least 1 - DEGREE / 2^128 over Delta
// (Schwartz-Zippel over F_{q^16}, with Delta uniform in a set of size 2^128). The other
// challenges contribute negligibly: chi and the hash key are uniform in F_{q^16}, of size
// q^16 > 2^187. Like FAEST v1, there's no grinding, so a prover making 2^k hash queries succeeds
// with probability about 2^k DEGREE / 2^128.
//
// Zero knowledge. Corrections, d, u-tilde, and the A_i are masked by the (uniform) contribution of
// the unopened leaves. Leaf vectors r_{t,x} are sampled by rejection sampling from AES-CTR, so they
// are exactly uniform; the rejection loop runs in time that depends on the PRG output (not on the
// witness).

#ifndef VOLE_MOLE_VOLEITH_FQ_VOLEITH_HPP
#define VOLE_MOLE_VOLEITH_FQ_VOLEITH_HPP

#include "voleith_fq/field.hpp"

#include "aes.hpp"        // from faest-arch-opt
#include "block.hpp"      // from faest-arch-opt
#include "constants.hpp"  // from faest-arch-opt
#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt
#include "prgs.hpp"       // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <utility>
#include <vector>

namespace vole_mole::voleith_fq::detail {

constexpr size_t TAU = EXT_DEGREE; // number of GGM trees, one per coordinate of Delta
constexpr size_t TREE_DEPTH = 8;
constexpr size_t LEAVES = size_t{1} << TREE_DEPTH;
constexpr size_t TREE_NODES = 2 * LEAVES - 1; // heap order: the children of n are 2n + 1, 2n + 2
static_assert(LEAVES <= Q, "leaf indices must be distinct elements of F_q");

constexpr size_t SEED_BYTES = 16;   // GGM node seeds and leaf PRG seeds (AES-128 keys)
constexpr size_t COM_BYTES = 32;    // leaf commitments
constexpr size_t IV_BYTES = 16;     // the PRG IV, chosen by the prover
constexpr size_t DIGEST_BYTES = 32; // mu, chal1, chal2, and h_com
constexpr size_t DELTA_BYTES = TAU; // chal3 = Delta, one byte per tree
constexpr size_t OPENING_BYTES = TREE_DEPTH * SEED_BYTES + COM_BYTES; // per tree

constexpr size_t PROVE_SEED_BYTES = 32;
using ProveSeed = std::array<uint8_t, PROVE_SEED_BYTES>;
using Digest = std::array<uint8_t, DIGEST_BYTES>;
using Seed = std::array<uint8_t, SEED_BYTES>;

// Domain separators, appended to each hash input.
enum : uint8_t {
    DS_MU = 1,
    DS_PROVER_SEED = 2,
    DS_TREE_ROOTS = 3,
    DS_LEAF = 4,
    DS_CHAL1 = 5,
    DS_VOLE_HASH_KEY = 6,
    DS_CHAL2 = 7,
    DS_QS_CHI = 8,
    DS_CHAL3 = 9,
    DS_LEAF_COMMITMENTS = 10,
};

// Layout of the VOLE and of the proof for Relation R.
template <typename R> struct Layout {
    static constexpr size_t L = R::WITNESS_LEN;
    static constexpr size_t D = R::DEGREE;
    static_assert(L % 2 == 0, "pack12 encodes pairs of elements");
    static_assert(D >= 2);

    // The VOLE: u = (witness masks, QuickSilver masks, VOLE check mask).
    static constexpr size_t OFF_QS_MASK = L;                        // D - 1 elements of F_{q^16}
    static constexpr size_t OFF_VC_MASK = L + (D - 1) * EXT_DEGREE; // 1 element of F_{q^16}
    static constexpr size_t LHAT = OFF_VC_MASK + EXT_DEGREE;

    // The proof.
    static constexpr size_t OFF_IV = 0;
    static constexpr size_t OFF_CORR = OFF_IV + IV_BYTES; // c_1, ..., c_{TAU - 1}
    static constexpr size_t CORR_BYTES = packed12_bytes((TAU - 1) * LHAT);
    static constexpr size_t OFF_UTILDE = OFF_CORR + CORR_BYTES;
    static constexpr size_t UTILDE_BYTES = packed12_bytes(EXT_DEGREE);
    static constexpr size_t OFF_D = OFF_UTILDE + UTILDE_BYTES; // witness correction
    static constexpr size_t D_BYTES = packed12_bytes(L);
    static constexpr size_t OFF_QS = OFF_D + D_BYTES; // A_1, ..., A_{D - 1}
    static constexpr size_t QS_BYTES = packed12_bytes((D - 1) * EXT_DEGREE);
    static constexpr size_t OFF_DELTA = OFF_QS + QS_BYTES;
    static constexpr size_t OFF_OPEN = OFF_DELTA + DELTA_BYTES;
    static constexpr size_t PROOF_BYTES = OFF_OPEN + TAU * OPENING_BYTES;
};

template <typename R> constexpr size_t PROOF_BYTES = Layout<R>::PROOF_BYTES;

// ---------------------------------------------------------------------------------------------
// Symmetric primitives

using Prg = faest::aes_ctr_prg<faest::secpar::s128>;

// PRG tweaks. Node and leaf PRGs are keyed by distinct seeds, but we domain separate them anyway.
constexpr uint32_t node_tweak(size_t t, size_t n) {
    return 0x4000'0000u | static_cast<uint32_t>(t << 9) | static_cast<uint32_t>(n);
}
constexpr uint32_t leaf_tweak(size_t t, size_t x, size_t chunk) {
    return 0x8000'0000u | static_cast<uint32_t>(chunk << 12) | static_cast<uint32_t>(t << 8) |
           static_cast<uint32_t>(x);
}

// Expand the GGM node at `seed` into its two children, written contiguously to `children`.
inline void expand_node(const Seed& seed, const faest::block128& iv, uint32_t tweak,
                        Seed* children) {
    const Prg::key_t key = faest::block128::load(seed.data());
    Prg::expanded_key_t expanded;
    std::array<faest::block128, 2> out;
    Prg::init<1, 2>(&key, &expanded, iv, tweak, uint32_t{0}, out.data());
    out[0].store(children[0].data());
    out[1].store(children[1].data());
}

// Expand a leaf's PRG seed into out.size() uniform elements of F_q, by rejection sampling 12-bit
// chunks of AES-CTR output (as in ML-KEM's SampleNTT).
inline void expand_leaf(const Seed& seed, const faest::block128& iv, size_t t, size_t x,
                        std::span<Fq> out) {
    // AES_MAX_CTR bounds the counter, so we change the tweak every CHUNK_BLOCKS blocks.
    constexpr size_t CHUNK_BLOCKS = 64;
    // constants.hpp provides AES_MAX_CTR through an architecture-specific header.
    static_assert(CHUNK_BLOCKS <= faest::AES_MAX_CTR); // NOLINT(misc-include-cleaner)
    Prg::expanded_key_t expanded;
    faest::aes_keygen<faest::secpar::s128>(&expanded, faest::block128::load(seed.data()));
    std::array<faest::block128, CHUNK_BLOCKS> blocks;
    std::array<uint8_t, CHUNK_BLOCKS * 16> buf;
    size_t n = 0;
    for (size_t chunk = 0; n < out.size(); ++chunk) {
        Prg::gen<1, CHUNK_BLOCKS>(&expanded, iv, leaf_tweak(t, x, chunk), uint32_t{0},
                                  blocks.data());
        for (size_t i = 0; i < CHUNK_BLOCKS; ++i) {
            blocks[i].store(&buf[16 * i]);
        }
        // The last byte of the buffer is dropped, since buf.size() isn't a multiple of 3.
        size_t off = 0;
        // Fast path: while there's room for two more elements, write both candidates
        // unconditionally and advance past the accepted ones.
        for (; off + 3 <= buf.size() && n + 2 <= out.size(); off += 3) {
            const uint32_t d1 = buf[off] | ((uint32_t{buf[off + 1]} & 0xf) << 8);
            const uint32_t d2 = (uint32_t{buf[off + 1]} >> 4) | (uint32_t{buf[off + 2]} << 4);
            out[n] = static_cast<Fq>(d1);
            n += static_cast<size_t>(d1 < Q);
            out[n] = static_cast<Fq>(d2);
            n += static_cast<size_t>(d2 < Q);
        }
        for (; off + 3 <= buf.size() && n < out.size(); off += 3) {
            const uint32_t d1 = buf[off] | ((uint32_t{buf[off + 1]} & 0xf) << 8);
            const uint32_t d2 = (uint32_t{buf[off + 1]} >> 4) | (uint32_t{buf[off + 2]} << 4);
            if (d1 < Q) {
                out[n++] = static_cast<Fq>(d1);
            }
            if (d2 < Q && n < out.size()) {
                out[n++] = static_cast<Fq>(d2);
            }
        }
    }
}

// The leaf PRG seed and commitment: (seed || com) <- H(leaf || iv || t || x).
constexpr size_t LEAF_HASH_BYTES = SEED_BYTES + COM_BYTES;
inline void hash_leaves(std::span<const Seed, LEAVES> leaves, std::span<const uint8_t, IV_BYTES> iv,
                        size_t t, std::span<std::array<uint8_t, LEAF_HASH_BYTES>, LEAVES> out) {
    for (size_t x = 0; x < LEAVES; x += 4) {
        std::array<std::array<uint8_t, 4>, 4> tweaks;
        for (size_t i = 0; i < 4; ++i) {
            const uint32_t tw = static_cast<uint32_t>((t << 8) | (x + i));
            for (size_t b = 0; b < 4; ++b) {
                tweaks[i][b] = static_cast<uint8_t>(tw >> (8 * b));
            }
        }
        faest::hash_state_x4 hasher;
        hasher.init(faest::secpar::s128);
        hasher.update_4(leaves[x].data(), leaves[x + 1].data(), leaves[x + 2].data(),
                        leaves[x + 3].data(), SEED_BYTES);
        hasher.update_1(iv.data(), iv.size());
        hasher.update_4(tweaks[0].data(), tweaks[1].data(), tweaks[2].data(), tweaks[3].data(), 4);
        hasher.update_1_byte(DS_LEAF);
        hasher.finalize_4(out[x].data(), out[x + 1].data(), out[x + 2].data(), out[x + 3].data(),
                          LEAF_HASH_BYTES);
    }
}

inline faest::hash_state new_hasher() {
    faest::hash_state h;
    h.init(faest::secpar::s128); // SHAKE128
    return h;
}

template <size_t N> std::array<uint8_t, N> finalize(faest::hash_state& h, uint8_t ds) {
    h.update_byte(ds);
    std::array<uint8_t, N> out;
    h.finalize(out);
    return out;
}

// A uniform element of F_{q^16} derived from a challenge.
inline Fq16 sample_fq16(std::span<const uint8_t> chal, uint8_t ds) {
    auto h = new_hasher();
    h.update(chal);
    h.update_byte(ds);
    Keccak_HashFinal(&h.ctx, nullptr);
    Fq16 out;
    size_t n = 0;
    while (n < EXT_DEGREE) {
        std::array<uint8_t, 3> b;
        Keccak_HashSqueeze(&h.ctx, b.data(), 8 * b.size());
        const uint32_t d1 = b[0] | ((uint32_t{b[1]} & 0xf) << 8);
        const uint32_t d2 = (uint32_t{b[1]} >> 4) | (uint32_t{b[2]} << 4);
        if (d1 < Q) {
            out.c[n++] = static_cast<Fq>(d1);
        }
        if (d2 < Q && n < EXT_DEGREE) {
            out.c[n++] = static_cast<Fq>(d2);
        }
    }
    return out;
}

// ---------------------------------------------------------------------------------------------
// GGM trees

struct Tree {
    std::array<Seed, TREE_NODES> nodes;

    std::span<const Seed, LEAVES> leaves() const {
        return std::span(nodes).template subspan<LEAVES - 1, LEAVES>();
    }
};

inline void expand_tree_from(Tree& tree, std::array<bool, TREE_NODES>* known,
                             const faest::block128& iv, size_t t) {
    for (size_t n = 0; n < LEAVES - 1; ++n) {
        if (!known || (*known)[n]) {
            expand_node(tree.nodes[n], iv, node_tweak(t, n), &tree.nodes[2 * n + 1]);
            if (known) {
                (*known)[2 * n + 1] = (*known)[2 * n + 2] = true;
            }
        }
    }
}

// The siblings of the path from the root to leaf p, from the top of the tree down.
inline std::array<size_t, TREE_DEPTH> copath(size_t p) {
    std::array<size_t, TREE_DEPTH> out;
    size_t node = LEAVES - 1 + p;
    for (size_t level = TREE_DEPTH; level > 0; --level) {
        out[level - 1] = (node % 2 == 1) ? node + 1 : node - 1;
        node = (node - 1) / 2;
    }
    return out;
}

// ---------------------------------------------------------------------------------------------
// The VOLE consistency check's universal hash, H(x) = sum_{j < m} alpha^(j + 1) x_j +
// sum_{k < 16} X^k x_{m + k}, where m = LHAT - 16. It's F_q-linear. For x != 0, H(x) = 0 with
// probability at most m / q^16 over alpha.

class VoleHash {
  public:
    VoleHash(const Fq16& alpha, size_t lhat) : powers_(lhat - EXT_DEGREE) {
        Fq16 p = alpha;
        for (auto& x : powers_) {
            x = p;
            p *= alpha;
        }
    }

    Fq16 operator()(std::span<const Fq> x) const {
        assert(x.size() == powers_.size() + EXT_DEGREE);
        // No overflow: acc < (lhat + 1) q^2 < 2^64.
        assert(x.size() < (uint64_t{1} << 40));
        std::array<uint64_t, EXT_DEGREE> acc{};
        for (size_t j = 0; j < powers_.size(); ++j) {
            for (size_t i = 0; i < EXT_DEGREE; ++i) {
                acc[i] += uint64_t{powers_[j].c[i]} * x[j];
            }
        }
        Fq16 out;
        for (size_t i = 0; i < EXT_DEGREE; ++i) {
            out.c[i] = static_cast<Fq>((acc[i] + x[powers_.size() + i]) % Q);
        }
        return out;
    }

  private:
    std::vector<Fq16> powers_;
};

// ---------------------------------------------------------------------------------------------
// QuickSilver

// A committed vector of `size()` elements of F_q. Lane t < TAU holds coordinate t of the MAC
// (prover: V, verifier: K) of each element; the prover has an extra lane TAU with the values.
template <bool IsVerifier> class CommittedVec {
  public:
    static constexpr size_t LANES = IsVerifier ? TAU : TAU + 1;

    explicit CommittedVec(size_t len) : len_(len), data_(LANES * len) {}

    size_t size() const { return len_; }
    std::span<Fq> lane(size_t i) { return std::span(data_).subspan(i * len_, len_); }
    std::span<const Fq> lane(size_t i) const { return std::span(data_).subspan(i * len_, len_); }

    // The MAC of element j as an element of F_{q^16}.
    Fq16 mac(size_t j) const {
        Fq16 out;
        for (size_t t = 0; t < TAU; ++t) {
            out.c[t] = data_[t * len_ + j];
        }
        return out;
    }

  private:
    size_t len_;
    std::vector<Fq> data_;
};

// Operations shared by the prover and verifier.
template <bool IsVerifier> class QsBase {
  public:
    using Vec = CommittedVec<IsVerifier>;

    const Vec& witness() const { return witness_; }

    // Apply a public F_q-linear map to a committed vector. f(in, out) must write L(in) to out,
    // where in.size() is in_len and out.size() is out_len.
    template <typename F> Vec apply_linear(const Vec& in, size_t out_len, F&& f) const {
        Vec out(out_len);
        for (size_t l = 0; l < Vec::LANES; ++l) {
            f(in.lane(l), out.lane(l));
        }
        return out;
    }

  protected:
    explicit QsBase(Vec witness, const Fq16& beta)
        : witness_(std::move(witness)), beta_(beta), chi_(Fq16::constant(1)) {}

    Vec witness_;
    Fq16 beta_;
    Fq16 chi_; // beta^c for the c-th constraint
};

template <size_t DEGREE> class ProverQs : public QsBase<false> {
  public:
    ProverQs(Vec witness, const Fq16& beta) : QsBase(std::move(witness), beta) {}

    // v += c for a public vector c.
    void add_constant(Vec& v, std::span<const Fq> c) const {
        auto values = v.lane(TAU);
        for (size_t j = 0; j < v.size(); ++j) {
            values[j] = fq_add(values[j], c[j]);
        }
    }

    // Constrain f(v_j) = 0 for each j, where f = sum_i f[i] x^i has degree at most DEGREE.
    void constrain_roots(const Vec& v, std::span<const Fq, DEGREE + 1> f) {
        // binom[t][m] = t choose m
        std::array<std::array<Fq, DEGREE + 1>, DEGREE + 1> binom{};
        for (size_t t = 0; t <= DEGREE; ++t) {
            binom[t][0] = 1;
            for (size_t m = 1; m <= t; ++m) {
                binom[t][m] = fq_add(binom[t - 1][m - 1], m < t ? binom[t - 1][m] : Fq{0});
            }
        }
        const auto values = v.lane(TAU);
        for (size_t j = 0; j < v.size(); ++j) {
            const Fq a = values[j];
            const Fq16 mac = v.mac(j);

            // The Taylor coefficients f^(m)(a) / m! = sum_{t >= m} f[t] (t choose m) a^(t - m).
            std::array<Fq, DEGREE + 1> a_pow;
            a_pow[0] = 1;
            for (size_t i = 1; i <= DEGREE; ++i) {
                a_pow[i] = fq_mul(a_pow[i - 1], a);
            }
            std::array<Fq, DEGREE + 1> taylor;
            for (size_t m = 0; m <= DEGREE; ++m) {
                static_assert(uint64_t{DEGREE + 1} * (Q - 1) < (uint64_t{1} << 32));
                uint32_t acc = 0;
                for (size_t t = m; t <= DEGREE; ++t) {
                    acc += fq_mul(fq_mul(f[t], binom[t][m]), a_pow[t - m]);
                }
                taylor[m] = fq_reduce(acc);
            }

            // chi * g(K, Delta) = sum_m taylor[m] chi V^m Delta^(DEGREE - m).
            coeffs_[DEGREE].add_scaled(taylor[0], chi_);
            Fq16 p = chi_ * mac;
            for (size_t m = 1; m <= DEGREE; ++m) {
                coeffs_[DEGREE - m].add_scaled(taylor[m], p);
                if (m < DEGREE) {
                    p *= mac;
                }
            }
            chi_ *= beta_;
        }
    }

    // The coefficients of the combined polynomial in Delta. The leading coefficient is zero if
    // all constraints hold.
    std::array<Fq16, DEGREE + 1>& coeffs() { return coeffs_; }

  private:
    std::array<Fq16, DEGREE + 1> coeffs_{};
};

template <size_t DEGREE> class VerifierQs : public QsBase<true> {
  public:
    VerifierQs(Vec witness, const Fq16& beta, std::span<const uint8_t, DELTA_BYTES> delta)
        : QsBase(std::move(witness), beta) {
        for (size_t t = 0; t < TAU; ++t) {
            delta_.c[t] = delta[t];
        }
        delta_pow_[0] = Fq16::constant(1);
        for (size_t i = 1; i <= DEGREE; ++i) {
            delta_pow_[i] = delta_pow_[i - 1] * delta_;
        }
    }

    // v += c for a public vector c: K += c Delta.
    void add_constant(Vec& v, std::span<const Fq> c) const {
        for (size_t t = 0; t < TAU; ++t) {
            auto lane = v.lane(t);
            for (size_t j = 0; j < v.size(); ++j) {
                lane[j] = fq_reduce(lane[j] + uint32_t{c[j]} * delta_.c[t]);
            }
        }
    }

    void constrain_roots(const Vec& v, std::span<const Fq, DEGREE + 1> f) {
        for (size_t j = 0; j < v.size(); ++j) {
            const Fq16 k = v.mac(j);
            // g(K, Delta) = sum_t f[t] K^t Delta^(DEGREE - t), by Horner's rule.
            Fq16 g = Fq16::constant(f[DEGREE]);
            for (size_t t = DEGREE; t-- > 0;) {
                g *= k;
                g.add_scaled(f[t], delta_pow_[DEGREE - t]);
            }
            sum_ += chi_ * g;
            chi_ *= beta_;
        }
    }

    const Fq16& delta() const { return delta_; }
    const Fq16& delta_pow(size_t i) const { return delta_pow_[i]; }
    Fq16& sum() { return sum_; }

  private:
    Fq16 delta_;
    std::array<Fq16, DEGREE + 1> delta_pow_;
    Fq16 sum_ = Fq16::zero();
};

// ---------------------------------------------------------------------------------------------
// Prover and verifier

namespace internal {

inline void hash_fq(faest::hash_state& h, std::span<const Fq> x) {
    for (const Fq a : x) {
        const std::array<uint8_t, 2> b = {static_cast<uint8_t>(a), static_cast<uint8_t>(a >> 8)};
        h.update(b);
    }
}

inline void hash_fq16(faest::hash_state& h, const Fq16& x) { h.update(x.serialize()); }

template <typename R> Digest hash_mu(const typename R::instance& x) {
    auto h = new_hasher();
    R::hash_instance(h, x);
    h.update(R::DST);
    return finalize<DIGEST_BYTES>(h, DS_MU);
}

// The mask (an element of F_{q^16}) whose 16 coordinates are u[off], ..., u[off + 15], or its MAC.
inline Fq16 gather16(std::span<const Fq> u, size_t off) {
    Fq16 out;
    std::copy_n(u.begin() + static_cast<ptrdiff_t>(off), EXT_DEGREE, out.c.begin());
    return out;
}
// sum_k X^k M_{off + k}, where M_j is the MAC with coordinates lanes[t][j].
inline Fq16 gather16_mac(std::span<const std::vector<Fq>, TAU> lanes, size_t off) {
    Fq16 out = Fq16::zero();
    for (size_t k = 0; k < EXT_DEGREE; ++k) {
        Fq16 m;
        for (size_t t = 0; t < TAU; ++t) {
            m.c[t] = lanes[t][off + k];
        }
        out += m.mul_monomial(k);
    }
    return out;
}

} // namespace internal

// Generate a proof that witness w satisfies relation R for instance x. rho is the prover's
// randomness. The proof is a deterministic function of (x, w, rho).
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by R::hash_instance or
// R::constraints are propagated. If w doesn't satisfy the relation, then the proof is invalid.
template <typename R>
void prove(std::span<uint8_t, PROOF_BYTES<R>> proof, const typename R::instance& x,
           std::span<const Fq, R::WITNESS_LEN> w, const ProveSeed& rho) {
    using Lay = Layout<R>;
    constexpr size_t L = Lay::L, D = Lay::D, LHAT = Lay::LHAT;

    const Digest mu = internal::hash_mu<R>(x);

    // (seed, iv) <- H(w || mu || rho)
    std::array<uint8_t, SEED_BYTES + IV_BYTES> seed_iv;
    {
        auto h = new_hasher();
        internal::hash_fq(h, w);
        h.update(mu);
        h.update(rho);
        seed_iv = finalize<SEED_BYTES + IV_BYTES>(h, DS_PROVER_SEED);
    }
    const auto iv = std::span(proof).template subspan<Lay::OFF_IV, IV_BYTES>();
    std::ranges::copy(std::span(seed_iv).template last<IV_BYTES>(), iv.begin());
    const faest::block128 iv_block = faest::block128::load(iv.data());

    // The roots of the GGM trees.
    std::vector<Tree> trees(TAU);
    {
        auto h = new_hasher();
        h.update(std::span(seed_iv).template first<SEED_BYTES>());
        h.update(iv);
        const auto roots = finalize<TAU * SEED_BYTES>(h, DS_TREE_ROOTS);
        for (size_t t = 0; t < TAU; ++t) {
            std::copy_n(&roots[t * SEED_BYTES], SEED_BYTES, trees[t].nodes[0].begin());
        }
    }

    // 1. VOLE commitment.
    std::vector<Fq> u(LHAT);                       // u_0
    std::array<std::vector<Fq>, TAU> v;            // v_t
    std::vector<Fq> corrections((TAU - 1) * LHAT); // c_t = u_0 - u_t
    std::vector<std::array<uint8_t, COM_BYTES>> coms(TAU * LEAVES);
    auto h_com = new_hasher();
    {
        std::vector<std::array<uint8_t, LEAF_HASH_BYTES>> leaf_hashes(LEAVES);
        std::vector<Fq> r(LHAT);
        std::vector<uint32_t> u_acc(LHAT), v_acc(LHAT);
        for (size_t t = 0; t < TAU; ++t) {
            expand_tree_from(trees[t], nullptr, iv_block, t);
            hash_leaves(trees[t].leaves(), iv, t,
                        std::span<std::array<uint8_t, LEAF_HASH_BYTES>, LEAVES>(leaf_hashes));
            std::ranges::fill(u_acc, 0);
            std::ranges::fill(v_acc, 0);
            for (size_t xi = 0; xi < LEAVES; ++xi) {
                Seed leaf_seed;
                std::copy_n(leaf_hashes[xi].begin(), SEED_BYTES, leaf_seed.begin());
                std::copy_n(leaf_hashes[xi].begin() + SEED_BYTES, COM_BYTES,
                            coms[t * LEAVES + xi].begin());
                h_com.update(coms[t * LEAVES + xi]);
                expand_leaf(leaf_seed, iv_block, t, xi, r);
                // No overflow: u_acc < 256 q and v_acc < 256^2 q.
                static_assert(uint64_t{LEAVES} * LEAVES * Q < (uint64_t{1} << 32));
                for (size_t j = 0; j < LHAT; ++j) {
                    u_acc[j] += r[j];
                    v_acc[j] += static_cast<uint32_t>(xi) * r[j];
                }
            }
            v[t].resize(LHAT);
            for (size_t j = 0; j < LHAT; ++j) {
                v[t][j] = fq_neg(fq_reduce(v_acc[j]));
                const Fq u_t = fq_reduce(u_acc[j]);
                if (t == 0) {
                    u[j] = u_t;
                } else {
                    corrections[(t - 1) * LHAT + j] = fq_sub(u[j], u_t);
                }
            }
        }
    }
    const auto corr_bytes = std::span(proof).template subspan<Lay::OFF_CORR, Lay::CORR_BYTES>();
    pack12(corrections, corr_bytes);
    const auto h_com_digest = finalize<DIGEST_BYTES>(h_com, DS_LEAF_COMMITMENTS);

    // chal1 <- H(mu || iv || h_com || c_1 || ... || c_{TAU - 1})
    Digest chal1;
    {
        auto h = new_hasher();
        h.update(mu);
        h.update(iv);
        h.update(h_com_digest);
        h.update(corr_bytes);
        chal1 = finalize<DIGEST_BYTES>(h, DS_CHAL1);
    }

    // 2. VOLE consistency check: u-tilde = H(u), h_t = H(v_t).
    const VoleHash vole_hash(sample_fq16(chal1, DS_VOLE_HASH_KEY), LHAT);
    const Fq16 u_tilde = vole_hash(u);
    const auto u_tilde_bytes =
        std::span(proof).template subspan<Lay::OFF_UTILDE, Lay::UTILDE_BYTES>();
    pack12(u_tilde.c, u_tilde_bytes);

    // 3. Witness commitment: d = w - u[0..L).
    std::vector<Fq> d(L);
    for (size_t j = 0; j < L; ++j) {
        d[j] = fq_sub(w[j], u[j]);
    }
    const auto d_bytes = std::span(proof).template subspan<Lay::OFF_D, Lay::D_BYTES>();
    pack12(d, d_bytes);

    // chal2 <- H(chal1 || u-tilde || h_0 || ... || h_{TAU - 1} || d)
    Digest chal2;
    {
        auto h = new_hasher();
        h.update(chal1);
        h.update(u_tilde_bytes);
        for (size_t t = 0; t < TAU; ++t) {
            internal::hash_fq16(h, vole_hash(v[t]));
        }
        h.update(d_bytes);
        chal2 = finalize<DIGEST_BYTES>(h, DS_CHAL2);
    }

    // 4. QuickSilver.
    typename ProverQs<D>::Vec witness(L);
    for (size_t t = 0; t < TAU; ++t) {
        std::copy_n(v[t].begin(), L, witness.lane(t).begin());
    }
    std::ranges::copy(w, witness.lane(TAU).begin());
    ProverQs<D> qs(std::move(witness), sample_fq16(chal2, DS_QS_CHI));
    R::constraints(qs, x);

    // Add the mask sum_{i = 1}^{D - 1} K_{r_i} Delta^(i - 1), where K_{r_i} = M_i + r_i Delta.
    auto& coeffs = qs.coeffs();
    for (size_t i = 1; i < D; ++i) {
        const size_t off = Lay::OFF_QS_MASK + (i - 1) * EXT_DEGREE;
        coeffs[i - 1] += internal::gather16_mac(v, off);
        coeffs[i] += internal::gather16(u, off);
    }
    std::array<Fq, (D - 1) * EXT_DEGREE> qs_proof;
    for (size_t i = 1; i < D; ++i) {
        std::ranges::copy(coeffs[i].c,
                          qs_proof.begin() + static_cast<ptrdiff_t>((i - 1) * EXT_DEGREE));
    }
    const auto qs_bytes = std::span(proof).template subspan<Lay::OFF_QS, Lay::QS_BYTES>();
    pack12(qs_proof, qs_bytes);

    // 5. Delta = chal3 <- H(chal2 || A_0 || A_1 || ... || A_{D - 1})
    const auto delta = std::span(proof).template subspan<Lay::OFF_DELTA, DELTA_BYTES>();
    {
        auto h = new_hasher();
        h.update(chal2);
        internal::hash_fq16(h, coeffs[0]);
        h.update(qs_bytes);
        std::ranges::copy(finalize<DELTA_BYTES>(h, DS_CHAL3), delta.begin());
    }

    // Open all leaves but leaf Delta_t of tree t.
    for (size_t t = 0; t < TAU; ++t) {
        const size_t p = delta[t];
        uint8_t* out = &proof[Lay::OFF_OPEN + t * OPENING_BYTES];
        for (const size_t node : copath(p)) {
            out = std::ranges::copy(trees[t].nodes[node], out).out;
        }
        std::ranges::copy(coms[t * LEAVES + p], out);
    }
}

// Verify a proof for instance x of relation R. Returns false if the proof is invalid.
//
// Throws std::bad_alloc if memory allocation fails. Exceptions thrown by R::hash_instance or
// R::constraints are propagated. An invalid proof never causes an exception.
template <typename R>
bool verify(std::span<const uint8_t, PROOF_BYTES<R>> proof, const typename R::instance& x) {
    using Lay = Layout<R>;
    constexpr size_t L = Lay::L, D = Lay::D, LHAT = Lay::LHAT;

    // Decode the proof. Every element of F_q must be in canonical form.
    const auto iv = proof.template subspan<Lay::OFF_IV, IV_BYTES>();
    const auto corr_bytes = proof.template subspan<Lay::OFF_CORR, Lay::CORR_BYTES>();
    const auto u_tilde_bytes = proof.template subspan<Lay::OFF_UTILDE, Lay::UTILDE_BYTES>();
    const auto d_bytes = proof.template subspan<Lay::OFF_D, Lay::D_BYTES>();
    const auto qs_bytes = proof.template subspan<Lay::OFF_QS, Lay::QS_BYTES>();
    const auto delta = proof.template subspan<Lay::OFF_DELTA, DELTA_BYTES>();
    std::vector<Fq> corrections((TAU - 1) * LHAT);
    Fq16 u_tilde;
    std::vector<Fq> d(L);
    std::array<Fq, (D - 1) * EXT_DEGREE> qs_proof;
    if (!unpack12(corr_bytes, corrections) || !unpack12(u_tilde_bytes, u_tilde.c) ||
        !unpack12(d_bytes, d) || !unpack12(qs_bytes, qs_proof)) {
        return false;
    }
    const faest::block128 iv_block = faest::block128::load(iv.data());

    const Digest mu = internal::hash_mu<R>(x);

    // 1. Reconstruct the VOLE: q_t = sum_{x != Delta_t} (Delta_t - x) r_{t,x}.
    std::array<std::vector<Fq>, TAU> q;
    auto h_com = new_hasher();
    {
        Tree tree;
        std::vector<std::array<uint8_t, LEAF_HASH_BYTES>> leaf_hashes(LEAVES);
        std::vector<Fq> r(LHAT);
        std::vector<uint32_t> q_acc(LHAT);
        for (size_t t = 0; t < TAU; ++t) {
            const size_t p = delta[t];
            const uint8_t* opening = &proof[Lay::OFF_OPEN + t * OPENING_BYTES];
            std::array<bool, TREE_NODES> known{};
            for (const size_t node : copath(p)) {
                std::copy_n(opening, SEED_BYTES, tree.nodes[node].begin());
                known[node] = true;
                opening += SEED_BYTES;
            }
            tree.nodes[LEAVES - 1 + p] = {}; // unknown; its hash is ignored
            expand_tree_from(tree, &known, iv_block, t);
            hash_leaves(tree.leaves(), iv, t,
                        std::span<std::array<uint8_t, LEAF_HASH_BYTES>, LEAVES>(leaf_hashes));
            std::ranges::fill(q_acc, 0);
            for (size_t xi = 0; xi < LEAVES; ++xi) {
                if (xi == p) {
                    h_com.update(opening, COM_BYTES);
                    continue;
                }
                Seed leaf_seed;
                std::copy_n(leaf_hashes[xi].begin(), SEED_BYTES, leaf_seed.begin());
                h_com.update(std::span(leaf_hashes[xi]).template last<COM_BYTES>());
                expand_leaf(leaf_seed, iv_block, t, xi, r);
                // No overflow: q_acc < 255 q^2 < 2^32.
                static_assert(uint64_t{LEAVES - 1} * (Q - 1) * (Q - 1) < (uint64_t{1} << 32));
                const uint32_t coeff = fq_sub(static_cast<Fq>(p), static_cast<Fq>(xi));
                for (size_t j = 0; j < LHAT; ++j) {
                    q_acc[j] += coeff * r[j];
                }
            }
            q[t].resize(LHAT);
            for (size_t j = 0; j < LHAT; ++j) {
                q[t][j] = fq_reduce(q_acc[j]);
            }
        }
    }
    const auto h_com_digest = finalize<DIGEST_BYTES>(h_com, DS_LEAF_COMMITMENTS);

    Digest chal1;
    {
        auto h = new_hasher();
        h.update(mu);
        h.update(iv);
        h.update(h_com_digest);
        h.update(corr_bytes);
        chal1 = finalize<DIGEST_BYTES>(h, DS_CHAL1);
    }

    // Apply the corrections: q_t += c_t Delta_t, so that q_t = v_t + u Delta_t.
    for (size_t t = 1; t < TAU; ++t) {
        const uint32_t delta_t = delta[t];
        for (size_t j = 0; j < LHAT; ++j) {
            q[t][j] = fq_reduce(q[t][j] + corrections[(t - 1) * LHAT + j] * delta_t);
        }
    }

    // 2. VOLE consistency check: h_t = H(q_t) - Delta_t u-tilde.
    const VoleHash vole_hash(sample_fq16(chal1, DS_VOLE_HASH_KEY), LHAT);
    Digest chal2;
    {
        auto h = new_hasher();
        h.update(chal1);
        h.update(u_tilde_bytes);
        for (size_t t = 0; t < TAU; ++t) {
            internal::hash_fq16(h, vole_hash(q[t]) - Fq{delta[t]} * u_tilde);
        }
        h.update(d_bytes);
        chal2 = finalize<DIGEST_BYTES>(h, DS_CHAL2);
    }

    // 3. Witness MACs: K_j = Q_j + d_j Delta.
    typename VerifierQs<D>::Vec witness(L);
    for (size_t t = 0; t < TAU; ++t) {
        const uint32_t delta_t = delta[t];
        auto lane = witness.lane(t);
        for (size_t j = 0; j < L; ++j) {
            lane[j] = fq_reduce(q[t][j] + d[j] * delta_t);
        }
    }

    // 4. QuickSilver.
    VerifierQs<D> qs(std::move(witness), sample_fq16(chal2, DS_QS_CHI), delta);
    R::constraints(qs, x);
    Fq16 a0 = qs.sum();
    for (size_t i = 1; i < D; ++i) {
        const size_t off = Lay::OFF_QS_MASK + (i - 1) * EXT_DEGREE;
        a0 += internal::gather16_mac(q, off) * qs.delta_pow(i - 1);
        Fq16 a_i;
        std::copy_n(qs_proof.begin() + static_cast<ptrdiff_t>((i - 1) * EXT_DEGREE), EXT_DEGREE,
                    a_i.c.begin());
        a0 -= a_i * qs.delta_pow(i);
    }

    // 5. Check Delta = H(chal2 || A_0 || A_1 || ... || A_{D - 1}).
    auto h = new_hasher();
    h.update(chal2);
    internal::hash_fq16(h, a0);
    h.update(qs_bytes);
    const auto delta_check = finalize<DELTA_BYTES>(h, DS_CHAL3);
    return std::ranges::equal(delta, delta_check);
}

} // namespace vole_mole::voleith_fq::detail

#endif
