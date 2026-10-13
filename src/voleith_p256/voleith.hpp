// VOLE-in-the-Head (VOLEitH) over the two prime fields of P-256: the base field F_p and the scalar
// field F_n.
//
// FAEST's VOLEitH (src/voleith.hpp) commits to bits with MACs in GF(2^128), so arithmetic modulo a
// 256-bit prime would need adder and multiplier circuits. This proof system commits to elements of
// F_p and F_n directly, so that arithmetic in either field is native. It's modeled on the VOLEitH
// paper of Baum et al. <https://ia.cr/2023/996> and FAEST v1 <https://faest.info>, and follows the
// F_3329 proof system of the ML-KEM proof of possession (PR #46), with two differences:
//
//   - The fields are larger than 2^128, so the VOLE key Delta, the MACs, and the QuickSilver
//     challenges are elements of the field itself; there's no extension field.
//   - The VOLE commits to elements of both fields at once, under the same Delta.
//
// Relations. A relation has a witness w_p in F_p^LP and w_n in F_n^LN, and constraints f = 0, where
// f is a polynomial expression in the committed values over either field, of degree at most DP
// (over F_p) or DN (over F_n). See qs.hpp.
//
// Protocol.
//
// 1. VOLE commitment. The prover expands TAU GGM trees of depth DEPTH, with N = 2^DEPTH leaves
//    each. For tree t, each leaf x in [0, N) yields a commitment com_{t,x} and a vector r_{t,x} of
//    LHAT = LHAT_P + LHAT_N field elements (the first LHAT_P in F_p, the rest in F_n). Viewing x as
//    an integer, the prover computes, in each row's field,
//
//      u_t = sum_x r_{t,x},  v_t = -sum_x x r_{t,x},
//
//    so that for any Delta_t in [0, N), q_t := sum_x (Delta_t - x) r_{t,x} = v_t + Delta_t u_t,
//    which the verifier can compute without r_{t,Delta_t}. The prover sends c_t = u_0 - u_t for
//    t > 0, after which the verifier can compute q_t = v_t + Delta_t u for u = u_0. Then
//
//      Q_j = V_j + u_j Delta,  where Q_j = sum_t N^t q_{t,j}, V_j = sum_t N^t v_{t,j}, and
//                                    Delta = sum_t N^t Delta_t,
//
//    i.e., a MAC Q_j of u_j under the key Delta, in the field of row j. Delta is an integer, uniform
//    in [0, N^TAU), and N^TAU < n < p, so it's uniform in a set of N^TAU elements of either field.
//
// 2. VOLE consistency check, per field (as in FAEST v1). The verifier's challenge determines a
//    linear universal hash H(x) = sum_{j < m} alpha^(j + 1) x_j + x_m, where m = LHAT_F - 1 and
//    x_m is a mask row. The prover sends u-tilde = H(u) and binds h_t = H(v_t) for each t to the
//    next challenge; the verifier recomputes h_t = H(q_t) - Delta_t u-tilde. This ensures that the
//    corrections c_t are consistent (up to guessing Delta_t for the trees where they aren't, which
//    costs as much as it saves, as in FAEST v1).
//
// 3. Witness commitment. The prover sends d = w - u[0..L), so the verifier gets MACs
//    K_j = Q_j + d_j Delta = V_j + w_j Delta of the witness.
//
// 4. QuickSilver, per field (qs.hpp), with the constraints combined by powers of a random chi. The
//    prover sends the middle coefficients A_1, ..., A_{D - 1} of the combined polynomial in Delta,
//    masked by sum_{i = 1}^{D - 1} K_{r_i} Delta^(i - 1) for D - 1 random mask rows r_i, and the
//    verifier recomputes A_0.
//
// 5. Fiat-Shamir. Delta = H(chal3_seed || A_0 || A_1 || ...) (for both fields), with A_0
//    recomputed by the verifier, as in FAEST. The prover opens all leaves of tree t but leaf
//    Delta_t.
//
// The proof is split in two steps, so that challenges of another proof can be derived from the
// commitment to the witness (see ecdsa_pok/): prove_commit produces the VOLE and witness commitment
// and chal2, a digest that binds it, and prove_finish produces the rest. The caller binds data
// (`binder`) to the QuickSilver challenges.
//
// Soundness. For each field, the QuickSilver check fails with probability at least
// 1 - D / N^TAU over Delta (Schwartz-Zippel, with Delta uniform in a set of size N^TAU). The other
// challenges are uniform in F_p or F_n and contribute negligibly. There's no grinding, so a prover
// making 2^k hash queries succeeds with probability about 2^k D / N^TAU.
//
// Zero knowledge. Corrections, d, u-tilde, and the A_i are masked by the (uniform) contribution of
// the unopened leaves. Leaf vectors are sampled from AES-CTR by rejection sampling (accepting 32-byte
// candidates less than the modulus, which fails with probability about 2^-32), so they're exactly
// uniform; the rejection loop runs in time that depends on the PRG output, not on the witness.

#ifndef VOLE_MOLE_VOLEITH_P256_VOLEITH_HPP
#define VOLE_MOLE_VOLEITH_P256_VOLEITH_HPP

#include "p256/field.hpp"
#include "voleith_p256/qs.hpp"

#include "block.hpp" // from faest-arch-opt
#include "hash.hpp"  // from faest-arch-opt
#include "prgs.hpp"  // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::voleith_p256 {

using p256::Fn;
using p256::Fp;

constexpr size_t ELEM_BYTES = 32;
constexpr size_t SEED_BYTES = 16;   // GGM node seeds and leaf PRG seeds (AES-128 keys)
constexpr size_t COM_BYTES = 32;    // leaf commitments
constexpr size_t IV_BYTES = 16;     // the PRG IV, chosen by the prover
constexpr size_t DIGEST_BYTES = 32; // mu, chal1, chal2, ...

constexpr size_t PROVE_SEED_BYTES = 32;
using ProveSeed = std::array<uint8_t, PROVE_SEED_BYTES>;
using Digest = std::array<uint8_t, DIGEST_BYTES>;
using Seed = std::array<uint8_t, SEED_BYTES>;

// The VOLE parameters: TAU trees of depth DEPTH, so Delta is uniform in a set of 2^(TAU DEPTH).
template <size_t TAU_, size_t DEPTH_> struct VoleParams {
    static constexpr size_t TAU = TAU_;
    static constexpr size_t DEPTH = DEPTH_;
    static constexpr size_t LEAVES = size_t{1} << DEPTH;
    static constexpr size_t TREE_NODES = 2 * LEAVES - 1; // heap order
    static_assert(TAU * DEPTH >= 128 && TAU * DEPTH < 255);
    static_assert(TAU <= 16 && DEPTH <= 16);
    static constexpr size_t DELTA_BYTES = 2 * TAU; // Delta_t as 2 little-endian bytes
    static constexpr size_t OPENING_BYTES = DEPTH * SEED_BYTES + COM_BYTES; // per tree
};

// FAEST-128f-like: 16 trees of 256 leaves.
using Fast = VoleParams<16, 8>;
// FAEST-128s-like: 11 trees of 4096 leaves.
using Small = VoleParams<11, 12>;

namespace detail {

// Domain separators, appended to each hash input.
enum : uint8_t {
    DS_PROVER_SEED = 1,
    DS_TREE_ROOTS = 2,
    DS_LEAF = 3,
    DS_LEAF_COMMITMENTS = 4,
    DS_CHAL1 = 5,
    DS_VOLE_HASH_P = 6,
    DS_VOLE_HASH_N = 7,
    DS_CHAL2 = 8,
    DS_QS_CHI_P = 9,
    DS_QS_CHI_N = 10,
    DS_CHAL3_SEED = 11,
    DS_CHAL3 = 12,
};

using Prg = faest::aes_ctr_prg<faest::secpar::s128>;

constexpr uint32_t node_tweak(size_t t, size_t n) {
    return 0x4000'0000u | static_cast<uint32_t>(t << 24) | static_cast<uint32_t>(n);
}
constexpr uint32_t leaf_tweak(size_t t, size_t x, size_t chunk) {
    return 0x8000'0000u | static_cast<uint32_t>(chunk << 20) | static_cast<uint32_t>(t << 16) |
           static_cast<uint32_t>(x);
}

inline void expand_node(const Seed& seed, const faest::block128& iv, uint32_t tweak,
                        Seed* children) {
    const Prg::key_t key = faest::block128::load(seed.data());
    Prg::expanded_key_t expanded;
    std::array<faest::block128, 2> out;
    Prg::init<1, 2>(&key, &expanded, iv, tweak, uint32_t{0}, out.data());
    out[0].store(children[0].data());
    out[1].store(children[1].data());
}

// A 32-byte little-endian candidate, accepted if it's less than F::M. It's used as the Montgomery
// representation of the element, which is uniform if the candidate is.
template <typename F> bool accept(const uint8_t* b, F& out) {
    p256::Limbs x;
    std::memcpy(x.data(), b, 32);
    if (p256::detail::limbs_ge(x, F::M)) {
        return false;
    }
    out = F::from_mont(x);
    return true;
}

// Expand a leaf's PRG seed into uniform elements of F_p (out_p) and then F_n (out_n).
inline void expand_leaf(const Seed& seed, const faest::block128& iv, size_t t, size_t x,
                        std::span<Fp> out_p, std::span<Fn> out_n) {
    constexpr size_t CHUNK_BLOCKS = 64; // AES_MAX_CTR bounds the counter, so we change the tweak
    Prg::expanded_key_t expanded;
    faest::aes_keygen<faest::secpar::s128>(&expanded, faest::block128::load(seed.data()));
    std::array<faest::block128, CHUNK_BLOCKS> blocks;
    alignas(16) std::array<uint8_t, CHUNK_BLOCKS * 16> buf;
    size_t np = 0, nn = 0;
    for (size_t chunk = 0; np < out_p.size() || nn < out_n.size(); ++chunk) {
        Prg::gen<1, CHUNK_BLOCKS>(&expanded, iv, leaf_tweak(t, x, chunk), uint32_t{0},
                                  blocks.data());
        for (size_t i = 0; i < CHUNK_BLOCKS; ++i) {
            blocks[i].store(&buf[16 * i]);
        }
        for (size_t off = 0; off < buf.size(); off += 32) {
            if (np < out_p.size()) {
                np += accept(&buf[off], out_p[np]);
            } else if (nn < out_n.size()) {
                nn += accept(&buf[off], out_n[nn]);
            } else {
                break;
            }
        }
    }
}

constexpr size_t LEAF_HASH_BYTES = SEED_BYTES + COM_BYTES;

// The leaf PRG seed and commitment: (seed || com) <- H(leaf || iv || t || x).
inline void hash_leaves(std::span<const Seed> leaves, std::span<const uint8_t, IV_BYTES> iv,
                        size_t t, std::span<std::array<uint8_t, LEAF_HASH_BYTES>> out) {
    for (size_t x = 0; x < leaves.size(); x += 4) {
        std::array<std::array<uint8_t, 4>, 4> tweaks;
        for (size_t i = 0; i < 4; ++i) {
            const uint32_t tw = static_cast<uint32_t>((t << 16) | (x + i));
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

// A uniform field element derived from H(chal || ds), by rejection sampling.
template <typename F> F sample(std::span<const uint8_t> chal, uint8_t ds) {
    auto h = new_hasher();
    h.update(chal);
    h.update_byte(ds);
    Keccak_HashFinal(&h.ctx, nullptr);
    for (;;) {
        std::array<uint8_t, 32> b;
        Keccak_HashSqueeze(&h.ctx, b.data(), 8 * b.size());
        F out;
        if (accept(b.data(), out)) {
            return out;
        }
    }
}

template <typename F> void hash_elems(faest::hash_state& h, std::span<const F> x) {
    for (const F& a : x) {
        h.update(a.to_bytes());
    }
}

template <typename F> void store(uint8_t* out, const F& x) {
    const auto b = x.to_bytes();
    std::memcpy(out, b.data(), b.size());
}
template <typename F> std::optional<F> load(const uint8_t* in) {
    return F::from_bytes(std::span<const uint8_t, 32>(in, 32));
}

template <typename P> struct Tree {
    std::vector<Seed> nodes = std::vector<Seed>(P::TREE_NODES);

    std::span<const Seed> leaves() const {
        return std::span(nodes).subspan(P::LEAVES - 1, P::LEAVES);
    }
};

template <typename P>
void expand_tree_from(Tree<P>& tree, std::vector<bool>* known, const faest::block128& iv,
                      size_t t) {
    for (size_t n = 0; n < P::LEAVES - 1; ++n) {
        if (!known || (*known)[n]) {
            expand_node(tree.nodes[n], iv, node_tweak(t, n), &tree.nodes[2 * n + 1]);
            if (known) {
                (*known)[2 * n + 1] = (*known)[2 * n + 2] = true;
            }
        }
    }
}

// The siblings of the path from the root to leaf p, from the top of the tree down.
template <typename P> std::array<size_t, P::DEPTH> copath(size_t p) {
    std::array<size_t, P::DEPTH> out;
    size_t node = P::LEAVES - 1 + p;
    for (size_t level = P::DEPTH; level > 0; --level) {
        out[level - 1] = (node % 2 == 1) ? node + 1 : node - 1;
        node = (node - 1) / 2;
    }
    return out;
}

// The VOLE consistency check's universal hash over F.
template <typename F> class VoleHash {
  public:
    VoleHash(const F& alpha, size_t lhat) : powers_(lhat - 1) {
        F p = alpha;
        for (auto& x : powers_) {
            x = p;
            p *= alpha;
        }
    }
    F operator()(std::span<const F> x) const {
        F acc = x[powers_.size()];
        for (size_t j = 0; j < powers_.size(); ++j) {
            acc += powers_[j] * x[j];
        }
        return acc;
    }

  private:
    std::vector<F> powers_;
};

} // namespace detail

// Layout of the VOLE and of the proof for relation R and VOLE parameters P.
template <typename R, typename P> struct Layout {
    static constexpr size_t TAU = P::TAU;
    static constexpr size_t LP = R::LP, LN = R::LN, DP = R::DP, DN = R::DN;
    static_assert(DP >= 2 && DN >= 2);

    // The VOLE rows of each field: witness, QuickSilver masks, VOLE check mask.
    static constexpr size_t LHAT_P = LP + DP;
    static constexpr size_t LHAT_N = LN + DN;

    static constexpr size_t OFF_IV = 0;
    static constexpr size_t OFF_CORR = OFF_IV + IV_BYTES; // c_1, ..., c_{TAU - 1}
    static constexpr size_t CORR_BYTES = (TAU - 1) * (LHAT_P + LHAT_N) * ELEM_BYTES;
    static constexpr size_t OFF_UTILDE = OFF_CORR + CORR_BYTES; // u-tilde_p, u-tilde_n
    static constexpr size_t OFF_D = OFF_UTILDE + 2 * ELEM_BYTES;
    static constexpr size_t D_BYTES = (LP + LN) * ELEM_BYTES;
    static constexpr size_t OFF_QS = OFF_D + D_BYTES; // A_1, ..., A_{D - 1} for F_p, then F_n
    static constexpr size_t QS_BYTES = (DP - 1 + DN - 1) * ELEM_BYTES;
    static constexpr size_t OFF_DELTA = OFF_QS + QS_BYTES;
    static constexpr size_t OFF_OPEN = OFF_DELTA + P::DELTA_BYTES;
    static constexpr size_t PROOF_BYTES = OFF_OPEN + TAU * P::OPENING_BYTES;
};

// The constraint context passed to R::constraints.
template <typename R, bool IsVerifier> class Context {
  public:
    using PV = Val<Fp, IsVerifier, R::DP>;
    using NV = Val<Fn, IsVerifier, R::DN>;
    static constexpr bool is_verifier = IsVerifier;

    PV wp(size_t i) const { return wp_[i]; }
    NV wn(size_t i) const { return wn_[i]; }
    PV cp(const Fp& x) const { return qp_.constant(x); }
    NV cn(const Fn& x) const { return qn_.constant(x); }
    void add_p(const PV& f) { qp_.add(f); }
    void add_n(const NV& f) { qn_.add(f); }

    QsField<Fp, IsVerifier, R::DP> qp_;
    QsField<Fn, IsVerifier, R::DN> qn_;
    std::vector<PV> wp_;
    std::vector<NV> wn_;
};

template <typename F> F field_pow2(size_t e) {
    F out = F::one();
    const F two = F::from_u64(2);
    for (size_t i = 0; i < e; ++i) {
        out *= two;
    }
    return out;
}

// The prover's state between prove_commit and prove_finish.
template <typename R, typename P> struct ProverState {
    Digest chal2;
    std::vector<Fp> up, wp, vp; // u, the witness, and V = sum_t N^t v_t (F_p rows)
    std::vector<Fn> un, wn, vn; // (F_n rows)
    std::vector<detail::Tree<P>> trees;
    std::vector<std::array<uint8_t, COM_BYTES>> coms;
};

// Step 1 of proving: commit to the witness (wp, wn). mu binds the statement. Writes the iv, the
// VOLE corrections, u-tilde, and d to the proof, and returns the state for prove_finish, including
// chal2, which binds everything written so far.
template <typename R, typename P>
ProverState<R, P> prove_commit(std::span<uint8_t, Layout<R, P>::PROOF_BYTES> proof,
                               const Digest& mu, std::span<const Fp, R::LP> wp,
                               std::span<const Fn, R::LN> wn, const ProveSeed& rho) {
    using namespace detail;
    using Lay = Layout<R, P>;
    constexpr size_t TAU = P::TAU, LEAVES = P::LEAVES;
    constexpr size_t LHAT_P = Lay::LHAT_P, LHAT_N = Lay::LHAT_N;

    ProverState<R, P> st;
    st.wp.assign(wp.begin(), wp.end());
    st.wn.assign(wn.begin(), wn.end());

    // (seed, iv) <- H(w || mu || rho)
    std::array<uint8_t, SEED_BYTES + IV_BYTES> seed_iv;
    {
        auto h = new_hasher();
        hash_elems<Fp>(h, wp);
        hash_elems<Fn>(h, wn);
        h.update(mu);
        h.update(rho);
        seed_iv = finalize<SEED_BYTES + IV_BYTES>(h, DS_PROVER_SEED);
    }
    const auto iv = proof.template subspan<Lay::OFF_IV, IV_BYTES>();
    std::ranges::copy(std::span(seed_iv).template last<IV_BYTES>(), iv.begin());
    const faest::block128 iv_block = faest::block128::load(iv.data());

    st.trees.resize(TAU);
    {
        auto h = new_hasher();
        h.update(std::span(seed_iv).template first<SEED_BYTES>());
        h.update(iv);
        const auto roots = finalize<TAU * SEED_BYTES>(h, DS_TREE_ROOTS);
        for (size_t t = 0; t < TAU; ++t) {
            std::copy_n(&roots[t * SEED_BYTES], SEED_BYTES, st.trees[t].nodes[0].begin());
        }
    }

    // 1. VOLE commitment: for each tree, u_t = sum_x r_x and s_t = sum_x x r_x = -v_t.
    std::vector<std::vector<Fp>> sp(TAU, std::vector<Fp>(LHAT_P));
    std::vector<std::vector<Fn>> sn(TAU, std::vector<Fn>(LHAT_N));
    st.coms.resize(TAU * LEAVES);
    auto h_com = new_hasher();
    uint8_t* corr = proof.data() + Lay::OFF_CORR;
    {
        std::vector<std::array<uint8_t, LEAF_HASH_BYTES>> leaf_hashes(LEAVES);
        std::vector<Fp> rp(LHAT_P), suf_p(LHAT_P);
        std::vector<Fn> rn(LHAT_N), suf_n(LHAT_N);
        for (size_t t = 0; t < TAU; ++t) {
            expand_tree_from<P>(st.trees[t], nullptr, iv_block, t);
            hash_leaves(st.trees[t].leaves(), iv, t, leaf_hashes);
            std::ranges::fill(suf_p, Fp::zero());
            std::ranges::fill(suf_n, Fn::zero());
            // From the last leaf down: suf = sum_{x' >= x} r_{x'}, and
            // sum_{x >= 1} suf_x = sum_x x r_x.
            for (size_t xi = LEAVES; xi-- > 0;) {
                Seed leaf_seed;
                std::copy_n(leaf_hashes[xi].begin(), SEED_BYTES, leaf_seed.begin());
                std::copy_n(leaf_hashes[xi].begin() + SEED_BYTES, COM_BYTES,
                            st.coms[t * LEAVES + xi].begin());
                expand_leaf(leaf_seed, iv_block, t, xi, rp, rn);
                for (size_t j = 0; j < LHAT_P; ++j) {
                    suf_p[j] += rp[j];
                }
                for (size_t j = 0; j < LHAT_N; ++j) {
                    suf_n[j] += rn[j];
                }
                if (xi > 0) {
                    for (size_t j = 0; j < LHAT_P; ++j) {
                        sp[t][j] += suf_p[j];
                    }
                    for (size_t j = 0; j < LHAT_N; ++j) {
                        sn[t][j] += suf_n[j];
                    }
                }
            }
            for (size_t xi = 0; xi < LEAVES; ++xi) {
                h_com.update(st.coms[t * LEAVES + xi]);
            }
            if (t == 0) {
                st.up = suf_p;
                st.un = suf_n;
            } else {
                for (size_t j = 0; j < LHAT_P; ++j, corr += ELEM_BYTES) {
                    store(corr, st.up[j] - suf_p[j]);
                }
                for (size_t j = 0; j < LHAT_N; ++j, corr += ELEM_BYTES) {
                    store(corr, st.un[j] - suf_n[j]);
                }
            }
        }
    }
    const auto h_com_digest = finalize<DIGEST_BYTES>(h_com, DS_LEAF_COMMITMENTS);
    const auto corr_bytes = proof.template subspan<Lay::OFF_CORR, Lay::CORR_BYTES>();

    // V = sum_t N^t v_t = -sum_t N^t s_t.
    st.vp.assign(LHAT_P, Fp::zero());
    st.vn.assign(LHAT_N, Fn::zero());
    {
        const Fp np = field_pow2<Fp>(P::DEPTH);
        const Fn nn = field_pow2<Fn>(P::DEPTH);
        Fp scale_p = Fp::one();
        Fn scale_n = Fn::one();
        for (size_t t = 0; t < TAU; ++t) {
            for (size_t j = 0; j < LHAT_P; ++j) {
                st.vp[j] -= scale_p * sp[t][j];
            }
            for (size_t j = 0; j < LHAT_N; ++j) {
                st.vn[j] -= scale_n * sn[t][j];
            }
            scale_p *= np;
            scale_n *= nn;
        }
    }

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

    // 2. VOLE consistency check: u-tilde = H(u), h_t = H(v_t) = -H(s_t).
    const VoleHash<Fp> hash_p(sample<Fp>(chal1, DS_VOLE_HASH_P), LHAT_P);
    const VoleHash<Fn> hash_n(sample<Fn>(chal1, DS_VOLE_HASH_N), LHAT_N);
    store(proof.data() + Lay::OFF_UTILDE, hash_p(st.up));
    store(proof.data() + Lay::OFF_UTILDE + ELEM_BYTES, hash_n(st.un));

    // 3. Witness commitment: d = w - u.
    uint8_t* d = proof.data() + Lay::OFF_D;
    for (size_t j = 0; j < R::LP; ++j, d += ELEM_BYTES) {
        store(d, wp[j] - st.up[j]);
    }
    for (size_t j = 0; j < R::LN; ++j, d += ELEM_BYTES) {
        store(d, wn[j] - st.un[j]);
    }

    // chal2 <- H(chal1 || u-tilde || h_0 || ... || h_{TAU - 1} || d)
    {
        auto h = new_hasher();
        h.update(chal1);
        h.update(proof.subspan(Lay::OFF_UTILDE, 2 * ELEM_BYTES));
        for (size_t t = 0; t < TAU; ++t) {
            h.update((-hash_p(sp[t])).to_bytes());
            h.update((-hash_n(sn[t])).to_bytes());
        }
        h.update(proof.subspan(Lay::OFF_D, Lay::D_BYTES));
        st.chal2 = finalize<DIGEST_BYTES>(h, DS_CHAL2);
    }
    return st;
}

namespace detail {

// chal3_seed <- H(chal2 || binder), from which the QuickSilver challenges are derived.
inline Digest chal3_seed(const Digest& chal2, std::span<const uint8_t> binder) {
    auto h = new_hasher();
    h.update(chal2);
    h.update(binder);
    return finalize<DIGEST_BYTES>(h, DS_CHAL3_SEED);
}

// Delta <- H(chal3_seed || A_0^p || A_0^n || A_1, ...), as TAU values in [0, LEAVES).
template <typename P>
std::array<uint8_t, P::DELTA_BYTES> derive_delta(const Digest& seed, const Fp& a0p, const Fn& a0n,
                                                 std::span<const uint8_t> qs_bytes) {
    auto h = new_hasher();
    h.update(seed);
    h.update(a0p.to_bytes());
    h.update(a0n.to_bytes());
    h.update(qs_bytes);
    auto out = finalize<P::DELTA_BYTES>(h, DS_CHAL3);
    for (size_t t = 0; t < P::TAU; ++t) {
        const size_t v = (out[2 * t] | (size_t{out[2 * t + 1]} << 8)) & (P::LEAVES - 1);
        out[2 * t] = static_cast<uint8_t>(v);
        out[2 * t + 1] = static_cast<uint8_t>(v >> 8);
    }
    return out;
}

template <typename P> size_t delta_t(std::span<const uint8_t> delta, size_t t) {
    return delta[2 * t] | (size_t{delta[2 * t + 1]} << 8);
}

template <typename F, typename P> F delta_elem(std::span<const uint8_t> delta) {
    const F n = field_pow2<F>(P::DEPTH);
    F acc = F::zero();
    for (size_t t = P::TAU; t-- > 0;) {
        acc = acc * n + F::from_u64(delta_t<P>(delta, t));
    }
    return acc;
}

} // namespace detail

// Step 2 of proving: prove that the committed witness satisfies R for instance x. The QuickSilver
// challenges are bound to `binder`.
//
// Throws std::logic_error if a constraint has too large a degree. If the witness doesn't satisfy
// the relation, then the proof is invalid.
template <typename R, typename P>
void prove_finish(std::span<uint8_t, Layout<R, P>::PROOF_BYTES> proof, ProverState<R, P>& st,
                  const typename R::instance& x, std::span<const uint8_t> binder,
                  size_t* failed = nullptr) {
    using namespace detail;
    using Lay = Layout<R, P>;
    constexpr size_t DP = R::DP, DN = R::DN;

    const Digest seed = chal3_seed(st.chal2, binder);
    Context<R, false> ctx;
    ctx.qp_ = QsField<Fp, false, DP>(sample<Fp>(seed, DS_QS_CHI_P));
    ctx.qn_ = QsField<Fn, false, DN>(sample<Fn>(seed, DS_QS_CHI_N));
    ctx.wp_.reserve(R::LP);
    for (size_t j = 0; j < R::LP; ++j) {
        ctx.wp_.push_back(Context<R, false>::PV::committed(st.vp[j], st.wp[j]));
    }
    ctx.wn_.reserve(R::LN);
    for (size_t j = 0; j < R::LN; ++j) {
        ctx.wn_.push_back(Context<R, false>::NV::committed(st.vn[j], st.wn[j]));
    }
    R::constraints(ctx, x);
    if (failed) {
        *failed = ctx.qp_.failed() + ctx.qn_.failed();
    }

    // Add the masks sum_{i = 1}^{D - 1} K_{r_i} Delta^(i - 1), where K_{r_i} = V_i + u_i Delta.
    auto& cp = ctx.qp_.coeffs();
    for (size_t i = 1; i < DP; ++i) {
        cp[i - 1] += st.vp[R::LP + i - 1];
        cp[i] += st.up[R::LP + i - 1];
    }
    auto& cn = ctx.qn_.coeffs();
    for (size_t i = 1; i < DN; ++i) {
        cn[i - 1] += st.vn[R::LN + i - 1];
        cn[i] += st.un[R::LN + i - 1];
    }
    uint8_t* q = proof.data() + Lay::OFF_QS;
    for (size_t i = 1; i < DP; ++i, q += ELEM_BYTES) {
        store(q, cp[i]);
    }
    for (size_t i = 1; i < DN; ++i, q += ELEM_BYTES) {
        store(q, cn[i]);
    }

    const auto delta = derive_delta<P>(seed, cp[0], cn[0], proof.subspan(Lay::OFF_QS, Lay::QS_BYTES));
    std::ranges::copy(delta, proof.begin() + Lay::OFF_DELTA);

    // Open all leaves but leaf Delta_t of tree t.
    for (size_t t = 0; t < P::TAU; ++t) {
        const size_t pt = delta_t<P>(delta, t);
        uint8_t* out = proof.data() + Lay::OFF_OPEN + t * P::OPENING_BYTES;
        for (const size_t node : copath<P>(pt)) {
            out = std::ranges::copy(st.trees[t].nodes[node], out).out;
        }
        std::ranges::copy(st.coms[t * P::LEAVES + pt], out);
    }
}

// The verifier's state between verify_commit and verify_finish.
template <typename R, typename P> struct VerifierState {
    Digest chal2;
    std::vector<Fp> kp; // the MACs Q_j of all F_p rows, with d applied to the witness rows
    std::vector<Fn> kn;
    Fp delta_p;
    Fn delta_n;
};

// Step 1 of verifying: reconstruct the verifier's VOLE keys and chal2. Returns nothing if the proof
// is malformed. An invalid proof never causes an exception other than std::bad_alloc.
template <typename R, typename P>
std::optional<VerifierState<R, P>>
verify_commit(std::span<const uint8_t, Layout<R, P>::PROOF_BYTES> proof, const Digest& mu) {
    using namespace detail;
    using Lay = Layout<R, P>;
    constexpr size_t TAU = P::TAU, LEAVES = P::LEAVES;
    constexpr size_t LHAT_P = Lay::LHAT_P, LHAT_N = Lay::LHAT_N;

    const auto iv = proof.template subspan<Lay::OFF_IV, IV_BYTES>();
    const auto delta = proof.template subspan<Lay::OFF_DELTA, P::DELTA_BYTES>();
    for (size_t t = 0; t < TAU; ++t) {
        if (delta_t<P>(delta, t) >= LEAVES) {
            return std::nullopt;
        }
    }
    // Decode every field element up front; they must be canonical.
    std::vector<std::vector<Fp>> cp(TAU, std::vector<Fp>(LHAT_P));
    std::vector<std::vector<Fn>> cn(TAU, std::vector<Fn>(LHAT_N));
    {
        const uint8_t* c = proof.data() + Lay::OFF_CORR;
        for (size_t t = 1; t < TAU; ++t) {
            for (size_t j = 0; j < LHAT_P; ++j, c += ELEM_BYTES) {
                const auto v = load<Fp>(c);
                if (!v) {
                    return std::nullopt;
                }
                cp[t][j] = *v;
            }
            for (size_t j = 0; j < LHAT_N; ++j, c += ELEM_BYTES) {
                const auto v = load<Fn>(c);
                if (!v) {
                    return std::nullopt;
                }
                cn[t][j] = *v;
            }
        }
    }
    const auto ut_p = load<Fp>(proof.data() + Lay::OFF_UTILDE);
    const auto ut_n = load<Fn>(proof.data() + Lay::OFF_UTILDE + ELEM_BYTES);
    if (!ut_p || !ut_n) {
        return std::nullopt;
    }
    std::vector<Fp> dp(R::LP);
    std::vector<Fn> dn(R::LN);
    {
        const uint8_t* d = proof.data() + Lay::OFF_D;
        for (size_t j = 0; j < R::LP; ++j, d += ELEM_BYTES) {
            const auto v = load<Fp>(d);
            if (!v) {
                return std::nullopt;
            }
            dp[j] = *v;
        }
        for (size_t j = 0; j < R::LN; ++j, d += ELEM_BYTES) {
            const auto v = load<Fn>(d);
            if (!v) {
                return std::nullopt;
            }
            dn[j] = *v;
        }
    }
    const faest::block128 iv_block = faest::block128::load(iv.data());

    // 1. Reconstruct q_t = sum_{x != Delta_t} (Delta_t - x) r_{t,x}.
    std::vector<std::vector<Fp>> qp(TAU, std::vector<Fp>(LHAT_P));
    std::vector<std::vector<Fn>> qn(TAU, std::vector<Fn>(LHAT_N));
    auto h_com = new_hasher();
    {
        Tree<P> tree;
        std::vector<std::array<uint8_t, LEAF_HASH_BYTES>> leaf_hashes(LEAVES);
        std::vector<Fp> rp(LHAT_P), suf_p(LHAT_P), sum_p(LHAT_P);
        std::vector<Fn> rn(LHAT_N), suf_n(LHAT_N), sum_n(LHAT_N);
        for (size_t t = 0; t < TAU; ++t) {
            const size_t pt = delta_t<P>(delta, t);
            const uint8_t* opening = proof.data() + Lay::OFF_OPEN + t * P::OPENING_BYTES;
            std::vector<bool> known(P::TREE_NODES, false);
            for (const size_t node : copath<P>(pt)) {
                std::copy_n(opening, SEED_BYTES, tree.nodes[node].begin());
                known[node] = true;
                opening += SEED_BYTES;
            }
            tree.nodes[LEAVES - 1 + pt] = {}; // unknown; its hash is ignored
            expand_tree_from<P>(tree, &known, iv_block, t);
            hash_leaves(tree.leaves(), iv, t, leaf_hashes);
            std::ranges::fill(suf_p, Fp::zero());
            std::ranges::fill(sum_p, Fp::zero());
            std::ranges::fill(suf_n, Fn::zero());
            std::ranges::fill(sum_n, Fn::zero());
            for (size_t xi = LEAVES; xi-- > 0;) {
                if (xi != pt) {
                    Seed leaf_seed;
                    std::copy_n(leaf_hashes[xi].begin(), SEED_BYTES, leaf_seed.begin());
                    expand_leaf(leaf_seed, iv_block, t, xi, rp, rn);
                    for (size_t j = 0; j < LHAT_P; ++j) {
                        suf_p[j] += rp[j];
                    }
                    for (size_t j = 0; j < LHAT_N; ++j) {
                        suf_n[j] += rn[j];
                    }
                }
                if (xi > 0) {
                    for (size_t j = 0; j < LHAT_P; ++j) {
                        sum_p[j] += suf_p[j];
                    }
                    for (size_t j = 0; j < LHAT_N; ++j) {
                        sum_n[j] += suf_n[j];
                    }
                }
            }
            for (size_t xi = 0; xi < LEAVES; ++xi) {
                if (xi == pt) {
                    h_com.update(opening, COM_BYTES);
                } else {
                    h_com.update(std::span(leaf_hashes[xi]).template last<COM_BYTES>());
                }
            }
            // q_t = Delta_t U' - S' (+ Delta_t c_t for t > 0).
            const Fp dtp = Fp::from_u64(pt);
            const Fn dtn = Fn::from_u64(pt);
            for (size_t j = 0; j < LHAT_P; ++j) {
                qp[t][j] = dtp * (suf_p[j] + cp[t][j]) - sum_p[j];
            }
            for (size_t j = 0; j < LHAT_N; ++j) {
                qn[t][j] = dtn * (suf_n[j] + cn[t][j]) - sum_n[j];
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
        h.update(proof.template subspan<Lay::OFF_CORR, Lay::CORR_BYTES>());
        chal1 = finalize<DIGEST_BYTES>(h, DS_CHAL1);
    }

    // 2. VOLE consistency check: h_t = H(q_t) - Delta_t u-tilde.
    const VoleHash<Fp> hash_p(sample<Fp>(chal1, DS_VOLE_HASH_P), LHAT_P);
    const VoleHash<Fn> hash_n(sample<Fn>(chal1, DS_VOLE_HASH_N), LHAT_N);
    VerifierState<R, P> st;
    {
        auto h = new_hasher();
        h.update(chal1);
        h.update(proof.subspan(Lay::OFF_UTILDE, 2 * ELEM_BYTES));
        for (size_t t = 0; t < TAU; ++t) {
            const size_t pt = delta_t<P>(delta, t);
            h.update((hash_p(qp[t]) - Fp::from_u64(pt) * *ut_p).to_bytes());
            h.update((hash_n(qn[t]) - Fn::from_u64(pt) * *ut_n).to_bytes());
        }
        h.update(proof.subspan(Lay::OFF_D, Lay::D_BYTES));
        st.chal2 = finalize<DIGEST_BYTES>(h, DS_CHAL2);
    }

    // 3. Q = sum_t N^t q_t, and K_j = Q_j + d_j Delta for the witness rows.
    st.delta_p = delta_elem<Fp, P>(delta);
    st.delta_n = delta_elem<Fn, P>(delta);
    st.kp.assign(LHAT_P, Fp::zero());
    st.kn.assign(LHAT_N, Fn::zero());
    {
        const Fp np = field_pow2<Fp>(P::DEPTH);
        const Fn nn = field_pow2<Fn>(P::DEPTH);
        Fp scale_p = Fp::one();
        Fn scale_n = Fn::one();
        for (size_t t = 0; t < TAU; ++t) {
            for (size_t j = 0; j < LHAT_P; ++j) {
                st.kp[j] += scale_p * qp[t][j];
            }
            for (size_t j = 0; j < LHAT_N; ++j) {
                st.kn[j] += scale_n * qn[t][j];
            }
            scale_p *= np;
            scale_n *= nn;
        }
    }
    for (size_t j = 0; j < R::LP; ++j) {
        st.kp[j] += dp[j] * st.delta_p;
    }
    for (size_t j = 0; j < R::LN; ++j) {
        st.kn[j] += dn[j] * st.delta_n;
    }
    return st;
}

// Step 2 of verifying. Returns false if the proof is invalid.
template <typename R, typename P>
bool verify_finish(std::span<const uint8_t, Layout<R, P>::PROOF_BYTES> proof,
                   const VerifierState<R, P>& st, const typename R::instance& x,
                   std::span<const uint8_t> binder) {
    using namespace detail;
    using Lay = Layout<R, P>;
    constexpr size_t DP = R::DP, DN = R::DN;

    std::array<Fp, DP> ap{};
    std::array<Fn, DN> an{};
    {
        const uint8_t* q = proof.data() + Lay::OFF_QS;
        for (size_t i = 1; i < DP; ++i, q += ELEM_BYTES) {
            const auto v = load<Fp>(q);
            if (!v) {
                return false;
            }
            ap[i] = *v;
        }
        for (size_t i = 1; i < DN; ++i, q += ELEM_BYTES) {
            const auto v = load<Fn>(q);
            if (!v) {
                return false;
            }
            an[i] = *v;
        }
    }

    const Digest seed = chal3_seed(st.chal2, binder);
    Context<R, true> ctx;
    ctx.qp_ = QsField<Fp, true, DP>(sample<Fp>(seed, DS_QS_CHI_P), st.delta_p);
    ctx.qn_ = QsField<Fn, true, DN>(sample<Fn>(seed, DS_QS_CHI_N), st.delta_n);
    ctx.wp_.reserve(R::LP);
    for (size_t j = 0; j < R::LP; ++j) {
        ctx.wp_.push_back(ctx.qp_.committed(st.kp[j]));
    }
    ctx.wn_.reserve(R::LN);
    for (size_t j = 0; j < R::LN; ++j) {
        ctx.wn_.push_back(ctx.qn_.committed(st.kn[j]));
    }
    R::constraints(ctx, x);

    // A_0 = sum + sum_i K_{r_i} Delta^(i - 1) - sum_{i >= 1} A_i Delta^i.
    Fp a0p = ctx.qp_.sum();
    for (size_t i = 1; i < DP; ++i) {
        a0p += st.kp[R::LP + i - 1] * ctx.qp_.delta_pow(i - 1) - ap[i] * ctx.qp_.delta_pow(i);
    }
    Fn a0n = ctx.qn_.sum();
    for (size_t i = 1; i < DN; ++i) {
        a0n += st.kn[R::LN + i - 1] * ctx.qn_.delta_pow(i - 1) - an[i] * ctx.qn_.delta_pow(i);
    }
    const auto delta_check =
        derive_delta<P>(seed, a0p, a0n, proof.subspan(Lay::OFF_QS, Lay::QS_BYTES));
    return std::ranges::equal(proof.subspan(Lay::OFF_DELTA, P::DELTA_BYTES), delta_check);
}

} // namespace vole_mole::voleith_p256

#endif
