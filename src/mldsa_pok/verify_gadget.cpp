#include "mldsa_pok/verify_gadget.hpp"

#include "vole_mole/keccak.hpp"
#include "vole_mole/mldsa.hpp"

#include "dst.hpp"
#include "mldsa/mldsa.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

namespace {

using mldsa::detail::fq_mul;
using mldsa::detail::fq_neg;
using mldsa::detail::fq_sub;

bool get_bit(std::span<const uint8_t> b, size_t i) { return ((b[i / 8] >> (i % 8)) & 1) != 0; }
void set_bit(std::span<uint8_t> b, size_t i, bool v) {
    b[i / 8] = static_cast<uint8_t>((b[i / 8] & ~(1u << (i % 8))) | (unsigned{v} << (i % 8)));
}

// sigma(p)(X) = p(X^-1) in R_q: sigma(p)_0 = p_0 and sigma(p)_{N - n} = -p_n.
Poly sigma(const Poly& p) {
    Poly out;
    out[0] = p[0];
    for (size_t n = 1; n < N; ++n) {
        out[N - n] = fq_neg(p[n]);
    }
    return out;
}

} // namespace

VerifyKey make_verify_key(const mldsa::PublicKey<P>& pk) {
    VerifyKey k{mldsa::detail::parse_public_key<P>(pk), {}, {}};
    for (size_t i = 0; i < K * L; ++i) {
        Poly a = k.parsed.a_hat[i];
        mldsa::detail::inv_ntt(a);
        k.sigma_a_hat[i] = sigma(a);
        mldsa::detail::ntt(k.sigma_a_hat[i]);
    }
    for (size_t i = 0; i < K; ++i) {
        Poly t;
        for (size_t n = 0; n < N; ++n) {
            t[n] = fq_mul(k.parsed.t1[i][n], 1u << mldsa::detail::D);
        }
        k.sigma_t1_hat[i] = sigma(t);
        mldsa::detail::ntt(k.sigma_t1_hat[i]);
    }
    return k;
}

std::vector<Elem> check_weights(const VerifyKey& key, std::span<const uint8_t> seed) {
    constexpr size_t T = ModQSpec::NUM_CHECKS;
    // gamma_{k,i}: 8 bytes per coefficient, reduced modulo q (statistically close to uniform).
    std::vector<uint8_t> stream(8 * T * K * N);
    {
        const std::array<std::span<const uint8_t>, 2> parts = {
            vole_mole::detail::MLDSA_POK_WEIGHTS_DST, seed};
        mldsa::detail::shake256(parts, stream);
    }
    std::vector<Elem> w(T * NUM_VALUES);
    for (size_t k = 0; k < T; ++k) {
        std::array<Poly, K> gamma, gamma_hat;
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                uint64_t v = 0;
                for (size_t b = 0; b < 8; ++b) {
                    v |= uint64_t{stream[8 * ((k * K + i) * N + n) + b]} << (8 * b);
                }
                gamma[i][n] = static_cast<Elem>(v % Q);
            }
            gamma_hat[i] = gamma[i];
            mldsa::detail::ntt(gamma_hat[i]);
        }
        const std::span<Elem> wk = std::span(w).subspan(k * NUM_VALUES, NUM_VALUES);
        // z_l: sum_i gamma_i sigma(a_il).
        for (size_t l = 0; l < L; ++l) {
            Poly acc{};
            for (size_t i = 0; i < K; ++i) {
                mldsa::detail::multiply_ntts_acc(acc, gamma_hat[i], key.sigma_a_hat[i * L + l]);
            }
            mldsa::detail::inv_ntt(acc);
            std::ranges::copy(acc, wk.begin() + static_cast<ptrdiff_t>(V_OFF_Z + l * N));
        }
        // c: -sum_i gamma_i sigma(t1_i 2^d).
        {
            Poly acc{};
            for (size_t i = 0; i < K; ++i) {
                mldsa::detail::multiply_ntts_acc(acc, gamma_hat[i], key.sigma_t1_hat[i]);
            }
            mldsa::detail::inv_ntt(acc);
            for (size_t x = 0; x < N; ++x) {
                wk[V_OFF_C + x] = fq_neg(acc[x]);
            }
        }
        // psi and f: -gamma2 gamma and -gamma.
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                wk[V_OFF_PSI + i * N + n] = fq_neg(fq_mul(GAMMA2, gamma[i][n]));
                wk[V_OFF_F + i * N + n] = fq_neg(gamma[i][n]);
            }
        }
    }
    return w;
}

void VerifyGadget::encode_witness(std::span<uint8_t> witness, const VerifyKey& key,
                                  std::span<const uint8_t, MU_BYTES> mu,
                                  const mldsa::detail::DecodedSignature<P>& sig) const {
    using mldsa::detail::fq_centered;
    if (witness.size() < base_ + WITNESS_BYTES) {
        throw std::logic_error("ML-DSA gadget: witness too short");
    }

    // ||z||_inf <= Z_BOUND
    for (const auto& p : sig.z) {
        for (const Fq zc : p) {
            const int32_t z = fq_centered(zc);
            if (z < -static_cast<int32_t>(Z_BOUND) || z > static_cast<int32_t>(Z_BOUND)) {
                throw std::invalid_argument("ML-DSA gadget: invalid signature");
            }
        }
    }

    const Poly c = mldsa::detail::sample_in_ball(sig.c_tilde, P::TAU);
    const auto r = mldsa::detail::w_approx<P>(key.parsed, sig.z, c);

    // w1, the hint classes, and f (see "The UseHint condition" in verify_gadget.hpp).
    std::array<Poly, K> w1;
    size_t weight = 0;
    for (size_t i = 0; i < K; ++i) {
        for (size_t n = 0; n < N; ++n) {
            const size_t j = i * N + n;
            w1[i][n] = mldsa::detail::use_hint(sig.h[i][n], r[i][n], GAMMA2);
            const int32_t e = fq_centered(fq_sub(r[i][n], fq_mul(ALPHA, w1[i][n])));
            const int32_t g2 = static_cast<int32_t>(GAMMA2);
            const bool w1_0 = w1[i][n] == 0, w1_43 = w1[i][n] == 43;
            int32_t f;
            uint32_t u; // psi + 1 - 2 w1
            if ((-g2 < e && e <= g2) || (e == -g2 && w1_0)) {
                f = e, u = 1;
            } else if ((g2 < e && e <= 2 * g2) || (e == 2 * g2 + 1 && w1_43)) {
                f = e - g2, u = 2;
            } else if (-2 * g2 <= e && e <= -g2 && (e != -2 * g2 || w1_0)) {
                f = e + g2, u = 0;
            } else {
                // Unreachable (see test_mldsa_pok.cpp).
                throw std::logic_error("ML-DSA gadget: UseHint");
            }
            // f = f' - (1 - nb) + yb with f' in (-gamma2, gamma2].
            const bool nb = f != -g2, yb = f == g2 + 1;
            const int32_t fp = f + (nb ? 0 : 1) - (yb ? 1 : 0);
            weight += u != 1;
            set_bit(witness, hint_bit(j, 0), u == 1);
            set_bit(witness, hint_bit(j, 1), u == 2);
            set_bit(witness, nb_bit(j), nb);
            set_bit(witness, yb_bit(j), yb);
            const auto fv = static_cast<uint32_t>(fp + g2 - 1);
            for (size_t b = 0; b < F_BITS; ++b) {
                set_bit(witness, f_bit(j, b), ((fv >> b) & 1) != 0);
            }
        }
    }
    // Every coefficient with u != none has a hint in the signature, which has at most omega.
    if (weight > OMEGA) {
        throw std::invalid_argument("ML-DSA gadget: invalid signature");
    }
    for (size_t i = 0; i < SLACK_BITS; ++i) {
        set_bit(witness, slack_bit(i), (((OMEGA - weight) >> i) & 1) != 0);
    }
    {
        HintCols::PlainOps ops{witness, bit(BOFF_HINT_CARRIES), HINT_CARRIES};
        std::vector<std::vector<uint8_t>> cols;
        hint_weight_columns(
            ops, [&](size_t i) { return static_cast<uint8_t>(get_bit(witness, i)); }, cols);
        bool ok = true;
        HintCols::reduce(ops, cols,
                         [&](size_t col, uint8_t w) { ok &= w == ((OMEGA >> col) & 1); });
        if (!ops.finish() || !ok) {
            throw std::logic_error("ML-DSA gadget: hint weight");
        }
    }

    // The c-tilde hash.
    const auto w1_enc = mldsa::detail::w1_encode(w1, GAMMA2);
    std::array<uint8_t, Ctilde::OUT_BYTES> c_tilde;
    const auto ct_wit =
        Ctilde::encode_witness(mu, std::span<const uint8_t, Ctilde::SECRET_BYTES>(w1_enc), c_tilde);
    std::ranges::copy(ct_wit, witness.begin() + static_cast<ptrdiff_t>(base_ + OFF_CTILDE));
    if (c_tilde != sig.c_tilde) {
        throw std::invalid_argument("ML-DSA gadget: invalid signature");
    }

    // The SampleInBall hash.
    Kf1600State st{};
    std::ranges::copy(c_tilde, st.begin());
    st[Ctilde::OUT_BYTES] ^= 0x1f;
    st[SHAKE256_RATE - 1] ^= 0x80;
    const auto states =
        witness.subspan(base_ + OFF_SIB_STATES).template first<SibPerm::COMMITTED_STATES_BYTES>();
    SibPerm::encode_committed_states(states, st);
    std::array<uint8_t, Sib::STREAM_BYTES> stream;
    std::copy_n(states.end() - KF1600_STATE_BYTES, stream.size(), stream.begin());

    // SampleInBall, and c + 1.
    const auto c_bits = Sib::encode_witness(stream, witness, bit(BOFF_SIB));
    if (!c_bits) {
        throw std::runtime_error("ML-DSA gadget: SampleInBall needs more than the scanned bytes");
    }
    for (size_t x = 0; x < N; ++x) {
        const int expect = c[x] == 0 ? 0 : (c[x] == 1 ? 1 : -1);
        if ((*c_bits)[x] != expect) {
            throw std::logic_error("ML-DSA gadget: SampleInBall mismatch");
        }
    }

    // z + Z_BOUND, and the range helper.
    for (size_t l = 0; l < L; ++l) {
        for (size_t n = 0; n < N; ++n) {
            const size_t j = l * N + n;
            const auto zv =
                static_cast<uint32_t>(fq_centered(sig.z[l][n]) + static_cast<int32_t>(Z_BOUND));
            for (size_t b = 0; b < Z_BITS; ++b) {
                set_bit(witness, z_bit(j, b), ((zv >> b) & 1) != 0);
            }
            set_bit(witness, z_helper_bit(j),
                    ZRange::helper([&](size_t b) { return ((zv >> b) & 1) != 0; }));
        }
    }
}

bool VerifyGadget::answer(std::span<const uint8_t> witness, const Weights& weights,
                          std::span<uint8_t, ANSWER_BYTES> out) const {
    return MlDsaModQ::answer(
        weights, [&](size_t j, size_t i) { return get_bit(witness, value_bit(j, i)); }, out);
}

bool VerifyGadget::holds(std::span<const uint8_t> witness, const Weights& weights) const {
    return MlDsaModQ::holds(weights,
                            [&](size_t j, size_t i) { return get_bit(witness, value_bit(j, i)); });
}

} // namespace vole_mole::mldsa_pok::detail
