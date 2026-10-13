// QuickSilver <https://ia.cr/2021/076> over a large prime field F, for constraints of arbitrary
// degree up to D, as used by the VOLEitH proof system in voleith.hpp.
//
// The verifier holds a MAC K = V + w Delta of each committed value w, under the global key Delta,
// and the prover holds (V, w). A polynomial expression f of degree d in committed values is
// evaluated homogeneously in Delta: the verifier computes Delta^d f(K / Delta) from the MACs, and
// the prover computes the same polynomial in Delta, sum_{i <= d} c_i Delta^i, whose leading
// coefficient c_d = f(w) is the value of the expression. A constraint f = 0 of degree d < D is
// lifted to degree D by multiplying by Delta^(D - d).
//
// Val is such an expression: for the prover, its coefficients c_0, ..., c_d; for the verifier, its
// homogeneous evaluation. Expressions are combined with +, -, and *, and with public constants (of
// degree 0). Both parties evaluate the same expressions in the same order, so their degrees agree.
//
// Constraints f_1, f_2, ... are combined as sum_c chi^c f_c (lifted to degree D) for a random chi in
// F. If some f_c(w) != 0, then the leading coefficient of the combination is nonzero except with
// probability (#constraints) / |F| over chi; see voleith.hpp for the rest of the check.

#ifndef VOLE_MOLE_VOLEITH_P256_QS_HPP
#define VOLE_MOLE_VOLEITH_P256_QS_HPP

#include <array>
#include <cstddef>
#include <stdexcept>

namespace vole_mole::voleith_p256 {

// The prover's or verifier's view of an expression of degree at most MAXD over F.
template <typename F, bool IsVerifier, size_t MAXD> class Val;

template <typename F, size_t MAXD> class Val<F, false, MAXD> {
  public:
    static constexpr bool is_verifier = false;
    using Field = F;

    Val() = default;

    // A public constant (degree 0).
    static Val constant(const F& x) {
        Val v;
        v.c_[0] = x;
        return v;
    }
    // A committed value with MAC V (degree 1).
    static Val committed(const F& mac, const F& value) {
        Val v;
        v.deg_ = 1;
        v.c_[0] = mac;
        v.c_[1] = value;
        return v;
    }

    size_t degree() const { return deg_; }
    // The value of the expression.
    const F& value() const { return c_[deg_]; }
    const F& coeff(size_t i) const { return c_[i]; }

    // Multiply by Delta^k: the same value with degree increased by k.
    Val lift(size_t to) const {
        check(to);
        if (to == deg_) {
            return *this;
        }
        Val out;
        out.deg_ = to;
        const size_t k = to - deg_;
        for (size_t i = 0; i <= deg_; ++i) {
            out.c_[i + k] = c_[i];
        }
        return out;
    }

    Val& operator+=(const Val& o) { return add(o, false); }
    Val& operator-=(const Val& o) { return add(o, true); }
    friend Val operator+(Val a, const Val& b) { return a += b; }
    friend Val operator-(Val a, const Val& b) { return a -= b; }
    Val operator-() const {
        Val out = *this;
        for (size_t i = 0; i <= deg_; ++i) {
            out.c_[i] = -out.c_[i];
        }
        return out;
    }
    Val& operator*=(const F& s) {
        for (size_t i = 0; i <= deg_; ++i) {
            c_[i] *= s;
        }
        return *this;
    }
    friend Val operator*(Val a, const F& s) { return a *= s; }
    friend Val operator*(const F& s, Val a) { return a *= s; }
    friend Val operator+(Val a, const F& s) { return a += constant(s); }
    friend Val operator-(Val a, const F& s) { return a -= constant(s); }

    friend Val operator*(const Val& a, const Val& b) {
        Val out;
        out.deg_ = a.deg_ + b.deg_;
        check(out.deg_);
        for (size_t i = 0; i <= a.deg_; ++i) {
            if (a.c_[i].is_zero()) {
                continue;
            }
            for (size_t j = 0; j <= b.deg_; ++j) {
                out.c_[i + j] += a.c_[i] * b.c_[j];
            }
        }
        return out;
    }

  private:
    static void check(size_t d) {
        if (d > MAXD) {
            throw std::logic_error("QuickSilver: degree too large");
        }
    }
    Val& add(const Val& o, bool sub) {
        if (o.deg_ > deg_) {
            *this = lift(o.deg_);
        }
        const size_t k = deg_ - o.deg_;
        for (size_t i = 0; i <= o.deg_; ++i) {
            c_[i + k] = sub ? c_[i + k] - o.c_[i] : c_[i + k] + o.c_[i];
        }
        return *this;
    }

    size_t deg_ = 0;
    std::array<F, MAXD + 1> c_{};
};

template <typename F, size_t MAXD> class Val<F, true, MAXD> {
  public:
    static constexpr bool is_verifier = true;
    using Field = F;

    // Delta^0, ..., Delta^MAXD.
    using Powers = std::array<F, MAXD + 1>;

    Val() = default;

    static Val constant(const F& x, const Powers* pw) { return Val(x, 0, pw); }
    static Val committed(const F& mac, const Powers* pw) { return Val(mac, 1, pw); }

    size_t degree() const { return deg_; }
    const F& eval() const { return k_; }

    Val lift(size_t to) const {
        check(to);
        return Val(to == deg_ ? k_ : k_ * (*pw_)[to - deg_], to, pw_);
    }

    Val& operator+=(const Val& o) { return add(o, false); }
    Val& operator-=(const Val& o) { return add(o, true); }
    friend Val operator+(Val a, const Val& b) { return a += b; }
    friend Val operator-(Val a, const Val& b) { return a -= b; }
    Val operator-() const { return Val(-k_, deg_, pw_); }
    Val& operator*=(const F& s) {
        k_ *= s;
        return *this;
    }
    friend Val operator*(Val a, const F& s) { return a *= s; }
    friend Val operator*(const F& s, Val a) { return a *= s; }
    friend Val operator+(Val a, const F& s) { return a += Val(s, 0, a.pw_); }
    friend Val operator-(Val a, const F& s) { return a -= Val(s, 0, a.pw_); }
    friend Val operator*(const Val& a, const Val& b) {
        const Val out(a.k_ * b.k_, a.deg_ + b.deg_, a.pw_ ? a.pw_ : b.pw_);
        check(out.deg_);
        return out;
    }

  private:
    Val(const F& k, size_t deg, const Powers* pw) : k_(k), deg_(deg), pw_(pw) {}

    static void check(size_t d) {
        if (d > MAXD) {
            throw std::logic_error("QuickSilver: degree too large");
        }
    }
    Val& add(const Val& o, bool sub) {
        if (!pw_) {
            pw_ = o.pw_;
        }
        const size_t to = deg_ > o.deg_ ? deg_ : o.deg_;
        const F a = deg_ == to ? k_ : k_ * (*pw_)[to - deg_];
        const F b = o.deg_ == to ? o.k_ : o.k_ * (*pw_)[to - o.deg_];
        k_ = sub ? a - b : a + b;
        deg_ = to;
        return *this;
    }

    F k_{};
    size_t deg_ = 0;
    const Powers* pw_ = nullptr;
};

// The accumulator of constraints of one field, of QuickSilver degree D.
template <typename F, bool IsVerifier, size_t D> class QsField;

template <typename F, size_t D> class QsField<F, false, D> {
  public:
    using V = Val<F, false, D>;

    QsField() = default;
    QsField(const F& beta) : beta_(beta), chi_(F::one()) {}

    V constant(const F& x) const { return V::constant(x); }

    // Add the constraint f = 0.
    void add(const V& f) {
        if (!f.value().is_zero()) {
            ++failed_;
        }
        const V g = f.lift(D);
        for (size_t i = 0; i <= D; ++i) {
            coeffs_[i] += chi_ * g.coeff(i);
        }
        chi_ *= beta_;
        ++count_;
    }

    std::array<F, D + 1>& coeffs() { return coeffs_; }
    // The number of constraints that don't hold (for tests).
    size_t failed() const { return failed_; }
    size_t count() const { return count_; }

  private:
    F beta_, chi_;
    std::array<F, D + 1> coeffs_{};
    size_t failed_ = 0, count_ = 0;
};

template <typename F, size_t D> class QsField<F, true, D> {
  public:
    using V = Val<F, true, D>;

    QsField() = default;
    QsField(const F& beta, const F& delta) : beta_(beta), chi_(F::one()) {
        pw_[0] = F::one();
        for (size_t i = 1; i <= D; ++i) {
            pw_[i] = pw_[i - 1] * delta;
        }
    }

    V constant(const F& x) const { return V::constant(x, &pw_); }
    V committed(const F& mac) const { return V::committed(mac, &pw_); }

    void add(const V& f) {
        sum_ += chi_ * f.lift(D).eval();
        chi_ *= beta_;
        ++count_;
    }

    const F& delta_pow(size_t i) const { return pw_[i]; }
    const F& sum() const { return sum_; }
    size_t count() const { return count_; }

  private:
    F beta_, chi_;
    typename V::Powers pw_{};
    F sum_{};
    size_t count_ = 0;
};

} // namespace vole_mole::voleith_p256

#endif
