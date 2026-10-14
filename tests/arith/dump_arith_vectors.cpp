// Dump differential test vectors for the Lean models of the constraint generators (see
// lean/VoleMole/Arith/ and `lake exe arith_vectors` in lean/).
//
// Usage: dump_arith_vectors OUTPUT_DIR (normally lean/vectors). Run explicitly, never as part of
// the test suite. All inputs are deterministic (fixed keys, fixed byte patterns, and fixed PRNG
// seeds), so rerunning it reproduces the same files.
//
// The constraints are evaluated by FieldQS below: a plaintext QuickSilver backend whose committed
// values, bits included, are arbitrary elements of GF(2^128). So it computes the value of each
// constraint polynomial at an arbitrary field-valued assignment of the witness bits, not only at
// bit vectors. (On bit vectors, it agrees with tests/test.hpp's BasicPlainQS, which the dumper
// checks.)
//
// File format (one file per relation or gadget, plus uov_keys.txt):
//
//   - Lines are `KEY VALUE`, separated by a single space. Blank lines and lines starting with '#'
//     are comments.
//   - A record is `record RELATION NAME`, then KEY VALUE lines, then `end`.
//   - Byte strings are lowercase hex. An element of GF(2^128) is 32 hex digits: the 16 bytes of
//     poly128::store, i.e., little endian, so bit j of byte i is the coefficient of X^(8i + j). A
//     list of field elements is the concatenation of their encodings (`-` if empty). Numbers are
//     decimal. A list of integers is comma-separated.
//   - uov_keys.txt has lines `key NAME HEX`: the expanded UOV public map (pqov's layout, see
//     uov::detail::for_each_monomial). Records refer to keys by NAME.
//
// field.txt has a single record `field arith` that checks the field arithmetic itself: beta (the 8
// elements poly128::from_8_byte(1 << b)), embed (poly128::from_8_byte(a) for a = 0, ..., 255),
// gf256_mul (pqov's gf256_mul(a, b) at byte 256 a + b), and mul_a, mul_b, mul_ab (lists of equal
// length with mul_ab[i] = mul_a[i] * mul_b[i] in GF(2^128)). The other files have these keys in
// every record:
//
//   wit             the witness bytes; witness bit i is bit i % 8 of byte i / 8.
//   num_constraints the number of add_constraint calls.
//   values_bits     the constraint values (in add_constraint order) at the bits of `wit`.
//   field_wit       one field element per witness bit: a uniformly random assignment.
//   values_field    the constraint values at `field_wit`.
//
// and, for the relations that use it, `chal2` (the QuickSilver challenge, hex). Relation-specific
// keys (instance fields as hex bytes unless noted; `l` is the list of the M = 45 coefficients of
// the random linear combination derived from chal2, uov::detail::Combination::coeff; `keccak_in_K`
// is the public part of the K-th Keccak-p[800] input state, as passed to keccak::detail::qs_input):
//
//   uov               pk, l (random rather than derived from a challenge), target (P(s), or `-`
//                     if s is random). One constraint: l(P(s)), with
//                     s_i = load_witness_8_bits_and_combine(8 i), i < N.
//   keccak            input_map (100 ints), public_state, wit_off_states, num_out_bits. The
//                     constraints are qs_keccak's segment constraints, then out[i] for
//                     i < num_out_bits, then qs_byte(out, k) for k < num_out_bits / 8.
//   pomfrit_redeem    pk, h, l
//   ihat_issue    t, ctx_iss, keccak_in_0
//   ihat_redeem   anchors (comma-separated key names), nf, ctx_iss, ctx_red, challenge_digest,
//                     l, keccak_in_0
//   act_issue c, t_init (decimal), ctx_iss, keccak_in_0
//   act_spend pk, nf, d (decimal), c_next, ctx_iss, l, keccak_in_0 (Com), keccak_in_1
//                     (Tag), keccak_in_2 (Com')
//
// Each relation has a record `honest` (an honest witness, so values_bits is all zero) and a record
// `random` (uniformly random witness bytes). The gadgets have records with an honest witness
// (`preimage`, `secret_input`, `mixed_input`; for keccak, the segment constraints vanish) and a
// record `random`.

#include "vole_mole/keccak.hpp"
#include "vole_mole/ihat.hpp"
#include "vole_mole/act.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"                // internal
#include "keccak/segmented.hpp"   // internal
#include "ihat/commit.hpp"    // internal
#include "ihat/issue.hpp"     // internal
#include "ihat/redeem.hpp"    // internal
#include "pomfrit/redeem.hpp"     // internal
#include "act/commit.hpp" // internal
#include "act/issue.hpp"  // internal
#include "act/spend.hpp"  // internal
#include "uov/circuit.hpp"        // internal
#include "uov/public_key.hpp"     // internal

#include "test.hpp"

#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

extern "C" {
#include "gf16.h" // from pqov
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <initializer_list>
#include <iostream>
#include <random>
#include <span>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::test {

// Plaintext stand-in for faest::quicksilver_state whose committed values are elements of GF(2^128):
// witness bit i has the value witness[i], which need not be 0 or 1. Records the value of each
// constraint, in order.
template <size_t max_deg> struct FieldQS {
    static constexpr faest::secpar secpar_v = faest::secpar::s128;
    static constexpr size_t secpar_bits = 128;
    static constexpr size_t max_degree = max_deg;
    static constexpr bool is_verifier = false;

    std::span<const faest::poly128> witness; // one value per witness bit
    std::vector<faest::poly128> values;      // one entry per constraint

    faest::quicksilver_gf2<FieldQS, 1> get_witness_bit(size_t i) const;
    // sum_b beta_b * witness[i + b], as faest-arch-opt's load_witness_8_bits_and_combine.
    faest::quicksilver_gfsecpar<FieldQS, 1> load_witness_8_bits_and_combine(size_t i) const;

    template <typename T> void add_constraint(const T& x) { values.push_back(x.v); }
    template <typename T> void add_bit_constraint(const T& x) {
        add_constraint(x * (x + faest::poly1(1)));
    }
};

} // namespace vole_mole::test

// A committed "bit" of degree `deg`, as an element of GF(2^128). Sums and products are those of
// GF(2^128), which agree with XOR and AND on {0, 1}.
template <size_t max_deg, size_t deg>
struct faest::quicksilver_gf2<vole_mole::test::FieldQS<max_deg>, deg> {
    using QS = vole_mole::test::FieldQS<max_deg>;

    faest::poly128 v = faest::poly128::set_zero();

    quicksilver_gf2() = default;
    explicit quicksilver_gf2(faest::poly128 x) : v(x) {}
    quicksilver_gf2(faest::poly1 c, const QS*) : v(faest::poly128::from_1(c)) {}
    template <size_t deg2>
    quicksilver_gf2(faest::poly1 c, const quicksilver_gf2<QS, deg2>&)
        : v(faest::poly128::from_1(c)) {}
    template <size_t deg2>
        requires(deg2 < deg)
    quicksilver_gf2(const quicksilver_gf2<QS, deg2>& lower) : v(lower.v) {}

    quicksilver_gf2 operator+(const quicksilver_gf2& o) const { return quicksilver_gf2(v + o.v); }
    quicksilver_gf2 operator+(faest::poly1 c) const {
        return quicksilver_gf2(v + faest::poly128::from_1(c));
    }
    template <typename T> quicksilver_gf2& operator+=(const T& o) {
        *this = *this + o;
        return *this;
    }
};

// A committed element of GF(2^128) of degree `deg`.
template <size_t max_deg, size_t deg>
struct faest::quicksilver_gfsecpar<vole_mole::test::FieldQS<max_deg>, deg> {
    using QS = vole_mole::test::FieldQS<max_deg>;
    using poly = faest::poly128;

    poly v = poly::set_zero();

    quicksilver_gfsecpar() = default;
    explicit quicksilver_gfsecpar(poly x) : v(x) {}
    quicksilver_gfsecpar(faest::poly1 c, const QS*) : v(poly::from_1(c)) {}
    quicksilver_gfsecpar(poly c, const QS*) : v(c) {}
    template <size_t deg2>
    quicksilver_gfsecpar(faest::poly1 c, const quicksilver_gfsecpar<QS, deg2>&)
        : v(poly::from_1(c)) {}
    template <size_t deg2>
    quicksilver_gfsecpar(poly c, const quicksilver_gfsecpar<QS, deg2>&) : v(c) {}
    template <size_t deg2>
        requires(deg2 < deg)
    quicksilver_gfsecpar(const quicksilver_gfsecpar<QS, deg2>& lower) : v(lower.v) {}
    // A committed bit is already an element of GF(2^128).
    template <size_t deg2>
        requires(deg2 <= deg)
    quicksilver_gfsecpar(const quicksilver_gf2<QS, deg2>& bit) : v(bit.v) {}

    quicksilver_gfsecpar operator+(const quicksilver_gfsecpar& o) const {
        return quicksilver_gfsecpar(v + o.v);
    }
    quicksilver_gfsecpar operator+(faest::poly1 c) const {
        return quicksilver_gfsecpar(v + poly::from_1(c));
    }
    template <typename T> quicksilver_gfsecpar& operator+=(const T& o) {
        *this = *this + o;
        return *this;
    }
};

namespace vole_mole::test {

inline faest::poly128 mul128(faest::poly128 a, faest::poly128 b) {
    return (a * b).template reduce_to<128>();
}

// Products, found by argument-dependent lookup and more specialized than faest-arch-opt's generic
// ones (which need the MAC representation).
template <size_t max_deg, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>
operator*(const faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a>& a,
          const faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_b>& b) {
    return faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>(mul128(a.v, b.v));
}
template <size_t max_deg, size_t deg_a, size_t deg_b>
faest::quicksilver_gf2<FieldQS<max_deg>, deg_a + deg_b>
operator*(const faest::quicksilver_gf2<FieldQS<max_deg>, deg_a>& a,
          const faest::quicksilver_gf2<FieldQS<max_deg>, deg_b>& b) {
    return faest::quicksilver_gf2<FieldQS<max_deg>, deg_a + deg_b>(mul128(a.v, b.v));
}
template <size_t max_deg, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>
operator*(const faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a>& a,
          const faest::quicksilver_gf2<FieldQS<max_deg>, deg_b>& b) {
    return faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>(mul128(a.v, b.v));
}
template <size_t max_deg, size_t deg_a, size_t deg_b>
faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>
operator*(const faest::quicksilver_gf2<FieldQS<max_deg>, deg_a>& a,
          const faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_b>& b) {
    return faest::quicksilver_gfsecpar<FieldQS<max_deg>, deg_a + deg_b>(mul128(a.v, b.v));
}

} // namespace vole_mole::test

template <size_t max_deg>
faest::quicksilver_gf2<vole_mole::test::FieldQS<max_deg>, 1>
vole_mole::test::FieldQS<max_deg>::get_witness_bit(size_t i) const {
    return faest::quicksilver_gf2<FieldQS, 1>(witness[i]);
}

template <size_t max_deg>
faest::quicksilver_gfsecpar<vole_mole::test::FieldQS<max_deg>, 1>
vole_mole::test::FieldQS<max_deg>::load_witness_8_bits_and_combine(size_t i) const {
    return faest::quicksilver_gfsecpar<FieldQS, 1>(faest::poly128::from_8_self(&witness[i]));
}

namespace {

using namespace vole_mole;
using faest::poly128;
using vole_mole::test::filled;
using vole_mole::test::to_hex;

std::string hex128(poly128 x) {
    std::array<uint8_t, 16> bytes;
    x.store(bytes.data());
    return to_hex(bytes);
}

std::string hex128_list(std::span<const poly128> xs) {
    if (xs.empty()) {
        return "-";
    }
    std::string out;
    out.reserve(32 * xs.size());
    for (const poly128 x : xs) {
        out += hex128(x);
    }
    return out;
}

// The witness bits as field elements (0 or 1).
std::vector<poly128> bits_as_field(std::span<const uint8_t> wit) {
    std::vector<poly128> out;
    out.reserve(8 * wit.size());
    for (size_t i = 0; i < 8 * wit.size(); ++i) {
        out.push_back(poly128::from_1(faest::poly1((wit[i / 8] >> (i % 8)) & 1)));
    }
    return out;
}

std::vector<poly128> random_field(size_t n, std::mt19937_64& rng) {
    std::vector<poly128> out;
    out.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        const std::array<uint64_t, 2> words = {rng(), rng()};
        out.push_back(poly128::load(words.data()));
    }
    return out;
}

template <size_t N> std::array<uint8_t, N> random_bytes(std::mt19937_64& rng) {
    std::array<uint8_t, N> out;
    for (uint8_t& b : out) {
        b = static_cast<uint8_t>(rng());
    }
    return out;
}

[[noreturn]] void fail(std::string_view msg) {
    std::cerr << "dump_arith_vectors: " << msg << '\n';
    std::exit(1);
}

// A vector file being written.
class VectorFile {
  public:
    VectorFile(const std::string& dir, std::string_view name, std::string_view description)
        : path_(dir + "/" + std::string(name) + ".txt"), out_(path_) {
        if (!out_) {
            fail("can't open " + path_);
        }
        out_ << "# " << description
             << "\n# Written by tests/arith/dump_arith_vectors.cpp (see its header comment for the "
                "format). Do not edit.\n";
    }
    ~VectorFile() {
        out_.flush();
        if (!out_) {
            std::cerr << "dump_arith_vectors: error writing " << path_ << '\n';
        }
        std::cout << "wrote " << path_ << '\n';
    }
    VectorFile(const VectorFile&) = delete;
    VectorFile& operator=(const VectorFile&) = delete;

    std::ofstream& out() { return out_; }

  private:
    std::string path_;
    std::ofstream out_;
};

using Fields = std::vector<std::pair<std::string, std::string>>;

// Evaluate `constraints(qs)` at the bits of `wit` and at a random field assignment, check the bit
// evaluation against BasicPlainQS and check that the first `must_hold` constraints hold at the
// bits, and write the record. `fields` are the relation-specific KEY VALUE lines.
template <size_t max_deg, typename Constraints>
void write_record(std::ostream& out, std::string_view relation, std::string_view name,
                  std::span<const uint8_t> wit, const Fields& fields, std::mt19937_64& rng,
                  size_t must_hold, const Constraints& constraints) {
    using FQS = vole_mole::test::FieldQS<max_deg>;
    using PQS = vole_mole::test::BasicPlainQS<max_deg>;

    const std::vector<poly128> bits = bits_as_field(wit);
    FQS qs_bits{bits, {}};
    constraints(&qs_bits);
    PQS plain{wit.data(), {}};
    constraints(&plain);

    const std::vector<poly128> field = random_field(bits.size(), rng);
    FQS qs_field{field, {}};
    constraints(&qs_field);

    const std::string where = std::string(relation) + " " + std::string(name);
    const size_t n = qs_bits.values.size();
    if (plain.violated.size() != n || qs_field.values.size() != n) {
        fail(where + ": inconsistent number of constraints");
    }
    for (size_t i = 0; i < n; ++i) {
        const bool nonzero = !(qs_bits.values[i] == poly128::set_zero());
        if (nonzero != plain.violated[i]) {
            fail(where + ": FieldQS and BasicPlainQS disagree at constraint " + std::to_string(i));
        }
        if (i < must_hold && nonzero) {
            fail(where + ": the witness violates constraint " + std::to_string(i));
        }
    }

    out << "\nrecord " << relation << ' ' << name << '\n';
    for (const auto& [key, value] : fields) {
        out << key << ' ' << value << '\n';
    }
    out << "wit " << to_hex(wit) << '\n'
        << "num_constraints " << n << '\n'
        << "values_bits " << hex128_list(qs_bits.values) << '\n'
        << "field_wit " << hex128_list(field) << '\n'
        << "values_field " << hex128_list(qs_field.values) << '\n'
        << "end\n";
}

constexpr size_t ALL = SIZE_MAX;

// Name of each UOV key in uov_keys.txt.
constexpr std::string_view KEY_TEST = "test"; // test::uov_key_pair()
constexpr std::string_view KEY_ALT = "alt61"; // the key pair with secret key filled(0x61)

const test::UovKeyPair& alt_key_pair() {
    static const test::UovKeyPair kp(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    return kp;
}

void dump_keys(const std::string& dir) {
    VectorFile f(dir, "uov_keys", "Expanded UOV public maps, referred to by name.");
    for (const auto& [name, pk] :
         {std::pair{KEY_TEST, &test::uov_key_pair().pk}, std::pair{KEY_ALT, &alt_key_pair().pk}}) {
        f.out() << "key " << name << ' ' << to_hex(uov::detail::PublicKeyAccess::expanded(*pk))
                << '\n';
    }
}

// The coefficients of the random linear combination derived from chal2.
template <typename QS>
std::string
combination_hex(std::span<const uint8_t, uov::detail::Combination<QS>::CHALLENGE_BYTES> chal2,
                std::span<const uint8_t> dst) {
    const uov::detail::Combination<QS> l(chal2, dst);
    std::vector<poly128> coeffs;
    coeffs.reserve(uov::M);
    for (size_t k = 0; k < uov::M; ++k) {
        coeffs.push_back(l.coeff(k));
    }
    return hex128_list(coeffs);
}

std::string input_map_string(const keccak::detail::InputMap& map) {
    std::string out;
    for (size_t i = 0; i < map.size(); ++i) {
        out += (i == 0 ? "" : ",") + std::to_string(map[i]);
    }
    return out;
}

// The field arithmetic: GF(2^128), GF(256), and the embedding.
void dump_field(const std::string& dir) {
    VectorFile f(dir, "field", "GF(2^128) and GF(256) arithmetic and the embedding of GF(256).");
    std::mt19937_64 rng(0x6669656c64);
    std::vector<poly128> beta, embed;
    for (size_t b = 0; b < 8; ++b) {
        beta.push_back(poly128::from_8_byte(static_cast<uint8_t>(1u << b)));
    }
    for (size_t a = 0; a < 256; ++a) {
        embed.push_back(poly128::from_8_byte(static_cast<uint8_t>(a)));
    }
    std::vector<uint8_t> gf256(256 * 256);
    for (size_t a = 0; a < 256; ++a) {
        for (size_t b = 0; b < 256; ++b) {
            gf256[256 * a + b] = ::gf256_mul(static_cast<uint8_t>(a), static_cast<uint8_t>(b));
        }
    }
    // Edge cases (0, 1, X, X^63, X^64, X^127, all ones), then random pairs.
    std::vector<poly128> special;
    for (const auto& [lo, hi] :
         std::initializer_list<std::pair<uint64_t, uint64_t>>{{0, 0},
                                                              {1, 0},
                                                              {2, 0},
                                                              {uint64_t{1} << 63, 0},
                                                              {0, 1},
                                                              {0, uint64_t{1} << 63},
                                                              {~uint64_t{0}, ~uint64_t{0}}}) {
        const std::array<uint64_t, 2> words = {lo, hi};
        special.push_back(poly128::load(words.data()));
    }
    std::vector<poly128> mul_a, mul_b, mul_ab;
    for (const poly128 x : special) {
        for (const poly128 y : special) {
            mul_a.push_back(x);
            mul_b.push_back(y);
        }
    }
    const std::vector<poly128> ra = random_field(256, rng), rb = random_field(256, rng);
    mul_a.insert(mul_a.end(), ra.begin(), ra.end());
    mul_b.insert(mul_b.end(), rb.begin(), rb.end());
    for (size_t i = 0; i < mul_a.size(); ++i) {
        mul_ab.push_back(vole_mole::test::mul128(mul_a[i], mul_b[i]));
    }
    f.out() << "\nrecord field arith\n"
            << "beta " << hex128_list(beta) << '\n'
            << "embed " << hex128_list(embed) << '\n'
            << "gf256_mul " << to_hex(gf256) << '\n'
            << "mul_a " << hex128_list(mul_a) << '\n'
            << "mul_b " << hex128_list(mul_b) << '\n'
            << "mul_ab " << hex128_list(mul_ab) << '\n'
            << "end\n";
}

// The standalone UOV gadget: l(P(s)) for the fixed test key and random coefficients l.
void dump_uov(const std::string& dir) {
    VectorFile f(dir, "uov", "UOV gadget: uov::detail::qs_eval_combined_public_map.");
    std::mt19937_64 rng(0x756f76);
    const std::vector<poly128> l_vec = random_field(uov::M, rng);
    std::array<poly128, uov::M> l_coeffs;
    std::ranges::copy(l_vec, l_coeffs.begin());
    const uov::Target target = filled<uov::M>(0x11);
    const uov::Preimage preimage = test::uov_key_pair().sk.derive_preimage(target);
    const auto constraints = [&](auto* qs) {
        using QS = std::remove_pointer_t<decltype(qs)>;
        const uov::detail::Combination<QS> l(l_coeffs);
        std::array<uov::detail::qs_val<QS, 1>, uov::N> s;
        for (size_t i = 0; i < uov::N; ++i) {
            s[i] = qs->load_witness_8_bits_and_combine(8 * i);
        }
        qs->add_constraint(
            uov::detail::qs_eval_combined_public_map<QS>(test::uov_key_pair().pk, s, l));
    };
    for (const bool honest : {true, false}) {
        const uov::Preimage s = honest ? preimage : random_bytes<uov::N>(rng);
        write_record<2>(f.out(), "uov", honest ? "preimage" : "random", s,
                        {{"pk", std::string(KEY_TEST)},
                         {"l", hex128_list(l_vec)},
                         {"target", honest ? to_hex(target) : "-"}},
                        rng, 0, constraints);
    }
}

// The standalone Keccak gadget: qs_keccak on an input that is partly public, partly witness.
void dump_keccak(const std::string& dir) {
    namespace kd = keccak::detail;
    VectorFile f(dir, "keccak", "Keccak-p[800] gadget: keccak::detail::qs_keccak and qs_byte.");
    std::mt19937_64 rng(0x6b656363);

    struct Case {
        std::string name;
        kd::InputMap map;
        size_t wit_input_bytes;
        size_t num_out_bits;
        bool honest;
    };
    kd::InputMap identity{}, odd{};
    for (size_t i = 0; i < KP800_STATE_BYTES; ++i) {
        identity[i] = static_cast<int>(i);
        odd[i] = i % 2 == 1 ? static_cast<int>(i / 2) : -1;
    }
    const std::array<Case, 3> cases = {
        Case{"secret_input", identity, KP800_STATE_BYTES, KP800_STATE_BITS, true},
        Case{"mixed_input", odd, KP800_STATE_BYTES / 2, 8 * uov::M, true},
        Case{"random", identity, KP800_STATE_BYTES, KP800_STATE_BITS, false},
    };
    for (const Case& c : cases) {
        // The full input state, and the public state with the witness bytes zeroed.
        const Kp800State input = random_bytes<KP800_STATE_BYTES>(rng);
        Kp800State public_state = input;
        std::vector<uint8_t> wit(c.wit_input_bytes + kd::COMMITTED_STATES_BYTES);
        for (size_t i = 0; i < KP800_STATE_BYTES; ++i) {
            if (c.map[i] >= 0) {
                wit[static_cast<size_t>(c.map[i])] = input[i];
                public_state[i] = 0;
            }
        }
        const std::span<uint8_t, kd::COMMITTED_STATES_BYTES> states(wit.data() + c.wit_input_bytes,
                                                                    kd::COMMITTED_STATES_BYTES);
        if (c.honest) {
            kd::encode_committed_states(states, input);
        } else {
            for (uint8_t& b : wit) {
                b = static_cast<uint8_t>(rng());
            }
        }
        const auto constraints = [&](auto* qs) {
            const auto out = kd::qs_keccak(qs, kd::qs_input(qs, public_state, c.map),
                                           c.wit_input_bytes, c.num_out_bits);
            for (size_t i = 0; i < c.num_out_bits; ++i) {
                qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(out[i]));
            }
            for (size_t k = 0; k < c.num_out_bits / 8; ++k) {
                qs->add_constraint(kd::qs_byte(out, k));
            }
        };
        write_record<kd::QS_DEGREE>(f.out(), "keccak", c.name, wit,
                                    {{"input_map", input_map_string(c.map)},
                                     {"public_state", to_hex(public_state)},
                                     {"wit_off_states", std::to_string(c.wit_input_bytes)},
                                     {"num_out_bits", std::to_string(c.num_out_bits)}},
                                    rng, c.honest ? kd::NUM_SEGMENT_CONSTRAINTS : 0, constraints);
    }
}

// Write an `honest` and a `random` record for relation `Rel`, whose QuickSilver degree is `deg`.
template <typename Rel, size_t deg, size_t WITNESS_BYTES>
void dump_relation(VectorFile& f, std::string_view relation,
                   const std::array<uint8_t, WITNESS_BYTES>& honest_wit,
                   const typename Rel::instance& x,
                   const std::array<uint8_t, Rel::params::CONSTS::QS::CHALLENGE_BYTES>& chal2,
                   Fields fields, std::mt19937_64& rng) {
    fields.insert(fields.begin(), {"chal2", to_hex(chal2)});
    const auto constraints = [&](auto* qs) { Rel::constraints(qs, x, chal2); };
    write_record<deg>(f.out(), relation, "honest", honest_wit, fields, rng, ALL, constraints);
    const auto random_wit = random_bytes<WITNESS_BYTES>(rng);
    write_record<deg>(f.out(), relation, "random", random_wit, fields, rng, 0, constraints);
}

template <size_t N> std::array<uint8_t, N> chal2_bytes() { return filled<N>(0x50); }

void dump_pomfrit_redeem(const std::string& dir) {
    namespace pd = pomfrit::detail;
    using Rel = pd::RedeemRelation;
    using FQS = test::FieldQS<pd::REDEEM_QS_DEGREE>;
    VectorFile f(dir, "pomfrit_redeem", "PomFRIT redemption relation, P(s) = h + r.");
    std::mt19937_64 rng(0x706f6d66);
    const uov::Target h = filled<uov::M>(0x70);
    const uov::Target r = filled<uov::M>(0xa0);
    uov::Target hr;
    for (size_t k = 0; k < uov::M; ++k) {
        hr[k] = h[k] ^ r[k];
    }
    const uov::Preimage s = test::uov_key_pair().sk.derive_preimage(hr);
    std::array<uint8_t, pd::REDEEM_WITNESS_BYTES> wit;
    std::ranges::copy(r, wit.begin() + pd::WIT_OFF_R);
    std::ranges::copy(s, wit.begin() + pd::WIT_OFF_S);
    const auto chal2 = chal2_bytes<Rel::params::CONSTS::QS::CHALLENGE_BYTES>();
    dump_relation<Rel, pd::REDEEM_QS_DEGREE>(
        f, "pomfrit_redeem", wit, {&test::uov_key_pair().pk, h}, chal2,
        {{"pk", std::string(KEY_TEST)},
         {"h", to_hex(h)},
         {"l", combination_hex<FQS>(chal2, vole_mole::detail::POMFRIT_COMBINE_DST)}},
        rng);
}

void dump_ihat(const std::string& dir) {
    namespace md = ihat::detail;
    const ihat::Context ctx_iss = filled<ihat::CTX_BYTES>(0x10);
    const ihat::Context ctx_red = filled<ihat::CTX_BYTES>(0x20);
    const ihat::ChallengeDigest challenge_digest =
        filled<ihat::CHALLENGE_DIGEST_BYTES>(0x70);
    const ihat::Nullifier nf = filled<ihat::NF_BYTES>(0x30);
    const md::Opening r = filled<md::R_BYTES>(0x40);
    const md::Commitment t = md::commit(nf, ctx_iss, ctx_red, r);

    {
        using Rel = md::IssueRelation;
        VectorFile f(dir, "ihat_issue",
                     "Ihat issuance relation, t = Com(nf, ctx_iss, ctx_red, r).");
        std::mt19937_64 rng(0x6d697373);
        dump_relation<Rel, md::ISSUE_QS_DEGREE>(
            f, "ihat_issue", md::encode_issue_witness(nf, ctx_iss, ctx_red, r), {t, ctx_iss},
            chal2_bytes<Rel::params::CONSTS::QS::CHALLENGE_BYTES>(),
            {{"t", to_hex(t)},
             {"ctx_iss", to_hex(ctx_iss)},
             {"keccak_in_0", to_hex(md::encode_com_state({}, ctx_iss, {}, {}))}},
            rng);
    }
    {
        using Rel = md::RedeemRelation;
        using FQS = test::FieldQS<md::REDEEM_QS_DEGREE>;
        VectorFile f(dir, "ihat_redeem",
                     "Ihat redemption relation, Q(s) = Com(nf, ctx_iss, ctx_red, r), Q in "
                     "the Anchor Set.");
        std::mt19937_64 rng(0x6d726564);
        // Two Anchors; the issuer (the fixed test key pair) is at index 1.
        const std::array<ihat::AnchorRef, 2> anchors = {alt_key_pair().pk,
                                                            test::uov_key_pair().pk};
        const uov::Preimage s = test::uov_key_pair().sk.derive_preimage(t);
        const auto chal2 = chal2_bytes<Rel::params::CONSTS::QS::CHALLENGE_BYTES>();
        dump_relation<Rel, md::REDEEM_QS_DEGREE>(
            f, "ihat_redeem", md::encode_redeem_witness(nf, ctx_iss, ctx_red, r, s, 1),
            {anchors, nf, ctx_iss, ctx_red, challenge_digest}, chal2,
            {{"anchors", std::string(KEY_ALT) + "," + std::string(KEY_TEST)},
             {"nf", to_hex(nf)},
             {"ctx_iss", to_hex(ctx_iss)},
             {"ctx_red", to_hex(ctx_red)},
             {"challenge_digest", to_hex(challenge_digest)},
             {"l", combination_hex<FQS>(chal2, vole_mole::detail::IHAT_REDEEM_COMBINE_DST)},
             {"keccak_in_0", to_hex(md::encode_com_state(nf, ctx_iss, ctx_red, {}))}},
            rng);
    }
}

void dump_act(const std::string& dir) {
    namespace rd = act::detail;
    using act::Credits;
    const act::Context ctx_iss = filled<act::CTX_BYTES>(0x10);
    const act::Nullifier nf = filled<act::NF_BYTES>(0x30);
    const rd::Opening r = filled<rd::R_BYTES>(0x40);

    {
        using Rel = rd::IssueRelation;
        VectorFile f(dir, "act_issue",
                     "Act issuance relation, c = Com(nf, ctx_iss, t_init, r).");
        std::mt19937_64 rng(0x72697373);
        const Credits t_init = 1000;
        const rd::Commitment c = rd::commit(nf, ctx_iss, t_init, r);
        dump_relation<Rel, rd::ISSUE_QS_DEGREE>(
            f, "act_issue", rd::encode_issue_witness(nf, ctx_iss, t_init, r),
            {c, t_init, ctx_iss}, chal2_bytes<Rel::params::CONSTS::QS::CHALLENGE_BYTES>(),
            {{"c", to_hex(c)},
             {"t_init", std::to_string(t_init)},
             {"ctx_iss", to_hex(ctx_iss)},
             {"keccak_in_0", to_hex(rd::encode_com_state({}, ctx_iss, t_init, {}))}},
            rng);
    }
    {
        using Rel = rd::SpendRelation;
        using FQS = test::FieldQS<rd::SPEND_QS_DEGREE>;
        VectorFile f(dir, "act_spend", "Act spend relation.");
        std::mt19937_64 rng(0x7273706e);
        const Credits t = 100, x_refund = 5, d = 30;
        const act::Nullifier nf_next = filled<act::NF_BYTES>(0x50);
        const rd::Opening r_next = filled<rd::R_BYTES>(0x60);
        const uov::Preimage s = test::uov_key_pair().sk.derive_preimage(
            rd::tag(rd::commit(nf, ctx_iss, t, r), x_refund));
        const rd::SpendState st{nf, t, r, x_refund, s, nf_next, t + x_refund - d, r_next};
        const rd::Commitment c_next = rd::commit(nf_next, ctx_iss, st.t_next, r_next);
        const auto chal2 = chal2_bytes<Rel::params::CONSTS::QS::CHALLENGE_BYTES>();
        dump_relation<Rel, rd::SPEND_QS_DEGREE>(
            f, "act_spend", rd::encode_spend_witness(st, d, ctx_iss),
            {test::uov_key_pair().pk, nf, d, c_next, ctx_iss}, chal2,
            {{"pk", std::string(KEY_TEST)},
             {"nf", to_hex(nf)},
             {"d", std::to_string(d)},
             {"c_next", to_hex(c_next)},
             {"ctx_iss", to_hex(ctx_iss)},
             {"l", combination_hex<FQS>(chal2, vole_mole::detail::ACT_SPEND_COMBINE_DST)},
             {"keccak_in_0", to_hex(rd::encode_com_state(nf, ctx_iss, 0, {}))},
             {"keccak_in_1", to_hex(rd::encode_tag_state({}, 0))},
             {"keccak_in_2", to_hex(rd::encode_com_state({}, ctx_iss, 0, {}))}},
            rng);
    }
}

} // namespace

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: dump_arith_vectors OUTPUT_DIR\n";
        return 1;
    }
    const std::string dir = argv[1];
    dump_field(dir);
    dump_keys(dir);
    dump_uov(dir);
    dump_keccak(dir);
    dump_pomfrit_redeem(dir);
    dump_ihat(dir);
    dump_act(dir);
    return 0;
}
