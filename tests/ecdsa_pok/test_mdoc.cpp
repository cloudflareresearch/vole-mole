// Tests of the experimental mdoc proof (src/ecdsa_pok/mdoc_relation.hpp), with mdocs from
// Longfellow's tests (mdoc_vectors.txt).

#include "ecdsa_pok/mdoc_relation.hpp"

#include "mdoc_vectors.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdio>
#include <fstream>
#include <functional>
#include <map>
#include <sstream>
#include <string>
#include <vector>

namespace {

namespace md = vole_mole::ecdsa_pok::detail::mdoc;
using vole_mole::ecdsa_pok::Params;
using vole_mole::ecdsa_pok::Vole;
using vole_mole::ecdsa_pok::WitnessPrg;
using vole_mole::ecdsa_pok::detail::PlainOps;
using vole_mole::ecdsa_pok::detail::SHAPE_DERIVED;
using vole_mole::ecdsa_pok::detail::SHAPE_DIRECT;

using namespace mdoc_vectors;

md::BinPublic dummy_public(size_t na) {
    md::BinPublic pub{};
    for (size_t a = 0; a < na; ++a) {
        pub.ei.emplace_back(20, 0x71);
        pub.ev.emplace_back(14, 0x6C);
    }
    return pub;
}

TEST(Mdoc, Counts) {
    for (size_t na = 1; na <= md::MAX_ATTRIBUTES; ++na) {
        const auto pub = dummy_public(na);
        const auto d = md::count_circuit<SHAPE_DIRECT>(pub);
        const auto r = md::count_circuit<SHAPE_DERIVED>(pub);
        std::printf("na %zu: direct {%zu, %zu}, derived {%zu, %zu}\n", na, d.prefix_bits,
                    d.constraints, r.prefix_bits, r.constraints);
        EXPECT_EQ(d.prefix_bits, md::counts(3, na).prefix_bits);
        EXPECT_EQ(d.constraints, md::counts(3, na).constraints);
        EXPECT_EQ(r.prefix_bits, md::counts(2, na).prefix_bits);
        EXPECT_EQ(r.constraints, md::counts(2, na).constraints);
    }
    for (const auto prg : {WitnessPrg::none, WitnessPrg::local}) {
        for (size_t na : {1, 4}) {
            std::printf("proof bytes (PRG %d, %zu attributes): fast %zu, medium %zu, small %zu\n",
                        static_cast<int>(prg), na, md::proof_bytes(na, {Vole::fast, prg}),
                        md::proof_bytes(na, {Vole::medium, prg}),
                        md::proof_bytes(na, {Vole::small, prg}));
        }
    }
}

// The witness of each vector satisfies the binary circuit.
TEST(Mdoc, Witness) {
    const std::vector<std::pair<int, std::vector<md::Attribute>>> cases = {
        {0, {AGE_OVER_18}},  {3, {FAMILY_NAME, BIRTH_DATE, HEIGHT, AGE_OVER_18}},
        {8, {BIRTH_YEAR}},   {15, {AGE_OVER_18}},
        {16, {AGE_OVER_18}},
    };
    for (const auto& [v, attrs] : cases) {
        const auto req = request(v, attrs);
        const auto m = md::parse(vectors().at(v).mdoc, req);
        const auto dmsg = md::device_sig_structure(req.transcript, req.doc_type);
        const auto rb = vole_mole::ecdsa_pok::detail::rr::encode_r(
            vole_mole::ecdsa_pok::detail::rr::nonce_point(m.q, dmsg, m.device_sig));
        const auto pub =
            md::make_public(req, rb, Vole::fast, vole_mole::ecdsa_pok::detail::BinPrg::local);
        ASSERT_TRUE(pub) << v;
        const std::array<uint8_t, 32> seed{};
        const auto wit = md::make_witness(req, m, *pub, seed);
        for (const size_t log : {2, 3}) {
            std::vector<uint8_t> w(md::counts(log, attrs.size()).prefix_bits / 8 + 1);
            PlainOps ops{w};
            if (log == 2) {
                md::prefix_circuit<2>(ops, pub->bin, &wit.bin);
            } else {
                md::prefix_circuit<3>(ops, pub->bin, &wit.bin);
            }
            EXPECT_EQ(ops.failed, 0u) << v << " " << log;
        }
    }
}

TEST(Mdoc, Honest) {
    const auto req = request(0, {AGE_OVER_18});
    const auto proof = md::prove(vectors().at(0).mdoc, req);
    EXPECT_EQ(proof.size(), md::proof_bytes(1));
    EXPECT_TRUE(md::verify(req, proof));
    auto bad = req;
    bad.attributes = {NOT_OVER_18};
    EXPECT_FALSE(md::verify(bad, proof));
    bad = req;
    bad.now[3] = '9'; // 2029
    EXPECT_FALSE(md::verify(bad, proof));
    bad = req;
    bad.transcript[5] ^= 1;
    EXPECT_FALSE(md::verify(bad, proof));
}

// Each vector, with 1 to 4 attributes, and items with keys in different orders (15, 16).
TEST(Mdoc, Vectors) {
    const std::vector<std::pair<int, std::vector<md::Attribute>>> cases = {
        {3, {FAMILY_NAME}},
        {3, {FAMILY_NAME, BIRTH_DATE}},
        {3, {HEIGHT, AGE_OVER_18, BIRTH_DATE}},
        {3, {FAMILY_NAME, BIRTH_DATE, HEIGHT, AGE_OVER_18}},
        {8, {BIRTH_YEAR}},
        {15, {AGE_OVER_18}},
        {16, {AGE_OVER_18}},
    };
    for (const auto& [v, attrs] : cases) {
        const auto req = request(v, attrs);
        const auto proof = md::prove(vectors().at(v).mdoc, req);
        EXPECT_EQ(proof.size(), md::proof_bytes(attrs.size()));
        EXPECT_TRUE(md::verify(req, proof)) << v << " " << attrs.size();
        // The attributes in another order.
        auto swapped = req;
        std::ranges::reverse(swapped.attributes);
        EXPECT_EQ(md::verify(swapped, proof), attrs.size() == 1) << v;
    }
    // Attributes the mdoc doesn't have.
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, request(0, {NOT_OVER_18})), std::invalid_argument);
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, request(0, {FAMILY_NAME})), std::invalid_argument);
    // Expired.
    auto late = request(0, {AGE_OVER_18});
    late.now[0] = '3';
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, late), std::invalid_argument);
    // The wrong transcript or issuer.
    auto other = request(0, {AGE_OVER_18});
    other.transcript[3] ^= 1;
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, other), std::invalid_argument);
    other = request(0, {AGE_OVER_18});
    other.issuer_pk = vectors().at(3).req.issuer_pk;
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, other), std::invalid_argument);
}

TEST(Mdoc, OtherParams) {
    const auto req = request(0, {AGE_OVER_18});
    for (const auto vole : {Vole::fast, Vole::medium, Vole::small}) {
        for (const auto prg : {WitnessPrg::none, WitnessPrg::local}) {
            const Params params{vole, prg};
            const auto proof = md::prove(vectors().at(0).mdoc, req, params);
            EXPECT_EQ(proof.size(), md::proof_bytes(1, params));
            EXPECT_TRUE(md::verify(req, proof, params));
            for (const auto vole2 : {Vole::fast, Vole::medium, Vole::small}) {
                for (const auto prg2 : {WitnessPrg::none, WitnessPrg::local}) {
                    if (vole2 != vole || prg2 != prg) {
                        EXPECT_FALSE(md::verify(req, proof, {vole2, prg2}));
                    }
                }
            }
        }
    }
    EXPECT_THROW(md::prove(vectors().at(0).mdoc, req, {Vole::fast, WitnessPrg::mq}),
                 std::invalid_argument);
    EXPECT_FALSE(md::verify(req, std::vector<uint8_t>(100), {Vole::fast, WitnessPrg::mq}));
}

TEST(Mdoc, RejectsBadInputs) {
    const auto req = request(0, {AGE_OVER_18});
    const auto proof = md::prove(vectors().at(0).mdoc, req);
    // R off the curve, or not a field element.
    auto bad = proof;
    bad[40] ^= 1;
    EXPECT_FALSE(md::verify(req, bad));
    std::fill_n(bad.begin(), 32, 0xff);
    EXPECT_FALSE(md::verify(req, bad));
    // No attributes, or too many.
    auto r = req;
    r.attributes.clear();
    EXPECT_FALSE(md::verify(r, proof));
    r.attributes.assign(md::MAX_ATTRIBUTES + 1, AGE_OVER_18);
    EXPECT_FALSE(md::verify(r, proof));
    // An invalid issuer key.
    r = req;
    r.issuer_pk[10] ^= 1;
    EXPECT_FALSE(md::verify(r, proof));
    // Not a DeviceResponse.
    EXPECT_THROW(md::prove(std::vector<uint8_t>{0xA0}, req), std::invalid_argument);
}

TEST(Mdoc, Tampered) {
    const auto req = request(0, {AGE_OVER_18});
    const auto proof = md::prove(vectors().at(0).mdoc, req);
    using S = md::Scheme<1, Vole::fast, vole_mole::ecdsa_pok::detail::BinPrg::local>;
    for (const size_t off : {size_t{3}, S::OFF_BIN + 100, S::OFF_BIN + S::BIN_BYTES - 5,
                             S::OFF_ARITH + 1000, S::OFF_ZN + 2, S::OFF_ZQ + 7, S::OFF_Y + 1}) {
        auto bad = proof;
        bad[off] ^= 0x10;
        EXPECT_FALSE(md::verify(req, bad)) << off;
    }
    EXPECT_FALSE(md::verify(req, std::vector<uint8_t>(proof.begin(), proof.end() - 1)));
}

// White-box tests: prove with a modified witness (or for a modified request), and check that the
// proof is rejected. faest-arch-opt's prover asserts that the binary constraints hold, so these
// only run with NDEBUG.
struct Cheat {
    int v = 0;
    std::vector<md::Attribute> attrs = {AGE_OVER_18}; // the witness's
    std::vector<md::Attribute> claimed = {};          // the request's, if different
    std::function<void(md::Request&)> request;        // modifies the request
    std::function<void(md::Witness&)> witness;        // modifies the witness
    md::Tamper tamper;                                // modifies the binary witness bits
    Params params = {};
};

bool cheat_verifies(const Cheat& c) {
    const auto real = request(c.v, c.attrs);
    const auto m = md::parse(vectors().at(c.v).mdoc, real);
    auto req = real;
    if (!c.claimed.empty()) {
        req.attributes = c.claimed;
    }
    if (c.request) {
        c.request(req);
    }
    const auto dmsg = md::device_sig_structure(req.transcript, req.doc_type);
    const auto rb = vole_mole::ecdsa_pok::detail::rr::encode_r(
        vole_mole::ecdsa_pok::detail::rr::nonce_point(m.q, dmsg, m.device_sig));
    const auto pub = md::make_public(req, rb, c.params.vole,
                                     vole_mole::ecdsa_pok::detail::rr::bin_prg_of(c.params.prg));
    if (!pub) {
        return false;
    }
    const std::array<uint8_t, 32> seed{1};
    // For another issuer, the issuer's witness is for the real one.
    auto wit = [&] {
        if (req.issuer_pk == real.issuer_pk) {
            return md::make_witness(req, m, *pub, seed);
        }
        auto r2 = req;
        r2.issuer_pk = real.issuer_pk;
        auto p2 = *pub;
        p2.issuer_tables = vole_mole::ecdsa_pok::detail::make_tables(
            *vole_mole::p256::decode_point(real.issuer_pk));
        return md::make_witness(r2, m, p2, seed);
    }();
    if (c.witness) {
        c.witness(wit);
    }
    const md::Tamper none = [](std::span<uint8_t>, const md::MdocWires<PlainOps>&) {};
    const md::Tamper* tamper = c.tamper ? &c.tamper : &none;
    const auto proof =
        md::dispatch(req.attributes.size(), c.params,
                     [&]<size_t NA, Vole V, vole_mole::ecdsa_pok::detail::BinPrg PRG>() {
                         std::vector<uint8_t> p(md::Scheme<NA, V, PRG>::PROOF_BYTES);
                         md::prove_with_witness<NA, V, PRG>(
                             std::span<uint8_t, md::Scheme<NA, V, PRG>::PROOF_BYTES>(p), rb, *pub,
                             wit, seed, tamper);
                         return p;
                     });
    return md::verify(req, proof, c.params);
}

void flip(std::span<uint8_t> w, size_t i) { w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8)); }

#ifdef NDEBUG
#define SKIP_IF_ASSERTS()
#else
#define SKIP_IF_ASSERTS() GTEST_SKIP() << "the binary prover asserts that its constraints hold"
#endif

TEST(Mdoc, CheatBaseline) {
    SKIP_IF_ASSERTS();
    // The white-box prover with an unmodified witness.
    EXPECT_TRUE(cheat_verifies({}));
    EXPECT_TRUE(cheat_verifies({.params = {Vole::fast, WitnessPrg::none}}));
}

TEST(Mdoc, CheatMessage) {
    SKIP_IF_ASSERTS();
    // e is the chaining value after a later (zero) block.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { ++w.bin.last; }}));
    // A nonzero byte after the last block.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) {
        w.bin.sig[64 * (w.bin.last + 1) + 5] = 0x42;
        w.bin.traces = vole_mole::ecdsa_pok::detail::sha256_traces(w.bin.sig);
    }}));
    // Two blocks selected.
    EXPECT_FALSE(
        cheat_verifies({.tamper = [](std::span<uint8_t> b, const md::MdocWires<PlainOps>& wr) {
            flip(b, wr.t_bit + 20);
        }}));
}

TEST(Mdoc, CheatWindows) {
    SKIP_IF_ASSERTS();
    for (size_t win = 0; win < md::W_ATTR + 1; ++win) {
        // The wrong offset.
        EXPECT_FALSE(cheat_verifies({.witness = [win](md::Witness& w) { ++w.bin.windows[win]; }}))
            << win;
        // Two blocks selected.
        EXPECT_FALSE(cheat_verifies({.tamper = [win](std::span<uint8_t> b,
                                                     const md::MdocWires<PlainOps>& wr) {
            flip(b, wr.window_bits[win] + 39);
        }})) << win;
    }
    // A date that isn't the MSO's.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { w.bin.valid_until[0] = '3'; }}));
    // A device key that isn't the MSO's.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { w.bin.qx[0] ^= 1; }}));
}

TEST(Mdoc, CheatStatement) {
    SKIP_IF_ASSERTS();
    // Expired, or not yet valid.
    EXPECT_FALSE(cheat_verifies({.request = [](md::Request& r) { r.now[0] = '3'; }}));
    EXPECT_FALSE(cheat_verifies({.request = [](md::Request& r) { r.now[0] = '1'; }}));
    // Another value, or identifier.
    EXPECT_FALSE(cheat_verifies({.claimed = {NOT_OVER_18}}));
    EXPECT_FALSE(cheat_verifies({.claimed = {{"age_over_21", {0xF5}}}}));
    // Another issuer.
    EXPECT_FALSE(cheat_verifies(
        {.request = [](md::Request& r) { r.issuer_pk = vectors().at(3).req.issuer_pk; }}));
}

TEST(Mdoc, CheatItem) {
    SKIP_IF_ASSERTS();
    // Swap the slots of digestID and random.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) {
        auto& it = w.bin.items[0];
        std::swap(it.slot_of[md::F_DIGEST_ID], it.slot_of[md::F_RANDOM]);
    }}));
    // The wrong length of a slot, or of the random value.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { ++w.bin.items[0].slot_len[1]; }}));
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { ++w.bin.items[0].rnd_n; }}));
    // The wrong class of digestID header.
    EXPECT_FALSE(cheat_verifies({.witness = [](md::Witness& w) { w.bin.items[0].id_class ^= 1; }}));
}

} // namespace
