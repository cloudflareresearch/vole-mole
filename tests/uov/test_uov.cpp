// Tests for UOV preimage derivation, as used by the PomFRIT Issuer to sign Moussaka commitments.

#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "test.hpp"

extern "C" {
#include "randomness.h" // from faest-arch-opt
}

#include <gtest/gtest.h>

#include <type_traits>
#include <utility>

using namespace vole_mole;
using vole_mole::test::filled;
using vole_mole::test::to_hex;

// A Moussaka commitment is a UOV target.
static_assert(std::is_same_v<moussaka::Commitment, uov::Target>);

namespace {

const moussaka::Context CTX_ISS = filled<moussaka::CTX_BYTES>(0x10);
const moussaka::Context CTX_RED = filled<moussaka::CTX_BYTES>(0x20);
const moussaka::Nullifier NF = filled<moussaka::NF_BYTES>(0x30);
const moussaka::Opening R = filled<moussaka::R_BYTES>(0x40);

const uov::SecretKeyBytes SK_BYTES = filled<uov::SECRET_KEY_BYTES>(0x60);

struct KeyPair {
    uov::PublicKey pk;
    uov::SecretKey sk;

    // Members are initialized in declaration order, so pk is expanded from sk_ before it's moved.
    explicit KeyPair(uov::SecretKey sk_) : pk(sk_.public_key()), sk(std::move(sk_)) {}
};

const KeyPair& key_pair() {
    static const KeyPair kp(uov::SecretKey{SK_BYTES});
    return kp;
}

} // namespace

TEST(Uov, DerivePreimageOfCommitment) {
    const auto& [pk, sk] = key_pair();
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    const uov::Preimage w = sk.derive_preimage(t);
    EXPECT_EQ(to_hex(pk.eval(w)), to_hex(t));
}

TEST(Uov, DerivePreimageIsDeterministic) {
    const auto& [pk, sk] = key_pair();
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_EQ(to_hex(sk.derive_preimage(t)), to_hex(sk.derive_preimage(t)));

    // A different target has a different preimage.
    moussaka::Opening r2 = R;
    r2[0] ^= 1;
    const moussaka::Commitment t2 = moussaka::commit(NF, CTX_ISS, CTX_RED, r2);
    const uov::Preimage w2 = sk.derive_preimage(t2);
    EXPECT_NE(to_hex(w2), to_hex(sk.derive_preimage(t)));
    EXPECT_EQ(to_hex(pk.eval(w2)), to_hex(t2));
}

TEST(Uov, SecretKeyExpansionIsDeterministic) {
    const auto& [pk, sk] = key_pair();
    const uov::SecretKey sk2(SK_BYTES);
    EXPECT_EQ(to_hex(sk2.public_key()), to_hex(sk.public_key()));
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_EQ(to_hex(sk2.derive_preimage(t)), to_hex(sk.derive_preimage(t)));
}

TEST(Uov, KeysAreMovable) {
    uov::SecretKey sk(SK_BYTES);
    const uov::PublicKeyBytes pk_bytes = sk.public_key();
    uov::SecretKey sk2 = std::move(sk);
    uov::PublicKey pk(pk_bytes);
    uov::PublicKey pk2 = std::move(pk);
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_EQ(to_hex(pk2.eval(sk2.derive_preimage(t))), to_hex(t));
}

TEST(Uov, RejectWrongKey) {
    const auto& [pk, sk] = key_pair();
    const KeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    EXPECT_NE(to_hex(other.sk.public_key()), to_hex(sk.public_key()));
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_NE(to_hex(other.pk.eval(sk.derive_preimage(t))), to_hex(t));
}

TEST(Uov, RejectTamperedPublicKey) {
    const auto& [pk, sk] = key_pair();
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    const uov::Preimage w = sk.derive_preimage(t);

    // Both the seed (first 16 bytes) and P3 (the rest) of the compressed key matter.
    for (const size_t i : {size_t{0}, size_t{15}, size_t{16}, uov::PUBLIC_KEY_BYTES - 1}) {
        uov::PublicKeyBytes bad = sk.public_key();
        bad[i] ^= 1;
        EXPECT_NE(to_hex(uov::PublicKey(bad).eval(w)), to_hex(t)) << "flipped a bit of byte " << i;
    }
}

TEST(Uov, RejectTamperedPreimage) {
    const auto& [pk, sk] = key_pair();
    const moussaka::Commitment t = moussaka::commit(NF, CTX_ISS, CTX_RED, R);
    const uov::Preimage w = sk.derive_preimage(t);
    for (size_t i = 0; i < w.size(); i += 7) {
        uov::Preimage bad = w;
        bad[i] ^= 1;
        EXPECT_NE(to_hex(pk.eval(bad)), to_hex(t)) << "flipped a bit of byte " << i;
    }
}
