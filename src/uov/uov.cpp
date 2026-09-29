#include "vole_mole/uov.hpp"

#include "uov/public_key.hpp"

#include "hash.hpp" // from faest-arch-opt

extern "C" {
#include "ov.h"         // from pqov
#include "randomness.h" // from faest-arch-opt
}

#include <cstdlib>
#include <cstring>
#include <stdexcept>

// pqov normally implements randombytes() with OpenSSL. We build it without OpenSSL, in which case
// the application must provide it.
extern "C" void PQOV_NAMESPACE(randombytes)(unsigned char* x, unsigned long long xlen) {
    if (rand_bytes(x, static_cast<size_t>(xlen)) != 0) {
        std::abort(); // pqov has no way to report the failure
    }
}

namespace vole_mole::uov {

// Check that pqov is built with the expected variant and parameter set.
static_assert(_GFSIZE == 256 && N == _PUB_N_BYTE && M == _PUB_M_BYTE);
static_assert(OV_PUBLICKEYBYTES == sizeof(cpk_t) && OV_SECRETKEYBYTES == sizeof(sk_t));
static_assert(SECRET_KEY_BYTES == LEN_SKSEED);
static_assert(PUBLIC_KEY_BYTES == sizeof(cpk_t));
static_assert(detail::V == _V && detail::EXPANDED_PUBLIC_KEY_BYTES == sizeof(pk_t));
static_assert(detail::EXPANDED_PUBLIC_KEY_BYTES == _PK_P1_BYTE + _PK_P2_BYTE + _PK_P3_BYTE);

struct SecretKey::Impl {
    sk_t sk;
    PublicKeyBytes public_key;
};

struct PublicKey::Impl {
    pk_t pk;
    detail::PublicKeyDigest digest;
};

SecretKey::SecretKey(const SecretKeyBytes& bytes) : impl_(std::make_unique<Impl>()) {
    cpk_t cpk;
    if (generate_keypair_pkc(&cpk, &impl_->sk, bytes.data()) != 0) {
        throw std::runtime_error("UOV key generation failed");
    }
    // Copy rather than cast; see PublicKey::PublicKey().
    std::memcpy(impl_->public_key.data(), &cpk, sizeof(cpk));
}

SecretKey::SecretKey(SecretKey&&) noexcept = default;
SecretKey& SecretKey::operator=(SecretKey&&) noexcept = default;
SecretKey::~SecretKey() = default;

const PublicKeyBytes& SecretKey::public_key() const { return impl_->public_key; }

PublicKey::PublicKey(const PublicKeyBytes& bytes) : impl_(std::make_unique<Impl>()) {
    // cpk_t is a packed struct of byte arrays, so `bytes` has exactly its layout, but casting
    // `bytes.data()` to `const cpk_t*` is technically undefined behavior: no cpk_t object exists
    // there, and C++ only allows accessing an object through a pointer to its own type (or as
    // bytes). Copying is well-defined and cheap relative to expanding the key.
    cpk_t cpk;
    std::memcpy(&cpk, bytes.data(), sizeof(cpk));
    expand_pk(&impl_->pk, &cpk); // always returns 0

    faest::hash_state hasher;
    hasher.init(faest::secpar::s256);
    hasher.update(bytes);
    hasher.finalize(impl_->digest);
}

PublicKey::PublicKey(PublicKey&&) noexcept = default;
PublicKey& PublicKey::operator=(PublicKey&&) noexcept = default;
PublicKey::~PublicKey() = default;

Preimage SecretKey::derive_preimage(const Target& target) const {
    Preimage preimage;
    if (ov_derive_preimage(preimage.data(), &impl_->sk, target.data()) != 0) {
        throw std::runtime_error("UOV preimage derivation failed");
    }
    return preimage;
}

Target PublicKey::eval(const Preimage& preimage) const {
    Target target;
    ov_publicmap(target.data(), impl_->pk.pk, preimage.data());
    return target;
}

std::span<const uint8_t, detail::EXPANDED_PUBLIC_KEY_BYTES>
detail::PublicKeyAccess::expanded(const PublicKey& pk) {
    return std::span<const uint8_t, EXPANDED_PUBLIC_KEY_BYTES>(pk.impl_->pk.pk,
                                                               EXPANDED_PUBLIC_KEY_BYTES);
}

const detail::PublicKeyDigest& detail::PublicKeyAccess::digest(const PublicKey& pk) {
    return pk.impl_->digest;
}

} // namespace vole_mole::uov
