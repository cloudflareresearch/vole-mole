#ifndef VOLE_MOLE_UOV_HPP
#define VOLE_MOLE_UOV_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>

namespace vole_mole::uov {

namespace detail {
struct PublicKeyAccess;
} // namespace detail

class PublicKey;

constexpr size_t N = 119; // number of variables (preimage length)
constexpr size_t M = 45;  // number of equations (target length)

constexpr size_t SECRET_KEY_BYTES = 32;
constexpr size_t PUBLIC_KEY_BYTES = 46591;

using Target = std::array<uint8_t, M>;
using Preimage = std::array<uint8_t, N>;
using SecretKeyBytes = std::array<uint8_t, SECRET_KEY_BYTES>;
using PublicKeyBytes = std::array<uint8_t, PUBLIC_KEY_BYTES>;

// Generate a fresh secret key using the operating system's random number generator.
//
// The returned bytes are the entire secret key: store them securely and use SecretKey to expand the
// key pair from them.
//
// Throws std::runtime_error if the operating system's random number generator fails.
SecretKeyBytes generate_secret_key_bytes();

// An expanded secret key, alongside the compressed and expanded public key.
//
// The key pair lives on the heap and is move-only.
class SecretKey {
  public:
    // Expand the key pair from the compact secret key.
    //
    // Throws std::bad_alloc if memory allocation fails and std::runtime_error if key generation
    // fails.
    explicit SecretKey(const SecretKeyBytes& bytes);

    SecretKey(SecretKey&&) noexcept;
    SecretKey& operator=(SecretKey&&) noexcept;
    ~SecretKey();

    // The compressed public key bytes.
    const PublicKeyBytes& public_key_bytes() const;

    // The expanded public key, i.e., PublicKey(public_key_bytes()). It's expanded once when the
    // secret key is constructed and owned by the key pair; it's not reference counted. The
    // reference remains valid when the secret key is moved (it then belongs to the moved-to secret
    // key), and is invalidated when the owning secret key is destroyed or assigned to. Must not be
    // called on a moved-from secret key.
    const PublicKey& expanded_public_key() const;

    // Derive the preimage of the given target, i.e., P(preimage) = target, where P is the public
    // map.
    //
    // WARNING: This API is dangerous and not suitable for all application scenarios. It can be used
    // to construct a UOV signature for any message without the signer being able to validate what
    // it's signing. The caller should ensure that the secret key is not reused for applications
    // that require full UOV signatures.
    //
    // Throws std::runtime_error if derivation fails (which happens with negligible probability).
    Preimage derive_preimage(const Target& target) const;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

// An expanded public key.
//
// The key lives on the heap and is move-only.
class PublicKey {
  public:
    // Expand the compressed public key.
    //
    // Throws std::bad_alloc if memory allocation fails.
    explicit PublicKey(const PublicKeyBytes& bytes);

    PublicKey(PublicKey&&) noexcept;
    PublicKey& operator=(PublicKey&&) noexcept;
    ~PublicKey();

    // Evaluate the public map P at preimage and return the target. The preimage is valid for
    // target if and only if P(preimage) = target.
    Target eval(const Preimage& preimage) const;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    friend struct detail::PublicKeyAccess;
};

} // namespace vole_mole::uov

#endif
