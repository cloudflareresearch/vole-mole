// Usage of UOV keys.

#include <vole_mole/random.hpp>
#include <vole_mole/uov.hpp>

#include <cstdio>
#include <cstdlib>
#include <print>

using namespace vole_mole;

int main() {
    // The UOV secret key is just a 32-byte random seed. This is the compact form of the key.
    const uov::SecretKeyBytes sk_bytes = uov::generate_secret_key_bytes();
    std::println("Secret key: {} bytes", sk_bytes.size());

    // Before the secret key can be used, it must first be expanded. This step is relatively
    // expensive, so keep the expanded key around for the lifetime of the process. This structure
    // also holds the expanded public key.
    const uov::SecretKey sk(sk_bytes);

    // The UOV public key, encoded in 46,591 bytes. Believe it or not, this is the compact form.
    const uov::PublicKeyBytes pk_bytes = sk.public_key();
    std::println("Public key: {} bytes", pk_bytes.size());

    // Before the public key can be used, it must first be expanded. Again, this step is relatively
    // expensive.
    const uov::PublicKey pk(pk_bytes);

    // Here is a minimal round-trip example for a UOV key pair as used in MOLE. The signer doesn't
    // produce a proper UOV signature. Instead, it directly derives a preimage for a target. This is
    // a building block for higher-level protocols, including PomFRIT, Moussaka, Ratatouille, and
    // UOV signatures themselves.
    //
    // WARNING: The target may be chosen by an attacker, and the signer can't tell what it's
    // signing. (A preimage for an attacker-chosen target is a valid UOV signature on any message
    // that hashes to it.) So this API should be used with care:
    //
    //   1. Don't expose this API to users directly. You will normally plumb it into some
    //      higher-level application whose security relies on one-more preimage resistance of UOV.
    //
    //   2. Enforce key separation: Use different keys for different protocols and deployments.
    const uov::Target t = random_bytes<uov::M>();
    if (pk.eval(sk.derive_preimage(t)) != t) {
        std::println(stderr, "the preimage doesn't map to the target");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
