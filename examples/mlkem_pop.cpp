// Proof of possession of an ML-KEM decapsulation key.

#include <vole_mole/mlkem.hpp>
#include <vole_mole/mlkem_pop.hpp>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <print>
#include <span>
#include <string_view>

using namespace vole_mole;

int main() {
    using P = mlkem::MlKem768;

    // Key generation.
    const auto [ek, dk] = mlkem::keygen<P>();

    // Verifier: Choose a fresh challenge, e.g., a CA issuing a certificate for ek. Binding the
    // proof to it prevents replay of a proof made for another context.
    constexpr std::string_view context_str = "example CA: certificate request #1";
    const std::span context(reinterpret_cast<const uint8_t*>(context_str.data()),
                            context_str.size());

    // Key holder: Prove possession of dk. The proof reveals nothing about dk.
    const auto proof = mlkem_pop::prove<P>(dk, context);

    // Verifier: Check the proof against ek alone.
    if (!mlkem_pop::verify<P>(ek, context, proof)) {
        std::println(stderr, "Verifier: the proof is invalid");
        return EXIT_FAILURE;
    }
    std::println("Verifier: accepted a {}-byte proof of possession for a {}-byte ML-KEM-768 key",
                 proof.size(), ek.size());

    return EXIT_SUCCESS;
}
