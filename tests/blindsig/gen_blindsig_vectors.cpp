// Write a test vector for the blind signature relation to stdout, for the Longfellow implementation
// in experiments/longfellow. Each line is "name HEX":
//
//   nf      the nullifier
//   r       the opening
//   s       the UOV preimage, P(s) = t
//   t       the commitment Com(nf, r)
//   state0  the input of Keccak-p[800, 12]
//   stateK  the state after K rounds, for K in 1..12
//   pk      the expanded public map: for each monomial s_i * s_j with i <= j, in increasing order
//           of i and then j, the M coefficients of the monomial in GF(256) (AES polynomial)

#include "test.hpp"

#include "blindsig/blindsig.hpp"

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <string>

using namespace vole_mole;
using namespace vole_mole::blindsig;
using vole_mole::test::to_hex;

int main() {
    const auto& [pk, sk] = vole_mole::test::uov_key_pair();
    const Nullifier nf = vole_mole::test::filled<moussaka::NF_BYTES>(0x30);
    const Opening r = vole_mole::test::filled<R_BYTES>(0x40);
    const uov::Target t = commit(nf, r);
    const uov::Preimage s = sk.derive_preimage(t);
    if (pk.eval(s) != t) {
        std::cerr << "P(s) != t\n";
        return EXIT_FAILURE;
    }

    // Check that the vector also satisfies the VOLEitH relation.
    Proof proof;
    prove(proof, pk, nf, r, s, {});
    if (!verify(proof, pk, nf)) {
        std::cerr << "proof failed to verify\n";
        return EXIT_FAILURE;
    }

    std::cout << "nf " << to_hex(nf) << '\n';
    std::cout << "r " << to_hex(r) << '\n';
    std::cout << "s " << to_hex(s) << '\n';
    std::cout << "t " << to_hex(t) << '\n';
    Kp800State state = encode_com_state(nf, r);
    std::cout << "state0 " << to_hex(state) << '\n';
    for (size_t k = 1; k <= KP800_ROUNDS; ++k) {
        keccak_p800_rounds(state, k - 1, 1);
        std::cout << "state" << k << ' ' << to_hex(state) << '\n';
    }

    std::string pk_hex;
    uov::detail::for_each_monomial(
        uov::detail::PublicKeyAccess::expanded(pk),
        [&](size_t, size_t, std::span<const uint8_t, uov::M> coeffs) { pk_hex += to_hex(coeffs); });
    std::cout << "pk " << pk_hex << '\n';
    return EXIT_SUCCESS;
}
