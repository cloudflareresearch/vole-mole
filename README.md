# vole-mole

Various post-quantum anonymous credentials based on the [UOV][uov] signature
scheme and the VOLE-in-the-Head (VOLEitH) proof system from [FAEST][faest]:

1. [PomFRIT][pomfrit], a blind signature. Allows a client to obtain and later
   present a signature without revealing the message to the issuer.

2. [VOLE-IHAT][ihat], an issuer-hiding anonymous token (IHAT). Similar to a
   blind signature, except presentation (aka redemption) also hides the issuer
   among an anonymity set.

3. [VOLE-ACT][act], an anonymous credit token (ACT). The token carries state
   across presentations (aka spends) that the issuer updates without learning
   its value.

> [!WARNING]
> Experimental and not audited. Do not use in production. APIs and wire formats
> will change as the specifications evolve.

## Build

You need [Meson][meson] 1.4 or later, Ninja, Python 3, and Clang 21 or later or
GCC 16 or later.

```sh
meson setup build
meson compile -C build
meson test -C build --print-errorlogs
```

On MacOS you might need to upgrade LLVM:

```sh
brew install meson ninja llvm@22
export CC=$(brew --prefix llvm@22)/bin/clang
export CXX=$(brew --prefix llvm@22)/bin/clang++
```

## Examples

The "Hello, World!" of this library is a blind signature:

```cpp
#include <vole_mole/pomfrit.hpp>
#include <vole_mole/uov.hpp>

using namespace vole_mole;

const uov::SecretKey sk(uov::generate_secret_key_bytes());
const uov::PublicKey pk(sk.public_key_bytes());

// Client: Generate issue request.
auto [pending, request] = pomfrit::issue_request(pk, msg);

// Issuer: Generate issue response.
const auto response = pomfrit::issue_response(sk, request);

// Client: Finalize the blind signature.
const auto sig = std::move(pending).finalize_issue(pk, response);
if (!sig) {
    return EXIT_FAILURE;
}

// Verifier: Verify the blind signature.
const bool ok = pomfrit::verify(pk, msg, *sig);
```

The `examples/` folder includes additional examples:

| Example                                         | Shows                                                 |
|:------------------------------------------------|:------------------------------------------------------|
| [`pomfrit.cpp`](examples/pomfrit.cpp)           | PomFRIT signature issuance and verification           |
| [`ihat.cpp`](examples/ihat.cpp)                 | VOLE-IHAT issuance and redemption                     |
| [`unbound_ihat.cpp`](examples/unbound_ihat.cpp) | VOLE-IHAT with late binding of the redemption context |
| [`act.cpp`](examples/act.cpp)                   | VOLE-ACT issuance and spend                           |

## Benchmarks

```sh
meson setup build-release --buildtype=release
meson test -C build-release --benchmark  -v
```

Client messages carrying proofs are 5–17 KB. On an Apple M4 Pro, every step
takes under 2 ms, except VOLE-IHAT redemption, which grows with the number of
Anchors (about 7 ms for 64). See [docs/perf.md](docs/perf.md) for full numbers,
the smaller-proof parameter trade-off (4-12KB), and how to run the benchmarks.

### Deriving the witness with a PRG

Each committed witness bit costs τ = 17 bits of proof. Instead, the witness `w`
can be derived from a short key `K` with a dense quadratic PRG `G` over `GF(2)`
([`src/mq/prg.hpp`](src/mq/prg.hpp)): the VOLE witness is `K`, and the proof
carries `e = w + G(K)`, one bit per witness bit. The constraints are evaluated
unchanged on the committed `w = e + G(K)`, which has degree 2, so the
QuickSilver degree doubles (see "Derived witnesses" in
[`src/voleith.hpp`](src/voleith.hpp)). `G` is split into `c` independent
instances ([`src/mq/split.hpp`](src/mq/split.hpp)), each with its own key: this
divides the cost of evaluating `G` by about `c`, while the total key grows like
`√c`.

Like τ, this is a VOLEitH parameter of each relation: `MQ_PRG_INSTANCES` (`c`,
or 0 to commit to the witness directly) next to its parameter set, e.g.,
`ISSUE_MQ_PRG_INSTANCES` in [`src/ihat/issue.hpp`](src/ihat/issue.hpp).
Changing it changes the proof size, so the size in the public header has to be
updated, too. By default, none of the protocols derives its witnesses. Deriving
them makes the proofs 32–52% smaller, but proving and verifying several
milliseconds slower (Apple M4 Pro, `c = 2` except for `spend_request`, which has
a much longer witness and uses `c = 8`):

| Protocol    | Step                      | Party     | Sends (off → on)  | Time (off → on)    |
|:------------|:--------------------------|:----------|------------------:|-------------------:|
| PomFRIT     | `issue_request`           | Client    | 45 B              | 0.26 → 1.53 ms     |
|             | `finalize_issue`          | Client    | 5643 → 3825 B     | 0.19 → 0.22 ms     |
|             | `verify`                  | Verifier  | —                 | 0.38 → 1.39 ms     |
| VOLE-IHAT   | `issue_request`           | Client    | 7317 → 4804 B     | 0.60 → 3.65 ms     |
|             | `issue_response`          | Anchor    | 119 B             | 0.36 → 2.38 ms     |
|             | `redeem_request` (N = 1)  | Client    | 8775 → 5006 B     | 0.77 → 5.62 ms     |
|             | `finalize_redeem` (N = 1) | Moderator | —                 | 0.51 → 4.16 ms     |
| VOLE-ACT    | `issue_request`           | Client    | 7032 → 4775 B     | 0.58 → 3.40 ms     |
|             | `issue_response`          | Issuer    | 119 B             | 0.35 → 2.26 ms     |
|             | `spend_request`           | Client    | 17383 → 8406 B    | 1.39 → 10.2 ms     |
|             | `spend_response`          | Issuer    | 127 B             | 0.83 → 6.75 ms     |

The key length of each instance is the smallest for which solving its MQ system
is *estimated* to cost 2^128 ([`tools/mq_key_bits.py`](tools/mq_key_bits.py)).
That estimate is crude and needs to be checked (e.g., with CryptographicEstimators)
before relying on it, and zero knowledge then also relies on `G` being a PRG.
It also changes the proof format, which then deviates from the drafts.

## Use in a Meson project

Create `subprojects/vole-mole.wrap` in your project:

```ini
[wrap-git]
url = https://github.com/cloudflareresearch/vole-mole.git
revision = <commit>
depth = 1
```

Set `revision` to a commit hash. The API is unstable, so don't track a branch.
Meson clones the repository and its dependencies during `meson setup`. Then
add to your `meson.build`:

```meson
vole_mole_dep = subproject('vole-mole',
  default_options : ['tests=false', 'benchmarks=false', 'examples=false'],
).get_variable('vole_mole_dep')
```

## Security considerations

This code has not been audited.

The library does not prevent double spending. VOLE-IHAT `finalize_redeem` and
VOLE-ACT `spend_response` return a nullifier; before accepting the presentation,
the caller needs to ensure that it has not recorded the same nullifier in a
previous presentation. Likewise, typical applications of PomFRIT will include a
nullifier in the message that the verifier is meant to use for double spend
prevention.

## License

BSD 3-Clause, see [LICENSE](LICENSE). Meson downloads
[faest-arch-opt][arch-opt] (MIT) and [pqov][pqov] (CC0 or Apache-2.0) as
subprojects. `src/voleith.hpp` is adapted from faest-arch-opt and keeps its MIT
notice.

## Acknowledgements

This library is based on a prototype by Tianyu Zhang, written during
his Summer 2026 internship at Cloudflare Research. Tianyu also contributed to
the circuit and protocol designs.

[mole]: https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts
[pomfrit]: https://eprint.iacr.org/2026/109
[fischlin]: https://www.cryptoplexity.informatik.tu-darmstadt.de/media/crypt/publications_1/fischlinblind-sigs2006.pdf
[ihat]: https://moderation-of-unlinkable-endorsements.github.io/internet-drafts/draft-authors-mole-vole-ihat.html
[act]: https://moderation-of-unlinkable-endorsements.github.io/internet-drafts/draft-authors-mole-vole-act.html
[faest]: https://faest.info
[arch-opt]: https://github.com/faest-sign/faest-arch-opt
[pqov]: https://github.com/pqov/pqov
[meson]: https://mesonbuild.com
[uov]: https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/UOV_Specification_R3.pdf
