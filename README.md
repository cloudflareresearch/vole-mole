# vole-mole

C++23 library for post-quantum anonymous tokens. A client gets a token from an
issuer, then presents it later without the issuer linking the two steps.

All protocols use [UOV][uov] signatures and the VOLE-in-the-Head (VOLEitH)
proof system from [FAEST][faest].

> [!WARNING]
> Experimental and not audited. Do not use in production. APIs and wire formats
> will change as the specifications evolve.

## Protocols

| Protocol    | Use it when                                                                    | Header                     |
|:------------|:-------------------------------------------------------------------------------|:---------------------------|
| PomFRIT     | You need a blind signature: the issuer signs a message it never sees.          | `vole_mole/pomfrit.hpp`    |
| VOLE-IHAT   | A verifier trusts several issuers and must not learn which one issued a token. | `vole_mole/ihat.hpp`       |
| VOLE-ACT    | A token carries a hidden credit balance that the issuer updates on each spend. | `vole_mole/act.hpp`        |

PomFRIT implements Algorithm 2 of [ePrint 2026/109][pomfrit], a
[Fischlin][fischlin]-style blind signature. VOLE-IHAT is an Issuer-Hiding
Anonymous Token ([draft-authors-mole-vole-ihat][ihat]). VOLE-ACT is an
Anonymous Credit Token ([draft-authors-mole-vole-act][act]). VOLE-IHAT and
VOLE-ACT were designed for [MOLE][mole], but do not depend on it.

## Build

You need [Meson][meson] 1.4 or later, Ninja, Python 3, and Clang 21+ or GCC 16+.
Apple Clang 17 is too old. Meson downloads the other dependencies.

Supported CPUs are aarch64 with the crypto extensions and x86_64. On x86_64 the
build uses `-march=native`, so binaries may not run on other machines.

```sh
meson setup build
meson compile -C build
meson test -C build --print-errorlogs
```

On macOS, install a recent LLVM with Homebrew and select it before setup:

```sh
brew install meson ninja llvm@22
export CC=$(brew --prefix llvm@22)/bin/clang
export CXX=$(brew --prefix llvm@22)/bin/clang++
```

## Quick start

Issue and verify a PomFRIT blind signature:

```cpp
#include <vole_mole/pomfrit.hpp>
#include <vole_mole/uov.hpp>

using namespace vole_mole;

// Issuer: generate a key pair once and publish pk.
const uov::SecretKey sk(uov::generate_secret_key_bytes());
const uov::PublicKey pk(sk.public_key_bytes());

// Client: blind the message. The Issuer never sees msg.
auto [pending, request] = pomfrit::issue_request(pk, msg);

// Issuer: sign the blinded request.
const auto response = pomfrit::issue_response(sk, request);

// Client: unblind. Returns std::nullopt if the response is invalid.
const auto sig = std::move(pending).finalize_issue(pk, response);
if (!sig) {
    return EXIT_FAILURE;
}

// Verifier: check the signature. It cannot be linked to the issuance.
const bool ok = pomfrit::verify(pk, msg, *sig);
```

`msg` is a `std::span<const uint8_t>`. Each public header documents its
functions, including what they return and throw.

## Examples

| Example                                        | Shows                                                         |
|:-----------------------------------------------|:--------------------------------------------------------------|
| [`keys.cpp`](examples/keys.cpp)                | UOV key generation, encoding, and expansion                   |
| [`pomfrit.cpp`](examples/pomfrit.cpp)          | Blind signature issuance and verification                     |
| [`ihat.cpp`](examples/ihat.cpp)                | Issuance from one of several Anchors and redemption, with replay rejection |
| [`unbound_ihat.cpp`](examples/unbound_ihat.cpp) | VOLE-IHAT with late binding of the redemption context |
| [`act.cpp`](examples/act.cpp)                  | Issuance, spending credits, and double-spend rejection        |

Build as above, then run:

```sh
./build/examples/example_pomfrit
```

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

There is no installed package or pkg-config file yet.

## Security considerations

This code has not been audited.

The library does not prevent double spending. VOLE-IHAT `finalize_redeem` and
VOLE-ACT `spend_response` return a nullifier for each accepted token. Store
it and reject any request that reuses it, for as long as you accept tokens for
those contexts. For VOLE-IHAT, one record must cover every Anchor Set you accept,
since a token is valid under any set that contains its Anchor. Expiring
contexts, such as an issuance epoch, bound the storage. PomFRIT has no built-in
nullifier; to make signatures single-use, put one in the signed message.

## Performance

Client messages carrying proofs are 5–17 KB. On an Apple M4 Pro, every step
takes under 2 ms, except VOLE-IHAT redemption, which grows with the number of
Anchors (about 7 ms for 64). See [docs/perf.md](docs/perf.md) for full numbers, the smaller-proof
parameter trade-off (4-12KB), and how to run the benchmarks.

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
