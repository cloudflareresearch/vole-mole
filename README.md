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
| PomFRIT     | You need a blind signature: the issuer signs a message it never sees.          | `vole_mole/pomfrit.hpp`     |
| Moussaka    | A verifier trusts several issuers and must not learn which one issued a token. | `vole_mole/moussaka.hpp`    |
| Ratatouille | A token carries a hidden credit balance that the issuer updates on each spend. | `vole_mole/ratatouille.hpp` |

PomFRIT implements Algorithm 2 of [ePrint 2026/109][pomfrit], a
[Fischlin][fischlin]-style blind signature. Moussaka is an Issuer-Hiding
Anonymous Token ([draft-authors-mole-vole-ihat][mous]). Ratatouille is an
Anonymous Credit Token ([draft-authors-mole-vole-act][rata]). Moussaka and
Ratatouille were designed for [MOLE][mole], but do not depend on it.

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
const uov::PublicKey pk(sk.public_key());

// Client: blind the message. The Issuer never sees msg.
auto [pending, request] = pomfrit::issue_request(pk, msg);

// Issuer: sign the blinded request.
const auto response = pomfrit::issue_response(sk, request);

// Client: unblind. Returns std::nullopt if the response is invalid.
const auto sig = std::move(pending).finalize_issue(pk, response);
if (!sig) return EXIT_FAILURE;

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
| [`moussaka.cpp`](examples/moussaka.cpp)        | Issuance from one of several Anchors and redemption, with replay rejection |
| [`ratatouille.cpp`](examples/ratatouille.cpp)  | Issuance, spending credits, and double-spend rejection        |

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

The library does not prevent double spending. Moussaka `finalize_redeem` and
Ratatouille `spend_response` return a nullifier for each accepted token. Store
it and reject any request that reuses it, for as long as you accept tokens for
those contexts. For Moussaka, one record must cover every Anchor Set you accept,
since a token is valid under any set that contains its Anchor. Expiring
contexts, such as an issuance epoch, bound the storage. PomFRIT has no built-in
nullifier; to make signatures single-use, put one in the signed message.

## Performance

Client messages carrying proofs are 5–17 KB. On an Apple M4 Pro, every step
takes under 2 ms, except Moussaka redemption, which grows with the number of
Anchors (about 7 ms for 64). See [docs/perf.md](docs/perf.md) for full numbers, the smaller-proof
parameter trade-off (4-12KB), and how to run the benchmarks.

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

Like τ, this is a VOLEitH parameter of each relation: its witness PRG
([`src/witness_prg.hpp`](src/witness_prg.hpp): `MqPrg<c>`, or `NoPrg` to commit
to the witness directly) next to its parameter set, e.g., `IssueWitnessPrg` in
[`src/moussaka/issue.hpp`](src/moussaka/issue.hpp).
Changing it changes the proof size, so the size in the public header has to be
updated, too. By default, none of the protocols derives its witnesses. Deriving
them makes the proofs 29–52% smaller, but proving and verifying several
milliseconds slower (Apple M4 Pro, `c = 2` except for `spend_request`, which has
a much longer witness and uses `c = 8`):

| Protocol    | Step                      | Party     | Sends (off → on)  | Time (off → on)    |
|:------------|:--------------------------|:----------|------------------:|-------------------:|
| PomFRIT     | `issue_request`           | Client    | 45 B              | 0.26 → 1.53 ms     |
|             | `finalize_issue`          | Client    | 5387 → 3825 B     | 0.19 → 0.22 ms     |
|             | `verify`                  | Verifier  | —                 | 0.38 → 1.39 ms     |
| Moussaka    | `issue_request`           | Client    | 7317 → 4804 B     | 0.60 → 3.65 ms     |
|             | `issue_response`          | Anchor    | 119 B             | 0.36 → 2.38 ms     |
|             | `redeem_request` (N = 1)  | Client    | 8775 → 5006 B     | 0.77 → 5.62 ms     |
|             | `finalize_redeem` (N = 1) | Moderator | —                 | 0.51 → 4.16 ms     |
| Ratatouille | `issue_request`           | Client    | 7032 → 4775 B     | 0.58 → 3.40 ms     |
|             | `issue_response`          | Issuer    | 119 B             | 0.35 → 2.26 ms     |
|             | `spend_request`           | Client    | 17383 → 8406 B    | 1.39 → 10.2 ms     |
|             | `spend_response`          | Issuer    | 127 B             | 0.83 → 6.75 ms     |

The key length of each instance is the smallest for which solving its MQ system
is *estimated* to cost 2^128 ([`tools/mq_key_bits.py`](tools/mq_key_bits.py)).
That estimate is crude and needs to be checked (e.g., with CryptographicEstimators)
before relying on it, and zero knowledge then also relies on `G` being a PRG.
It also changes the proof format, which then deviates from the drafts.

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
[mous]: https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts/blob/main/draft-authors-mole-vole-ihat.md
[rata]: https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts/blob/main/draft-authors-mole-vole-act.md
[faest]: https://faest.info
[arch-opt]: https://github.com/faest-sign/faest-arch-opt
[pqov]: https://github.com/pqov/pqov
[meson]: https://mesonbuild.com
[uov]: https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/UOV_Specification_R3.pdf
