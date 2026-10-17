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

Alternatively, `LocalPrg<1>` derives the witness with Goldreich's local PRG with
the predicate XOR₁₆-AND₂ ([`src/mq/local.hpp`](src/mq/local.hpp)): each output
bit is the sum of 16 key bits plus the product of 2 more, at public
pseudorandom positions. It's much cheaper to evaluate than the MQ PRG, but
needs a longer key. For Moussaka (Apple M4 Pro):

| Step                      | Sends (MQ, `c = 2` → local) | Time (MQ, `c = 2` → local) |
|:--------------------------|----------------------------:|---------------------------:|
| `issue_request`           | 4804 → 5212 B               | 3.65 → 1.05 ms             |
| `issue_response`          | —                           | 2.38 → 0.34 ms             |
| `redeem_request` (N = 1)  | 5006 → 5499 B               | 5.62 → 1.28 ms             |
| `finalize_redeem` (N = 1) | —                           | 4.16 → 0.48 ms             |

Local PRGs are a different and less studied assumption than dense MQ, and the
key length (704 bits for 2048 outputs, from
[`tools/local_key_bits.py`](tools/local_key_bits.py)) only accounts for a
guess-and-determine attack and the dense MQ estimate. It has *not* been checked
against the literature on attacks on local PRGs (e.g., Couteau et al.,
Asiacrypt 2018; Ünal, Eurocrypt 2023), so it's experimental, and no protocol
uses it by default.

## Proof of knowledge of an ECDSA signature

`vole_mole/ecdsa_pok.hpp` is an experimental proof of knowledge of an
ECDSA-P256-SHA256 signature on a hidden message. The public key, the message
length (at most 119 bytes) and a context string are public; the message and
signature stay hidden. It combines two VOLEitH proofs:

- a binary proof (FAEST-EM-128 parameters) of SHA-256 on the padded message,
  of `X < p` for the x-coordinate `X` of `R`, and of two masked integer
  linear combinations of the hash `e` and `X`. By default, its witness is
  derived from a short key with the (experimental) local PRG, see
  [above](#deriving-the-witness-with-a-prg);
- a prime-field proof over F_p and F_n, which proves that `R = u1 G + u2 Q`
  using two interleaved radix-16 fixed-base combs on precomputed tables of `G`
  and `Q` (only the slopes are committed), with constraints of degree 16. It also proves `u1 X = u2 e` and `u2 X != 0` over F_n (so
  `r = X mod n`), and that the digits of `u1` and `u2` match their values over
  F_n. With the local PRG, its F_p witness (260 elements) is also derived from
  a key of 124 elements, with an (experimental) local quadratic PRG over F_p
  ([`src/voleith_p256/prg.hpp`](src/voleith_p256/prg.hpp)), which doubles the
  QuickSilver degree.

The same masked linear combinations, with a challenge derived after both
proofs commit, tie `e` and `X` across the two proofs. See
`src/ecdsa_pok/relation.hpp` for the full relation and soundness argument.

| Parameters | Message   | Proof     | Prove   | Verify  |
|:-----------|:----------|----------:|--------:|--------:|
| fast       | ≤ 55 B    | 108627 B  | 10.3 ms | 5.8 ms  |
| fast       | 56–119 B  | 110739 B  | 11.0 ms | 6.0 ms  |
| medium     | ≤ 55 B    | 91949 B   | 18.0 ms | 13.5 ms |
| medium     | 56–119 B  | 94061 B   | 18.7 ms | 13.7 ms |
| small      | ≤ 55 B    | 79783 B   | 46.2 ms | 41.7 ms |
| small      | 56–119 B  | 81781 B   | 49.8 ms | 41.9 ms |

Without deriving the witnesses (`WitnessPrg::none`), proofs are
202276 B (fast), 174078 B (medium) and 138788 B (small) for messages of up to
55 bytes, and proving takes up to 50% longer. With the MQ PRG (`WitnessPrg::mq`),
only the binary witness is derived: proofs are 162512 B (fast), 134314 B
(medium) and 114198 B (small), and proving takes about 0.45 s. The times include
computing the comb tables of the public key (0.4 ms; the tables of `G` are
computed once), which prover and verifier both do. Measured with Apple clang 21,
release build.

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
