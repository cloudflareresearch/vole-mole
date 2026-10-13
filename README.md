# vole-mole

> WARNING: This code is still fairly experimental and is subject to breaking
> changes as the specifications evolve.

Implementation of various post-quantum anonymous tokens, all built
on the [UOV][uov] signature scheme and the VOLE-in-the-Head (VOLEitH) proof
system of [FAEST][faest]:

1. PomFRIT ([ePrint 2026/109][pomfrit], Algorithm 2), a
   [Fischlin][fischlin]-style blind signature. The issuer signs a commitment,
   then the client produces a proof of knowledge of the signature and the
   opening of the commitment. This proof constitutes the blind signature.

2. Moussaka ([draft-authors-mole-vole-ihat][mous]), an Issuer-Hiding Anonymous
   Token (IHAT). Similar to the blind signature, except the client proves
   knowledge of a signature produced by _some_ issuer without revealing which.

3. Ratatouille ([draft-authors-mole-vole-act][rata]), an Anonymous Credit Token
   (ACT). Here the token encodes a small amount of client-secret state, which
   the issuer updates when the token is spent.

Moussaka and Ratatouille were designed for [MOLE][mole].

The table below summarizes the performance of each protocol, including the
runtime and communication cost for each step. The `Party` column indicates which
party performs the operation; the `Sends` column indicates the number of bytes
sent by the party; and the `Time` column indicates the runtime of the operation.
`N` indicates the number of Anchors in the Anchor Set for IHAT redemption. Each
protocol uses a 46591 B (byte) UOV public key.

| Protocol    | Step                       | Party     | Sends   | Time     |
|:------------|:---------------------------|:----------|--------:|---------:|
| PomFRIT     | `issue_request`            | Client    | 45 B    | 0.26 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 0.013 ms |
|             | `finalize_issue`           | Client    | 5387 B  | 0.19 ms  |
|             | `verify`                   | Verifier  | —       | 0.37 ms  |
| Moussaka    | `issue_request`            | Client    | 7317 B  | 0.60 ms  |
|             | `issue_response`           | Anchor    | 119 B   | 0.36 ms  |
|             | `finalize_issue`           | Client    | —       | 0.008 ms |
|             | `redeem_request` (N = 1)   | Client    | 8775 B  | 0.77 ms  |
|             | `redeem_request` (N = 8)   | Client    | 8775 B  | 1.44 ms  |
|             | `redeem_request` (N = 64)  | Client    | 8775 B  | 6.87 ms  |
|             | `finalize_redeem` (N = 1)  | Moderator | —       | 0.51 ms  |
|             | `finalize_redeem` (N = 8)  | Moderator | —       | 1.19 ms  |
|             | `finalize_redeem` (N = 64) | Moderator | —       | 6.55 ms  |
| Ratatouille | `issue_request`            | Client    | 7032 B  | 0.58 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 0.35 ms  |
|             | `finalize_issue`           | Client    | —       | 0.008 ms |
|             | `spend_request`            | Client    | 17383 B | 1.45 ms  |
|             | `spend_response`           | Issuer    | 127 B   | 0.84 ms  |
|             | `finalize_spend`           | Client    | —       | 0.008 ms |

We use the VOLEitH implementation from [faest-arch-opt][arch-opt] and the UOV
implementation from [pqov][pqov]. Measurements were taken for the release build
running on an Apple M4 Pro.

## Proof of knowledge of an ECDSA signature

`vole_mole/ecdsa_pok.hpp` is an experimental proof of knowledge of an
ECDSA-P256-SHA256 signature on a hidden message. The public key, the message
length (at most 119 bytes) and a context string are public; the message and
signature stay hidden. It combines two VOLEitH proofs:

- a binary proof (FAEST-EM-128 parameters) of SHA-256 on the padded message,
  of `X < p` for the x-coordinate `X` of `R`, and of two masked integer
  linear combinations of the hash `e` and `X`;
- a prime-field proof over F_p and F_n, which proves that `R = u1 G + u2 Q`
  using a radix-16 fixed-base comb on precomputed tables (only the slopes are
  committed). It also proves `u1 X = u2 e` and `u2 X != 0` over F_n (so
  `r = X mod n`), and that the digits of `u1` and `u2` match their values over
  F_n.

The same masked linear combinations, with a challenge derived after both
proofs commit, tie `e` and `X` across the two proofs. See
`src/ecdsa_pok/relation.hpp` for the full relation and soundness argument.

| Parameters | Message   | Proof     | Prove   | Verify  |
|:-----------|:----------|----------:|--------:|--------:|
| fast       | ≤ 55 B    | 192505 B  | 41.5 ms | 19.7 ms |
| fast       | 56–119 B  | 238388 B  | 46.4 ms | 21.7 ms |
| small      | ≤ 55 B    | 131451 B  | 156 ms  | 131 ms  |
| small      | 56–119 B  | 161140 B  | 163 ms  | 136 ms  |

Computing the comb tables for a public key takes another 5 ms. Prover and
verifier both do this.

## Building

Requirements: [Meson][meson] >= 1.4, Ninja, Python 3, and a compiler with good
C++23 support (faest-arch-opt is tested with Clang >= 21 or GCC >= 16; Apple
Clang 17 is too old). On macOS with Homebrew:

```sh
brew install meson ninja llvm@22
CC=$(brew --prefix llvm@22)/bin/clang CXX=$(brew --prefix llvm@22)/bin/clang++ meson setup build
meson compile -C build
meson test -C build --print-errorlogs
./build/tests/test_pomfrit  # verbose test output
./build/tests/test_moussaka
./build/tests/test_ratatouille
./build/examples/example_keys  # run examples
./build/examples/example_pomfrit
./build/examples/example_moussaka
./build/examples/example_ratatouille
```

Benchmarks should be run in the release build:

```sh
CC=$(brew --prefix llvm@22)/bin/clang CXX=$(brew --prefix llvm@22)/bin/clang++ meson setup build-release --buildtype=release
meson test -C build-release --benchmark -v
# or, to pass Google Benchmark flags (e.g., repetitions, JSON output):
./build-release/tests/bench_moussaka --benchmark_repetitions=10 --benchmark_report_aggregates_only=true
```

## Reducing communication cost

The VOLEitH proofs in our protocols use the same parameters as FAEST-EM-128f.
These parameters optimize for speed, at the cost of larger proofs. Using the
FAEST-EM-128s parameters, which optimize for size, our proofs would be 22–31%
smaller, but proving and verifying would be roughly 1.3–7× slower:

| Protocol    | Step                       | Party     | Sends   | Time     |
|:------------|:---------------------------|:----------|--------:|---------:|
| PomFRIT     | `issue_request`            | Client    | 45 B    | 1.76 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 0.013 ms |
|             | `finalize_issue`           | Client    | 4179 B  | 0.46 ms  |
|             | `verify`                   | Verifier  | —       | 1.95 ms  |
| Moussaka    | `issue_request`            | Client    | 5557 B  | 2.47 ms  |
|             | `issue_response`           | Anchor    | 119 B   | 2.02 ms  |
|             | `finalize_issue`           | Client    | —       | 0.008 ms |
|             | `redeem_request` (N = 1)   | Client    | 6493 B  | 2.73 ms  |
|             | `redeem_request` (N = 8)   | Client    | 6493 B  | 3.45 ms  |
|             | `redeem_request` (N = 64)  | Client    | 6493 B  | 8.91 ms  |
|             | `finalize_redeem` (N = 1)  | Moderator | —       | 2.27 ms  |
|             | `finalize_redeem` (N = 8)  | Moderator | —       | 2.96 ms  |
|             | `finalize_redeem` (N = 64) | Moderator | —       | 8.33 ms  |
| Ratatouille | `issue_request`            | Client    | 5368 B  | 2.43 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 2.01 ms  |
|             | `finalize_issue`           | Client    | —       | 0.008 ms |
|             | `spend_request`            | Client    | 12077 B | 4.04 ms  |
|             | `spend_response`           | Issuer    | 127 B   | 3.20 ms  |
|             | `finalize_spend`           | Client    | —       | 0.008 ms |

In fact, the proof size can be driven down even further, but VOLEitH imposes a
lower limit, and we start to see diminishing returns the more we optimize. For
example, we can get PomFRIT signatures down to ~3.5KB, but the high verification
time (~80ms) would make the scheme impractical for many use cases.

## License

BSD 3-Clause, see [LICENSE](LICENSE). [faest-arch-opt][arch-opt], which is
downloaded as a subproject, is MIT-licensed. `src/voleith.hpp` is adapted from
faest-arch-opt and includes its MIT notice. [pqov][pqov], also downloaded as a
subproject, is licensed under CC0 or Apache-2.0.

## Acknowledgements

This work is based on a prototype written by Tianyu Zhang during his
internship at Cloudflare Research (Summer 2026). Tianyu also contributed to the
circuit design and the overall design of the protocols.

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
