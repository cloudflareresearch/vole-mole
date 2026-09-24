# vole-mole

Implementation of the post-quantum candidates for [MoLE][mole] crypto:

1. Moussaka ([draft-authors-mole-vole-ihat][draft]), a plausibly post-quantum
   variant of the Issuer-Hiding Anonymous Token protocol built on UOV and the
   VOLE-in-the-Head (VOLEitH) proof system of [FAEST][faest].

The VOLEitH machinery comes from [faest-arch-opt][arch-opt].

## Building

Requirements: [Meson][meson] >= 1.4, Ninja, Python 3, and a compiler with good
C++23 support (faest-arch-opt is tested with Clang >= 22 or GCC >= 16; Apple
Clang 17 is too old). On macOS with Homebrew:

```sh
brew install meson ninja llvm@22
CC=$(brew --prefix llvm@22)/bin/clang CXX=$(brew --prefix llvm@22)/bin/clang++ meson setup build
meson compile -C build
meson test -C build            # add --print-errorlogs to see failures
./build/tests/test_moussaka    # verbose test output
```

Benchmarks should be run in the release build:

```sh
CC=$(brew --prefix llvm@22)/bin/clang CXX=$(brew --prefix llvm@22)/bin/clang++ meson setup build-release --buildtype=release
meson test -C build-release --benchmark -v
# or, to pass Google Benchmark flags (e.g., repetitions, JSON output):
./build-release/tests/bench_moussaka --benchmark_repetitions=10 --benchmark_report_aggregates_only=true
```

## License

BSD 3-Clause, see [LICENSE](LICENSE). faest-arch-opt, which is downloaded as a
subproject, is MIT-licensed. `src/voleith.hpp` is adapted from faest-arch-opt
and includes its MIT notice.

## Acknowledgements

This work is based on a prototype written by Tianyu Zhang during his
internship at Cloudflare Research (Summer 2026). Tianyu also contributed to the
circuit design and the overall design of the protocols.

[mole]: https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts
[draft]: https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts/blob/main/draft-authors-mole-vole-ihat.md
[faest]: https://faest.info
[arch-opt]: https://github.com/faest-sign/faest-arch-opt
[meson]: https://mesonbuild.com
