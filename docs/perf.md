# Performance

Measurements are for the release build on an Apple M4 Pro. Each protocol uses
a 46,591-byte UOV public key. `Party` is who runs the step, `Sends` is how many
bytes that party sends, and `Time` is the step's runtime. `N` is the number of
Anchors in the Anchor Set during Moussaka redemption.

## Default parameters

The VOLEitH proofs use the FAEST-EM-128f parameters, which favor speed over
proof size.

| Protocol    | Step                       | Party     | Sends   | Time     |
|:------------|:---------------------------|:----------|--------:|---------:|
| PomFRIT     | `issue_request`            | Client    | 45 B    | 0.26 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 0.013 ms |
|             | `finalize_issue`           | Client    | 5643 B  | 0.19 ms  |
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

## Smaller proofs

With the FAEST-EM-128s parameters, which favor size, proofs would be 23–31%
smaller, but proving and verifying would be roughly 1.3–7× slower:

| Protocol    | Step                       | Party     | Sends   | Time     |
|:------------|:---------------------------|:----------|--------:|---------:|
| PomFRIT     | `issue_request`            | Client    | 45 B    | 1.76 ms  |
|             | `issue_response`           | Issuer    | 119 B   | 0.013 ms |
|             | `finalize_issue`           | Client    | 4339 B  | 0.46 ms  |
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

Proofs can shrink further, but VOLEitH has a lower bound and returns diminish.
PomFRIT signatures can reach about 3.5 KB, but verification takes about 80 ms,
which is too slow for many applications.

## Running benchmarks

Use a release build:

```sh
meson setup build-release --buildtype=release
meson compile -C build-release
meson test -C build-release --benchmark -v
```

To pass Google Benchmark flags, such as repetitions or JSON output, run a
benchmark directly:

```sh
./build-release/tests/bench_moussaka --benchmark_repetitions=10 --benchmark_report_aggregates_only=true
```

On macOS, set `CC` and `CXX` before `meson setup`, as shown in the
[README](../README.md#build).
