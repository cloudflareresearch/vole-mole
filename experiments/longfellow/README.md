# VOLEitH vs. Longfellow: a simplified Moussaka blind signature

This experiment compares the VOLEitH proof system used by vole-mole with
[Longfellow](https://github.com/google/longfellow-zk)
([draft-google-cfrg-libzk](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)).
Both prove the same statement.

Issuance:

1. The Client commits `t = Com(nf, r)` and sends `t` to the Issuer.
2. The Issuer derives `s` such that `P(s) = t` and sends `s` to the Client.

The blind signature on `nf` is a proof of knowledge of `(r, s)` such that
`P(s) = Com(nf, r)`. `P` is the UOV public map (N = 119, M = 45, over GF(256)).
`Com` is the Moussaka commitment with both contexts set to zero, i.e., the first
45 bytes of Keccak-p[800, 12].

- VOLEitH: [`tests/blindsig/blindsig.hpp`](../../tests/blindsig/blindsig.hpp)
  is Moussaka's redemption relation without the Anchor selector. It uses the
  FAEST-EM-128f parameters.
- Longfellow: [`blindsig_circuit.h`](blindsig_circuit.h) is a circuit over
  GF(2^128). Keccak state bits are field elements. GF(256) is embedded as a
  subfield, so the UOV map is a quadratic form in 119 field elements. The
  public key is hardcoded into the circuit, and `nf` is a public input. The
  proof uses Longfellow's current Ligero parameters (rate 7, 132 queries,
  about 109 bits of statistical security).

The two implementations use the same key, nullifier, opening, and preimage,
which vole-mole's `gen_blindsig_vectors` writes out.

## Results

Apple M1 Pro, single thread, release builds, Homebrew Clang 22. Times are
medians of 5 repetitions.

| System                                 | Proof    | Prove   | Verify  |
|:---------------------------------------|---------:|--------:|--------:|
| vole-mole (VOLEitH, FAEST-EM-128f)     | 8,615 B  | 1.03 ms | 0.66 ms |
| Longfellow (no intermediate states)    | ~80.7 KB | 9.75 ms | 3.46 ms |
| Longfellow (states after rounds 4, 8)  | ~75.9 KB | 9.76 ms | 3.46 ms |
| Longfellow (states after rounds 3,6,9) | ~75.5 KB | 10.0 ms | 3.45 ms |

The Longfellow proof size varies by a few hundred bytes between runs, because
the number of Merkle digests depends on which columns are opened.

Notes:

- Longfellow's proof is mostly the Ligero opening (about 71 KB: 132 columns
  plus Merkle paths). Sumcheck adds 4–10 KB. Most opened rows are blinding,
  quadratic-check, or sumcheck-pad rows, which are full-field (16 bytes per
  element). Only the bit witnesses are compressed to 2-byte subfield
  elements.
- The prover spends about two thirds of its time in sumcheck and one third
  in the Ligero commitment. The circuit has about 600k quadratic terms,
  split roughly evenly between Keccak-p[800, 12] (about 285k) and the dense
  UOV map (about 330k, i.e., 45 × 7140 coefficients). In VOLEitH, the 45
  components are collapsed by a random linear combination that is chosen
  after the witness is committed, so the map costs one quadratic form. A
  Longfellow circuit is fixed in advance, so it can't do this.
- The Longfellow circuit depends on the issuer's public key. Compiling it
  takes about 21 s per key, and the verifier needs the same circuit.
  vole-mole takes the key at runtime.
- The security levels differ: FAEST-EM-128f targets 128 bits, and
  Longfellow's Ligero parameters give about 109 bits of statistical
  security.

## Running

Build vole-mole with benchmarks (see the top-level README), then:

```sh
./build-release/tests/bench_blindsig
./build-release/tests/gen_blindsig_vectors > experiments/longfellow/vector.txt
```

Clone Longfellow and install its dependencies (on macOS:
`brew install googletest google-benchmark zstd openssl@3`). Then, from this
directory:

```sh
cmake -S . -B build -D CMAKE_BUILD_TYPE=Release -D LONGFELLOW_DIR=/path/to/longfellow-zk
cmake --build build -j --target longfellow_blindsig
./build/longfellow_blindsig vector.txt --benchmark_repetitions=5 --benchmark_report_aggregates_only=true
```

Before benchmarking, the Longfellow harness checks that:

- `P(s) = t` in GF(256), using the exported key.
- The proof verifies after serialization.
- The proof doesn't verify for a different `nf`.
- The prover refuses a wrong preimage. This step logs `V->v_[i] != F.zero()`
  once per circuit, which is expected.

Results above used longfellow-zk at commit `b4f7dd9`.
