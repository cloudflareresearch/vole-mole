// Benchmark of the blind signature relation (see blindsig_circuit.h) in
// Longfellow.
//
// Usage: longfellow_blindsig [VECTOR] [benchmark flags]
//
// VECTOR is the output of vole-mole's gen_blindsig_vectors (default:
// vector.txt).

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <memory>
#include <string>
#include <vector>

#include "arrays/dense.h"
#include "benchmark/benchmark.h"
#include "blindsig_circuit.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/panic.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace {

using namespace proofs;
using blindsig::M;
using blindsig::N;
using blindsig::ROUNDS;
using blindsig::Slicing;

using Field = GF2_128<>;
using Elt = Field::Elt;
using RSFactory = LCH14ReedSolomonFactory<Field>;
using CompilerBackendF = CompilerBackend<Field>;
using LogicCircuit = Logic<Field, CompilerBackendF>;

// Longfellow's current Ligero parameters (version 7 of the mdoc circuits; about
// 109 bits of statistical security).
constexpr size_t kRate = 7;
constexpr size_t kNreq = 132;

const Field F;
const RSFactory RSF(F);

struct Vector {
  std::vector<uint8_t> nf, r, s, t, pk;
  std::vector<std::vector<uint8_t>>
      states;  // states[k]: the state after k rounds
};

std::vector<uint8_t> hex_decode(const std::string& hex) {
  check(hex.size() % 2 == 0, "odd-length hex");
  std::vector<uint8_t> out(hex.size() / 2);
  for (size_t i = 0; i < out.size(); ++i) {
    out[i] =
        static_cast<uint8_t>(std::stoul(hex.substr(2 * i, 2), nullptr, 16));
  }
  return out;
}

Vector read_vector(const std::string& path) {
  std::ifstream in(path);
  check(in.good(),
        "cannot open the test vector; run vole-mole's gen_blindsig_vectors");
  Vector v;
  v.states.resize(ROUNDS + 1);
  std::string label, hex;
  while (in >> label >> hex) {
    auto bytes = hex_decode(hex);
    if (label == "nf")
      v.nf = bytes;
    else if (label == "r")
      v.r = bytes;
    else if (label == "s")
      v.s = bytes;
    else if (label == "t")
      v.t = bytes;
    else if (label == "pk")
      v.pk = bytes;
    else if (label.rfind("state", 0) == 0)
      v.states[std::stoul(label.substr(5))] = bytes;
  }
  check(v.nf.size() == blindsig::NF_BYTES && v.r.size() == blindsig::R_BYTES &&
            v.s.size() == N && v.t.size() == M &&
            v.pk.size() == blindsig::MONOMIALS * M,
        "malformed test vector");
  for (const auto& st : v.states)
    check(st.size() == blindsig::STATE_BYTES, "malformed state");
  return v;
}

uint8_t gf256_mul(uint8_t a, uint8_t b) {
  uint8_t p = 0;
  for (int i = 0; i < 8; ++i) {
    if (b & 1) p ^= a;
    const bool hi = a & 0x80;
    a = static_cast<uint8_t>(a << 1);
    if (hi) a ^= 0x1b;
    b >>= 1;
  }
  return p;
}

// Check that P(s) = t in GF(256), which validates the public key layout and the
// field.
void check_public_map(const Vector& v) {
  std::vector<uint8_t> p(M, 0);
  size_t m = 0;
  for (size_t i = 0; i < N; ++i) {
    for (size_t j = i; j < N; ++j, ++m) {
      const uint8_t sij = gf256_mul(v.s[i], v.s[j]);
      for (size_t k = 0; k < M; ++k) p[k] ^= gf256_mul(v.pk[m * M + k], sij);
    }
  }
  check(p == v.t, "P(s) != t");
}

// A root alpha of the AES polynomial X^8 + X^4 + X^3 + X + 1 in GF(2^128), and
// its powers.
std::array<Elt, 8> aes_root_powers() {
  const auto pow2k = [](Elt a, size_t k) {
    for (size_t i = 0; i < k; ++i) a = F.mulf(a, a);
    return a;
  };
  const auto pow = [](Elt a, size_t e) {
    Elt r = F.one();
    for (; e; e >>= 1, a = F.mulf(a, a)) {
      if (e & 1) r = F.mulf(r, a);
    }
    return r;
  };
  for (uint64_t h = 2;; ++h) {
    // c = h^((2^128 - 1) / 255) = prod_i h^(2^(8i)) lies in GF(256)^*.
    Elt c = F.one();
    Elt hi = F.of_scalar_field(h);
    for (size_t i = 0; i < 16; ++i, hi = pow2k(hi, 8)) c = F.mulf(c, hi);
    if (pow(c, 255) != F.one()) continue;  // sanity
    if (pow(c, 85) == F.one() || pow(c, 51) == F.one() || pow(c, 15) == F.one())
      continue;
    // c generates GF(256)^*; find a root of the AES polynomial among its
    // powers.
    Elt a = c;
    for (size_t k = 1; k < 255; ++k, a = F.mulf(a, c)) {
      Elt y = F.addf(F.addf(pow(a, 8), pow(a, 4)),
                     F.addf(pow(a, 3), F.addf(a, F.one())));
      if (y == F.zero()) {
        std::array<Elt, 8> out;
        out[0] = F.one();
        for (size_t j = 1; j < 8; ++j) out[j] = F.mulf(out[j - 1], a);
        return out;
      }
    }
    check(false, "no root of the AES polynomial");
  }
}

struct Compiled {
  std::unique_ptr<Circuit<Field>> circuit;
  double compile_ms;
  size_t depth, nwires, nquad_terms, ninputs;
};

Compiled compile(const Vector& v, const Slicing& slicing) {
  const auto start = std::chrono::steady_clock::now();
  QuadCircuit<Field> q(F);
  const CompilerBackendF cbk(&q);
  const LogicCircuit lc(&cbk, F);
  blindsig::Circuit<LogicCircuit> bc(lc, F, aes_root_powers(), v.pk);
  typename blindsig::Circuit<LogicCircuit>::Inputs in;
  bc.input(q, in, slicing);
  bc.assert_valid(in, slicing);
  auto circuit = q.mkcircuit(/*nc=*/1);
  const auto end = std::chrono::steady_clock::now();
  return {std::move(circuit),
          std::chrono::duration<double, std::milli>(end - start).count(),
          q.depth_,
          q.nwires_,
          q.nquad_terms_,
          q.ninput()};
}

void push_bytes(DenseFiller<Field>& filler, const std::vector<uint8_t>& bytes) {
  for (uint8_t b : bytes) {
    for (size_t j = 0; j < 8; ++j)
      filler.push_back((b >> j) & 1 ? F.one() : F.zero());
  }
}

std::unique_ptr<Dense<Field>> witness(const Circuit<Field>& c, const Vector& v,
                                      const Slicing& slicing) {
  auto w = std::make_unique<Dense<Field>>(1, c.ninputs);
  DenseFiller<Field> filler(*w);
  filler.push_back(F.one());
  push_bytes(filler, v.nf);
  push_bytes(filler, v.r);
  push_bytes(filler, v.s);
  for (size_t i = 0; i < ROUNDS; ++i) {
    if (slicing[i]) push_bytes(filler, v.states[i + 1]);
  }
  check(filler.size() == c.ninputs, "witness size mismatch");
  return w;
}

std::unique_ptr<Dense<Field>> public_inputs(const Circuit<Field>& c,
                                            const Vector& v) {
  auto pub = std::make_unique<Dense<Field>>(1, c.npub_in);
  DenseFiller<Field> filler(*pub);
  filler.push_back(F.one());
  push_bytes(filler, v.nf);
  check(filler.size() == c.npub_in, "public input size mismatch");
  return pub;
}

constexpr uint8_t kTranscriptInit[] = "vole-mole blindsig";
constexpr size_t kTranscriptVersion = 7;

// Returns the serialized proof, or an empty vector if proving fails.
std::vector<uint8_t> prove(const Circuit<Field>& c, const Dense<Field>& w) {
  SecureRandomEngine rng;
  ZkProof<Field> zkpr(c, kRate, kNreq);
  ZkProver<Field, RSFactory> prover(c, F, RSF);
  Transcript tp(kTranscriptInit, sizeof(kTranscriptInit), kTranscriptVersion);
  prover.commit(zkpr, w, tp, rng);
  if (!prover.prove(zkpr, w, tp)) return {};
  std::vector<uint8_t> buf;
  zkpr.write(buf, F);
  return buf;
}

bool verify(const Circuit<Field>& c, const Dense<Field>& pub,
            const std::vector<uint8_t>& proof) {
  ZkProof<Field> zkpv(c, kRate, kNreq);
  ReadBuffer rb(proof);
  if (!zkpv.read(rb, F) || rb.remaining() != 0) return false;
  ZkVerifier<Field, RSFactory> verifier(c, RSF, kRate, kNreq, F);
  Transcript tv(kTranscriptInit, sizeof(kTranscriptInit), kTranscriptVersion);
  verifier.recv_commitment(zkpv, tv);
  return verifier.verify(zkpv, pub, tv);
}

std::string slicing_name(const Slicing& slicing) {
  std::string name;
  for (size_t i = 0; i < ROUNDS; ++i) {
    if (slicing[i]) name += (name.empty() ? "" : ",") + std::to_string(i + 1);
  }
  return name.empty() ? "none" : name;
}

Slicing slice_every(size_t period) {
  Slicing s{};
  if (period == 0) return s;
  for (size_t i = period - 1; i + 1 < ROUNDS; i += period) s[i] = true;
  return s;
}

}  // namespace

int main(int argc, char** argv) {
  std::string path = "vector.txt";
  if (argc > 1 && argv[1][0] != '-') {
    path = argv[1];
    --argc;
    ++argv;
  }
  set_log_level(ERROR);
  static const Vector v = read_vector(path);
  check_public_map(v);

  // States committed after rounds k, 2k, ... (excluding the output) for each
  // period k.
  for (size_t period : {0, 6, 4, 3, 2}) {
    const Slicing slicing = slice_every(period);
    auto compiled = std::make_shared<Compiled>(compile(v, slicing));
    const Circuit<Field>& c = *compiled->circuit;
    std::shared_ptr<Dense<Field>> w = witness(c, v, slicing);
    std::shared_ptr<Dense<Field>> pub = public_inputs(c, v);

    // Log the composition of the proof (sumcheck and Ligero).
    set_log_level(INFO);
    const auto proof = prove(c, *w);
    set_log_level(ERROR);
    check(!proof.empty(), "proving failed");
    check(verify(c, *pub, proof), "proof failed to verify");

    // A proof for a different nullifier must not verify.
    Vector other = v;
    other.nf[0] ^= 1;
    check(!verify(c, *public_inputs(c, other), proof),
          "proof verified for the wrong nf");

    // A witness with a bad preimage must not be provable.
    other = v;
    other.s[0] ^= 1;
    check(prove(c, *witness(c, other, slicing)).empty(),
          "proved a false statement");

    std::printf(
        "slices after rounds {%s}: depth %zu, %zu wires, %zu quad terms, %zu "
        "inputs "
        "(%zu public), %zu-byte proof, compiled in %.0f ms\n",
        slicing_name(slicing).c_str(), compiled->depth, compiled->nwires,
        compiled->nquad_terms, compiled->ninputs, c.npub_in, proof.size(),
        compiled->compile_ms);

    const std::string label = "slices:" + slicing_name(slicing);
    const size_t proof_bytes = proof.size();
    benchmark::RegisterBenchmark(
        ("BM_Prove/" + label).c_str(),
        [compiled, w, proof_bytes](benchmark::State& state) {
          for (auto _ : state) {
            auto p = prove(*compiled->circuit, *w);
            benchmark::DoNotOptimize(p);
          }
          state.SetLabel(std::to_string(proof_bytes) + "-byte proof");
        })
        ->Unit(benchmark::kMillisecond);
    benchmark::RegisterBenchmark(
        ("BM_Verify/" + label).c_str(),
        [compiled, pub, proof](benchmark::State& state) {
          for (auto _ : state) {
            bool ok = verify(*compiled->circuit, *pub, proof);
            benchmark::DoNotOptimize(ok);
          }
        })
        ->Unit(benchmark::kMillisecond);
  }
  std::fflush(stdout);

  benchmark::Initialize(&argc, argv);
  benchmark::RunSpecifiedBenchmarks();
  benchmark::Shutdown();
  return 0;
}
