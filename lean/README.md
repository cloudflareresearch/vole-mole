# Security proofs for vole-mole: an LLM-assisted, partial formalization

> **Read this first.** Everything in this directory was produced with heavy assistance from a large
> language model (Claude), working under the direction of a human maintainer. It has **not been
> peer reviewed or audited**. The Lean files are checked by Lean's kernel, but a Lean theorem is
> only as meaningful as its statement and its model of the code, and those were written by the
> same process. The paper proofs (Markdown) are unreviewed drafts. Treat all of it as a detailed
> starting point for expert review, not as a security guarantee.

This directory holds the security analysis of the zero-knowledge proofs (FAEST v3 VOLE-in-the-head
with QuickSilver, `src/voleith.hpp`) and of the three token protocols built on them: PomFRIT,
Moussaka and Ratatouille. The analysis has three layers, and every result below says which layer it
lives in:

| Layer | What it means |
|---|---|
| **[Lean]** | Machine-checked in `VoleMole/`. No `sorry`, no `axiom`, no `native_decide`; `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. Covers the deterministic steps: linear algebra, counting, polynomial degrees, combinatorics, numeric bounds. |
| **[paper]** | A written proof in `docs/`. Covers the probabilistic steps: random-oracle and ideal-cipher arguments, quantum oracle arguments, union bounds, reductions. |
| **[test]** | A Lean model or a deterministic fact checked against the C++ by a test in `tests/` (exhaustively where the domain is small). This is how the Lean models are tied to the code. |

**Partial** means: no end-to-end statement is machine-checked. The Lean results are the
deterministic cores that the paper proofs call. The C++ is tested against the Lean models, never
proved equal to them, and constant-time behaviour and side channels are out of scope.

## Layout

```
lean/
  README.md                 this file
  VoleMole.lean             root of the Lean library (imports every module below)
  VoleMole/
    Extraction/             label-based extraction core (the sketch's Core Theorem)
    SeedExtraction.lean     seed-based extraction core (Claims 3–4, case analysis)
    Seed/                   cores of L0–L8 and Q1–Q7 (commitments, KOS, QuickSilver, SE, quantum)
    ZK/                     cores of the zero-knowledge proofs
    Protocols/              cores of the PomFRIT, Moussaka, Ratatouille, domain-separation and
                            UOV-assumption notes
    Arith/                  executable constraint generators + soundness/completeness (in progress)
    Spec/                   executable protocol specs
    Verifier/               executable VOLEitH verifier and prover, and their bridge theorems
    Prob/                   uniform-probability layer: single-challenge bounds, per-chain theorem
    ROM/                    random-oracle model (VCVio): union bound over queries, per-chain terms,
                            the executable verifier against the oracle, domain separation
    Privacy/                privacy games on the executable specs (blindness, issuer hiding,
                            unlinkability), with zero knowledge and hiding as hypotheses
  vectors/                  test vectors dumped by the C++ for the Arith/ cross-check
  docs/
    sketch.md               the maintainer's original design note
    lean-correspondence.md  sketch item → Lean name, and code-correspondence findings
    extraction/             proof of knowledge, simulation-extractability, quantum versions
      README.md             the main theorems and how the lemmas assemble (start here)
      L0-…L8-*.md           classical lemmas
      Q1-…Q7-*.md           quantum (QROM) lemmas
    zk.md, zk-qrom.md       zero knowledge, classical and quantum
    security/               protocol-level security notes
```

All `file:line` citations in `docs/` are relative to the repository root. Most refer to commit
`6d7113e` (`main`); those about the zero-knowledge fix refer to branch `voleith-label-rows`.

## Building and checking

```sh
cd lean
lake exe cache get     # prebuilt Mathlib
lake build             # the whole library; must finish with no warnings
lake env lean VoleMole/Arith/UOV.lean    # check a single file
lake build VoleMole.ROM.Comb             # the random-oracle layer (§9), which needs VCVio
```

Toolchain and Mathlib: `v4.34.0`. [VCVio](https://github.com/dtumad/VCV-io) is pinned to a commit
in `lakefile.toml` and imported only by `VoleMole/ROM/`. It has no prebuilt cache: the first build
of `VoleMole/ROM/` compiles the part of VCVio, PolyFun and cslib it imports (about 120 modules, about
2 minutes with 2 threads). The executables link VCVio's native-backend archives as empty stubs
(`lake` prints `info: … native backend disabled`); nothing here calls them.

The prover is checked against the KAT proofs with `lake exe prover_vectors` (from `lean/`; `lake exe
prover_vectors DIR/tests labelrows` for the KAT files of a `voleith-label-rows` build), and the
zero-knowledge simulator with `lake exe zk_sim [DIR/tests [main|labelrows [FILTER]]]` (about 10
minutes per layout; `FILTER` is a label prefix such as `moussaka` or `ratatouille 0`).

The C++ side of the cross-checks runs with the normal test suite:

```sh
ninja -C build && meson test -C build    # includes `lean-models`
```

## The results

### 1. Proof of knowledge (classical) — `docs/extraction/`

**Statement.** For every classical prover, the proof system is a *straight-line* proof of
knowledge for each of the repo's five relations: an extractor that only reads the prover's oracle
queries (no rewinding, no programming) outputs a valid witness whenever the verifier accepts, except
with probability

    ε_ext = Q·max(d,1)·2⁻¹²⁸ + q₁·ε_KOS + q₂·(ε_QS + 2⁻¹²⁸) + q_c·2⁻⁴⁴⁸ + ε_bind + ε_dead + (q²+q)·2⁻²⁵⁶

which is about 2⁻⁶⁰·⁸ at q = 2⁶⁴ queries. Model: SHAKE as random oracles, AES-128 as an ideal
cipher.

**Proof structure.** `docs/extraction/README.md` assembles it from these lemmas:

| Lemma | Content | Status |
|---|---|---|
| L0 | All hash domains are disjoint; AES inputs of different roles never collide | [paper] + [Lean] `Seed/Commitments.lean` |
| L1 | Committed data (commitment preimages, leaf keys) is well defined and binding | [paper] |
| L2 | A leaf the prover cannot open is always the hidden one | [paper] |
| L3 | KOS consistency check forces affine VOLE correlations (ε_KOS ≈ 2⁻¹⁵⁴) | [paper] + [Lean] `Seed/KOS.lean` + [test] |
| L4 | QuickSilver with challenge-dependent constraints: either the constraints hold or few challenges accept | [paper] + [Lean] `Seed/QuickSilver.lean` + [test] |
| L5 | A tree whose challenge block varies holds the witness (Claim 4) | [Lean] `SeedExtraction.lean` |
| L6 | Per-chain case analysis: extract, or accept at most max(d,1) challenges | [Lean] `SeedExtraction.lean` |
| L7 | Arithmetization soundness: satisfied constraints imply the relation | [Lean] `Arith/` for all five relations + [test] cross-check (§6); paper `L7-uov.md`, `L7-keccak.md` |

**End-to-end deterministic theorem** ([Lean] `EndToEnd/`). For each of the five relations,
`*_extract` joins L5–L7 with the real constraint system: on a chain satisfying the hypotheses that
L1–L4 provide (stated explicitly in `EndToEnd/Relations.lean`), either some known tree's candidate
decodes to a witness of the actual relation (e.g. `P(s) = h ⊕ r`), or at most max(d,1) challenges
are accepted. The QuickSilver check polynomial is built from the relation's `Arith` system and
matched to the verifier's MAC arithmetic. What remains on paper is the probability of each
hypothesis (ε_KOS, ε_QS, 1/|F| for the combination, and L1's binding).

Along the way the analysis corrected the sketch's definition of an "alive" leaf (the original
admitted an attack with probability about τ·q₂·2⁻¹²⁸) and found that bad-challenge terms must be
charged per H₂¹/H₂² query, not per H₂³ query.

### 2. Simulation-extractability (classical) — `docs/extraction/L8-*.md`

**Statement.** Strong simulation-extractability: extraction still works when the prover also sees
simulated proofs, for any accepting proof that differs from all simulated ones. [paper] +
[Lean] `Seed/SimExt.lean`. No malleability attack was found.

### 3. Zero knowledge — `docs/zk.md`, `docs/zk-qrom.md`

**Finding (on `main`): the proofs are not zero-knowledge.** The free-XOR label offset of FAEST's
CRT masks equals the first 128 witness bits (up to a public value). A verifier who knows those bits
learns the masks. In PomFRIT the Issuer knows them, so it can link redemptions to issuances:
blindness fails.

**Fix:** derive the labels from dedicated VOLE rows (branch `voleith-label-rows`, faest-arch-opt
patch 0005, +256 bytes per proof).

**Statement (on `main`, `docs/zk.md` §4.1).** [Lean] `ZK/Main.lean`, `ZK/Relations.lean`: in the
`main` layout the view `(d, c_i, forced labels)` is witness-independent, but the label offset is
`π(d) − π(w)`; the probability that some of `q` H₅ queries hits a sibling label *equals* a sum of
success probabilities of explicit predictors of `w[0..128)` from the adversary's auxiliary
information, so it is `≤ q·ε_PU` under (PU), stated as a hypothesis on those predictors (also with
the masked responses, and for a token's two proofs jointly). From the `Arith/` witness layouts,
`w[0..16) = r` is the commitment opening for Moussaka issue/redeem and Ratatouille issue/spend
(`moussaka_main_zk`, `ratatouille_main_zk`; (PU) there is one-wayness of Keccak-p[800] in `r`, an
assumption); towards a Moussaka Moderator that never sees `t`, `ε_PU = 2⁻¹²⁸` unconditionally
(`moussakaRedeem_main_zk_uniform`). For PomFRIT the Issuer's `t ⊕ h(σ)` is `r` in every honest run
(`issuerGuess_eq`), so its query hits with probability 1 and the attack test accepts every real
proof (`pomfrit_issuer_hits`, `pomfrit_attack_test`). Still [paper]: H1–H4, H8, the
identical-until-bad coupling of H5 and H6 and the reduction of an oracle adversary to the query
functions (`docs/zk.md` §4.1, "Still on paper").

**Statement (with the fix).** Adaptive, multi-proof, statistical-in-the-witness zero knowledge in
the classical ROM [paper] + [Lean] `ZK/`. Against quantum distinguishers [paper], with a bound of
about 2⁻¹⁹ at 2³⁰ queries and 2³⁰ proofs. The dominant term, Q_P·√(q/2¹²⁸), is the standard
adaptive-reprogramming loss and has no known matching attack. A 128-bit `rho` does admit a real
multi-target Grover attack around 2⁵⁰ queries. Both are removed by a 256-bit `rho` and a salt in
chal1/chal2 (recommended, not implemented).

**Statement (executable prover, with the fix, `docs/zk.md` §10.1).** [Lean] `ZK/Sim.lean` …
`ZK/Exec.lean`: an executable simulator (`Sim.simulate`; `Sim.simulateRO` also programs `H₂³`,
and the verifier accepts its proofs under the programmed oracle, `simulateRO_accept'`: with no
assumption beyond `Δ ≠ 0`, i.e. except with probability `≤ noHitProb + 2⁻¹¹¹ ≤ 2⁻¹¹⁰` over the
simulator's coins, `pr_simulateRO_reject_110`). The
executable Lean prover equals an ideal-tape prover at its own run's tape (`prove_eq_proveIdeal`),
and on a uniform tape the ideal-tape prover's output is distributed exactly as the simulator's
(`proveIdeal_close`; with label rows Θ is moreover uniform and independent of the proof,
`prove_guess_theta`). So the zero-knowledge advantage of any distinguisher equals its advantage
on the tape (`zk_reduction`), and `Privacy.ZeroKnowledge` holds with error `ε` for statement
families with dedicated label rows (`labelRows_zeroKnowledge`) under the **tape hypothesis**
`TapeHyp … ε` (H1, H4, H6 and the grinding answers: the run's tape is `ε`-close to uniform) and
deterministic hypotheses (the witness satisfies the system for every `chal1`, `N_MASK ≤ 32`, and
the two correctness facts of the completeness theorem, proved for faest-arch-opt's tables;
correct interpolation is proved, `ZK/Interp.lean`). The tape hypothesis is in turn **derived from
one hypothesis per hop** by a proved hybrid argument (`ZK/Hops.lean`, `HopHyps`,
`tapeHyp_of_hops`), so `labelRows_zeroKnowledge_tables` has error
`ε_rho + ε_grind + ε_bavc + ε_lab`: `H₃`'s answer at the seed input is close to uniform (H1),
the `H₂³` answers at the grinding points are (grinding), the hidden part of a commitment from a
uniform root seed is (H4, BAVC hiding: AES), and the `H₅` answers at the sibling labels are,
through the ideal-tape prover (H6). With the hashed domain a uniform table (`ZK/HopsROM.lean`),
H1 and grinding hold with `ε = 0`, H1 with `≤ q₃·2⁻¹²⁸` against a distinguisher reading `H₃` at
`q₃` inputs, programming `H₂³` at the grinding points is perfect (the prover's grinding prefix
provably does not read `H₂³`, `ZK/HopsRead.lean`), and H6 costs `≤ (q₅ + 1)·2⁻¹²⁸` against a
distinguisher reading `H₅` at `q₅` inputs (`lab_rom_hyp`, `ZK/HopsH6.lean`: the prover reads
`H₅` only at the active labels, and each query is a guess of the label offset `Θ`, which is
independent of the proof). H4 is proved in the ideal-cipher model (`ZK/HopsH4Ideal.lean`: the
BAVC rebuilt with the cipher a uniform table, equal to the executable one at AES, `hiddenOut_eq`;
a GGM hybrid over the `≤ 221` hidden-path nodes gives `≤ 221·(4607 + q)·2⁻¹²⁸` against a
distinguisher reading the table at `q` keys, `hide_rom_query`), with the rows uniform functions
(the PRP/PRF switching term is on paper). The hops are composed into one experiment
(`zk_rom_ic`, `ZK/HopsJoint.lean`): with `H₃`, `H₂³`, `H₅` independent uniform tables (the
other domains fixed) and the BAVC's cipher a uniform table in a proof-only cipher-parametric
prover `proveE` (the executable prover at AES, `proveE_recOf_aes`), one proof is
`q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to the simulator against a
distinguisher reading `H₃`, `H₅` and the cipher at `q₃`, `q₅`, `q_E` keys; it does not read
`H₂³`, and only the hidden part of the commitment uses `E`. With `H₂³` visible as well
(`zk_rom_h23`, `ZK/HopsH23.lean`, with `H₅` a table on every 37-byte input), for the executable
prover with BAVC hiding assumed: the
simulator programs `H₂³` at the grinding points of the prefix it recomputes from its own proof as
the verifier does (`simulateRO`'s points), and one proof is
`q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸`-close against a distinguisher that also reads
`H₂³` without limit, `Pr[GrindBad] ≤ noHitProb + Pr[Δ' = 0]` (the recomputed points are the
prover's otherwise: `hyb3_vPre`, `ZK/VerifyPre.lean`). Both at once (`zk_rom_ic_h23`,
`ZK/HopsIC.lean`): the executable BAVC, VOLE expansion, prover and verifier call their CTR PRG
through a class (`HasPrg`, `Verifier/Prg.lean`; AES for the executables, which are unchanged), so
they run with the cipher a uniform table `E` (`icPrg E`, the executable code at `E = aesTable`)
and `zk_rom_h23`'s chain holds for every cipher; with `H₅` a table on every 37-byte input and the
honest recomputation's reads of `E` (the reconstructed tree, at most `4607` keys) counted, the
executable prover with the ideal cipher is
`q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to the
programming simulator against a distinguisher reading `H₃`, `H₅`, `E` at `q₃`, `q₅`, `q_E` keys
and `H₂³` freely (`docs/zk.md` §10.1). The grinding term is numeric (`ZK/AcceptCount.lean`,
`ZK/GrindNum.lean`): the accepted set has `|A| ≥ 2¹¹¹` of the `2¹²⁸` values of `Δ` (a Markov
bound on a box of hidden-index tuples, with the summed open count evaluated by the kernel), so no
grinding answer is accepted with probability `≤ 2^{−2¹⁵}`; `W_CRT` is injective, so `Δ' = 0` only
at `Δ = 0`, which is the first accepted answer with probability `≤ 1/|A|`; hence
`Pr[GrindBad] ≤ 2⁻¹¹⁰` and `zk_rom_ic_h23_num`, `zk_rom_h23_num` state both bounds with `2⁻¹¹⁰` in
its place. PomFRIT's two-phase zero knowledge, with
the instance chosen after step 1, is derived the same way (`ZK/TwoPhase.lean`: step 1's fields
are uniform and independent of the witness, step 2 stays uniform given them for every adaptive
choice; `twoPhase_close` under the two-phase tape hypothesis `TapeHyp2`; `twoPhase_close_tables`;
`TapeHyp2` from the hops, with one more term, the abort probability `noHitProb`:
`ZK/TwoPhaseHops.lean`, `≤ 2^{−2¹⁵}` by `noHitProb_le`). For all three protocols the per-relation statements are assembled and
every deterministic hypothesis is proved (`Privacy/MoussakaLean.lean`,
`Privacy/RatatouilleLean.lean`, `Privacy/PomFRITLean.lean`; with SHAKE, `*_shake`, only the hop
hypotheses and hiding remain, each proof's error the sum of the named terms). `lake exe zk_sim`
checks the tape equation, the simulator and the ideal-tape prover on all 18 KAT runs of each
layout.

**Privacy in the random-oracle and ideal-cipher model** ([Lean] `Privacy/ZeroKnowledgeRO.lean`,
`ZK/ReadsRO.lean`, `Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`, `ZK/TwoPhaseRO.lean`,
`ZK/TwoPhaseIC.lean`, `ZK/TwoPhaseReadsRO.lean`, `Privacy/PomFRITRO.lean`, `ZK/CollideRO.lean`,
`ZK/CollideRO2.lean`, `Privacy/MoussakaDelta.lean`, `Privacy/RatatouilleDelta.lean`,
`Privacy/PomFRITDelta.lean`; `docs/zk.md` §10.2).
`ZeroKnowledgeRO` is zero knowledge against distinguishers that also see (and read, with budgets)
the random tables; `zk_rom_ic_h23_num` instantiates it (`lean_zeroKnowledgeRO`). The executable
prover reads the cipher at `≤ 4607` and `H₅` at `≤ 624` keys, the simulator's programming at
`≤ 4607` and `≤ 312` (`realRO_rdE`, `realRO_rd5`, `progRO_isProg`), which bounds what a reduction
that runs the other proofs itself reads. `hop_ro` is the hybrid step for proofs sharing the tables;
each step after the first costs an explicit programming-collision term `δ`. Moussaka anonymity and
Ratatouille unlinkability, with the adversary's guess seeing all tables and all four proofs on the
same tables: `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + (collision terms of both worlds) + 2·εhide`
(`anonymityRO_lean`, `unlinkabilityRO_lean`), `εRO` the single-proof bound. For PomFRIT's
two-phase prover the same single-proof bound holds (`zk2_rom_ic_h23_num`: the simulator programs
`H₂³` at the prefix it recomputes for the instance picked after step 1; the fallback block is
inside `Pr[GrindBad]`), for a continuation that may itself read `H₅` and the cipher (its reads
are added to the budget): the Issuer answers after seeing both requests, which read the tables.
It is `ZeroKnowledgeROS` (`lean_zeroKnowledgeROS2`, a simulator that may read the tables it does
not program), and PomFRIT blindness with both sessions on the same tables is
`≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)` (`blindnessRO_lean`). **The collision
terms are bounded in Lean** (`ZK/CollideRO.lean`, `pr_collide_zk`): the real prover reads `H₂³`
only at its own grinding prefix `chal2 ‖ qs_check ‖ ã` (`72 + 16·(d − 1)` bytes), a simulator
programs one prefix block, whose last `16·(d − 1)` bytes are its uniform `ã` (the simulated opening
reconstructs, `reconstruct_openingOf`); for the second issuance `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`, for a
redemption or spend (whose statement may depend on the earlier `ã`), with a second application of
zero knowledge, `δ ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 3·2⁻¹⁰²⁴`, and for PomFRIT
`δ(A) ≤ noHitProb + 2⁻¹²⁸`. So `anonymityRO_lean_num`, `unlinkabilityRO_lean_num`:
`≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ +
2·εhide` (about `2⁻¹⁰²` plus the budget terms), and `blindnessRO_lean_num`:
`≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸` (`noHitProb ≤ 2^{−2¹⁵}`). The paper
bound for redemptions and spends (`docs/zk.md` §10.2) missed the `Δ' = 0` part of `GrindBad` and
undercounted the earlier `ã` by one; both negligible. **Statements chosen from the tables**
(`docs/zk.md` §10.3, `ZK/AdaptRO.lean`). `zk_adaptive` covers an adversary that reads the tables
(the proof's `H₃` slice, `H₂³`, `H₅`, the cipher, at `s₃`, `s₂`, `s₅`, `s_E` keys, adaptively and
consistently) before it picks the statement and witness. The bound is
`εRO(q₃, q₅, q_E) + (s₃ + s₅ + 1 + 221·s_E)·2⁻¹²⁸`, plus, if it reads `H₂³`, a second
zero-knowledge application and `2·s₂·2⁻¹⁰²⁴` (`ρ` is 16 bytes; the simulated block's 128-byte `ã`
is uniform). The proof samples the reader's view lazily (`Privacy/Resample.lean`) and runs the
chain with the tables patched at its queries (`ZK/HopsPatch.lean`, `ZK/IdealCipherP.lean`).
Moussaka anonymity is restated with an interaction (responses, Anchor Sets, digests) that reads
every table: `anonymityRA_lean_num` (`Privacy/MoussakaRA.lean`), about `2⁻¹⁰¹·⁹` plus the budget
terms. So is Ratatouille unlinkability, with an Issuer whose two message stages (issuance
responses and `d₁`; round 1's response and `d₂`, which reads spend 1's proof) read every table:
`unlinkabilityRA_lean_num` (`Privacy/RatatouilleRA.lean`), about `2⁻¹⁰¹·⁵` plus the budget terms.
PomFRIT blindness is restated with an Issuer whose key, messages and responses read every table
but `H₂³` (`Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`, `blindnessRA_lean_num`:
`≤ 4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`, about `2⁻¹⁰³·²`
plus the budget terms), from the two-phase `zk2_adaptive` (`ZK/TwoPhaseAd.lean`): the
continuation, the Issuer's response to the request computed from step 1's output, reads the
slice, `H₅` and the cipher at keys depending on that output, and these reads are added to the
budget of the H1, H4 and H6 hops (`εRO(q₃ + q_k3, q₅ + q_k5, q_E + q_kE)`). Left open: a PomFRIT
interaction that reads `H₂³` (the two-phase simulator programs the zero-prefix block when the
continuation stops, and the reductions see only programmed tables; `docs/zk.md` §10.3).

The analysis also found a gap in the FAEST v3 specification's own ZK proof (between games G8 and
G9).

### 4. Quantum adversaries (QROM + quantum ideal cipher) — `docs/extraction/Q1…Q7`

| Doc | Result | Status |
|---|---|---|
| Q1 | Key-level compressed oracle for AES as a quantum ideal cipher; online extraction of leaf keys | [paper] + [Lean] `Seed/QuantumCipher.lean` |
| Q2 | Straight-line extraction for quantum provers; leading term ≈ 200·q²·2⁻¹²⁸ (Grover-inherent) | [paper] + [Lean] `Seed/QROM.lean` |
| Q3 | Comparison of AES models; the sketch's "AES-CTR as random oracle" model is unfaithful | [paper] |
| Q4 | Efficient simulation of the quantum ideal cipher (within 2⁻¹⁷²), so the extractor is efficient | [paper] + [Lean] `Seed/CipherSim.lean` |
| Q5 | Simulation-extractability in the QROM (superseded numerically by Q6/Q7) | [paper] + [Lean] `Seed/QSimExt.lean` |
| Q6 | Binding of AES leaf commitments for all q; tightness of key-level techniques | [paper] + [Lean] `Seed/CipherBinding.lean` |
| Q7 | Extraction from many proofs at once; quantum versions of the protocol theorems | [paper] + [Lean] `Seed/QMulti.lean` |

**Numbers.** Total extraction failure: 2⁻⁶⁰·⁴ at 2³⁰ quantum queries, 2⁻⁴⁰·² at 2⁴⁰, 2⁻²³·³ at 2⁴⁵,
vacuous beyond about 2⁵¹·⁷. Up to about 2⁴¹ the bound is dominated by the q²/2¹²⁸ term that Grover
search makes unavoidable for any 128-bit scheme. Beyond that, the AES binding term (a proof
limitation, not an attack) takes over. Strong simulation-extractability: 2⁻⁶⁰·⁴ at 2³⁰ queries and
2³⁰ simulated proofs.

### 5. The protocols — `docs/security/`

| Note | Main results | Main findings |
|---|---|---|
| `pomfrit.md` | One-more unforgeability (classical: proved; quantum: Q7, under new quantum UOV assumptions). Blindness: **fails on `main`**, proved with the ZK fix. | The paper's reduction has a gap (its first-phase extractor is not well defined for multi-tree VOLEitH), repaired by Lemma P at a 2⁻⁷¹ per-query loss ([Lean] `Protocols/PomFRIT.lean`). A holder can make many valid signatures per message (non-minimal grinding counter): deduplicate on the message. |
| `moussaka.md` | One-more unforgeability, double-spend detection, redemption non-malleability, issuer hiding: proved. | Nullifier squatting (low). The draft's one-more-UOV argument is invalid as written; restructured. |
| `ratatouille.md` | Balance (no inflation), no theft, unlinkability, correctness: proved. | Spends are not bound to a session, so a copied spend request can be redeemed first (medium). |
| `domain-separation.md` | Every hash/XOF/permutation call lies in a disjoint domain, except below. [Lean] `Protocols/DomainSeparation.lean` | PomFRIT's `hash_to_target` overlaps four proof-system domains (no exploit found; fix: a final domain byte). |
| `uov-assumptions.md` | Relates the protocol-specific UOV assumptions to each other and to standard UOV. [Lean] `Protocols/UOVAssumptions.lean` | Several reductions are unavailable; the note states why. |
| Privacy on the specs ([Lean] `VoleMole/Privacy/`) | The privacy theorems as games on `Spec/*`, each hybrid hop mechanized: PomFRIT blindness (`Privacy.PomFRIT.blindness`, `≤ 4ε`), Moussaka issuer hiding and unlinkability against a Moderator colluding with all Anchors (`Privacy.Moussaka.anonymity`, `≤ 4εI + 4εR + 2εhide`), Ratatouille unlinkability of spends from issuances and from each other through change tokens (`Privacy.Ratatouille.unlinkability`, `≤ 4εI + 4εS + 2εhide`). Hypotheses: zero knowledge of the abstract proof systems (`Privacy.ZeroKnowledge`: a simulator from the instance alone, output `ε`-close to the prover's for every valid witness; `ε = 0` is equality of distributions), hiding of `Com` for the explicit reductions. The final hybrids are exact. With the executable Lean prover (label rows) as the proof system, zero knowledge is reduced to the tape hypothesis (`Privacy/LeanProver.lean`; `docs/zk.md` §10.1): with every other hypothesis proved (`Privacy.Moussaka.anonymity_label_rows`, `Privacy.Ratatouille.unlinkability_label_rows`, `Privacy.PomFRIT.blindness_lean`, assuming the hash record's output lengths; `*_shake` with SHAKE and the tape hypothesis from the hop hypotheses, so each proof's error is `ε_rho + ε_grind + ε_bavc + ε_lab` (PomFRIT: `+ ε_abort`); the latter two on the label-row layout, `Spec.Ratatouille.Sizes.labelRows` and `Spec/PomFRITLayout.lean`). On paper: the seed-XOF hop, the hop hypotheses (H4 for AES; the random-oracle hops are proved for the hashed domain as a uniform table, `ZK/HopsROM.lean`, `ZK/HopsH6.lean`). In the random-oracle and ideal-cipher model with the adversary seeing the tables, from `zk_rom_ic_h23_num` (`Privacy.ZeroKnowledgeRO`, `hop_ro`): Moussaka (`Privacy.Moussaka.anonymityRO_lean`) and Ratatouille (`Privacy.Ratatouille.unlinkabilityRO_lean`), `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + δ's + 2εhide`, and PomFRIT (`Privacy.PomFRIT.blindnessRO_lean`, from the two-phase `zk2_rom_ic_h23_num`), `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)`, with the programming-collision terms `δ` bounded in Lean (`*_lean_num`: `≤ 8·εRO(…) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2εhide`; PomFRIT `≤ 4·εRO(…) + 2·noHitProb + 2·2⁻¹²⁸`), the adversary's interaction table-oblivious; for Moussaka and Ratatouille also with a table-reading interaction (`Privacy.Moussaka.anonymityRA_lean_num`, `Privacy.Ratatouille.unlinkabilityRA_lean_num`, from the adaptive-statement `ZK.Sim.zk_adaptive`, `docs/zk.md` §10.3), and PomFRIT with an Issuer whose key, messages and responses read every table but `H₂³` (`Privacy.PomFRIT.blindnessRA_lean_num`, `≤ 4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`, from the two-phase `ZK.Sim.zk2_adaptive`) | The zero-knowledge hypothesis is false on `main` for PomFRIT (`ZK.pomfrit_issuer_hits`, `ZK.pomfrit_attack_test`); for Moussaka and Ratatouille no efficient simulator satisfies it per proof on `main`, and the joint (PU) hop replaces it (paper). PomFRIT note §8.3: the "both ⊥" rule is needed. Moussaka Thm 4(a) needs no `2⁻¹⁹²` term; Thm 4(b) misses an abort term. Ratatouille H3 needs the Client's validity check against the commitment it sent |

**Cross-cutting finding (critical, deployment):** PomFRIT's Issuer signs arbitrary targets, and
all protocols share the UOV key type. If one key serves PomFRIT and another protocol, anyone can
mint Ratatouille credits or forge Moussaka tokens (demonstrated). Keys must be separated by
protocol.

### 6. Arithmetization in Lean — `VoleMole/Arith/`

Goal: replace the paper proof of L7 with executable Lean models of each relation's constraint
generator, mirroring the C++ call by call, with Lean proofs of

- **completeness**: an honest witness satisfies every constraint;
- **soundness**: if the constraints vanish at any committed values, those values are bits and
  encode a witness, except for a 1/|F| fraction of combination challenges;

and a differential test that evaluates the C++ constraints at random *field-valued* inputs (which
pins down the constraint polynomials, not just their values on bits) and compares with Lean.

| Piece | Status |
|---|---|
| `Arith/Basic.lean`: shared constraint-expression interface | done |
| `Arith/UOV.lean`: UOV public-map gadget (`src/uov/circuit.hpp`) | done: generator, completeness, soundness, 1/\|F\| combination bound |
| `Arith/PomFRIT.lean`: PomFRIT redeem, `P(s) = h ⊕ r` | done: generator, completeness, soundness, end-to-end 1/\|F\| bound |
| `Arith/Keccak/`, `Arith/Keccak.lean`: Keccak-p[800,12] segmented gadget (`src/keccak/`) | done: reference permutation (checked on the KATs), inverse layers proved, generator, completeness, soundness (outputs equal Keccak-p[800] of the input) |
| `Arith/Adder.lean`: Ratatouille's 64-bit credit adder | done: exact 65-bit sum |
| `Arith/GF.lean`, `GFEmbedding.lean`: concrete GF(2¹²⁸), GF(256), the embedding | done; embedding proved an injective ring homomorphism in the kernel |
| `Arith/GFField.lean`: `GF128` is the field GF(2¹²⁸) | done, in the kernel: `X¹²⁸ + X⁷ + X² + X + 1` irreducible over GF(2), `GF128 ≃+* GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`, `Field GF128`, `CharP GF128 2` |
| `Arith/ConcreteField.lean`, `EndToEnd/Concrete.lean`: the soundness corollaries at GF(2¹²⁸) | done: `uov_*`, `*_complete`, `*_sound_card` and the five `EndToEnd` `*_extract` theorems at `F := GF128`, `β := beta`, `K := GF256`, with `IsEmbedding beta`, `beta 0 = 1` and `\|F\| = 2¹²⁸` discharged; the bad-`l` fraction is `≤ 2⁻¹²⁸` |
| C++ dumper (`tests/arith/`) and `lake exe arith_vectors` | done; Lean and C++ constraint values agree on every UOV and PomFRIT record, at bit and random field-valued witnesses |
| `Arith/Moussaka.lean`: Moussaka issue (commitment opening) and redeem (one-hot selector, UOV preimage under the selected anchor key, Keccak commitment) | done: generators, completeness, soundness, 1/\|F\| bound; cross-checked |
| `Arith/Pqov.lean`, `Arith/Concrete.lean`: pqov's `ov_publicmap` equals the model; the relations read as the C++ byte checks on concrete GF(256) | done; cross-checked |
| `Arith/Ratatouille.lean`: Ratatouille issue (commitment opening) and spend (two commitments, tag, conservation `t + x = t' + d` over ℕ with 64-bit ranges, UOV preimage of the tag) | done: generators, completeness, soundness, 1/\|F\| bound; cross-checked |

The UOV gadget's hypothesis, that the embedding GF(256) → GF(2¹²⁸) given by the β constants is an
injective ring homomorphism, is discharged in the kernel for the concrete constants
(`VoleMole.Arith.isEmbedding`), and with `Field GF128` the soundness theorems are instantiated at
the concrete field with no hypotheses left (`Arith/ConcreteField.lean`, e.g.
`Moussaka.redeem_sound_card_gf128`; `EndToEnd/Concrete.lean`, e.g. `moussaka_redeem_extract_gf128`). The constants themselves, and the GF(2¹²⁸) and GF(256)
multiplications, are checked against the C++ tables by `arith_vectors`.

`Arith/GFField.lean` proves that the concrete `GF128` operations form the field GF(2¹²⁸), without
`native_decide`: Mathlib's degree criterion (an irreducible factor of `X^(2ⁿ) − X` over GF(2) has
degree dividing `n`) reduces irreducibility of the modulus to `X^(2¹²⁸) = X` and the invertibility
of `X^(2⁶⁴) + X` modulo it, which the kernel computes with `GF128` arithmetic (128 squarings, and a
product with an inverse found offline); evaluation at the root of `GF(2)[X]/(modulus)` is proved
multiplicative symbolically and bijective by counting.

To regenerate and check the vectors (the first `lake build arith_vectors` compiles Mathlib to native
code and takes about 10 minutes; `lean/vectors/` is not committed):

```sh
./build/tests/dump_arith_vectors lean/vectors
cd lean && lake build arith_vectors && lake exe arith_vectors
```

### 7. Executable protocol specs — `VoleMole/Spec/`

Byte-level Lean models of the protocol logic, with the proof system and UOV signing as abstract
parameters (UOV verification is concrete). Cross-checked against the C++ known answers by
`lake exe spec_kats` (about 15 s). UOV public keys are generated in Lean from the KATs' compact
secret keys (pqov key generation, `Verifier/Keygen.lean`); `lean/vectors/uov_keys.txt` (§6) is
compared with them when present but not needed.

| Piece | Status |
|---|---|
| `Spec/SHAKE.lean`: Keccak-f[1600], SHAKE128/256 | done; standard vectors |
| `Spec/PomFRIT.lean`, `Spec/Moussaka.lean` | done: every party's steps and errors; honest runs succeed; at most one acceptance per nullifier and context over any request sequence; injectivity of the hashed encodings (`H_T` binds d[0..M), Moussaka binds `challenge_digest`); input validation. All deterministic KAT fields match (`tests/pomfrit/pomfrit_kat.txt` is new). Moussaka's redemption requests are also checked by `finalizeRedeem` with the abstract verifier instantiated by the Lean verifier (§8), under the Anchor Set generated from the `anchor_sk` fields, so the digests of all Anchors (not only the issuer's) are checked against the KATs; swapping two non-issuer Anchors is rejected |
| `Spec/Ratatouille.lean` | done: issue, spend, refund, change tokens, every abort path; honest runs succeed; nullifiers accepted once; balance `Σd ≤ ΣT_init + Σx′` per context over adversarial request sequences (soundness and unforgeability as hypotheses); the findings of `security/ratatouille.md` (copied requests, consumed pending state, unbounded refunds, signing before the nullifier check) as theorems, including a concrete run that breaks balance after one leaked response. All deterministic KAT fields match. |

### 8. A Lean VOLEitH verifier and prover (both match the C++ on all KAT proofs, both layouts) — `VoleMole/Verifier/`

Goal: an executable Lean verifier that accepts the real C++ proofs (the KAT files contain them) and
rejects mutated ones, built from the same models the proofs use, and an executable Lean prover that
reproduces them. Plan and milestones: `docs/verifier-plan.md`. Checked by `lake exe
verifier_vectors` against vectors from `tests/voleith/dump_verifier_vectors.cpp`, and by `lake exe
prover_vectors` against the KAT files.

| Milestone | Status |
|---|---|
| SHAKE, AES-128, faest-arch-opt's CTR PRG | done; FIPS-197 and C++ vectors |
| One-tree BAVC (GGM) reconstruction and `vole_commit_check` | done; reproduces a real Moussaka issuance proof byte for byte |
| Proof parsing, `chal1`, ConvertToVOLE, CRT VOLE (lifted rows, masks, lifted Δ) | done; on one real proof of each of the five relations, every value matches the C++ byte for byte |
| KOS VOLE check and `chal2` (`KOS.lean`) | done; matches the C++ for all five relations |
| QuickSilver (`QuickSilver.lean`) | done; the verifier's value for a degree-`d` constraint is `Δ^d·f(q/Δ)`, so the proved `Arith/*` generators are evaluated unchanged at `q·Δ⁻¹`; the UOV gadget is evaluated directly over arrays (`UovEval.lean`), proved equal to the generator's value |
| Full verification (`Verify.lean`, `Relations.lean`, `Kats.lean`) | done; all 18 proofs in the three KAT files are accepted (3 PomFRIT, 6 Moussaka, 9 Ratatouille), with statements built in Lean from the KAT fields and the `Spec/*` instance encoders; 51 mutations (each proof field, each instance field, PomFRIT's refresher) are rejected. Runtime about 25 s (was about 5 min): the UOV public maps are evaluated over arrays with `Combination`'s tables (`UovEval.lean`, ≈ 10 ms per key, proved equal to the `Arith/*` evaluators), `GF128.mul` runs as an unboxed loop proved equal to it (`@[csimp]`, ≈ 0.3 µs), and AES uses round tables |
| CRT tables (`CrtData.lean`, `CrtGen.lean`, `CrtSearch.lean`) | done: `W_crt` and `M_tree` are recomputed from the moduli; F, G, W_tree, W_gate (copied from faest-arch-opt's build output into `CrtData` as hex literals, which the verifier reads) are checked against their defining bilinear identity on all basis pairs (at run time, and in the kernel for the verifier's own computation: `Bridge/CrtCheck.lean`) and regenerated by a port of `vole_mult_tables.py --preset 128f` (tree moduli, cost search and portfolio, bilinear algorithms including Montgomery's formula and the F₄ towers, interpolation, pruning), which reproduces them exactly |
| UOV keys | done: pqov's key generation (`generate_keypair_pkc`, uov-Ip-pkc: `SHAKE256(sk_seed)` → `pk_seed ‖ O`, `P1 ‖ P2` by AES-128-CTR, `P3 = UT(M + Mᵀ)` with `M = Oᵀ(P1·O + P2)`, `Keygen.lean`, about 0.08 s per key) and `expand_pk` in Lean; the KAT runners derive every key from the compact secret keys. The 64 generated compressed keys equal the C++ ones in `lean/vectors/verifier_keys.txt`, and the expanded `test`/`alt61`/`alt62` keys equal `uov_keys.txt` (both optional cross-checks) |
| Label-rows variant (`Params.labelRows`) | done; the same verifier, with the flag set, accepts all 18 KAT proofs of branch `voleith-label-rows` (KATs regenerated there, PomFRIT's too) and rejects the same 51 mutations; every intermediate value of the five dumped proofs matches |
| Hash record (`Hashes.lean`) | done: the verifier takes its hashes as a record `Hs : Hashes`, one function per L0 domain (`Kind`: `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₅`, `H₂¹`, `H₂²`, `H₂³`, the combination); `Hashes.shake` is SHAKE128, which the runners use (same results on both layouts). The UOV combination is hashed by the verifier (`Statement.comb`, `combBytes`). Hashes outside L0 (UOV key digests and expansion, PomFRIT's `hash_to_target` and refresher commitment) stay SHAKE. The bridge theorems below are generic in `Hs`; §9 runs the verifier with the random oracle's answers (`Hashes.ofTable`) |
| Bridge theorems (`Verifier/Bridge/*`) | partly: proved that the executable CTR blocks are `Seed.Commitments.ctrInput` (and its role separation applies to the verifier's tweaks), that the VOLE check is `Seed.kosValue`, that the QuickSilver check value is `EndToEnd.qsCheck` + `Seed.maskPoly` (including the `Δ^d·f(q/Δ)` shortcut), and that acceptance gives `EndToEnd`'s accepting equation at that transcript. The field embedding is constructed (`Bridge/Concrete.lean`, from `Arith/GFField.lean`) and the theorems that assumed one (`accept_hacc`, `map_constraintKeys`, `map_gfInv`, `map_voleHashReceiver`) are restated at it without that hypothesis. Per relation (`Bridge/Relations.lean`): with `GF128` itself as the field, each relation's evaluator is `System.values` of its `Arith/*` system (`betaFast = beta`, cached UOV coefficients unchanged, the array-based UOV evaluation of `UovEval.lean` equal to the generator's), so acceptance by the executable `verify` gives `EndToEnd`'s accepting equation for that system over GF(2¹²⁸) with no hypothesis (`moussakaIssue_accept`, …, `pomfritVerify_accept`), i.e. `hacc` of `*_extract_gf128` at that Δ. |
| Bridge across Δ (`Bridge/Lift.lean`, `Columns.lean`, `Chain.lean`, `ChainRelations.lean`) | done, modulo the probabilistic steps: ConvertToVOLE and the CRT step are read as functions of the challenge blocks with the commitments fixed (the steps take `Δ` as bits and the commitments as arguments: `convertToVoleAt`, `crtReconstructAt`). Proved: each column is `V_{i,b} + Δ_{i,b}·u^{(i)}` with `u^{(i)} = c_i + Σ_j PRG(K_{i,j})` (the hidden leaf's key never read), so each lifted witness row is `C_r + Σ_i u^{(i)}_r·e_i(Δ_i)` (`resp_row`); the executable lift `Δ ↦ Σ Δ_c W_CRT[c]` is additive and injective (`lift_injective`, an explicit left inverse checked by `decide +kernel`); an opening that reconstructs the committed keys makes the run equal to the committed response (`crtReconstruct_eq_respAt`). On a chain (fixed `iv`, `H₅`, `chal1`, `h_V`, `z`; `chal2` determined before Δ), `chain_claim4` gives `Claim4Hyp` and the accepting equation on all of `A` with one remainder `maskPoly d a b ã z` (masks affine by L3); `onChain_of_accept` puts every accepted proof of the chain in `A` with `Δ = chal3`; `*_extract_chain` (five relations) apply `*_extract_gf128`. Assumed: `KOSGood` for `chal1` (L3), `IsFixed` for dead-leaf trees (L2), `hQS`/`hcomb` (L4), `hδ`/`hclaim1` and binding of the leaf commitments (L1). §9 discharges L3, L4 and `hδ` for uniform independent `chal1`, `chal2`, `l` |
| Prover (`Prover.lean`, `ProverKats.lean`) | done: `voleith_vole_gen` + `voleith_prove_commit` with the C++'s seed derivation (`H₃(w_prefix ‖ mu₁ ‖ rho ‖ 3)`, `rho` from the `Spec/*` seed expanders). Each sender step is the verifier's step function at `Δ = 0` (tag columns, gate hashes, lifted rows, masks, VOLEHash), plus the prover-only `u`, `u_mask` (`M_tree`·PRG), the second gate labels and `c_mult`; QuickSilver's `ã` and check value are the coefficients of the verifier's check value as a polynomial in `Δ'`, obtained by evaluating it at `d + 1` points and interpolating (no coefficient decomposition of the constraints); grinding and the BAVC opening as `grind_and_open`. `lake exe prover_vectors` reproduces all 18 KAT proofs byte for byte on `main`, and all 18 of the label-rows KATs with `labelrows`; the Lean verifier accepts every Lean proof, also on random statements of all five relations (issuers' UOV preimages from a test-only oil-space sampler); a non-satisfying witness is refused. About 44 s per layout |
| Zero-knowledge simulator (`ZK/Sim.lean`, `ZK/SimKats.lean`, `docs/zk.md` §10.1) | done: the simulator, `H₂³` programming, the ideal-tape prover and the real run's tape (`tapeOf`), executable. `lake exe zk_sim` checks on all 18 KAT runs of each layout that `proveIdeal (tapeOf …) = prove`, that the verifier accepts the simulated proof with the programmed oracle (proved for every run with `Δ ≠ 0`, `simulateRO_accept'` in `ZK/SimAcceptFull.lean`, so this check is redundant) and rejects it without, and (except PomFRIT) that it accepts the ideal-tape prover's proof on a pseudorandom tape with programmed grinding answers. About 10 minutes per layout |
| Completeness (`Bridge/Prover.lean`, `Bridge/BAVCComplete.lean`, `Bridge/CrtCheck.lean`, `Bridge/CrtComplete.lean`, `Bridge/Complete.lean`) | proved: the VOLE correlation of the prover's output for every `Δ` on columns and lifted rows (`prover_column`, `prover_row`), the VOLE check identity (`voleHash_complete`), QuickSilver completeness for every `Δ' ≠ 0` (`qsProve_complete`, via `EndToEnd.sysCheckPoly` and Lagrange uniqueness), BAVC opening correctness for every seed and `Δ` (`bavcComplete`: the walks are folds, read as functions of the node index; the opened nodes are exactly the unmarked children of marked nodes, and top-down derivation recovers every node off the hidden paths), the CRT masks' VOLE correlation for faest-arch-opt's tables and every `Δ` (`crtComplete`: gate labels and `c_mult` read back, `r̃` bilinear, and the tables' bilinear identity `L_c(a) = a · W_crt[c]` checked in the kernel on all `120 · 128` basis pairs, packed into 120 numbers of `2¹⁶³⁸⁴` bits, ≈ 1 min), and **completeness of `verify` on the prover's output** (`verify_proveCommit_tables`, `verify_prove_tables`, `*_complete_tables` for the five relations, `*_complete_shake` with SHAKE; for PomFRIT also `pomfritVerify` on the final signature, `Privacy.PomFRIT.pomfritVerify_complete_tables`). The general versions (`verify_prove`, `*_complete`: any tables) keep `BAVCComplete` and `CrtComplete` as hypotheses. Assumed: `Δ' ≠ 0` (`Δ' = 0` only at `Δ = 0`, `ZK.Sim.tDL_eq_zero`; the prover's first accepted grinding answer is `0` with probability `≤ 2⁻¹¹¹`, `pr_hitZero_le`) and, for a general hash record, its output lengths (SHAKE: `hashesWF_shake`) |

### 9. Probabilistic layer — `VoleMole/Prob/` (single challenges) and `VoleMole/ROM/` (random oracle)

Plan: `docs/probabilistic-plan.md`. **Phase A** (`Prob/`, milestones M1–M3, Mathlib only): every
statement is a probability `prU α P` under `PMF.uniformOfFintype`, over the byte strings the random
oracle returns, decoded exactly as the executable verifier decodes them. The samples are uniform and
independent by assumption; phase B justifies this per query.

| Piece | Status |
|---|---|
| `Prob/Uniform.lean` | done: `prU`, count → probability (`prU_eq_card`, `prU_le_of_card_le`), union bound, pushforward along an equivalence, averaging over a product |
| `Prob/Bytes.lean` | done: `Bytes n`; the little-endian words determine the bytes (`word_byte`); `gf128OfBytesEquiv : Bytes 16 ≃ GF128`, `chal1Equiv : Bytes 136 ≃ Seed.Ch GF128 shortKeys` (forward map `chOf`), `chal2Equiv : Bytes 56 ≃ GF128³ × shortKeys` (the `zkCoeff` arguments), `card_shortKeys = 2⁶⁴` (no enumeration); `hδ` deterministically: the `2¹²⁰` admissible `chal3` (`check_format`) decode injectively into blocks (`deltaBlocks_injOn`), and `prU_accept_le` (at most `N` accepted ⇒ probability `≤ N·2⁻¹²⁸`) |
| `Prob/Challenges.lean` | done: L3 over a uniform 136-byte `chal1`, `≤ epsKOS ≤ 2⁻¹⁵⁰` for `≤ 2¹²⁰` challenges (`chain_kos_bad_le`, `epsKOS_le`); the canonical slope `Chain.AV`, `Chain.uCanon`, `slope_eq_uCanon` (L4 §5: every slope on `A ⊆ A_V`, `\|A\| ≥ 2`, is `uCanon`, fixed before `chal2`); L4 over a uniform 56-byte `chal2` (`prU_qs_bad_le`, `≤ ε_QS(n)`), over uniform `l` (`prU_comb_bad_le`, `≤ 2⁻¹²⁸`) and over both independently (`prU_qs_comb_bad_le`) |
| `Prob/ChainRelations.lean` | done: the per-chain theorem for all five relations (`*_chain_prob`, generic `chain_prob`). For a chain whose commitments are fixed before `chal1` and whose `ũ`, `d`, `h_V` are fixed before `chal2` (`Chain.SamePrefix`, `Chain.SameMid`), with `chal1`, `chal2`, `l` uniform and independent: `Pr[L2 ∧ hclaim1 ∧ ¬(extraction ∨ at most max(d,1) admissible chal3 accepted)] ≤ 2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸` (no `2⁻¹²⁸` term for the issue relations; `ε_QS(n) ≤ 2⁻¹²⁷`, `epsQS_le`). L2 and `hclaim1` remain conjuncts of the event |
| `Prob/Bytes.lean` (M5) | `combEquiv M : Bytes (16·M) ≃ (Fin M → GF128)`, the decoding of `l` |

To make `chal2` and `l` samplable, `Bridge/Chain.lean`'s `Chain` has `chal2` and the constraint
evaluator `vals` as fields (it was `Chain.chal2 := Verifier.chal2 …`), and since the hash record
(§8) also `iv` and the gate hash `h5`; `onChain_of_accept` takes `chal2 = Verifier.chal2 Hs …`,
`vals = st.values chal1 (st.combBytes Hs chal2)`, `iv = ivOf Hs …` and `h5 = Hs.hash .h5` as
hypotheses, and the combined relations' `*_extract_chain` take the system at a free `l` (`*SysL`).

**Phase B** (`ROM/`, milestones M4–M5, VCVio). The SHAKE128 calls are one VCVio oracle specification
indexed by L0 domain (`L0-L2-commitments.md` §2.1) and input string, answered by VCVio's lazy random
oracle; one oracle on byte strings with L0's domain rule is proved equivalent (`ROM/DomainSep.lean`).
The theorems bound an event of an arbitrary adversary `oa : OracleComp spec α` with at most
`q₁`, `q₂`, `Q` queries to `H₂¹`, `H₂²`, `H₂³` (and `n` in total), and then the event "the executable
verifier, with the oracle's hashes, accepts the prover's proof and extraction fails"
(`ROM/Accept.lean`). `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (VCVio's lemmas
used here add nothing).

| Piece | Status |
|---|---|
| `ROM/Basic.lean` | done: `Pr{let x ← $ᵗ α}[P x] = prU α P` (`prEvent_uniformSample_eq_prU`), so every phase-A bound is a VCVio bound; the domains `Kind` (L0's rows 1–12, `comb M` for `l`; defined with the hash record, `Verifier/Hashes.lean`) with their output lengths; `spec = OracleSpec.ofFn` over `Kind × ByteArray` |
| `ROM/UnionBound.lean` | done: per-domain query counts `IsKindQueryBound` and their weighted budget; the union bound `prEvent_exists_bad_query_le` (VCVio's `prEvent_randomOracle_le_of_bad_queries_weighted`: a bad event may read the whole answer table, provided resampling its own cell bounds it) |
| `ROM/Fresh.lean` | done: the union bound when a fresh query's bad event reads a second cell chosen by its answer, with a charge for that cell being cached (`prEvent_randomOracle_le_of_fresh_bad_queries`, `prEvent_completeTable_le_two_cells`) |
| `ROM/Chains.lean` | done: bad `H₂¹` (KOS), `H₂²` (QS at the canonical witness), `H₂³` (accepted among at most `N`) queries, each bounded by its M2 lemma when its cell is resampled; `prEvent_le_chain_terms`: `Pr[event] ≤ q₁·ε_KOS + q₂·ε_QS(n) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`, numerically for the issue relations (`q₁·2⁻¹⁵⁰`, `N = 9`); the per-chain deterministic step (`chain_good_of_not_bad`, `*Issue_good_of_not_bad`) |
| `ROM/Comb.lean` | done: the combined relations, with `l` read from the table at `chal2 ‖ dst`: per `H₂²` query `ε_QS(n) + 2⁻¹²⁸ + n·2⁻⁴⁴⁸` (the last term: `chal2 ‖ dst` already queried, L0 §2.2); `prEvent_le_comb_terms`, numerically for Moussaka redemption, Ratatouille spend and PomFRIT (`*_prEvent_le`); `comb_good_of_not_bad`, `moussakaRedeem_good_of_not_bad`, `ratatouilleSpend_good_of_not_bad`, `pomfritRedeem_good_of_not_bad` |
| `ROM/Verifier.lean` | done: the executable verifier against the oracle. `Hashes.ofTable g` (the hashes of an answer table); `verifyQ`, the verifier with each hash a query, equal to `verify (Hashes.ofTable g)` against every complete table (`evalWithAnswerFn_verifyQ`); on an accepted proof its `H₂¹`, `H₂²`, `H₂³` queries at the run's inputs are in the log (`inLog_verifyQ`); at most one query to each of them and 337 in total (`isKindQueryBound_verifyQ`, `isTotalQueryBound_verifyQ`); `game T st oa`: the prover (outputting a proof and the extractor's data) then the verifier |
| `ROM/Accept.lean` | done: **the event is the executable verifier's**: `Pr[accept ∧ ¬Extracted] ≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(n') [+ 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸]) + (Q+1)·N·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain` for all five relations (`moussakaIssue_accept_le`, …, `pomfritRedeem_accept_le`; generic `prEvent_accept_le_chain_terms`, `prEvent_accept_le_comb_terms`), `Extracted` the candidate of `*_extract_chain` from the extractor's keys. `htrace` is proved (`chainBad_of_accept`, `combBad_of_accept`); assumed: binding (a bound on the concrete `bindFail`), the "same chain" step (`SameChain`, which now contains `hclaim1`, outside `chainFail`) and L2 (outside `deadFail`) |
| `ROM/DomainSep.lean` | done: **domain separation ⇒ independent oracles**: one lazy random oracle on byte strings with a domain rule `κ` gives every event of a computation whose queries respect `κ` the probability of the per-domain oracles (`prEvent_route_eq`), and every single-oracle adversary is such a computation (`unroute`, `prEvent_unroute_eq`, with its per-domain query counts) |
| `ROM/SingleOracle.lean` | done: L0's rule (`l0Kind`, the final byte); the verifier's queries respect it (`allQueriesSatisfy_verifyQ`, all five relations: `combOk_*`); the game against one SHAKE oracle has the per-domain game's probabilities (`prEvent_game₁_eq`) |

Still hypotheses of the phase-B theorems (`ROM/Accept.lean`): the "same chain" step (`hsame`: the
data committed at the verifier's own `H₂¹`, `H₂²`, `H₂³` inputs are the accepted proof's chain, and
the `chal3` accepted at its `H₂³` input are those on the chain; outside an event `chainFail`,
`ε_chain`), the binding failure `ε_bind` (a bound on the concrete `bindFail`) and the dead-leaf
failure `ε_dead` (L2) (ideal cipher, query ordering: plan M6). Not done: the statement-binding term
`(q²+q)·2⁻²⁵⁶` (VCVio's birthday lemmas do not fit; plan §2c).

## Gaps

What is **not** established, roughly in order of importance:

1. **The probabilistic arguments are not machine-checked.** All random-oracle, ideal-cipher and
   quantum-oracle steps, and all reductions, are paper proofs. Mechanizing the classical ones (e.g.
   with VCVio or EasyCrypt) is possible but a large project; the quantum ones are beyond current
   tools.
   For the Lean verifier (§8), what the end-to-end extraction theorems still assume about the
   executable verifier is exactly these steps: a good `chal1` (L3's `KOSGood`), fixed blocks for
   dead-leaf trees (L2), good `chal2`/`l` (L4's `hQS`, `hcomb`), and binding of the leaf
   commitments with accepted `chal3` landing in the chain's set (L1); `Verifier/Bridge/ChainRelations.lean`.
   §9 machine-checks the single-challenge part: for one chain with uniform independent `chal1`,
   `chal2`, `l`, the L3 and L4 failures have probability `≤ 2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸`
   (`Prob/ChainRelations.lean`), and, in the random-oracle model, the union over all `H₂¹`, `H₂²`,
   `H₂³` queries with the freshness of `chal2 ‖ dst`, for the executable verifier run against the
   oracle (`ROM/`): "accepts and extraction fails" has probability `≤ (q₁+1)·2⁻¹⁵⁰ +
   (q₂+1)·(ε_QS(n) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·max(d,1)·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`,
   also against one SHAKE oracle with L0's domain rule. Still on paper: the "same chain" step
   (`SameChain`, `ε_chain`: the data committed at the verifier's own queries are the accepted
   proof's chain; this includes `hclaim1`), L2 (`IsFixed`, ideal cipher, `ε_dead`), binding of
   the leaf commitments (`ε_bind`), and statement binding (`(q²+q)·2⁻²⁵⁶`).
2. **Code ↔ model is tested, not proved.** Each Lean model was written by reading the C++ and is
   tied to it by tests in `tests/voleith/test_lean_models.cpp` (and, when finished, the `Arith`
   cross-check). Compiler behaviour, memory safety and constant-time execution are out of scope.
3. **Arithmetization: small leftovers.** All five relations are modelled and proved (§6), and
   pqov's `ov_publicmap` is proved equal to the modelled public map over any commutative ring
   (`Arith/Pqov.lean`). The soundness corollaries are proved over an abstract field and
   instantiated at the concrete GF(2¹²⁸) with all hypotheses discharged (`Arith/ConcreteField.lean`,
   `EndToEnd/Concrete.lean`); the verifier's evaluators are proved to be the systems' values
   (`Verifier/Bridge/Relations.lean`), and agreement with the C++ is checked by `arith_vectors`. pqov's
   constant-time `ov_publicmap_ct`, which the code calls, is checked against `ov_publicmap` by the
   dumper, not modelled. The step "`l` is uniform because it is a random-oracle output" is proved in
   the random-oracle model (`ROM/Comb.lean`), for `l` read from the oracle table, which is where the
   verifier reads it (`ROM/Accept.lean`).
4. **Idealized models.** AES-128 is an ideal cipher (classical and quantum), SHAKE and Keccak-p are
   random oracles or random permutations. The Keccak-p[800,12] relations additionally need
   one-wayness/binding assumptions on a 12-round permutation that have little cryptanalysis.
5. **New assumptions.** The protocol proofs use protocol-specific UOV assumptions (one-more
   preimage resistance and variants; chosen-target unforgeability for Moussaka). The quantum
   protocol theorems need quantum-oracle versions of these that are new. Whether standard OMPR
   implies the τ-shift variant used for PomFRIT's tight bound is open.
6. **Quantum bounds stop at about 2⁵¹·⁷ queries.** Going further needs a point-level
   multi-collision lemma for the compressed ideal cipher (M1–M3 in `Q6-cipher-binding.md` §7.3);
   none is known. Parallel quantum queries are not treated.
7. **Zero knowledge on `main` is false** for PomFRIT, and the fix is on a branch. For Moussaka and
   Ratatouille on `main`, ZK rests on (PU), i.e. on the one-wayness of Keccak-p[800] in `r`
   (except towards a Moussaka Moderator that never sees `t`); the bad-event bound is in Lean
   (`ZK/Main.lean`, `ZK/Relations.lean`), but the hybrid chaining around it (H1–H4, the H5/H6
   coupling, the reduction of an oracle adversary to query functions) is paper. The QROM ZK bound
   is loose (2⁻¹⁹ at 2³⁰) until the 256-bit `rho` and salt are added.
   The protocol privacy theorems (`VoleMole/Privacy/`) take per-proof zero knowledge (the
   simulator is a function of the instance; in the random-oracle model it also programs the
   oracle, which the abstract specs do not expose) and hiding of `Com` (for the explicit
   reductions) as hypotheses, so they apply to the label-row fix; on `main` the joint (PU) hop over
   proofs sharing `r` replaces the per-proof hypothesis and is paper. For the executable Lean prover
   (§8) with dedicated label rows the hypothesis is discharged (`ZK/Exec.lean`,
   `Privacy/LeanProver.lean`, `docs/zk.md` §10.1) except for the **hop hypotheses** (`HopHyps`,
   `ZK/Hops.lean`, from which the tape hypothesis `TapeHyp` is proved: H1 `ε_rho`, the grinding
   answers `ε_grind`, BAVC hiding `ε_bavc`, H6 `ε_lab`; for PomFRIT `HopHyps2` and `TapeHyp2`,
   `ZK/TwoPhaseHops.lean`, plus the abort term). Each is a `Close` bound on a small experiment
   for a fixed hash record, an idealization as every statement against all distinguishers in
   `Privacy/Basic.lean`. With the hashed domain a uniform table the random-oracle ones are proved
   (`ZK/HopsROM.lean`, `ZK/HopsRead.lean`, `ZK/HopsH6.lean`: H1 and grinding exact, H1
   `≤ q₃·2⁻¹²⁸` and H6 `≤ (q₅ + 1)·2⁻¹²⁸` with oracle access), and composed with H4 into one
   bound for one record of independent tables and an ideal cipher (`ZK/HopsJoint.lean`,
   `zk_rom_ic`, for a proof-only cipher-parametric prover equal to the executable one at AES,
   with the distinguisher not reading `H₂³`; with `H₂³` visible, `zk_rom_h23`, for the executable
   prover in the ROM with BAVC hiding assumed, plus `Pr[GrindBad]`; and `zk_rom_ic_h23`,
   `ZK/HopsIC.lean`, with `H₂³` visible and the ideal cipher in the whole executable prover and
   verifier, plus `Pr[GrindBad]` and the honest recomputation's `≤ 4607` reads of the cipher;
   `Pr[GrindBad] ≤ 2⁻¹¹⁰` for the real tables and grinding parameters, `ZK/GrindNum.lean`,
   `zk_rom_ic_h23_num`, `zk_rom_h23_num`; several proofs and the privacy corollaries for
   Moussaka, Ratatouille and PomFRIT in this model: `Privacy/MoussakaRO.lean`,
   `Privacy/RatatouilleRO.lean`, `Privacy/PomFRITRO.lean` (the last on the two-phase
   `zk2_rom_ic_h23_num`, `ZK/TwoPhaseIC.lean`), with the programming-collision terms bounded in
   Lean, `ZK/CollideRO.lean`, `Privacy/*Delta.lean`, `*_lean_num`, and an adversary whose
   interaction does not read the tables; for Moussaka and Ratatouille also with an interaction
   that reads them, from zero knowledge for statements chosen from the tables, `ZK/AdaptRO.lean`,
   `zk_adaptive`, `Privacy/MoussakaRA.lean`, `anonymityRA_lean_num`,
   `Privacy/RatatouilleRA.lean`, `unlinkabilityRA_lean_num`, and for PomFRIT with an interaction
   that reads every table but `H₂³`, from the two-phase `zk2_adaptive`, `ZK/TwoPhaseAd.lean`,
   `Privacy/PomFRITRAGame.lean`, `blindnessRA_lean_num`); H4 is proved with the cipher a uniform table of
   uniform-function rows (`ZK/HopsH4Ideal.lean`, `hide_rom_query`: the GGM, leaf-commitment and
   leaf-PRG hybrids, `≤ 221·(4607 + q)·2⁻¹²⁸`), leaving the PRP/PRF switching of the hidden
   paths' rows and AES as an ideal cipher; and that SHAKE is a random oracle remains the
   modelling step. Every other side condition is proved (the witness encodings satisfy the
   systems, interpolation, `N_MASK`, the CRT certificate, BAVC and CRT completeness:
   `Privacy/MoussakaLean.lean`, `Privacy/RatatouilleLean.lean`, `Privacy/PomFRITLean.lean`,
   `Verifier/Bridge/BAVCComplete.lean`, `Verifier/Bridge/CrtComplete.lean`). The seed-XOF hop (the games
   draw the XOF's outputs uniformly), Moussaka's non-colluding mode (Thm 4b) and the quantum
   versions are not mechanized.
8. **Open deployment issues** found by the analysis and not yet fixed in the code: cross-protocol
   key reuse, Ratatouille spend binding, PomFRIT's `hash_to_target` domain byte and signature
   multiplicity, Moussaka nullifier squatting.

Some notes in `docs/` were written at different times and may contain status lines that later
notes superseded (for example, `security/pomfrit.md` lists quantum unforgeability as open, which
`extraction/Q7-qrom-multi-extraction.md` later addressed). Where they disagree, `extraction/README.md`
and this file are the most recent.
