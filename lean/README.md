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
```

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

**Statement (with the fix).** Adaptive, multi-proof, statistical-in-the-witness zero knowledge in
the classical ROM [paper] + [Lean] `ZK/`. Against quantum distinguishers [paper], with a bound of
about 2⁻¹⁹ at 2³⁰ queries and 2³⁰ proofs. The dominant term, Q_P·√(q/2¹²⁸), is the standard
adaptive-reprogramming loss and has no known matching attack. A 128-bit `rho` does admit a real
multi-target Grover attack around 2⁵⁰ queries. Both are removed by a 256-bit `rho` and a salt in
chal1/chal2 (recommended, not implemented).

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

### 8. A Lean VOLEitH verifier (accepts all KAT proofs, both layouts) — `VoleMole/Verifier/`

Goal: an executable Lean verifier that accepts the real C++ proofs (the KAT files contain them) and
rejects mutated ones, built from the same models the proofs use. Plan and milestones:
`docs/verifier-plan.md`. Checked by `lake exe verifier_vectors` against vectors from
`tests/voleith/dump_verifier_vectors.cpp`.

| Milestone | Status |
|---|---|
| SHAKE, AES-128, faest-arch-opt's CTR PRG | done; FIPS-197 and C++ vectors |
| One-tree BAVC (GGM) reconstruction and `vole_commit_check` | done; reproduces a real Moussaka issuance proof byte for byte |
| Proof parsing, `chal1`, ConvertToVOLE, CRT VOLE (lifted rows, masks, lifted Δ) | done; on one real proof of each of the five relations, every value matches the C++ byte for byte |
| KOS VOLE check and `chal2` (`KOS.lean`) | done; matches the C++ for all five relations |
| QuickSilver (`QuickSilver.lean`) | done; the verifier's value for a degree-`d` constraint is `Δ^d·f(q/Δ)`, so the proved `Arith/*` generators are evaluated unchanged at `q·Δ⁻¹`; the UOV gadget is evaluated directly over arrays (`UovEval.lean`), proved equal to the generator's value |
| Full verification (`Verify.lean`, `Relations.lean`, `Kats.lean`) | done; all 18 proofs in the three KAT files are accepted (3 PomFRIT, 6 Moussaka, 9 Ratatouille), with statements built in Lean from the KAT fields and the `Spec/*` instance encoders; 51 mutations (each proof field, each instance field, PomFRIT's refresher) are rejected. Runtime about 25 s (was about 5 min): the UOV public maps are evaluated over arrays with `Combination`'s tables (`UovEval.lean`, ≈ 10 ms per key, proved equal to the `Arith/*` evaluators), `GF128.mul` runs as an unboxed loop proved equal to it (`@[csimp]`, ≈ 0.3 µs), and AES uses round tables |
| CRT tables (`CrtData.lean`, `CrtGen.lean`, `CrtSearch.lean`) | done: `W_crt` and `M_tree` are recomputed from the moduli; F, G, W_tree, W_gate (copied from faest-arch-opt's build output into `CrtData`, which the verifier reads) are checked against their defining bilinear identity on all basis pairs and regenerated by a port of `vole_mult_tables.py --preset 128f` (tree moduli, cost search and portfolio, bilinear algorithms including Montgomery's formula and the F₄ towers, interpolation, pruning), which reproduces them exactly |
| UOV keys | done: pqov's key generation (`generate_keypair_pkc`, uov-Ip-pkc: `SHAKE256(sk_seed)` → `pk_seed ‖ O`, `P1 ‖ P2` by AES-128-CTR, `P3 = UT(M + Mᵀ)` with `M = Oᵀ(P1·O + P2)`, `Keygen.lean`, about 0.08 s per key) and `expand_pk` in Lean; the KAT runners derive every key from the compact secret keys. The 64 generated compressed keys equal the C++ ones in `lean/vectors/verifier_keys.txt`, and the expanded `test`/`alt61`/`alt62` keys equal `uov_keys.txt` (both optional cross-checks) |
| Label-rows variant (`Params.labelRows`) | done; the same verifier, with the flag set, accepts all 18 KAT proofs of branch `voleith-label-rows` (KATs regenerated there, PomFRIT's too) and rejects the same 51 mutations; every intermediate value of the five dumped proofs matches |
| Bridge theorems (`Verifier/Bridge/*`) | partly: proved that the executable CTR blocks are `Seed.Commitments.ctrInput` (and its role separation applies to the verifier's tweaks), that the VOLE check is `Seed.kosValue`, that the QuickSilver check value is `EndToEnd.qsCheck` + `Seed.maskPoly` (including the `Δ^d·f(q/Δ)` shortcut), and that acceptance gives `EndToEnd`'s accepting equation at that transcript. The field embedding is constructed (`Bridge/Concrete.lean`, from `Arith/GFField.lean`) and the theorems that assumed one (`accept_hacc`, `map_constraintKeys`, `map_gfInv`, `map_voleHashReceiver`) are restated at it without that hypothesis. Per relation (`Bridge/Relations.lean`): with `GF128` itself as the field, each relation's evaluator is `System.values` of its `Arith/*` system (`betaFast = beta`, cached UOV coefficients unchanged, the array-based UOV evaluation of `UovEval.lean` equal to the generator's), so acceptance by the executable `verify` gives `EndToEnd`'s accepting equation for that system over GF(2¹²⁸) with no hypothesis (`moussakaIssue_accept`, …, `pomfritVerify_accept`), i.e. `hacc` of `*_extract_gf128` at that Δ. |
| Bridge across Δ (`Bridge/Lift.lean`, `Columns.lean`, `Chain.lean`, `ChainRelations.lean`) | done, modulo the probabilistic steps: ConvertToVOLE and the CRT step are read as functions of the challenge blocks with the commitments fixed (the steps take `Δ` as bits and the commitments as arguments: `convertToVoleAt`, `crtReconstructAt`). Proved: each column is `V_{i,b} + Δ_{i,b}·u^{(i)}` with `u^{(i)} = c_i + Σ_j PRG(K_{i,j})` (the hidden leaf's key never read), so each lifted witness row is `C_r + Σ_i u^{(i)}_r·e_i(Δ_i)` (`resp_row`); the executable lift `Δ ↦ Σ Δ_c W_CRT[c]` is additive and injective (`lift_injective`, an explicit left inverse checked by `decide +kernel`); an opening that reconstructs the committed keys makes the run equal to the committed response (`crtReconstruct_eq_respAt`). On a chain (fixed `chal1`, `h_V`, `z`; `chal2` determined before Δ), `chain_claim4` gives `Claim4Hyp` and the accepting equation on all of `A` with one remainder `maskPoly d a b ã z` (masks affine by L3); `onChain_of_accept` puts every accepted proof of the chain in `A` with `Δ = chal3`; `*_extract_chain` (five relations) apply `*_extract_gf128`. Assumed: `KOSGood` for `chal1` (L3), `IsFixed` for dead-leaf trees (L2), `hQS`/`hcomb` (L4), `hδ`/`hclaim1` and binding of the leaf commitments (L1) |

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
   dumper, not modelled. The step "`l` is uniform because it is a random-oracle output" is on paper.
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
7. **Zero knowledge on `main` is false**, and the fix is on a branch. The QROM ZK bound is loose
   (2⁻¹⁹ at 2³⁰) until the 256-bit `rho` and salt are added.
8. **Open deployment issues** found by the analysis and not yet fixed in the code: cross-protocol
   key reuse, Ratatouille spend binding, PomFRIT's `hash_to_target` domain byte and signature
   multiplicity, Moussaka nullifier squatting.

Some notes in `docs/` were written at different times and may contain status lines that later
notes superseded (for example, `security/pomfrit.md` lists quantum unforgeability as open, which
`extraction/Q7-qrom-multi-extraction.md` later addressed). Where they disagree, `extraction/README.md`
and this file are the most recent.
