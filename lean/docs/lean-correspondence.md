# Lean formalization of the FAEST v3 extraction arguments

This directory formalizes the deterministic cores of two straight-line extraction arguments for the
FAEST v3 proof system that vole-mole uses in `src/voleith.hpp`. The source is the design note
`lean/docs/sketch.md`. Everything is proved: there is no `sorry` and no `axiom`.

- `VoleMole/Extraction/`: the label-based QROM argument (sketch §§3–5, the Core Theorem).
- `VoleMole/SeedExtraction.lean`: the full-witness extractor with the seed PRG as a random oracle
  (sketch section "Full-witness straight-line extraction …"). See [below](#seed-based-extraction).

```sh
cd lean
lake exe cache get   # fetch the prebuilt Mathlib
lake build
```

## What is proved

| Sketch item | Lean | File |
| --- | --- | --- |
| L1 (fibres of a homomorphism) | `card_fiber_mul_card_range`, `card_fiber_mul_card_range_le` | `Gates.lean` |
| L2 (uniform hit probability) | `uniform_hit_le` | `Gates.lean` |
| Π_S as a fibre average | `avg`, `avg_eq_fiber_sum` | `Ops.lean` |
| L3.1 (Π_S idempotent, self-adjoint) | `avg_avg`, `sum_mul_avg` | `Ops.lean` |
| L3.2 (Π_S commutes with diagonals independent of S) | `avg_smul_left` | `Ops.lean` |
| L3.4 (P_Θ is an orthogonal projector) | `dproj_dproj`, `sum_mul_dproj`, `Model.isIdempotentElem_badOp`, `Model.isSelfAdjoint_badOp` | `Ops.lean`, `Product.lean`, `State.lean` |
| Abstract model (§3: φ, γ, τ, Valid, F_Θ/S_Θ, c_Θ, P_Θ, U, Im_U, ε) | `Model`, `Model.check`, `Model.sib`, `Model.bad`, `Model.disagree`, `ImU`, `Model.eps` | `Model.lean`, `Gates.lean` |
| L4 (‖P_Θ P_Θ'‖ ≤ \|Im_U\|⁻¹) | `Model.norm_badOp_comp_le`; on plain functions, `Model.sum_bad_bad_sq_le` | `Product.lean` |
| L5 (block Schur test) | `norm_avg_projections_le` (as stated in the sketch), `norm_sum_projections_le`, `schur_projections` | `Schur.lean` |
| L6 (state lemma) | `state_lemma` | `State.lean` |
| L7 (one game step) | `Model.game_step` | `State.lean` |
| ‖M‖ ≤ ε | `Model.norm_M_le_eps` | `State.lean` |
| **Core Theorem** | `Model.core`, `Model.core_normalized` | `State.lean` |
| §5 "Evaluation of ε" | `Model.eps_le_of_linear_gamma` | `Evaluation.lean` |

`Model.core_normalized` says: for a finite family `ψ_x : Ω → E` with `Σ_x ‖ψ_x‖² = 1` and
norm-preserving block-diagonal `W_{x,Θ}`,

```
Σ_x E_Θ ‖P_Θ W_{x,Θ} ψ_x‖² ≤ ‖M‖ ≤ ε.
```

## Where the formalization deviates from the sketch

These are differences in proof route or in generality. None of them weakens a statement.

- **L4 is proved without the four-block tensor factorization.** The proof applies Cauchy–Schwarz
  pointwise and bounds the sibling average of a check (`Model.avg_check_le`, which uses L1) twice,
  once per challenge. Self-adjointness of Π_{S_Θ'} moves the second average onto c_Θ. This avoids
  the `‖X ⊗ Y‖` step and any currying of Ω. The module docstring of `Product.lean` gives the
  outline.
- **L1 is applied to a homomorphism on all of Ω**, not on V^U. This is `Model.sibHom`, which reads
  the S_Θ-coordinates at Θ′'s forced labels. Its image contains Im_U. The literal V^U statement of
  L2 is also proved (`uniform_hit_le`), but L4 does not use it.
- **L5 is proved on vectors** (x_i := P_i v), with no block operator `X = [P_1 ⋯ P_m]`. The constant
  is the sketch's: no square root is lost. The core lemma `schur_projections` needs only
  self-adjointness and idempotence, not linearity.
- **The operators P_Θ and M act on real ℓ²(Ω)** (`EuclideanSpace ℝ Ω`). The Core Theorem only ever
  feeds M real profiles a_ψ, so this is all it needs. The sketch's ‖M‖ on complex ℓ²(Ω) equals the
  real one for a real matrix, but that is not formalized.
- **The register space E is any real normed space.** A complex inner product space qualifies through
  `InnerProductSpace.complexToReal`. Blocks need only preserve norms (`‖W H v‖ = ‖v‖`), as the
  sketch notes. They need not be linear or unitary.
- **L3.1's Π_S Π_S' = Π_{S∪S'} is not formalized**, because no step of this route uses it.
- **Validity is a `Finset Ch`, and invalid challenges get c_Θ = 0**, as the sketch recommends.
  `Model.eps` is a supremum over `Ch` of a term that is 0 off `Valid`. This equals the sketch's
  max over `Valid`, and is 0 when `Valid` is empty.

## Not formalized

These are out of scope by design (sketch §6):

- X1–X5: the purified oracle, DFM20 measure-and-reprogram, (A1) collision bounds, the classical
  completion, and the timing of the database measurement.
- The FAEST bound |Im_U| ≥ 2^{4ρ(U)}.
- The numerical value of ε_gate.

`eps_le_of_linear_gamma` stops at `ε ≤ |Ch|⁻¹ Σ_c |Im_{supp(Gc)}|⁻¹`.

## Correspondence with the code in this repository

The model was checked against `src/voleith.hpp` and faest-arch-opt v3.0.0 with this repo's patches.

**These match the code:**
- Labels L¹_e = L⁰_e ⊕ u[0..λ) are hashed with H₅ = H(iv ‖ e ‖ label ‖ 0x05). The prover hashes
  both labels (`vole_commit.inc:364,393`); the verifier hashes only the forced one.
- γ_e(Δ') = G[e]·Δ' is F₂-linear in the first n_Δ bits of chall₃, with no other decoding.
  `eps_le_of_linear_gamma` captures this.
- Each gate enters the check F₂-linearly through W_gate, and c_mult enters the target.
- T = F_{2^λ}^4 from the four direct masks.
- chall₃ must have its last w_grind bits zero, and the BAVC opening must succeed. Both are folded
  into `Valid`.

The Core Theorem itself is generic in V, T, φ, γ and Ch, so the parameter differences below do not
affect anything proved here. They do affect sketch §5–§6:

- **n_mask = d − 1 + 4, not 10.** The degree d is 9 for Moussaka and Ratatouille and 2 for PomFRIT,
  giving n_mask = 12 and 5. Patch 0002 widens the H₅ output to 32 bits; φ_e ignores the extra bits.
- **Parameters.** All relations use FAEST-EM-128f parameters: λ = 128, w_grind = 8, n_Δ = 120. Only
  that row of the sketch's table applies.
- **(X4) Extraction target: this is the main gap.** A sibling label reveals only u[0..λ), so the
  extractor recovers only the first 16 witness bytes. In FAEST these are the key, which determines
  the rest of the witness. In this repo's relations they are a prefix that does not determine the
  rest:
  - PomFRIT redeem: r ‖ s, where s is the UOV preimage.
  - Moussaka issue: r ‖ ctx_red ‖ nf ‖ ….
  - Moussaka redeem and Ratatouille have similar layouts.
  
  So the Bad bound (what is proved here) still holds, but "sibling in D ⇒ valid witness" does not.
  The extractor needs a different completion step for these relations.
- **(X3)** The EM parameter sets use the `aes_ctr` leaf hash, which has no u_hash = H₀(iv). The
  sketch's "statistically binding LeafHash" step therefore needs a computational binding term.
- **(X3)** In delayed-instance mode (PomFRIT), the instance is bound only in H₂², after the labels
  are fixed. (A1) still holds, since everything is a function of chall₂.
- **c_Θ relaxes the acceptance condition.** It models only the VOLE check. The QuickSilver masks also
  carry gate contributions into H₂³. Dropping that constraint enlarges c_Θ, so the bound remains
  sound.

## Seed-based extraction

`VoleMole/SeedExtraction.lean` formalizes the deterministic parts of the sketch's section
"Full-witness straight-line extraction with the seed PRG as a random oracle".

| Sketch item | Lean |
| --- | --- |
| Claim 4 (ii): every free tree is known and holds u\* | `free_tree_holds_witness` (hypotheses bundled in `Claim4Hyp`) |
| Claim 4 (iii): all trees fixed ⇒ \|A\| ≤ 1 | `card_le_one_of_all_fixed` |
| Claim 3, root counting: nonzero check polynomial of degree ≤ d_zk ⇒ \|A\| ≤ d_zk | `card_le_natDegree` |
| Theorem, per-chain case analysis: \|A\| ≤ d_zk, or \|A\| ≤ 1, or the extractor succeeds | `extraction_cases`, `accepting_card_le` |
| Random linear combination of constraints (not in the sketch; see below) | `card_combination_eq_zero`, `combination_prob` |

Model: a challenge is its blocks Δ' = (Δ_i)_i. The CRT lift `e : Π_i B_i →+ F` is injective, and
e_i = e ∘ single i. `known` is the set of trees with no dead leaf. Claim 2 (KOS) and Claim 4 (i)
enter as hypotheses. The field is arbitrary: the argument needs only that u^{(i)}[j] and u\*[j] are
bits, not characteristic 2.

Not formalized:
- Claim 1 (dead leaves never open) and Claim 2 (KOS): random-oracle arguments.
- The probability that the QuickSilver polynomial vanishes identically (ε_zk).
- The union bound over the Q chains.

### Correspondence with the code

The Claim 4 algebra matches faest-arch-opt v3.0.0 as configured by this repo's relations:
- τ = 17 blocks: 8 bits for tree 0 and 7 bits for trees 1–16. They partition Δ' (n_Δ = 120).
- c_i = u_0 ⊕ u_i on the ℓ witness rows, with c_0 = 0.
- The verifier forms Q_col = V_col + (u_i ⊕ c_i)·Δ'_b and lifts it with W_crt.
- Δ = W_crt·Δ' is the CRT lift, an F₂-linear bijection onto the polynomials of degree < 120 (so
  injective).
- d = u_0[0..ℓ) ⊕ w, so the candidate w^{(i)} = u_i[0..ℓ) ⊕ c_i ⊕ d.

The relations use FAEST-EM-128f's `aes_ctr` leaf commitment: com_{i,j} = PRG(k, iv, i+L−1)[0..2λ)
and sd = k. They are not EM one-way functions.

Gaps in the sketch's theorem:
- **Constraints depend on chall₂.** PomFRIT redeem, Moussaka redeem and Ratatouille spend check
  one combination Σ_k l_k (P(s) − t)_k = 0, with l = H(chall₂ ‖ dst). They do not check the M
  components. So "f(w) = 0 ⇒ R" is false as stated.
  - It holds except with probability 2⁻¹²⁸ (`combination_prob`) for a w fixed before chall₂.
    u\* + d is fixed before chall₂: u\* comes from committed data and d is hashed into H₂².
  - This adds about Q·2⁻¹²⁸ to the theorem.
  - The extractor should test R itself, not the chall₂-combination.
- **Arithmetization soundness is unproved.** Nothing shows that the QuickSilver constraints of the
  repo's relations imply the relations. This covers the bit constraints, the GF(256) → GF(2¹²⁸)
  embedding, the Keccak segment constraints, and Moussaka's selector bit. The tests only check
  completeness.
- **Error terms.** Use the EM error terms: Claim 1 is q·2^{−2λ} (not 2^{−3λ}), leaf binding is
  O(q²/2^{2λ}), and there is no q_{H₀}·2^{−λ} term.
- **PRF/PRP switching.** RO_P is really AES_k(iv ⊞ (ctr, 0, 0, twk)). Modelling it as a random
  function costs a PRP/PRF switching term, which is missing. Within a proof, (iv, twk) pairs are
  not distinct inputs, so the extractor should match AES inputs.
- **Mask top bits.** These come from PRG(root seed, iv, 2³¹ − 1) and are prover-chosen, not
  committed tree data. This doesn't affect Claim 4, which concerns witness rows only.

## Models validated by tests

Several models were matched to the C++ by reading. The tests in `tests/voleith/test_lean_models.cpp`
(`meson test lean-models`) compute each model's formula directly and compare it with the code:

- KOS VOLEHash (`Seed/KOS.lean`: `voleHashP`, `hornerPoly`, `voleHashL`, `kosValue`):
  `LeanModels.KosVoleHashMatchesModel`.
- ZKHash and χ (`Seed/QuickSilver.lean`: `blockedStep`, `blockedHash_eq_sum`, `horner_eq_sum`,
  `zkHash_eq_code`, `zkHash_eq_sum`): `LeanModels.BlockedHornerMatchesModel`,
  `LeanModels.ShortKeyHornerMatchesModel`, `LeanModels.ZkHashMatchesModel`.
- Check polynomial and top coefficient (`QSExpr.eval`, `QSExpr.eval_natDegree_coeff`, `maskPoly`,
  `checkPoly_natDegree_coeff`): `LeanModels.QuickSilverVerifierMatchesEvalModel`,
  `LeanModels.QuickSilverCheckPolynomialTopCoefficient`,
  `LeanModels.QuickSilverProverPolynomialMatchesVerifier`,
  `LeanModels.PomfritCheckPolynomialTopCoefficient`,
  `LeanModels.MoussakaIssueCheckPolynomialTopCoefficient`.
- Constraint counts n (L4 §7): `LeanModels.ConstraintCountsMatchNumConstraints`.
- Grinding (`ZK/Grinding.lean`: `IsFirstHit`, `card_isFirstHit`): `LeanModels.GrindingReturnsFirstHit`,
  `LeanModels.CheckFormatMatchesGrindingPredicate`.
- Domain separation (`Protocols/DomainSeparation.lean`, rows H2^1, H2^2, H2^3 and UOV combination):
  `LeanModels.ProofHashLengthsMatchDomainTable`, `LeanModels.CombinationHashMatchesDomainTable`.
