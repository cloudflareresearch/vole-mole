# QROM extraction lemma for FAEST v3 — Lean formalization notes

Oct 13, 2026 · @Bas Westerbaan

## Purpose and scope

The target of the Lean development is one theorem of finite-dimensional linear algebra (the **Core Theorem** in §4), which is the only part of the QROM straight-line extraction argument for FAEST v3 that is not a citation. Everything quantum-cryptographic (measure-and-reprogram, the purified random oracle, Fiat–Shamir chaining) enters only as the *shape* of the hypotheses of the Core Theorem, and is listed in §6 as an unformalized interface.

What the Core Theorem says, in one sentence: for an average of projectors of the form "a diagonal check on the forced oracle cells, times uniform-averaging on the sibling cells", the operator norm is at most ε\_gate, and this bounds the probability of the event "verifier accepts and no sibling label was queried" for any block-diagonal (oracle-respecting) evolution.

In scope for Lean:

- finite abelian groups V (label values) and T (check targets), homomorphisms φ\_e : V → T, a finite challenge set Ch;
- the Hilbert space of functions (L → V) → E for a finite-dimensional inner product space E, with the diagonal projector C\_Θ and the averaging projector Π\_S written as explicit finite sums (no tensor products);
- Lemmas L1–L7 and the Core Theorem, all elementary (counting fibres of a group homomorphism, Cauchy–Schwarz, a block Schur test, operator norms of products on disjoint coordinates).

Out of scope (stated as axioms or left to the paper): DFM20 Theorem 2, Zhandry's purified-oracle characterisation of "not in the database", the collision bounds behind assumption (A1), the classical completion from "a sibling is in the database" to "the extracted key is valid", and the numerical evaluation of ε\_gate from the FAEST tables.

Notation fixed throughout: E\_x f(x) is the average over a finite set, |X| the cardinality, ‖·‖ the ℓ²-norm on vectors and the operator norm on linear maps, and ⟨a, b⟩ the inner product (conjugate-linear in the first slot, though every inner product that matters below is between real nonnegative vectors).

## The cryptographic statement being supported

FAEST v3 (spec v3.0, 1 Sep 2026) generates its F\_{2^λ} VOLE masks with a CRT bilinear circuit of n\_mult AND gates, each evaluated free-XOR style: for gate e the signer forms two λ-bit labels L^0\_e and L^1\_e = L^0\_e ⊕ u\[0..λ) and queries H₅(iv, e, L^b\_e) for both b (VOLECommit, Fig. 6.2, lines 19–26). Here u\[0..λ) is the VOLE mask of the first λ witness rows and d\[0..λ) = u\[0..λ) ⊕ k, so the two labels of any single gate XOR to u\[0..λ) and hence reveal the key k.

The verifier, on a proof whose decoded challenge is Δ', queries H₅ at the *forced* label L^{γ\_e(Δ')}\_e of every gate, γ\_e(Δ') = G\[e\]·Δ' ∈ F₂, and uses the resulting n\_mask-bit values in the VOLE consistency check (VOLEReconstruct, Fig. 6.3, lines 23–30). The *sibling* label L^{1−γ\_e(Δ')}\_e is never touched by the verifier.

**Extractor E (straight-line, QROM).** Run the prover with H₅ as a compressed oracle. After it outputs its proof, measure the H₅ database D (at most q entries). For every entry x' ∈ D and every gate e, test k := d\[0..λ) ⊕ x' ⊕ L^{γ\_e(Δ')}\_e against the public key. Output the first hit. Cost: one run of the prover plus at most q·n\_mult evaluations of the one-way function.

E fails only on

```latex
\mathrm{Bad} := \{\text{verifier accepts}\} \wedge \{\text{no sibling label is in } D\}
```

because, when some sibling is in D, x' ⊕ L^{γ\_e}\_e = u\*\[0..λ) for the consistent VOLE value u\* furnished by the KOS lemma (spec §10.6), and the QuickSilver argument then makes k = d ⊕ u\*\[0..λ) a valid key except on the bad-challenge events for chall₁, chall₂, chall₃.

**Theorem (QROM Bad bound).** Under (A1) and (A2) of §6, for every prover making q quantum queries to H₂³ and any number of queries to H₅, H₂¹, H₂²:

```latex
\Pr[\mathrm{Bad}] \;\le\; (2q+1)^2 \cdot 2^{-w_{\mathrm{grind}}} \cdot \varepsilon_{\mathrm{gate}},
\qquad
\varepsilon_{\mathrm{gate}} := \mathop{\mathbb{E}}_{c \in \mathbb{F}_2^{n_\Delta}} 2^{-4\rho(\mathrm{supp}(Gc))},
```

where ρ(U) is the F₂-rank of the W\_gate columns indexed by U. The factor (2q+1)² is DFM20 Theorem 2; the rest is the Core Theorem of §4 applied with the data of §5. The c = 0 term contributes (2q+1)²·2^{−λ}.

**Resulting knowledge error** (straight-line, extraction probability ε − κ\_Q, not divided by q²):

```latex
\kappa_Q \;\approx\; (2q+1)^2\, 2^{-w_{\mathrm{grind}}}\, \varepsilon_{\mathrm{gate}}
\;+\; 8(q+3)^2\,(\varepsilon_{\mathrm{KOS}} + \varepsilon_{\mathrm{zk}} + d_{\mathrm{zk}} 2^{-\lambda})
\;+\; O(q^3/2^{2\lambda}).
```

The middle term is the Hülsing–Rijneveld–Song bound for finding a bad chall₁/chall₂/chall₃ by quantum search; the last term is the collision cost of discharging (A1).

## Abstract model

All crypto-specific structure is compressed into the following finite data; nothing below mentions AES, GGM trees or hash chaining.

**Finite data.**

- A finite set of gates 𝔼 and the label set L := 𝔼 × {0,1}. Write ℓ(e,b) for the label.
- A finite abelian group V (label values; FAEST: F₂^{n\_mask}) and a finite abelian group T (check targets; FAEST: F\_{2^λ}^4 as an F₂-space, or any supergroup).
- For each gate e a group homomorphism φ\_e : V → T (the contribution of gate e's hash value to the check). For U ⊆ 𝔼 write Im\_U := Σ\_{e∈U} φ\_e(V) ≤ T for the subgroup generated by the images.
- A finite challenge set Ch, a map γ : 𝔼 × Ch → {0,1} (which label is forced), a target map τ : Ch → T, and a validity predicate Valid ⊆ Ch (grinding and opening-size conditions; invalid challenges are rejected outright).
- For Θ ∈ Ch: the forced labels F\_Θ := {ℓ(e, γ\_e(Θ)) : e ∈ 𝔼} and the sibling labels S\_Θ := {ℓ(e, 1−γ\_e(Θ)) : e ∈ 𝔼}. These partition L, so (A2) holds by construction.
- For Θ, Θ' ∈ Ch the disagreement set U(Θ,Θ') := {e : γ\_e(Θ) ≠ γ\_e(Θ')}.

**Hilbert space.** Let Ω := (L → V) be the set of oracle truth tables and E a finite-dimensional complex inner product space (the prover's registers). The state space is

```latex
\mathcal{H} := \ell^2(\Omega; E) = \{\psi : \Omega \to E\},\qquad \langle \psi, \psi' \rangle := \sum_{H \in \Omega} \langle \psi(H), \psi'(H) \rangle_E .
```

This is the tensor product ℂ^Ω ⊗ E written without tensor products; for E = ℂ it is ℓ²(Ω). A pure product state |H⟩ ⊗ v is the function H' ↦ \[H' = H\] v. The uniform state on a single cell is |u⟩ := |V|^{−1/2} Σ\_{v∈V} |v⟩.

**Operators** (all are linear maps 𝓗 → 𝓗 acting on the Ω-argument only, i.e. of the form A ⊗ id\_E):

- *Diagonal check.* For Θ ∈ Ch let c\_Θ : Ω → {0,1} be

```latex
c_\Theta(H) := [\Theta \in \mathrm{Valid}] \cdot \Big[\sum_{e\in\mathbb{E}} \varphi_e\big(H(\ell(e,\gamma_e(\Theta)))\big) = \tau(\Theta)\Big],
```

and C\_Θ ψ := c\_Θ · ψ (pointwise). c\_Θ depends on H only through the coordinates in F\_Θ.

- *Averaging on a coordinate set.* For S ⊆ L define

```latex
(\Pi_S \psi)(H) := |V|^{-|S|} \sum_{H' \in \Omega,\; H'|_{L\setminus S} = H|_{L \setminus S}} \psi(H').
```

Π\_S is the orthogonal projector onto functions constant in the S-coordinates; it equals (|u⟩⟨u|)^{⊗S} ⊗ id on the rest. Π\_∅ = id.

- *Bad projector for Θ.* P\_Θ := C\_Θ Π\_{S\_Θ}. Since c\_Θ ignores the S\_Θ-coordinates, C\_Θ and Π\_{S\_Θ} commute and P\_Θ is an orthogonal projector (L3).
- *The averaged operator.* M := E\_{Θ∈Ch} P\_Θ.

**Norm profile of a state.** For ψ ∈ 𝓗 define a\_ψ : Ω → ℝ≥0 by a\_ψ(H) := the E-norm of ψ(H). Then the ℓ²(Ω)-norm of a\_ψ equals the 𝓗-norm of ψ.

**The quantity.** For a finite abelian group bound we use |Im\_U|^{−1}; in FAEST |Im\_U| ≥ 2^{4ρ(U)}. Define

```latex
\varepsilon := \max_{\Theta \in \mathrm{Valid}} \; \mathop{\mathbb{E}}_{\Theta' \in Ch} \Big( [\Theta' \in \mathrm{Valid}] \cdot |\mathrm{Im}_{U(\Theta,\Theta')}|^{-1} \Big),
```

with the convention ε := 0 if Valid is empty. In §5 this evaluates to 2^{−w\_grind}·ε\_gate.

**Block-diagonal evolutions.** A linear map W : 𝓗 → 𝓗 is *block-diagonal* if there is a family of linear maps W\_H : E → E, one per H ∈ Ω, with (Wψ)(H) = W\_H ψ(H). Standard-oracle queries (controlled on the oracle register) and unitaries on E alone are block-diagonal; compositions of block-diagonal maps are block-diagonal. If every W\_H is unitary then the norm profile is preserved: a\_{Wψ} = a\_ψ (L7 uses only this).

## Main theorem and lemma chain

The dependency order is L1 → L2 → L4, L3 → L4, L5 standalone, L6 standalone, L7 uses L6, Core Theorem uses L4, L5, L7. Every statement is over finite index sets; every proof is a finite sum manipulation.

**L1 (fibres of a homomorphism).** Let A, B be finite abelian groups and f : A → B a homomorphism. For every t ∈ B, the number of a ∈ A with f(a) = t is either 0 or |A| / |f(A)|; in particular it is at most |A| / |f(A)|.

*Proof.* The non-empty fibres are cosets of ker f, all of size |ker f| = |A| / |f(A)| by the first isomorphism theorem. ∎

**L2 (uniform hit probability).** Let U ⊆ 𝔼 and t ∈ T. Then

```latex
|V|^{-|U|} \cdot \#\Big\{ (v_e)_{e\in U} \in V^U : \textstyle\sum_{e\in U} \varphi_e(v_e) = t \Big\} \;\le\; |\mathrm{Im}_U|^{-1}.
```

*Proof.* Apply L1 to f : V^U → T, f((v\_e)) := Σ\_e φ\_e(v\_e), whose image is exactly Im\_U (it contains each φ\_e(V) and is contained in their sum). ∎

For U = ∅ the left side is \[t = 0\] ≤ 1 = |Im\_∅|^{−1}, consistent.

**L3 (structure of C\_Θ, Π\_S, P\_Θ).**

1. Π\_S is self-adjoint and idempotent (an orthogonal projector), and Π\_S Π\_{S'} = Π\_{S∪S'} = Π\_{S'} Π\_S.
2. If a diagonal operator D (multiplication by d : Ω → ℂ) has d independent of the S-coordinates, then D Π\_S = Π\_S D. More generally Π\_S commutes with every operator that acts trivially on the S-coordinates.
3. Diagonal operators commute with each other.
4. P\_Θ = C\_Θ Π\_{S\_Θ} is an orthogonal projector (by 1, 2 and F\_Θ ∩ S\_Θ = ∅).

*Proof.* 1: Π\_S is the orthogonal projector onto the subspace of functions constant along the S-coordinates (it averages over the fibres of the restriction Ω → (L∖S → V); the fibres partition Ω). Products of averaging operators over disjoint coordinate sets average over the union. 2: both sides send ψ to H ↦ d(H)·|V|^{−|S|} Σ\_{H'} ψ(H'), using d(H') = d(H) on the fibre. 4: C\_Θ is diagonal with c\_Θ depending only on F\_Θ; by 2 it commutes with Π\_{S\_Θ}; a product of two commuting orthogonal projectors is an orthogonal projector. ∎

**L4 (product of two bad projectors).** For Θ, Θ' ∈ Valid, with U := U(Θ,Θ'),

```latex
\| P_\Theta P_{\Theta'} \| \;\le\; |\mathrm{Im}_U|^{-1}.
```

If Θ ∉ Valid or Θ' ∉ Valid the left side is 0.

*Proof.* Partition the labels into four blocks: for e ∈ U put a\_e := ℓ(e, γ\_e(Θ)) (forced under Θ, sibling under Θ') and b\_e := ℓ(e, γ\_e(Θ')) (forced under Θ', sibling under Θ); for e ∉ U put f\_e := ℓ(e, γ\_e(Θ)) (forced under both) and s\_e := ℓ(e, 1−γ\_e(Θ)) (sibling under both). Write A, B, F, S for the four coordinate sets. Then

```latex
P_\Theta = C_\Theta\, \Pi_B\, \Pi_S, \qquad P_{\Theta'} = C_{\Theta'}\, \Pi_A\, \Pi_S,
```

with c\_Θ depending only on (A, F) and c\_{Θ'} only on (B, F). Using L3 (diagonal operators commute with each other; Π\_X commutes with anything trivial on X; Π\_S Π\_S = Π\_S),

```latex
P_\Theta P_{\Theta'} = \big(C_\Theta \Pi_A\big)\,\big(\Pi_B C_{\Theta'}\big)\,\Pi_S .
```

All three factors are block-diagonal with respect to the F-coordinates (C's are diagonal; Π\_A, Π\_B, Π\_S do not touch F), so the operator norm is the maximum over fixed values H|\_F =: f of the norm of the restricted operator. For fixed f, the first factor acts only on the A-coordinates, the second only on the B-coordinates, the third only on S, and A, B, S are pairwise disjoint; on a product space the norm of a product of operators acting on disjoint factors is the product of the norms. Hence

```latex
\|P_\Theta P_{\Theta'}\| \le \max_f \|C_{\Theta}^{(f)} \Pi_A\| \cdot \|\Pi_B C_{\Theta'}^{(f)}\| \cdot \|\Pi_S\| ,
```

where C^{(f)}\_Θ is multiplication by c\_Θ(·, f) on ℓ²(V^A). Now Π\_A = |u⟩⟨u| on ℓ²(V^A) (the uniform unit vector), so ‖C Π\_A‖ = ‖C|u⟩‖, and

```latex
\|C_\Theta^{(f)} |u\rangle\|^2 = |V|^{-|A|} \#\{ v \in V^A : c_\Theta(v,f) = 1 \} \le |\mathrm{Im}_U|^{-1}
```

by L2, because for fixed f the condition c\_Θ(v, f) = 1 reads Σ\_{e∈U} φ\_e(v\_{a\_e}) = τ(Θ) − Σ\_{e∉U} φ\_e(f\_e), a single target in T. Likewise ‖Π\_B C^{(f)}\_{Θ'}‖ = ‖C^{(f)}\_{Θ'}|u⟩‖ ≤ |Im\_U|^{−1/2}. With ‖Π\_S‖ ≤ 1 the product is at most |Im\_U|^{−1}. ∎

Remark for the formalisation: the two norm identities used are (i) for a diagonal D and the rank-one projector |u⟩⟨u|, ‖D|u⟩⟨u|‖ = ‖D|u⟩‖, and (ii) ‖X ⊗ Y‖ = ‖X‖·‖Y‖ for operators on disjoint coordinate blocks, which in the function picture is: if X acts on the A-argument and Y on the B-argument then ‖XY ψ‖ ≤ ‖X‖‖Y‖‖ψ‖ (only ≤ is needed).

**L5 (block Schur test for averages of projectors).** Let P\_1, …, P\_m be orthogonal projectors on a finite-dimensional Hilbert space. Then

```latex
\Big\| \frac{1}{m} \sum_{i=1}^m P_i \Big\| \;\le\; \max_i \frac{1}{m} \sum_{j=1}^m \|P_i P_j\| .
```

*Proof.* Let R := Σ\_i P\_i (positive semidefinite). Define the block row operator X := \[P\_1 ⋯ P\_m\] : 𝓗^m → 𝓗, X(ψ\_1,…,ψ\_m) = Σ\_j P\_j ψ\_j. Then X X\* = Σ\_j P\_j P\_j\* = R and X\*X is the block matrix with (i,j)-block P\_i\* P\_j = P\_i P\_j. Since ‖R‖ = ‖X X\*‖ = ‖X‖² = ‖X\*X‖, it suffices to bound ‖X\*X‖. For a block operator Y = (Y\_{ij}) the Schur test gives ‖Y‖ ≤ (max\_i Σ\_j ‖Y\_{ij}‖ · max\_j Σ\_i ‖Y\_{ij}‖)^{1/2}: for unit vectors φ = (φ\_i), χ = (χ\_j), |⟨φ, Yχ⟩| ≤ Σ\_{i,j} ‖Y\_{ij}‖ ‖φ\_i‖ ‖χ\_j‖ ≤ Σ\_{i,j} ‖Y\_{ij}‖ (s‖φ\_i‖² + ‖χ\_j‖²/s)/2 for any s > 0, and choosing s = (c/r)^{1/2} with r := max\_i Σ\_j ‖Y\_{ij}‖, c := max\_j Σ\_i ‖Y\_{ij}‖ gives (rc)^{1/2}. Here ‖P\_iP\_j‖ = ‖(P\_jP\_i)\*‖ = ‖P\_jP\_i‖, so r = c = max\_i Σ\_j ‖P\_iP\_j‖. Divide by m. ∎

Note the naive bound ‖R‖ = sup\_v Σ\_{i,j}⟨v, P\_iP\_j v⟩ only gives the square root of the right-hand side; the block Schur test is what removes it.

**L6 (state lemma).** Let S ⊆ L, let D be multiplication by d : Ω → {0,1} with d independent of the S-coordinates, and let ψ ∈ 𝓗 with norm profile a := a\_ψ. Then

```latex
\|D\,\Pi_S\, \psi\|^2 \;\le\; \langle a, D\,\Pi_S\, a \rangle_{\ell^2(\Omega)} .
```

*Proof.* Write H = (H\_S, H\_R) with R := L ∖ S. Then (Π\_S ψ)(H) = |V|^{−|S|} Σ\_{H'\_S} ψ(H'\_S, H\_R), and

```latex
\|D \Pi_S \psi\|^2 = \sum_{H_R}\ \sum_{H_S} d(H_R)\, |V|^{-2|S|} \Big\| \sum_{H'_S} \psi(H'_S,H_R) \Big\|_E^2
= \sum_{H_R} d(H_R)\, |V|^{-|S|} \Big\| \sum_{H'_S} \psi(H'_S,H_R) \Big\|_E^2 .
```

By the triangle inequality the E-norm of Σ\_{H'\_S} ψ(H'\_S, H\_R) is at most Σ\_{H'\_S} a(H'\_S, H\_R), and the right-hand side of the claim is exactly Σ\_{H\_R} d(H\_R) |V|^{−|S|} (Σ\_{H'\_S} a(H'\_S, H\_R))², the same computation with a in place of ψ, where the inner sum is a nonnegative real. ∎

**L7 (one game step).** Let ψ ∈ 𝓗 with profile a. Let W\_Θ (Θ ∈ Ch) be block-diagonal maps with unitary blocks. Then

```latex
\mathop{\mathbb{E}}_{\Theta} \| P_\Theta W_\Theta \psi \|^2 \;\le\; \langle a, M a \rangle \;\le\; \|M\|\, \|\psi\|^2 .
```

*Proof.* By L6 with D = C\_Θ, S = S\_Θ, applied to W\_Θ ψ, whose profile is a (block-diagonal unitary blocks preserve the profile): ‖P\_Θ W\_Θ ψ‖² ≤ ⟨a, P\_Θ a⟩. Average over Θ; M = E\_Θ P\_Θ is self-adjoint, so ⟨a, Ma⟩ ≤ ‖M‖‖a‖² = ‖M‖‖ψ‖². ∎

**Core Theorem.** Let (ψ\_x), x ∈ X, be a finite family of vectors in 𝓗 with Σ\_x ‖ψ\_x‖² = 1, and for each x and Θ let W\_{x,Θ} be a block-diagonal map with unitary blocks. Then

```latex
\sum_{x \in X} \mathop{\mathbb{E}}_{\Theta \in Ch} \| P_\Theta W_{x,\Theta} \psi_x \|^2 \;\le\; \|M\| \;\le\; \varepsilon .
```

*Proof.* The first inequality is L7 summed over x. For the second, L5 with the family (P\_Θ), Θ ∈ Ch, gives ‖M‖ ≤ max\_Θ E\_{Θ'} ‖P\_Θ P\_{Θ'}‖; by L4 each term is 0 unless both challenges are valid, and then at most |Im\_{U(Θ,Θ')}|^{−1}; the maximum over invalid Θ is 0. This is ε by definition. ∎

**Reading of the Core Theorem.** x ranges over the outcomes of the measure-and-reprogram measurement (the H₂³ input), ψ\_x is the unnormalised post-measurement state (prover registers plus purified oracle), W\_{x,Θ} is the prover's continuation after the challenge Θ is reprogrammed, and ‖P\_Θ W\_{x,Θ} ψ\_x‖² is the joint probability of outcome x, challenge Θ, acceptance, and all siblings being in the uniform state (= absent from the compressed database). The left side is therefore exactly Pr\[Bad\] in the simulated game, and DFM20 Theorem 2 multiplies by (2q+1)² to return to the real game.

## Instantiation to FAEST v3

With the identifications below, ε = 2^{−w\_grind}·ε\_gate, so the Core Theorem gives Pr\[Bad\] ≤ (2q+1)²·2^{−λ}·Σ\_{c ∈ F₂^{n\_Δ}} 2^{−4ρ(supp(Gc))}. The c = 0 term is (2q+1)²·2^{−λ}; the remaining sum must be O(1) for the bound to be meaningful, which is the single table-dependent condition to verify numerically.

**Identifications** (all from spec v3.0 §6, Figs. 6.2–6.3, and §4.2.3):

- 𝔼 = \[0..n\_mult), labels L^b\_e = (iv, e, L^b\_e) as H₅ inputs; (A2) holds because e is part of the input and L^1\_e = L^0\_e ⊕ u\*\[0..λ) with u\*\[0..λ) ≠ 0 (the case u\*\[0..λ) = 0 is handled by adding d\[0..λ) itself as a candidate).
- V = F₂^{n\_mask}, n\_mask = d\_zk + 3 = 10.
- T = F\_{2^λ}^4 viewed as an F₂-vector space of dimension 4λ (the four coordinates of the VOLE check Q̃ = Ṽ + ũ·Δ).
- φ\_e(h) := Σ\_m h\[m\]·κ\_{m,e} where κ\_{m,e} ∈ F\_{2^λ}^4 is the coefficient with which the gate q-share q̃\_{m,e} enters Q̃: for the four direct masks m ∈ {6,…,9}, κ\_{m,e} = W\_e placed in coordinate m − 6; for the six hashed masks m < 6, κ\_{m,e} = (coefficient of q̄\_m in VOLEHash\_{chall₁}) · W\_e. Here W\_e := ToField(W\_gate\[·, e\], λ) ∈ F\_{2^λ} (column e of W\_gate; nonzero for every gate, otherwise the gate would be dead). φ\_e is F₂-linear, i.e. a group homomorphism.
- Im\_U ⊇ (span\_{F₂}{W\_e : e ∈ U})^4 from the four direct masks alone, hence |Im\_U| ≥ 2^{4ρ(U)} with ρ(U) := rank\_{F₂}{W\_gate\[·,e\] : e ∈ U}. The hashed masks can only enlarge Im\_U; the bound ignores them.
- Ch = {0,1}^λ (the output space of H₂³). Valid := {Θ : Θ\[λ−w\_grind..λ) = 0 and the BAVC opening for DecodeAllChall3(Θ) has size ≤ T\_open}; enlarging Valid to all Θ with zero grinding bits only increases ε, so the bound below uses that superset. Δ' := Θ\[0..n\_Δ), n\_Δ = λ − w\_grind.
- γ\_e(Θ) := G\[e\]·Δ' (line 24 of VOLEReconstruct) for valid Θ, arbitrary otherwise.
- τ(Θ) := Ṽ + ũ·Δ − (the Wtree part of Q̃) − Σ\_e γ\_e(Θ)·Σ\_m c\_mult\[m,e\]·κ\_{m,e}; under (A1) this is a function of (x, Θ) only.
- U(Θ,Θ') = supp(G(Δ' ⊕ Δ'')) for the decoded Δ', Δ''.

**Evaluation of ε.** For valid Θ, E\_{Θ'}\[Θ' valid\]·|Im\_{U(Θ,Θ')}|^{−1} ≤ 2^{−w\_grind}·E\_{c ∈ F₂^{n\_Δ}} 2^{−4ρ(supp(Gc))} = 2^{−w\_grind}·ε\_gate, independent of Θ; hence ε ≤ 2^{−w\_grind}·ε\_gate and

```latex
\Pr[\mathrm{Bad}] \;\le\; (2q+1)^2 \cdot 2^{-\lambda} \cdot \sum_{c \in \mathbb{F}_2^{n_\Delta}} 2^{-4\rho(\mathrm{supp}(Gc))} .
```

**Numerical condition to verify from the tables.** Σ\_{c≠0} 2^{−4ρ(supp(Gc))} ≤ κ\_tab for a small constant κ\_tab, equivalently #{c : ρ(supp(Gc)) ≤ r} ≤ 2^{4r}·(geometric slack) for every r. This is a weight-distribution computation on the binary code generated by the columns of G (length n\_mult, dimension ≤ n\_Δ), combined with the rank of the corresponding W\_gate columns. The c that touch few gates are multiples of many of the extra CRT moduli M\_τ, …, M\_{s−1} (or hit only the place-at-infinity gates), so the check should enumerate those explicitly rather than sample. The tables G and W\_gate are in the `tables` folder of the reference implementation (spec §6.2, Appendix B).

| Parameter set | λ | w\_grind | n\_Δ | n\_mult | n\_mask |
| --- | --- | --- | --- | --- | --- |
| FAEST-128s | 128 | 7 | 121 | 312 | 10 |
| FAEST-128f | 128 | 8 | 120 | 312 | 10 |
| FAEST-192s | 192 | 12 | 180 | 504 | 10 |
| FAEST-192f | 192 | 8 | 184 | 504 | 10 |
| FAEST-256s | 256 | 6 | 250 | 696 | 10 |
| FAEST-256f | 256 | 8 | 248 | 704 | 10 |
| FAEST-EM-128s | 128 | 7 | 121 | 312 | 10 |
| FAEST-EM-128f | 128 | 8 | 120 | 312 | 10 |
| FAEST-EM-192s | 192 | 8 | 184 | 504 | 10 |
| FAEST-EM-192f | 192 | 8 | 184 | 504 | 10 |
| FAEST-EM-256s | 256 | 6 | 250 | 696 | 10 |
| FAEST-EM-256f | 256 | 8 | 248 | 704 | 10 |

Values from spec v3.0 Table 3.2; n\_Δ = λ − w\_grind. ε\_gate itself has not been computed (the tables were not reachable from this session).

## Interface to the unformalized cryptographic argument

Five external facts turn the Core Theorem into the QROM Bad bound and the Bad bound into a knowledge-error statement. Each is listed with the exact form in which the Core Theorem consumes it, so that a Lean development can state them as hypotheses (or `axiom`s in a sandbox file) with no quantum-information library.

**X1 — Purified oracle and database membership (Zhandry 2019).** A random oracle H₅ : L → V is simulated by the uniform superposition over truth tables, and a query is the unitary |H⟩|ℓ⟩|y⟩ ↦ |H⟩|ℓ⟩|y ⊕ H(ℓ)⟩, which is block-diagonal in the H-register. In the compressed-oracle basis, "cell ℓ is not in the database" is the projector |u⟩⟨u| on the ℓ-th cell. Hence Π\_{S\_Θ} is exactly the projector onto "no sibling of Θ is in D", and the state after any sequence of queries and prover-local unitaries, starting from |u⟩^{⊗L} ⊗ |init⟩, is of the form H ↦ ψ(H) ∈ E. *Consumed as:* the shape of 𝓗 and the block-diagonality of W\_{x,Θ}.

**X2 — Measure-and-reprogram, single round (Don–Fehr–Majenz 2020, Theorem 2).** For any q-query oracle algorithm A with output (x, z), the simulator S^A that measures a uniformly random query (or the output), outputs x, receives a uniform Θ, reprograms H₂³(x) := Θ and continues, satisfies for every predicate V: Pr\_Θ\[V(x, Θ, z) in the simulated game\] ≥ (2q+1)^{−2}·Pr\_H\[V(x, H(x), z) in the real game\], with no additive term. Here the other oracles G = (H₀, H₁, H₂¹, H₂²) and H₅ are held as purified registers inside A and included in z, and V is the projective measurement "checks pass ∧ all siblings in |u⟩". *Consumed as:* the sum over x of ‖P\_Θ W\_{x,Θ} ψ\_x‖², averaged over Θ, is the simulated-game Bad probability; the real-game Bad probability is at most (2q+1)² times it. *To double-check before relying on it:* DFM20 is stated for classical predicates on a classical output; the proof only runs A forward and applies V once at the end, so a projective V on a quantum z should go through unchanged, but this needs a line in the write-up.

**X3 — Assumption (A1), discharged by collision bounds.** The Core Theorem needs the labels L^b\_e and the target τ(Θ) to be functions of the measured H₂³ input x = (chall₂, msg₃, ctr) and Θ. In FAEST, chall₂ = H₂²(chall₁ ∥ msg₂) fixes msg₂ (hence ũ, Ṽ, d) and chall₁; chall₁ = H₂¹(ivpre ∥ msg₁) fixes msg₁ (hence c\_mult, com); com fixes the leaf commitments through H₁; LeafHash with u\_hash = H₀(iv) is statistically binding, so the leaf seeds and therefore the V-columns, the labels L^0\_e and u\*\[0..λ) are fixed. Failure requires a collision in H₂¹, H₂² or H₁ (quantum collision bound O(q³/2^{2λ}) for 2λ-bit outputs; H₂¹ and H₂² outputs are the challenge lengths, which must be checked) or a bad u\_hash (density 2^{−λ}, found by Grover with probability O(q²/2^{λ})). *Consumed as:* the maps Θ ↦ (c\_Θ, F\_Θ, S\_Θ) exist per x; the collision/binding failure is an additive term.

**X4 — Classical completion (sibling present ⇒ valid key).** If some sibling (iv, e, x') is in D, then x' = L^{1−γ\_e}\_e = L^{γ\_e}\_e ⊕ u\*\[0..λ), so the candidate equals d\[0..λ) ⊕ u\*\[0..λ) = w\*\[0..λ) for the consistent VOLE value u\* of the KOS lemma (spec §10.6) on the accepting set; the ℓ bit-constraints and the degree-7 QuickSilver identity then give f(w\*) = 0 unless chall₂ is a bad ZKHash seed or Θ is one of at most d\_zk roots. Finding a bad chall₁ (density ε\_KOS), chall₂ (ε\_zk) or Θ (d\_zk·2^{−λ}) is a Bernoulli search, bounded by 8(q+1)²·density (Hülsing–Rijneveld–Song, PKC 2016, Theorem 1). *Consumed as:* additive terms; none of this touches the Core Theorem.

**X5 — Measuring D after the prover's output.** The verifier's H₅ queries are classical; a standard-basis measurement of the compressed database commutes with subsequent classical queries, so the extractor may measure D before or after verification. With the sibling rule this does not matter anyway, since the verifier never queries a sibling (by (A2)). *Consumed as:* justification that Pr\[Bad\] is the right quantity for the extractor's failure.

**What is not needed.** No transition-capacity bound (Chung–Fehr–Huang–Liao), no Zhandry Lemma 5, no online-extractable simulator (Don–Fehr–Majenz–Schaffner 2022), no lifting theorem (Yamakawa–Zhandry), and no rewinding. The two features that make the argument go through are that the norm profile a\_ψ is fixed before Θ (X1 block-diagonality, used in L7) and that projecting a sibling onto |u⟩ forces a coherent average over its value (L6), after which the problem is the operator-norm computation L4–L5.

**Why the sibling rule rather than "both labels in D".** On a one-gate toy instance with a 1-bit mask, the quantum optimum of Pr\[accept ∧ ¬(both labels in D, measured before verification)\] is 0.854 against a classical 0.75; the excess comes from branches where the forced label is absent but the sibling present. The sibling event has quantum optimum equal to the classical optimum on all toy instances tried (mask widths 1–4), and L4 is tight: max\_τ ‖M‖ = ε on random small instances. The extractor's candidate set under the sibling rule is q·n\_mult instead of q².

## Full-witness straight-line extraction with the seed PRG as a random oracle (proof sketch)

Result: with the scheme unchanged, and with the AES-CTR seed expansion PRG modelled as a random oracle (on top of the spec's random oracles), there is a straight-line extractor for the *whole* committed witness w\* ∈ F₂^ℓ, hence for any statement proved with the FAEST v3 machinery. Classical ROM knowledge error ≈ Q·(d\_zk·2^{−λ} + ε\_KOS + ε\_zk) + collision terms. The extractor never needs the gate labels. The QROM version is not written here; see the remarks at the end.

**Model.** H₀, H₁, H₂ʲ, H₄, H₅ are random oracles as in the spec. Additionally PRG(sd, iv, twk; m) := RO\_P(sd, iv, twk)\[0..m) for a random oracle RO\_P : {0,1}^λ × {0,1}^{128} × {0,1}^{32} → {0,1}^∞. This replaces the spec's standard-model PRG assumption on AES by an idealisation of the same kind as the ROM for SHAKE; it is strictly stronger than what the spec assumes for plain FAEST, and implicit already in the Even–Mansour one-wayness of FAEST-EM. Only forward evaluations are modelled, so no ideal-cipher inverse queries are needed. All RO\_P uses in the spec are of this form: GGM node expansion (tweak = node index), LeafCommit (tweak = i + L − 1 for tree i), ConvertToVOLE seed expansion (tweak = i + 2^{31}) and the mask top bits.

**Statement framework.** The relation R is arithmetised as (Ext, Dec, f) with f of degree ≤ d\_zk including the ℓ bit-constraints, and constraint-sound: every w ∈ F₂^ℓ with f(w) = 0 has (x, Dec(w)) ∈ R. The witness w is arbitrary; nothing is assumed about which rows it occupies.

**Extractor E.** Record the prover's queries to RO\_P and H₁. When it outputs a proof π, run the verifier: this yields chall₃, the decoded (Δ₀, …, Δ\_{τ−1}), the opened seeds sd\_{i,j} for j ≠ Δ\_i, and the hidden-leaf commitments com\_{i,Δ\_i} from decom\_I. For each tree i:

1. Search the RO\_P query list for a query (k, iv, i + L − 1) with LeafHash(u\_hash, RO\_P(k, iv, i+L−1)\[0..4λ)) = com\_{i,Δ\_i} (FAEST), or with RO\_P(k, iv, i+L−1)\[0..2λ) = com\_{i,Δ\_i} (EM). If one exists, call tree i *known* and set sd\_{i,Δ\_i} := RO\_P(k, …)\[0..λ) (FAEST) or := k (EM).
2. For a known tree, E now has all N\_i seeds. It computes (u\_i, V\_i) := ConvertToVOLE(sd\_{i,0}, …, sd\_{i,N\_i−1}, iv, i+2^{31}; ℓ̂) by querying RO\_P itself, and the candidate w^{(i)} := u\_i\[0..ℓ) ⊕ c\_i ⊕ d, with c₀ := 0.
3. Output the first candidate w^{(i)} with f(w^{(i)}) = 0 (equivalently (x, Dec(w^{(i)})) ∈ R).

Cost: at most q\_P LeafHash evaluations per tree, then at most τ ConvertToVOLE runs and τ relation checks — about the cost of one verification plus one signing.

**Committed data and the accepting set.** Fix the prover's randomness and the oracles. The H₁ query list gives the unique (up to H₁ collisions) preimages of com and of each h\_i, hence the full family of leaf commitments (com\_{i,j}) the prover committed to before chall₁. Call leaf (i,j) *alive* if some RO\_P query (k, iv, i+L−1) made before the H₂¹ query that produced chall₁ has LeafHash(RO\_P(k, …)) = com\_{i,j} (resp. RO\_P(k, …)\[0..2λ) = com\_{i,j}), and *dead* otherwise. For an alive leaf, LeafHash binding (resp. the 2λ-bit collision bound) makes k, hence the seed and its ConvertToVOLE expansion, unique; for a dead leaf no seed is defined. The committed per-tree vectors u^{(i)}, V\_i, the masks and the labels are thus determined by the committed data on trees with no dead leaf; a tree with a dead leaf (i, j\_i) has committed data only for the other leaves.

Define the accepting set A as the set of challenges Δ (zero grinding bits) such that (a) every dead leaf is hidden, i.e. Δ\_i = j\_i for every tree i with a dead leaf, and (b) the VOLE check and the ZK check pass when Q(Δ), the masks and the gate shares are computed from the committed data and the prover's fixed (c\_mult, ũ, Ṽ, ã). A is a deterministic function of the committed data, the challenge seeds chall₁, chall₂ and the prover's messages; no prover behaviour on challenges other than the real one enters.

**Claim 1 (the real challenge lies in A).** If the verifier accepts π then Δ^π ∈ A, except with probability q·2^{−3λ} (FAEST) or q·2^{−2λ} (EM). *Sketch.* (b) holds because the verifier computes exactly the quantities in (b) from the opened seeds, which agree with the committed data by binding. For (a): opening a dead leaf means presenting k with LeafHash(RO\_P(k, …)) = com for a com that has no RO\_P preimage among the queries made before chall₁; since the prover sees chall₁ only after com is fixed, each later RO\_P query hits com with probability 2^{−3λ} (fresh 3λ-bit x₁ under LeafHash, resp. fresh 2λ-bit output). A tree with two or more dead leaves therefore never opens; a tree with one dead leaf opens only for Δ\_i = j\_i. ∎

**Claim 2 (consistency, from the spec).** Except with probability ε\_KOS over chall₁, there exist u\* ∈ F\_{2^λ}^ℓ and V\* with Q(Δ) = V\* + u\*·Δ for all Δ ∈ A, and likewise for the masks. (This is the spec's §10.6 lemma applied to the committed data; a tree with a dead leaf contributes a constant to Q on A, because its Δ\_i is constant on A and its opened seeds are fixed, so it is absorbed into V\*.)

**Claim 3 (QuickSilver).** Except with probability ε\_zk over chall₂, either f(u\* + d) = 0 — in particular u\* ∈ F₂^ℓ by the bit-constraints — or |A| ≤ d\_zk. (Degree-d\_zk polynomial identity; §4 of the classical argument.)

**Claim 4 (a free tree holds the witness).** Assume Claims 1–3 hold and f(u\* + d) = 0. Call tree i *fixed* if Δ\_i is constant on A and *free* otherwise. Then: (i) every tree with a dead leaf is fixed; (ii) every free tree is known and satisfies u^{(i)} = u\*; (iii) if all trees are fixed then |A| ≤ 1.

*Sketch.* (i) is (a) in the definition of A. (iii) is immediate. For (ii): for Δ ∈ A and a witness row j,

```latex
Q[j](\Delta) \;=\; V[j] + \sum_{i \in \mathrm{known}} u^{(i)}[j]\, e_i(\Delta) \;+\; (\text{constant on } A \text{ from fixed trees}),
```

where e\_i(Δ) := ToField(W\_crt · (Δ' restricted to block i)) is the lift of the i-th block, so Σ\_i e\_i(Δ) = Δ and W\_crt injective makes Δ' ↦ (e\_i(Δ))\_i an isomorphism onto its image. Comparing with Claim 2 and using u\*\[j\] ∈ F₂ and u^{(i)}\[j\] ∈ F₂:

```latex
\sum_{i \in D_j} e_i(\Delta) \;=\; \text{constant on } A, \qquad D_j := \{ i \text{ known} : u^{(i)}[j] \neq u^*[j] \},
```

because the coefficient u^{(i)}\[j\] − u\*\[j\] is 0 or 1. By injectivity of the lift, Σ\_{i∈D\_j} e\_i(Δ) constant on A means Δ' restricted to the blocks in D\_j is constant on A, i.e. every tree in D\_j is fixed. Hence a free tree i is in no D\_j, so u^{(i)}\[j\] = u\*\[j\] for every j. A free tree has no dead leaf by (i), so it is known. ∎

The step that makes this work is that both the tree values and u\* are *bits*: with field coefficients the sum Σ\_i δ\_{i,j} e\_i(Δ) could be constant on a large set through cancellation across trees, and the extractor could not point at a single tree. The bit-constraints in the QuickSilver proof remove that case.

**Theorem (classical ROM + PRG as RO, Fiat–Shamir).** Let the prover make q queries in total and Q queries to H₂³ (counting grinding attempts). Then Pr\[verifier accepts ∧ E fails\] ≤ Q·(d\_zk + 1)·2^{−λ} + Q·(ε\_KOS + ε\_zk) + q·2^{−3λ} + O(q²/2^{2λ}) + q\_{H₀}·2^{−λ}, and E runs in time about one verification plus one signing plus q·τ LeafHash evaluations.

*Sketch.* Fix a chain (msg₁, chall₁, msg₂, chall₂, msg₃, chall₃) whose chall₃ is one of the Q outputs of H₂³ used by the prover. Discard chains where Claim 1's event or an H₁/LeafHash/EM collision occurs (the additive collision and binding terms) and chains with a bad chall₁ or chall₂ (Q·(ε\_KOS + ε\_zk), since each chain's seeds are fresh when queried). On a surviving chain, either f(u\* + d) ≠ 0 and |A| ≤ d\_zk, or all trees are fixed and |A| ≤ 1, or some free known tree gives w^{(i)} = u\* + d, which satisfies f = 0, and E succeeds. In the first two cases the chain's chall₃ lands in A with probability at most (d\_zk + 1)·2^{−λ}, as chall₃ is uniform in {0,1}^λ and A contains only zero-grinding challenges. Union over the Q chains. ∎

**What changed relative to the label-based extractor.** Nothing in the scheme. The extractor reads seeds instead of labels; the price is the random-oracle model for the seed-expansion PRG. The gate hash H₅ plays no role, so the ε\_gate condition on the tables disappears, and the extracted object is the full u\*, not u\*\[0..λ).

**QROM status (not done).** All oracles, RO\_P included, are random oracles, so the compressed-oracle framework applies without ideal-cipher machinery. The expected structure is: measure the RO\_P and H₁ databases after the prover outputs; "dead leaf" becomes "no database entry maps to com", and opening a dead leaf is bounded by a Zhandry Lemma-5-type argument (output consistent with an unqueried cell, 2^{−3λ} per leaf); Claims 2–3 are the spec's round-by-round events, handled as in its §10.11 with the HRS16-type factor 8(q+1)²; Claim 4 is classical linear algebra on the measured data and needs no change. The piece requiring care is that the committed data is fixed by the chain *before* chall₁ while the prover may expand seeds *after* chall₁; classically this is harmless because RO\_P values are independent of chall₁, and in the QROM it should be handled by the same round-by-round argument the spec already uses for its own proof, but this has not been written out.

## Lean / Mathlib formalization plan

The recommended route avoids tensor products and matrices entirely: states are functions Ω → E, operators are explicit finite sums, and operator norms are taken on `ContinuousLinearMap`s between finite-dimensional spaces. Estimated size: the whole chain is a few hundred lines once the representation is settled; L5 and L4 are the two pieces that need care.

**Representation choices.**

- Index types: `E : Type` with `[Fintype E] [DecidableEq E]` for gates; labels `L := E × Bool`; `V T : Type` with `[AddCommGroup V] [Fintype V] [AddCommGroup T] [Fintype T] [DecidableEq T]`; `φ : E → V →+ T` (`AddMonoidHom`); challenges `Ch : Type` `[Fintype Ch]`, `γ : E → Ch → Bool`, `τ : Ch → T`, `Valid : Ch → Prop` decidable.
- Truth tables `Ω := L → V`, finite via `Pi.fintype`.
- State space `𝓗 := EuclideanSpace ℂ Ω` for E = ℂ, or `PiLp 2 (fun _ : Ω => E)` with `E` an `InnerProductSpace ℂ E` `[FiniteDimensional ℂ E]` for the general case. Start with E = ℂ for L1–L5 (they do not involve E) and introduce E only for L6–L7; L6 with general E is a one-line triangle inequality over the inner sum.
- Operators as `𝓗 →L[ℂ] 𝓗` built from linear maps via `LinearMap.toContinuousLinearMap`. Define `diag (c : Ω → ℂ)`, `avg (S : Finset L)` (the averaging operator Π\_S written as a sum over the restriction fibre), and `P Θ := diag (cΘ Θ) ∘L avg (S Θ)`.
- Norm: `‖·‖` on `𝓗 →L[ℂ] 𝓗` is the operator norm (`ContinuousLinearMap.opNorm`); use `ContinuousLinearMap.opNorm_le_bound` and `ContinuousLinearMap.le_opNorm`. For the projector facts, `IsIdempotentElem` and `ContinuousLinearMap.adjoint` on `EuclideanSpace` (`LinearMap.IsSymmetric`) are available; `ContinuousLinearMap.opNorm_le_one_of_isIdempotent`-type facts may need to be proved locally (norm of an orthogonal projector is ≤ 1: from ‖Pv‖² = ⟨v, Pv⟩ ≤ ‖v‖‖Pv‖).
- Averages: `Finset.expect` (Mathlib `Mathlib.Algebra.BigOperators.Expect`) or just `(Finset.univ.sum f) / Fintype.card`.

**Proof obligations.**

| Item | Statement | Mathlib ingredients | Effort |
| --- | --- | --- | --- |
| L1 | fibres of `f : A →+ B` have size ≤ | A | / |
| L2 | uniform hit probability ≤ | Im\_U | ⁻¹ |
| L3 | Π\_S orthogonal projector; commutation with diagonals independent of S; Π\_S Π\_{S'} = Π\_{S∪S'} | finite sums over fibres of restriction `Ω → (L∖S → V)`; `Finset.sum_comm`, `Function.update` / `Pi` lemmas; adjointness via `EuclideanSpace.inner` unfolding | medium (bookkeeping) |
| L4 | ‖P\_Θ P\_Θ'‖ ≤ | Im\_U | ⁻¹ |
| L5 | block Schur test for projectors | `ContinuousLinearMap.adjoint`, ‖X‖² = ‖X\*X‖ (`ContinuousLinearMap.norm_adjoint_comp_self`), Cauchy–Schwarz, the AM–GM step with free s > 0 | medium–high |
| L6 | state lemma | triangle inequality `norm_sum_le` inside a double sum; `Finset.sum_fiberwise` | low |
| L7 | profile preserved by block-diagonal unitaries; ⟨a, Ma⟩ ≤ ‖M‖‖a‖² | `LinearIsometry.norm_map`, `real_inner_le_norm`/`ContinuousLinearMap.le_opNorm` | low |
| Core | assembly | `Finset.sum_le_sum`, `Finset.expect` monotonicity | low |

**Suggested file layout.**

1. `Gates.lean`: finite data, `Im U`, L1, L2.
2. `Ops.lean`: 𝓗, `diag`, `avg`, `P`, L3.
3. `Schur.lean`: L5 as a standalone statement about a `Fin m → (𝓗 →L[ℂ] 𝓗)` family of projectors (reusable; worth upstreaming).
4. `Product.lean`: L4.
5. `State.lean`: L6, L7, Core Theorem with E general.
6. `FAEST.lean`: the instantiation of §5 as definitions plus the inequality |Im\_U| ≥ 2^{4ρ(U)} (optional; can be left as a numeric input), and the interface hypotheses X1–X5 as a `structure` of assumptions.

**Pitfalls and conventions.**

- Keep everything real where possible: a\_ψ is real nonnegative and L5–L7 only ever use ⟨a, Ma⟩ with a real; working over `ℝ` for `Schur.lean` is fine since the final application restricts to real vectors, but the projectors live on a complex space. Simplest: prove L5 over a general `RCLike 𝕜` field.
- Invalid challenges are handled by making `cΘ Θ = 0`, so P\_Θ = 0 and all products vanish; no separate case analysis in L5.
- (A2) is structural: forced and sibling label sets are complements in L, so Π\_{S\_Θ} and C\_Θ act on disjoint coordinates by construction. Do not model labels as arbitrary strings.
- The L4 factorisation needs the four-block partition A, B, F, S of L to be definable from (Θ, Θ') with decidable membership; define it via `γ` and use `Finset.filter`.
- Operator norm of `avg S` is 1 (not needed; ≤ 1 suffices). Operator norm of a diagonal with entries in {0,1} is ≤ 1.
- For the "product on disjoint blocks" step in L4, the cleanest formal route is to prove for operators X, Y acting on disjoint coordinate sets A, B of Ω: ‖XYψ‖ ≤ ‖X‖‖Y‖‖ψ‖ by writing 𝓗 ≅ ℓ²(V^A; ℓ²(V^B; ℓ²(rest))) via currying (`Equiv.piCongrLeft` / `Equiv.sumArrowEquivProdArrow`) and applying the one-block bound slice by slice. Avoid `TensorProduct` of normed spaces.
- L5's constant: the statement is ‖(1/m)Σ P\_i‖ ≤ max\_i (1/m)Σ\_j ‖P\_iP\_j‖, not its square root; the naive ⟨v, Rv⟩ expansion gives only the square root (see note under L5), so the Schur test over the block operator X\*X is essential.

**Sanity checks before formalising.** Run the script in the appendix; it checks L4 (tight), L5 and L6 numerically on random toy instances with |V| = 2, 3–4 gates, 2–3 challenge bits.

## Appendix: numerical sanity-check script

The script builds the full matrices on a toy instance (|V| = 2, 4 gates, 3 challenge bits; dimension 2^8 = 256) and checks L4 (as an exact equality on these instances, i.e. tightness), L5 and L6. Output on the two instances run: `max ||P P'|| * |Im_U| = 1.0`, `||E P|| = 0.4268 <= Schur 0.5 <= eps 0.75` (3 gates, 2 bits) and `||E P|| = 0.2152 <= Schur 0.25 <= eps 0.3438` (4 gates, 3 bits). Larger |V| makes the dense Π\_S construction slow; rewrite it as a Kronecker product if you want |V| = 4 or more.

```python
#!/usr/bin/env python3
"""Numerical sanity checks for the core operator-norm lemma.

Toy instance: gates E, label-value group V = F_2^v, target group T = F_2^t,
homomorphisms phi_e : V -> T (random F_2-matrices), challenge set Ch = F_2^d,
gamma_e(Theta) = <G[e], Theta>, target tau(Theta) random.

Hilbert space l^2(V^L), L = E x {0,1}.  P_Theta = C_Theta * Pi_{S_Theta}.
Checks:
  (1) ||P_Theta P_Theta'|| <= 1/|Im_U|,  U = {e : gamma_e(Theta) != gamma_e(Theta')}
  (2) ||E_Theta P_Theta|| <= max_Theta E_Theta' ||P_Theta P_Theta'||  (block Schur)
  (3) state lemma: ||(C Pi_S (x) I) psi||^2 <= <a, C Pi_S a>, a(H) = ||chi_H||
"""
import itertools, numpy as np
rng = np.random.default_rng(1)

nE, v, t, d = 4, 1, 3, 3            # gates, bits per label value, target bits, challenge bits
E = range(nE); L = [(e, b) for e in E for b in (0, 1)]
V = list(itertools.product((0, 1), repeat=v)); nV = len(V)
Ch = list(itertools.product((0, 1), repeat=d))
phi = [rng.integers(0, 2, size=(t, v)) for _ in E]        # phi_e : V -> T
G = rng.integers(0, 2, size=(nE, d))
tau = {Th: rng.integers(0, 2, size=t) for Th in Ch}
gamma = lambda e, Th: int(np.dot(G[e], Th) % 2)

Hs = list(itertools.product(range(nV), repeat=len(L)))     # truth tables H : L -> V (as indices)
idx = {H: i for i, H in enumerate(Hs)}; N = len(Hs)
lab = {l: i for i, l in enumerate(L)}

def C_mat(Th):
    diag = np.zeros(N)
    for H in Hs:
        s = np.zeros(t, dtype=int)
        for e in E:
            s = (s + phi[e] @ np.array(V[H[lab[(e, gamma(e, Th))]]])) % 2
        diag[idx[H]] = float(np.array_equal(s, tau[Th]))
    return np.diag(diag)

def Pi_mat(S):                       # average over coordinates in S (orthogonal projector)
    M = np.zeros((N, N))
    for H in Hs:
        for H2 in Hs:
            if all(H[i] == H2[i] for i in range(len(L)) if i not in S):
                M[idx[H], idx[H2]] = 1.0 / nV ** len(S)
    return M

P = {}
for Th in Ch:
    S = [lab[(e, 1 - gamma(e, Th))] for e in E]
    P[Th] = C_mat(Th) @ Pi_mat(S)
    assert np.allclose(P[Th] @ P[Th], P[Th]) and np.allclose(P[Th], P[Th].T)

opn = lambda M: np.linalg.norm(M, 2)
def im_size(U):
    vecs = {tuple(np.zeros(t, dtype=int))}
    for e in U:
        vecs = {tuple((np.array(a) + phi[e] @ np.array(x)) % 2) for a in vecs for x in V}
    return len(vecs)

# (1)
worst = 0.0
for Th in Ch:
    for Th2 in Ch:
        U = [e for e in E if gamma(e, Th) != gamma(e, Th2)]
        worst = max(worst, opn(P[Th] @ P[Th2]) * im_size(U))
print("(1) max ||P P'|| * |Im_U| =", round(worst, 6), "(must be <= 1)")

# (2)
Mavg = sum(P.values()) / len(Ch)
schur = max(np.mean([opn(P[Th] @ P[Th2]) for Th2 in Ch]) for Th in Ch)
eps = max(np.mean([1 / im_size([e for e in E if gamma(e, Th) != gamma(e, Th2)]) for Th2 in Ch]) for Th in Ch)
print("(2) ||E P|| =", round(opn(Mavg), 6), "<= Schur bound", round(schur, 6), "<= eps", round(eps, 6))
assert opn(Mavg) <= schur + 1e-9 <= eps + 1e-9

# (3) state lemma with H_A = C^3
dA = 3
Th = Ch[1]; S = [lab[(e, 1 - gamma(e, Th))] for e in E]
chi = rng.normal(size=(N, dA)) + 1j * rng.normal(size=(N, dA)); chi /= np.linalg.norm(chi)
lhs = np.linalg.norm((C_mat(Th) @ Pi_mat(S)) @ chi) ** 2        # (C Pi (x) I) psi
a = np.linalg.norm(chi, axis=1)
rhs = a @ (C_mat(Th) @ Pi_mat(S)) @ a
print("(3) ||(C Pi x I) psi||^2 =", round(lhs, 6), "<= <a, C Pi a> =", round(rhs, 6))
assert lhs <= rhs + 1e-9
print("all checks passed")
```

Sources: FAEST v3.0 specification (faest.info/faest-spec-v3.0.pdf, 1 Sep 2026), §2.1, §4.2.3, §6, Fig. 6.2–6.3, Table 3.2; Don–Fehr–Majenz, "The Measure-and-Reprogram Technique 2.0", CRYPTO 2020, Theorem 2; Zhandry, "How to Record Quantum Queries", CRYPTO 2019; Hülsing–Rijneveld–Song, PKC 2016, Theorem 1.
