import VoleMole.SeedExtraction

/-!
# Q2: bookkeeping for the QROM Fiat–Shamir lift

Paper proof: `lean/docs/extraction/Q2-qrom-fiat-shamir.md`. This file checks the parts of the lift that are
finite-dimensional linear algebra or arithmetic. Nothing here is quantum-specific: states are
vectors in a normed space, oracle queries and adversary steps are linear maps, and the "bad"
database property is an idempotent operator `Pi`.

## Results

* `telescope` (paper §4.1, Lemma T, step 1, a version of CFHL Lemma 5.6): if every query moves
  at most `c s` of norm from `¬P` into `P`, and adversary steps are isometries commuting with `P`,
  then `‖P ψ_T‖ ≤ Σ_{s<T} c s`.
* `proj_mul_mul_compl_le`, `compl_mul_mul_proj_le` (Lemma T, step 2): for a projector `Π` with
  `‖1 − Π‖ ≤ 1`, both transition operators `Π O (1 − Π)` and `(1 − Π) O Π` have norm at most
  `‖[O, Π]‖`. This is why the lift needs no monotonicity of the bad property: removal transitions
  are bounded by the same commutator as insertion transitions.
* `conj_commutator_le` (Lemma T, step 3; DFMS Lemma 3.3 / Q1 Lemma 3.1 structure): if `O`
  commutes with `Π` (a query is controlled on the register `Π` reads), then
  `‖[F O F, Π]‖ ≤ 2‖[F, Π]‖` for contractions `F`, `O`.
* `card_B3_le` (paper §5, H₂³ transition): reuses `accepting_card_le` unchanged. On a chain where
  L1–L4 hold, the H₂³ answers that are accepted while the extractor fails number at most
  `max d 1`.
* `main_term_eq`, `main_term_at_2_50`, `main_term_at_2_64` (paper §7): the dominant term
  `8·(5q·2^{−64})² = 200·q²·2^{−128}` and its values.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed.QROM

section Telescope

variable {𝕜 E : Type*} [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- **Telescoping (CFHL Lemma 5.6, vector form).** `ψ (s+1) = U s (O s (ψ s))`. The adversary step
`U s` is an isometry commuting with `P`; the query `O s` does not increase `‖P ·‖` on `Im P`; and the
transition `P O (1 − P)` applied to the current state has norm `≤ c s`. Then
`‖P ψ_T‖ ≤ Σ_{s<T} c s` whenever `P ψ_0 = 0`. -/
theorem telescope (P : E →ₗ[𝕜] E) (O U : ℕ → E →ₗ[𝕜] E) (ψ : ℕ → E)
    (hψ : ∀ s, ψ (s + 1) = U s (O s (ψ s)))
    (hU : ∀ s v, ‖U s v‖ = ‖v‖) (hcomm : ∀ s v, P (U s v) = U s (P v))
    (hOP : ∀ s v, ‖P (O s (P v))‖ ≤ ‖P v‖)
    (c : ℕ → ℝ) (hc : ∀ s, ‖P (O s (ψ s - P (ψ s)))‖ ≤ c s) (h0 : P (ψ 0) = 0) :
    ∀ T, ‖P (ψ T)‖ ≤ ∑ s ∈ range T, c s := by
  intro T
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [hψ, hcomm, hU, Finset.sum_range_succ]
    have hsplit : O T (ψ T) = O T (ψ T - P (ψ T)) + O T (P (ψ T)) := by
      rw [← map_add, sub_add_cancel]
    calc ‖P (O T (ψ T))‖
        = ‖P (O T (ψ T - P (ψ T))) + P (O T (P (ψ T)))‖ := by rw [hsplit, map_add]
      _ ≤ ‖P (O T (ψ T - P (ψ T)))‖ + ‖P (O T (P (ψ T)))‖ := norm_add_le _ _
      _ ≤ c T + ‖P (ψ T)‖ := add_le_add (hc T) (hOP T _)
      _ ≤ c T + ∑ s ∈ range T, c s := by linarith
      _ = ∑ s ∈ range T, c s + c T := add_comm _ _

end Telescope

section Commutator

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Insertion transitions.** For an idempotent `Π` with `‖1 − Π‖ ≤ 1`,
`‖Π O (1 − Π)‖ ≤ ‖O Π − Π O‖`. -/
theorem proj_mul_mul_compl_le (Pi O : E →L[𝕜] E) (hPi : Pi * Pi = Pi) (h1 : ‖1 - Pi‖ ≤ 1) :
    ‖Pi * O * (1 - Pi)‖ ≤ ‖O * Pi - Pi * O‖ := by
  have key : Pi * O * (1 - Pi) = -((O * Pi - Pi * O) * (1 - Pi)) := by
    have : O * Pi * (1 - Pi) = 0 := by
      rw [mul_assoc, mul_sub, mul_one, hPi, sub_self, mul_zero]
    calc Pi * O * (1 - Pi) = Pi * O * (1 - Pi) - O * Pi * (1 - Pi) := by rw [this, sub_zero]
      _ = -((O * Pi - Pi * O) * (1 - Pi)) := by noncomm_ring
  rw [key, norm_neg]
  calc ‖(O * Pi - Pi * O) * (1 - Pi)‖ ≤ ‖O * Pi - Pi * O‖ * ‖1 - Pi‖ := norm_mul_le _ _
    _ ≤ ‖O * Pi - Pi * O‖ * 1 := by gcongr
    _ = ‖O * Pi - Pi * O‖ := mul_one _

/-- **Removal transitions.** For an idempotent `Π` with `‖1 − Π‖ ≤ 1`,
`‖(1 − Π) O Π‖ ≤ ‖O Π − Π O‖`. In the QROM this bounds the amplitude with which a query *forgets*
a database entry that the bad property needs to be absent, so the bad property need not be
monotone. -/
theorem compl_mul_mul_proj_le (Pi O : E →L[𝕜] E) (hPi : Pi * Pi = Pi) (h1 : ‖1 - Pi‖ ≤ 1) :
    ‖(1 - Pi) * O * Pi‖ ≤ ‖O * Pi - Pi * O‖ := by
  have key : (1 - Pi) * O * Pi = (1 - Pi) * (O * Pi - Pi * O) := by
    have : (1 - Pi) * Pi * O = 0 := by
      rw [sub_mul, one_mul, hPi, sub_self, zero_mul]
    calc (1 - Pi) * O * Pi = (1 - Pi) * O * Pi - (1 - Pi) * Pi * O := by rw [this, sub_zero]
      _ = (1 - Pi) * (O * Pi - Pi * O) := by noncomm_ring
  rw [key]
  calc ‖(1 - Pi) * (O * Pi - Pi * O)‖ ≤ ‖1 - Pi‖ * ‖O * Pi - Pi * O‖ := norm_mul_le _ _
    _ ≤ 1 * ‖O * Pi - Pi * O‖ := by gcongr
    _ = ‖O * Pi - Pi * O‖ := one_mul _

/-- **Conjugated queries.** A compressed query is `F O F` with `O` controlled on (hence commuting
with) the register that `Π` reads, and `F` the swap `⊥ ↔ u`. Then `‖[F O F, Π]‖ ≤ 2‖[F, Π]‖`. With
DFMS Lemma 3.3 / Q1 Lemma 3.1 (`‖[F, Π]‖ ≤ √(2ρ)` for a relation of density `ρ`), this gives the
per-query transition bound `2√(2ρ)` of Lemma T. -/
theorem conj_commutator_le (F O Pi : E →L[𝕜] E) (hOPi : O * Pi = Pi * O) (hF : ‖F‖ ≤ 1)
    (hO : ‖O‖ ≤ 1) :
    ‖F * O * F * Pi - Pi * (F * O * F)‖ ≤ 2 * ‖F * Pi - Pi * F‖ := by
  have key : F * O * F * Pi - Pi * (F * O * F)
      = F * O * (F * Pi - Pi * F) + (F * Pi - Pi * F) * O * F := by
    have : F * O * Pi * F = F * Pi * O * F := by
      rw [mul_assoc F O Pi, hOPi, ← mul_assoc]
    calc F * O * F * Pi - Pi * (F * O * F)
        = F * O * (F * Pi - Pi * F) + (F * O * Pi * F - Pi * (F * O * F)) := by noncomm_ring
      _ = F * O * (F * Pi - Pi * F) + (F * Pi * O * F - Pi * (F * O * F)) := by rw [this]
      _ = F * O * (F * Pi - Pi * F) + (F * Pi - Pi * F) * O * F := by noncomm_ring
  rw [key]
  set C := F * Pi - Pi * F
  have hFO : ‖F * O‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg F, norm_nonneg O])
  calc ‖F * O * C + C * O * F‖ ≤ ‖F * O * C‖ + ‖C * O * F‖ := norm_add_le _ _
    _ ≤ ‖F * O‖ * ‖C‖ + ‖C‖ * ‖O‖ * ‖F‖ := by
        gcongr
        · exact norm_mul_le _ _
        · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 1 * ‖C‖ + ‖C‖ * 1 * 1 := by gcongr
    _ = 2 * ‖C‖ := by ring

end Commutator

section B3

open VoleMole.SeedExtraction

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- **The H₂³ transition (paper §5.5), from `accepting_card_le` unchanged.** On a chain where the
hypotheses of L6 hold, the extractor's success does not depend on the H₂³ answer (it uses the
known trees, which are the same for every accepted challenge). So the answers in `Z` (zero
grinding bits) that are accepted while the extractor fails number at most `max d_zk 1`. -/
theorem card_B3_le {Ch : Type*} {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)}
    {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (sat : (J → F) → Prop) (d : J → F)
    (dzk : ℕ) (hclaim3 : sat (uStar + d) ∨ A.card ≤ dzk)
    (hbits : sat (uStar + d) → ∀ j, uStar j = 0 ∨ uStar j = 1)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A)
    [Decidable (∃ i ∈ known, sat (fun j => bit (u i j) + d j))] :
    #{x ∈ Z | acc x ∧ ¬ ∃ i ∈ known, sat (fun j => bit (u i j) + d j)} ≤ max dzk 1 := by
  rcases accepting_card_le h sat d dzk hclaim3 hbits Z δ hδ acc hclaim1 with hext | hcard
  · have : #{x ∈ Z | acc x ∧ ¬ ∃ i ∈ known, sat (fun j => bit (u i j) + d j)} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun _ _ hx => hx.2 hext
    omega
  · refine le_trans (Finset.card_le_card ?_) hcard
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩

end B3

section Numbers

/-- The dominant term of the main theorem, for `λ = 128`, with the largest per-query coefficient
`√d + 2 = 5` (`d = 9`, combined slot; paper §7): `8·(5q·2^{−64})² = 200·q²·2^{−128}`. -/
theorem main_term_eq (q : ℝ) : 8 * (5 * q / 2 ^ 64) ^ 2 = 200 * q ^ 2 / 2 ^ 128 := by
  ring

/-- At `q = 2^50` the dominant term is below `2^{−20}`. -/
theorem main_term_at_2_50 : 200 * ((2 : ℝ) ^ 50) ^ 2 / 2 ^ 128 ≤ 1 / 2 ^ 20 := by
  norm_num

/-- At `q = 2^64` the dominant term is `200 > 1`: the bound is vacuous there, as any QROM bound
of the form `Ω(q²·d·2^{−λ})` must be (Grover search over the grinding counter). -/
theorem main_term_at_2_64 : 200 * ((2 : ℝ) ^ 64) ^ 2 / 2 ^ 128 = 200 := by
  norm_num

/-- The KOS term stays small at `q = 2^64`: `8·q²·ε_KOS ≤ 8·2^{128}·2^{−153} = 2^{−22}`. -/
theorem kos_term_at_2_64 : 8 * ((2 : ℝ) ^ 64) ^ 2 * (1 / 2 ^ 153) = 1 / 2 ^ 22 := by
  norm_num

/-- The free-iv `multi` bound of the AES instantiation, `(32/9)·q_E³/(N − 1)`, at `q_E = 2^{30}`
is below `2^{−36}`; at `q_E = 2^{40}` it exceeds `2^{−7}` (paper §6.3). -/
theorem multi_free_at_2_30 :
    32 / 9 * ((2 : ℝ) ^ 30) ^ 3 / (2 ^ 128 - 1) ≤ 1 / 2 ^ 36 := by
  norm_num

theorem multi_free_at_2_40 :
    1 / 2 ^ 7 ≤ 32 / 9 * ((2 : ℝ) ^ 40) ^ 3 / (2 ^ 128 - 1) := by
  norm_num

/-- `Σ_{s<n} √s ≤ n·√n`, used for the database-size-dependent terms (`(32/9)` uses the sharper
`(2/3)n^{3/2}`, which the paper cites). -/
theorem sum_sqrt_le (n : ℕ) : ∑ s ∈ range n, Real.sqrt s ≤ n * Real.sqrt n := by
  calc ∑ s ∈ range n, Real.sqrt s ≤ ∑ _s ∈ range n, Real.sqrt n := by
        refine Finset.sum_le_sum fun s hs => Real.sqrt_le_sqrt ?_
        exact_mod_cast (Finset.mem_range.1 hs).le
    _ = n * Real.sqrt n := by simp

end Numbers

end VoleMole.Seed.QROM
