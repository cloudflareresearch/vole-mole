import VoleMole.ZK.IdealCipherPt

/-!
# A chain of hops with expected charges, all charged in the first world

A one-proof zero-knowledge chain goes from the real world to the simulated one through a few
hybrids. With point-level charges (`ZK/HopsH4Pt.lean`, `ZK/HopsROMExp.lean`, `ZK/HopsH6Exp.lean`)
each hop costs a constant plus a multiple of the **expected** number of the distinguisher's reads
at the proof's points, but the expectation is taken in **different** worlds: H1 and H4 in the
world before the hop, H6 over the simulated proof's fields. The joint many-proof step
(`Theft.hyb_hop_exp`) needs every charge in the **real** world.

The worlds are close, and the charges are bounded functions of the view whose level sets are
events the hops apply to; so (as in `IC.puncturePt_real` and `Theft.joint_le`) each expectation is
within `M·S` of the real one, `S` the chain's total, and solving for `S`:

    |real − sim| ≤ (a + b + c + k_A·E_0[Y_A] + k_B·E_0[Y_B] + k_C·E_0[Y_C]) / (1 − k_B·M_B − k_C·M_C)

(`chain3_le`). Worlds are given by their event probabilities (`μ : (V → Prop) → ℝ`), so that the
hybrids may live on different coin spaces; expectations are layer cakes (`lcE`), equal to `exP`
of the charge through the view for a world `pr α (F ∘ view)` (`lcE_pr`).

* `lcE`, `lcE_pr`, `lcE_sub_le`: layer-cake expectations of an event functional.
* **`chain3_le`**: three hops, charged in the worlds before, before and after them, moved to the
  first world.
* `abs_pr_prod_sub_le_exP`, `pr_prod_le_exP`: hop and bad-event bounds that vary with a shared
  coordinate, averaged (`abs_pr_prod_sub_le`, `pr_prod_le` with `exP` in place of a constant).
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-! ## Layer-cake expectations of event functionals -/

section LC

variable {V : Type*}

/-- **The expectation of `Y` under the world `μ`**, as a layer cake up to `M`:
`Σ_{l < M} μ[l < Y]`. For `Y ≤ M` and `μ` the law of a view, it is `E[Y]` (`lcE_pr`). -/
noncomputable def lcE (μ : (V → Prop) → ℝ) (Y : V → ℕ) (M : ℕ) : ℝ :=
  ∑ l ∈ range M, μ (fun v => l < Y v)

/-- For the law of a view on a uniform tape, the layer cake is the expectation. -/
theorem lcE_pr {α : Type*} [Fintype α] (t : α → V) (Y : V → ℕ) {M : ℕ} (hY : ∀ a, Y (t a) ≤ M) :
    lcE (fun F => pr α (fun a => F (t a))) Y M = exP α (fun a => (Y (t a) : ℝ)) :=
  (exP_eq_sum_pr (fun a => Y (t a)) hY).symm

/-- Layer cakes under close worlds are close: `M` times the distance on the level sets. -/
theorem lcE_sub_le (μ ν : (V → Prop) → ℝ) (Y : V → ℕ) (M : ℕ) {δ : ℝ}
    (h : ∀ l < M, |μ (fun v => l < Y v) - ν (fun v => l < Y v)| ≤ δ) :
    lcE μ Y M ≤ lcE ν Y M + M * δ := by
  unfold lcE
  have : ∑ l ∈ range M, μ (fun v => l < Y v) - ∑ l ∈ range M, ν (fun v => l < Y v) ≤ M * δ := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ l ∈ range M, (μ (fun v => l < Y v) - ν (fun v => l < Y v))
        ≤ ∑ _l ∈ range M, δ := Finset.sum_le_sum fun l hl =>
          (le_abs_self _).trans (h l (Finset.mem_range.1 hl))
      _ = M * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

end LC

/-! ## Three hops, charged in the first world -/

section Chain

variable {V : Type*}

/-- **A chain of three hops with expected charges, all moved to the first world.** Worlds
`μ₀ … μ₃` on views `V`; `Adm` the events the hops apply to, containing the level sets of the
charges. Hop `0 → 1` costs `a + k_A·E_0[Y_A]`, hop `1 → 2` costs `b + k_B·E_1[Y_B]` and hop
`2 → 3` costs `c + k_C·E_3[Y_C]` (expectations as layer cakes up to `M_A`, `M_B`, `M_C`). If
`k_B·M_B + k_C·M_C < 1`, then for every admissible event

    |μ₀ F − μ₃ F| ≤ (a + b + c + k_A·E_0[Y_A] + k_B·E_0[Y_B] + k_C·E_0[Y_C])
                     / (1 − k_B·M_B − k_C·M_C). -/
theorem chain3_le (Adm : (V → Prop) → Prop) (μ0 μ1 μ2 μ3 : (V → Prop) → ℝ)
    (YA YB YC : V → ℕ) (MA MB MC : ℕ) {a b c kA kB kC : ℝ} (hkB : 0 ≤ kB) (hkC : 0 ≤ kC)
    (hAA : ∀ l, Adm (fun v => l < YA v)) (hAB : ∀ l, Adm (fun v => l < YB v))
    (hAC : ∀ l, Adm (fun v => l < YC v))
    (h01 : ∀ F, Adm F → |μ0 F - μ1 F| ≤ a + kA * lcE μ0 YA MA)
    (h12 : ∀ F, Adm F → |μ1 F - μ2 F| ≤ b + kB * lcE μ1 YB MB)
    (h23 : ∀ F, Adm F → |μ2 F - μ3 F| ≤ c + kC * lcE μ3 YC MC)
    (hsmall : kB * MB + kC * MC < 1) (F : V → Prop) (hF : Adm F) :
    |μ0 F - μ3 F| ≤ (a + b + c + kA * lcE μ0 YA MA + kB * lcE μ0 YB MB + kC * lcE μ0 YC MC) /
      (1 - kB * MB - kC * MC) := by
  set eA := a + kA * lcE μ0 YA MA
  set eB := b + kB * lcE μ1 YB MB
  set eC := c + kC * lcE μ3 YC MC
  set S := eA + eB + eC
  have hA0 : 0 ≤ eA := (abs_nonneg _).trans (h01 _ (hAA 0))
  have hB0 : 0 ≤ eB := (abs_nonneg _).trans (h12 _ (hAB 0))
  have hC0 : 0 ≤ eC := (abs_nonneg _).trans (h23 _ (hAC 0))
  -- the distances to the first world
  have d1 : ∀ G, Adm G → |μ1 G - μ0 G| ≤ S := fun G hG => by
    rw [abs_sub_comm]; have := h01 G hG; linarith
  have d3 : ∀ G, Adm G → |μ3 G - μ0 G| ≤ S := fun G hG => by
    have h1 := h01 G hG; have h2 := h12 G hG; have h3 := h23 G hG
    have t1 := abs_sub_le (μ0 G) (μ1 G) (μ2 G)
    have t2 := abs_sub_le (μ0 G) (μ2 G) (μ3 G)
    rw [abs_sub_comm]
    linarith
  have hB : lcE μ1 YB MB ≤ lcE μ0 YB MB + MB * S := lcE_sub_le _ _ _ _ fun l _ => d1 _ (hAB l)
  have hC : lcE μ3 YC MC ≤ lcE μ0 YC MC + MC * S := lcE_sub_le _ _ _ _ fun l _ => d3 _ (hAC l)
  have hS : S ≤ a + b + c + kA * lcE μ0 YA MA + kB * lcE μ0 YB MB + kC * lcE μ0 YC MC +
      (kB * MB + kC * MC) * S := by
    have := mul_le_mul_of_nonneg_left hB hkB
    have := mul_le_mul_of_nonneg_left hC hkC
    simp only [S, eA, eB, eC] at *
    nlinarith
  have hden : 0 < 1 - kB * MB - kC * MC := by linarith
  have hfin : |μ0 F - μ3 F| ≤ S := by
    have := d3 F hF; rwa [abs_sub_comm] at this
  refine hfin.trans ?_
  rw [le_div_iff₀ hden]
  nlinarith

end Chain

/-! ## Averaging bounds that vary with a shared coordinate -/

section Avg

variable {α β β' : Type*} [Fintype α] [Fintype β] [Fintype β']

/-- **Hop lemma with a bound that depends on the shared coordinate**: averaged. -/
theorem abs_pr_prod_sub_le_exP [Nonempty α] (P : α × β → Prop) (Q : α × β' → Prop)
    (η : α → ℝ) (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ η a) :
    |pr (α × β) P - pr (α × β') Q| ≤ exP α η := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα, exP]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => h a)

/-- The same with the shared coordinate second. -/
theorem abs_pr_prod_sub_le_exP' {α' : Type*} [Fintype α'] [Nonempty β] (P : α × β → Prop)
    (Q : α' × β → Prop) (η : β → ℝ)
    (h : ∀ b, |pr α (fun a => P (a, b)) - pr α' (fun a => Q (a, b))| ≤ η b) :
    |pr (α × β) P - pr (α' × β) Q| ≤ exP β η := by
  rw [← pr_equiv (Equiv.prodComm β α), ← pr_equiv (Equiv.prodComm β α')]
  exact abs_pr_prod_sub_le_exP _ _ η h

/-- **A bad event's probability, bounded for each shared coordinate**: averaged. -/
theorem pr_prod_le_exP (P : α × β → Prop) (η : α → ℝ) (h : ∀ a, pr β (fun b => P (a, b)) ≤ η a) :
    pr (α × β) P ≤ exP α η := by
  rw [pr_prod, exP]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

/-- An expectation over a product, as the average of the inner expectations. -/
theorem exP_prod (f : α × β → ℝ) :
    exP (α × β) f = exP α (fun a => exP β (fun b => f (a, b))) := by
  simp only [exP]
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div,
    mul_comm]

lemma exP_div (f : α → ℝ) (c : ℝ) : exP α (fun a => f a / c) = exP α f / c := by
  simp only [exP]
  rw [← Finset.sum_div, div_div, div_div, mul_comm]

lemma exP_add (f g : α → ℝ) : exP α (fun a => f a + g a) = exP α f + exP α g := by
  simp only [exP]
  rw [Finset.sum_add_distrib, add_div]

lemma exP_mul_left (c : ℝ) (f : α → ℝ) : exP α (fun a => c * f a) = c * exP α f := by
  simp only [exP]
  rw [← Finset.mul_sum, mul_div_assoc]

end Avg

end VoleMole.ZK.IC
