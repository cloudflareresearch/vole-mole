import VoleMole.ZK.HopsROM
import VoleMole.ZK.IdealCipherPt

/-!
# Hop H1 with an expected charge

`Privacy.abs_pr_hidden_one_le` (the core of hop H1, `h3_rom_query`) bounds the advantage of a
distinguisher that reads a random table at most at `q` keys, against a uniform programmed point,
by `q / |C|`, `q` a worst-case budget. The bad event is the distinguisher reading the table at the
point; the point is uniform and independent of its view in the ideal world, so the bound holds
with the **expected** number of keys read (`pr_mem_indep_exp`):

* `abs_pr_hidden_one_exp`: `≤ E_ideal[#keys read] / |C|`;
* **`abs_pr_hidden_one_real`**: for a consistent reader (`hQc`) of at most `qm` keys, with the
  expectation in the **real** experiment: `≤ E_real[#keys read] / (|C| − qm)` (the expectations
  of the two worlds differ by at most `qm` times their distance, which the bound itself bounds);
* **`h3_rom_query_real`**: H1 for the `H₃` table: `≤ E_real[#H₃ keys read] / (2¹²⁸ − qm)`.

In a game with many proofs, each with its own `H₃` slice, a read of the `H₃` table concerns at most
one proof, so these charges sum to the `H₃` budget once.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.IC

open VoleMole.Privacy

section Exp

variable {α β K R C : Type*} [Fintype α] [Fintype β]

/-- **A uniform coordinate lands, through an injective encoding, in a set of candidates that
depend on independent coins with probability `≤ E[#candidates] / |α|`.** -/
theorem pr_mem_indep_exp [Nonempty β] (enc : α → K) (henc : Function.Injective enc)
    (S : β → Finset K) :
    pr (α × β) (fun p => enc p.1 ∈ S p.2) ≤ exP β (fun b => ((S b).card : ℝ)) / Fintype.card α := by
  rw [← pr_equiv (Equiv.prodComm β α), pr_prod]
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ b, pr α (fun a => enc ((Equiv.prodComm β α) (b, a)).1 ∈
      S ((Equiv.prodComm β α) (b, a)).2) ≤ ∑ b, ((S b).card : ℝ) / Fintype.card α :=
    Finset.sum_le_sum fun b _ => pr_mem_le enc henc (S b)
  calc (∑ b, pr α (fun a => enc ((Equiv.prodComm β α) (b, a)).1 ∈
        S ((Equiv.prodComm β α) (b, a)).2)) / Fintype.card β
      ≤ (∑ b, ((S b).card : ℝ) / Fintype.card α) / Fintype.card β :=
        div_le_div_of_nonneg_right h1 hβ.le
    _ = exP β (fun b => ((S b).card : ℝ)) / Fintype.card α := by
        simp only [exP]; rw [← Finset.sum_div, div_div, div_div, mul_comm]

variable [Fintype K] [DecidableEq K] [Fintype R] [Nonempty R] [Fintype C] [Nonempty C]

/-- **Identical until the programmed point is read, with the expected number of reads**
(`abs_pr_hidden_one_le` with `E_ideal[#keys read]` for the worst case `q`). -/
theorem abs_pr_hidden_one_exp {x : C → K} (hx : Function.Injective x)
    (A : R → (K → R) → Prop) (Q : R → (K → R) → Finset K)
    (hQ : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → (A u g ↔ A u g')) :
    |pr (C × (K → R)) (fun p => A (p.2 (x p.1)) p.2) -
        pr (C × ((K → R) × R)) (fun p => A p.2.2 p.2.1)| ≤
      exP ((K → R) × R) (fun b => ((Q b.2 b.1).card : ℝ)) / Fintype.card C := by
  have h := abs_pr_hidden_le (ι := Unit) (R := R) (x := fun c _ => x c)
    (fun c _ _ _ => rfl) (fun _ u g => A (u ()) g) (fun _ u g => Q (u ()) g)
    (fun _ u g g' h => hQ (u ()) g g' h)
  let e : (K → R) × (Unit → R) ≃ (K → R) × R :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique Unit R)
  have h2 : pr (C × ((K → R) × (Unit → R))) (fun p => A (p.2.2 ()) p.2.1) =
      pr (C × ((K → R) × R)) (fun p => A p.2.2 p.2.1) := by
    rw [pr_prod, pr_prod]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    exact pr_equiv e (fun p => A p.2 p.1)
  have h3 : pr (C × ((K → R) × (Unit → R))) (fun p => ∃ i : Unit, x p.1 ∈ Q (p.2.2 ()) p.2.1) ≤
      exP ((K → R) × R) (fun b => ((Q b.2 b.1).card : ℝ)) / Fintype.card C := by
    have := pr_mem_indep_exp (β := (K → R) × (Unit → R)) x hx (fun b => Q (b.2 ()) b.1)
    rw [← exP_equiv e.symm] at this
    refine le_trans (le_of_eq (pr_congr fun p => ?_)) (this.trans (le_of_eq ?_))
    · simp
    · rfl
  simp only [Function.comp_apply] at h
  rw [h2] at h
  exact h.trans h3

/-- **The same, charged in the real experiment**: for a consistent reader `Q` (`hQc`) of at most
`qm < |C|` keys,

    |real − ideal| ≤ E_real[#keys read] / (|C| − qm). -/
theorem abs_pr_hidden_one_real {x : C → K} (hx : Function.Injective x)
    (A : R → (K → R) → Prop) (Q : R → (K → R) → Finset K)
    (hQ : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → (A u g ↔ A u g'))
    (hQc : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → Q u g = Q u g')
    {qm : ℕ} (hqm : ∀ u g, (Q u g).card ≤ qm) (hC : (qm : ℝ) < Fintype.card C) :
    |pr (C × (K → R)) (fun p => A (p.2 (x p.1)) p.2) -
        pr (C × ((K → R) × R)) (fun p => A p.2.2 p.2.1)| ≤
      exP (C × (K → R)) (fun p => ((Q (p.2 (x p.1)) p.2).card : ℝ)) / (Fintype.card C - qm) := by
  set Eid := exP ((K → R) × R) (fun b => ((Q b.2 b.1).card : ℝ))
  set Ere := exP (C × (K → R)) (fun p => ((Q (p.2 (x p.1)) p.2).card : ℝ))
  have hCpos : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hlev : ∀ l < qm, |pr ((K → R) × R) (fun b => l < (Q b.2 b.1).card) -
      pr (C × (K → R)) (fun p => l < (Q (p.2 (x p.1)) p.2).card)| ≤ Eid / Fintype.card C := by
    intro l _
    have h := abs_pr_hidden_one_exp hx (fun u g => l < (Q u g).card) Q
      (fun u g g' h => by rw [hQc u g g' h])
    rw [pr_prod_snd (fun b : (K → R) × R => l < (Q b.2 b.1).card)] at h
    rwa [abs_sub_comm] at h
  have hE := exP_sub_le_of_levels (fun b : (K → R) × R => (Q b.2 b.1).card)
    (fun p : C × (K → R) => (Q (p.2 (x p.1)) p.2).card) (fun b => hqm _ _) (fun p => hqm _ _) hlev
  have hE' : Eid ≤ Ere + qm * (Eid / Fintype.card C) := by
    have := (le_abs_self _).trans hE; linarith
  have hfin := abs_pr_hidden_one_exp hx A Q hQ
  refine hfin.trans ?_
  have hden : (0 : ℝ) < Fintype.card C - qm := by linarith
  rw [div_le_div_iff₀ hCpos hden]
  have : Eid * Fintype.card C ≤ Ere * Fintype.card C + qm * Eid := by
    have h1 := mul_le_mul_of_nonneg_right hE' hCpos.le
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hCpos.ne'] at h1
    linarith
  nlinarith

end Exp

end VoleMole.ZK.IC

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

variable {mu1 wPrefix : ByteArray}

/-- **H1 in the ROM with the expected number of `H₃` reads**: as `h3_rom_query`, for a consistent
reader `Q` of at most `qm < 2¹²⁸` keys, with the expectation over the real experiment (a uniform
`rho` and table, `A` given the real seed and `iv_pre`):

    ≤ E_real[#H₃ keys read] / (2¹²⁸ − qm). -/
theorem h3_rom_query_real (Hs : Hashes) (A : Bytes 16 × Bytes 16 → (Bytes 16 → Bytes 32) → Prop)
    (Q : Bytes 16 × Bytes 16 → (Bytes 16 → Bytes 32) → Finset (Bytes 16))
    (hQ : ∀ v G G', (∀ k ∈ Q v G, G k = G' k) → (A v G ↔ A v G'))
    (hQc : ∀ v G G', (∀ k ∈ Q v G, G k = G' k) → Q v G = Q v G')
    {qm : ℕ} (hqm : ∀ v G, (Q v G).card ≤ qm) (hsmall : (qm : ℝ) < 2 ^ 128) :
    |pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hs.withTable .h3 (seedInput mu1 wPrefix) p.2) mu1 wPrefix (ba p.1)) p.2) -
      pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32))
        (fun p => A (splitSeed p.2.2) p.2.1)| ≤
      exP (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p => ((Q (splitSeed (p.2 p.1)) p.2).card : ℝ)) /
        (2 ^ 128 - qm) := by
  have hC : (Fintype.card (Bytes 16) : ℝ) = 2 ^ 128 := by rw [Prob.card_bytes]; norm_num
  have h := abs_pr_hidden_one_real (C := Bytes 16) (x := id) Function.injective_id
    (fun u G => A (splitSeed u) G) (fun u G => Q (splitSeed u) G) (fun u G G' h => hQ _ G G' h)
    (fun u G G' h => hQc _ G G' h) (fun u G => hqm _ G) (by rw [hC]; exact hsmall)
  rw [hC] at h
  simp only [h3Seed_withTable]
  exact h

end VoleMole.ZK.Sim
