import VoleMole.ZK.IdealCipherPt

/-!
# How many proofs one read value concerns

With permutation rows a read is charged to a proof also when its **value** is one the proof
reveals (`IC.vkeys`, `ZK/IdealCipherPtPerm.lean`). In a game with `N` proofs, a read with value
`y` is charged to every proof that reveals `y`. This file bounds that number, as `ZK/IvOverlap.lean`
does for inputs.

Each proof `i` reveals the `m` values `g i : Fin m → K` (its value set is their image). Then:

* **`sum_inV_le`** (deterministic, for any reads `Z` with values `val`, chosen after seeing the
  values): `Σ_i #{a ∈ Z | val a ∈ g i} ≤ |Z|·(1 + #valPairs)`, `valPairs` the pairs `i < j` of
  proofs that reveal an equal value;
* **`exP_valPairs_le`**: for independent uniform values, `E[#valPairs] ≤ N²·m²/|K|` (each pair
  `≤ m²/|K|`, `pr_meet_le`);
* **`exP_sum_inV_le`**: hence, for reads `Z g` of at most `q` items (any function of the values),
  `E[Σ_i #{a ∈ Z g | val a ∈ g i}] ≤ q·(1 + N²·m²/|K|)`.

So the total value charge of all `N` proofs is the read budget once, times `1 + N²·m²/|K|`. In the
simulated game the revealed blocks are uniform; with `K` the blocks, `N ≤ 2³¹` and `m ≤ 2¹⁶` the
factor is `≤ 1 + 2⁻⁶⁴`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.IC

open VoleMole.Privacy

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {N m : ℕ}

/-- **The pairs of proofs that reveal an equal value.** -/
def valPairs (g : Fin N → Fin m → K) : Finset (Fin N × Fin N) :=
  univ.filter fun ij => ij.1 < ij.2 ∧ ∃ r r', g ij.1 r = g ij.2 r'

/-- **One value concerns at most `1 + #valPairs` proofs.** -/
lemma card_inV_le (g : Fin N → Fin m → K) (y : K) :
    (univ.filter fun i => y ∈ univ.image (g i)).card ≤ 1 + (valPairs g).card := by
  set S := univ.filter fun i => y ∈ univ.image (g i)
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty]; omega
  set i0 := S.min' hS
  have hi0 : i0 ∈ S := S.min'_mem hS
  have hmap : ∀ j ∈ S.erase i0, (i0, j) ∈ valPairs g := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.1 hj
    refine Finset.mem_filter.2 ⟨mem_univ _, lt_of_le_of_ne (S.min'_le j hjS) (Ne.symm hji), ?_⟩
    obtain ⟨r, -, hr⟩ := mem_image.1 (Finset.mem_filter.1 hi0).2
    obtain ⟨r', -, hr'⟩ := mem_image.1 (Finset.mem_filter.1 hjS).2
    exact ⟨r, r', hr.trans hr'.symm⟩
  have h := Finset.card_le_card_of_injOn (fun j => (i0, j)) hmap
    (fun j _ j' _ e => (Prod.mk.inj e).2)
  rw [Finset.card_erase_of_mem hi0] at h
  omega

/-- **The reads charged to all proofs at once**: for any reads `Z` with values `val` (which may
depend on the revealed values), `Σ_i #{a ∈ Z | val a ∈ g i} ≤ |Z|·(1 + #valPairs)`. -/
theorem sum_inV_le {α : Type*} (g : Fin N → Fin m → K) (Z : Finset α) (val : α → K) :
    ∑ i, (Z.filter fun a => val a ∈ univ.image (g i)).card ≤ Z.card * (1 + (valPairs g).card) := by
  classical
  have e : ∑ i, (Z.filter fun a => val a ∈ univ.image (g i)).card =
      ∑ a ∈ Z, (univ.filter fun i => val a ∈ univ.image (g i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [e]
  calc ∑ a ∈ Z, (univ.filter fun i => val a ∈ univ.image (g i)).card
      ≤ ∑ _a ∈ Z, (1 + (valPairs g).card) := Finset.sum_le_sum fun a _ => card_inV_le g (val a)
    _ = Z.card * (1 + (valPairs g).card) := by rw [Finset.sum_const, smul_eq_mul]

/-- **Two proofs with independent uniform values reveal an equal value with probability
`≤ m²/|K|`.** -/
lemma pr_meet_le {a a' : Fin N} (h : a ≠ a') :
    pr (Fin N → Fin m → K) (fun g => ∃ r r', g a r = g a' r') ≤ (m : ℝ) ^ 2 / Fintype.card K := by
  have h1 : ∀ r : Fin m, pr (Fin N → Fin m → K) (fun g => g a r ∈ univ.image (g a')) ≤
      (m : ℝ) / Fintype.card K := by
    intro r
    have hr := pr_mem_reset_le (α := Fin N → Fin m → K) (K := K) (fun g => g a r)
      (fun g k => Function.update g a (Function.update (g a) r k))
      (fun g k => by simp) (fun g k k' => by simp) (fun g => by simp)
      (fun g => univ.image (g a')) (fun g k => by rw [Function.update_of_ne h.symm])
      (q := m) (fun g => card_image_le.trans (by simp))
    exact hr
  calc pr (Fin N → Fin m → K) (fun g => ∃ r r', g a r = g a' r')
      = pr (Fin N → Fin m → K) (fun g => ∃ r, g a r ∈ univ.image (g a')) :=
        pr_congr fun g => by simp only [mem_image, mem_univ, true_and]; exact
          ⟨fun ⟨r, r', e⟩ => ⟨r, r', e.symm⟩, fun ⟨r, r', e⟩ => ⟨r, r', e.symm⟩⟩
    _ ≤ ∑ r : Fin m, pr (Fin N → Fin m → K) (fun g => g a r ∈ univ.image (g a')) :=
        pr_exists_le_sum _
    _ ≤ ∑ _r : Fin m, (m : ℝ) / Fintype.card K := Finset.sum_le_sum fun r _ => h1 r
    _ = (m : ℝ) ^ 2 / Fintype.card K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **`E[#valPairs] ≤ N²·m²/|K|`** for independent uniform values. -/
theorem exP_valPairs_le :
    exP (Fin N → Fin m → K) (fun g => ((valPairs g).card : ℝ)) ≤
      (N : ℝ) ^ 2 * m ^ 2 / Fintype.card K := by
  have e : ∀ g : Fin N → Fin m → K, ((valPairs g).card : ℝ) =
      ∑ ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2),
        if ∃ r r', g ij.1 r = g ij.2 r' then (1 : ℝ) else 0 := by
    intro g
    rw [Finset.sum_boole, Finset.filter_filter]
    rfl
  have hpr : ∀ ij : Fin N × Fin N, ij.1 < ij.2 →
      exP (Fin N → Fin m → K) (fun g => if ∃ r r', g ij.1 r = g ij.2 r' then (1 : ℝ) else 0) ≤
        (m : ℝ) ^ 2 / Fintype.card K := by
    intro ij hij
    have h := pr_meet_le (K := K) (m := m) hij.ne
    rw [pr_def, ← Finset.sum_boole] at h
    exact h
  simp only [exP] at hpr ⊢
  rw [Finset.sum_congr rfl fun g _ => e g, Finset.sum_comm, Finset.sum_div]
  have hK : (0 : ℝ) ≤ (m : ℝ) ^ 2 / Fintype.card K := by positivity
  calc ∑ ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2),
        (∑ g : Fin N → Fin m → K, if ∃ r r', g ij.1 r = g ij.2 r' then (1 : ℝ) else 0) /
          Fintype.card (Fin N → Fin m → K)
      ≤ ∑ _ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2),
          (m : ℝ) ^ 2 / Fintype.card K :=
        Finset.sum_le_sum fun ij hij => hpr ij (Finset.mem_filter.1 hij).2
    _ ≤ ∑ _ij : Fin N × Fin N, (m : ℝ) ^ 2 / Fintype.card K :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hK
    _ = (N : ℝ) ^ 2 * m ^ 2 / Fintype.card K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **The expected total value charge of `N` proofs is the read budget once, times
`1 + N²·m²/|K|`**: for independent uniform revealed values and reads `Z g` of at most `q` items
with values `val g` (any functions of the values),
`E[Σ_i #{a ∈ Z g | val g a ∈ g i}] ≤ q·(1 + N²·m²/|K|)`. -/
theorem exP_sum_inV_le {α : Type*} (Z : (Fin N → Fin m → K) → Finset α)
    (val : (Fin N → Fin m → K) → α → K) {q : ℕ} (hq : ∀ g, (Z g).card ≤ q) :
    exP (Fin N → Fin m → K) (fun g =>
      ((∑ i, ((Z g).filter fun a => val g a ∈ univ.image (g i)).card : ℕ) : ℝ)) ≤
      q * (1 + (N : ℝ) ^ 2 * m ^ 2 / Fintype.card K) := by
  calc exP (Fin N → Fin m → K) (fun g =>
        ((∑ i, ((Z g).filter fun a => val g a ∈ univ.image (g i)).card : ℕ) : ℝ))
      ≤ exP (Fin N → Fin m → K) (fun g => (q : ℝ) * (1 + ((valPairs g).card : ℝ))) :=
        exP_mono fun g => by
          have h := (sum_inV_le g (Z g) (val g)).trans (Nat.mul_le_mul_right _ (hq g))
          exact_mod_cast h
    _ = q * (1 + exP (Fin N → Fin m → K) (fun g => ((valPairs g).card : ℝ))) := by
        simp only [exP]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, mul_div_assoc, add_div,
          div_self (by exact_mod_cast Fintype.card_ne_zero)]
    _ ≤ q * (1 + (N : ℝ) ^ 2 * m ^ 2 / Fintype.card K) := by
        gcongr
        exact exP_valPairs_le

end VoleMole.ZK.IC
