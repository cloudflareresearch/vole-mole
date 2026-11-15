import VoleMole.Theft.JointLean

/-!
# The charges summed over the proofs

`real_sim_leN_lean` (`Theft/JointLean.lean`) needs `J`, a bound on the charges of all slots summed,
in the simulated game. A slot's charge (`nZK`) is the game reader's reads at the slot's `iv` plus
`h` per other slot whose `iv` may share them. Here the sum over the slots is bounded for `iv`s that
are blocks `g_j` (or absent: an output with no `iv`), deterministically:

* **`sum_cEof_le`**: `Σ_i cE(iv_i, Q) ≤ #ptCls Q·(1 + #collPairs g) + #none·#keys Q`;
* **`sum_c5of_le`**: `Σ_i c5(iv_i, Q₅) ≤ #Q₅·(1 + #collPairs g) + #none·#Q₅` (a gate input
  determines its `iv`, `gate5_iv_eq`);
* **`sum_ovE_le`**, **`sum_ov5_le`**: `Σ_i Σ_{j ≠ i} ov(iv_i, iv_j) ≤ 2·#collPairs g + 2N·#none`;
* **`sum_nZK_le`**: hence the weighted sum of the charges of all slots.

With the `iv`s read off a uniform table at inputs that do not read it, `E[#collPairs] ≤
N²·2⁻⁶⁴ + E[#dupPairs]` (`exP_collPairs_tab_le`), so the budget is charged once, times
`1 + N²·2⁻⁶⁴` plus the input-collision term.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier VoleMole.Verifier.Bridge

section Count

variable {N : ℕ}

/-- The `iv`s `iv j`, `j < N`, are the blocks `g j` or absent. -/
def IvsOf (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16) : Prop :=
  ∀ j : Fin N, iv j = none ∨ iv j = some (ba (g j))

/-- The number of slots with no `iv`. -/
noncomputable def nNone (iv : ℕ → Option ByteArray) (N : ℕ) : ℕ :=
  ((range N).filter fun j => iv j = none).card

lemma ind_none_sum (iv : ℕ → Option ByteArray) :
    ∑ i ∈ range N, (if iv i = none then 1 else 0) = nNone iv N := by
  rw [Finset.sum_boole]; rfl

/-- **The cipher charges of all slots.** -/
theorem sum_cEof_le (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16) (hiv : IvsOf iv g)
    (Q : Finset (Blk × Blk)) :
    ∑ i ∈ range N, cEof (iv i) Q ≤
      (ptCls Q).card * (1 + (collPairs g).card) + nNone iv N * (Q.image Prod.fst).card := by
  classical
  have hpt : ∀ i : Fin N, cEof (iv i) Q ≤ (qkeys (InY (ba (g i))) Q).card +
      (if iv i = none then 1 else 0) * (Q.image Prod.fst).card := by
    intro i
    rcases hiv i with h | h
    · rw [h]; simp [cEof]
    · rw [h]; simp [cEof]
  calc ∑ i ∈ range N, cEof (iv i) Q = ∑ i : Fin N, cEof (iv i) Q :=
        (Fin.sum_univ_eq_sum_range (fun i => cEof (iv i) Q) N).symm
    _ ≤ ∑ i : Fin N, ((qkeys (InY (ba (g i))) Q).card +
          (if iv i = none then 1 else 0) * (Q.image Prod.fst).card) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i : Fin N, (qkeys (InY (ba (g i))) Q).card +
          (∑ i : Fin N, (if iv i = none then 1 else 0)) * (Q.image Prod.fst).card := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (ptCls Q).card * (1 + (collPairs g).card) + nNone iv N * (Q.image Prod.fst).card := by
        refine add_le_add (sum_qkeys_inY_le g Q) (le_of_eq ?_)
        rw [Fin.sum_univ_eq_sum_range (fun i => if iv i = none then 1 else 0) N, ind_none_sum]

/-- **The slots whose `iv` has a given gate input all have the same `iv`.** -/
lemma card_gate5_le (p : Params) (T : CrtTables) (g : Fin N → Bytes 16) (k : Bytes 37) :
    (univ.filter fun i : Fin N => Gate5 p T (ba (g i)) k).card ≤ 1 + (collPairs g).card := by
  classical
  set S := univ.filter fun i : Fin N => Gate5 p T (ba (g i)) k
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · rw [hS, Finset.card_empty]; omega
  refine (Finset.card_le_card fun i hi => ?_).trans (card_midB_eq_le g (midB (g i0)))
  have h1 := (Finset.mem_filter.1 hi).2
  have h0 := (Finset.mem_filter.1 hi0).2
  have e := gate5_iv_eq h1 h0 (size_ba _) (size_ba _)
  exact Finset.mem_filter.2 ⟨mem_univ _, by rw [ba_injective e]⟩

/-- **The `H₅` charges of all slots.** -/
theorem sum_c5of_le (p : Params) (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16)
    (hiv : IvsOf iv g) (Q5 : Finset (Bytes 37)) :
    ∑ i ∈ range N, c5of p CrtGen.tables (iv i) Q5 ≤
      Q5.card * (1 + (collPairs g).card) + nNone iv N * Q5.card := by
  classical
  have hpt : ∀ i : Fin N, c5of p CrtGen.tables (iv i) Q5 ≤
      (Q5.filter (Gate5 p CrtGen.tables (ba (g i)))).card + (if iv i = none then 1 else 0) * Q5.card := by
    intro i
    rcases hiv i with h | h
    · rw [h]; simp [c5of]
    · rw [h]; simp [c5of]
  have hsum : ∑ i : Fin N, (Q5.filter (Gate5 p CrtGen.tables (ba (g i)))).card ≤
      Q5.card * (1 + (collPairs g).card) := by
    have e : ∑ i : Fin N, (Q5.filter (Gate5 p CrtGen.tables (ba (g i)))).card =
        ∑ k ∈ Q5, (univ.filter fun i : Fin N => Gate5 p CrtGen.tables (ba (g i)) k).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [e]
    calc _ ≤ ∑ _k ∈ Q5, (1 + (collPairs g).card) :=
          Finset.sum_le_sum fun k _ => card_gate5_le p CrtGen.tables g k
      _ = Q5.card * (1 + (collPairs g).card) := by rw [Finset.sum_const, smul_eq_mul]
  calc ∑ i ∈ range N, c5of p CrtGen.tables (iv i) Q5 = ∑ i : Fin N, c5of p CrtGen.tables (iv i) Q5 :=
        (Fin.sum_univ_eq_sum_range (fun i => c5of p CrtGen.tables (iv i) Q5) N).symm
    _ ≤ ∑ i : Fin N, ((Q5.filter (Gate5 p CrtGen.tables (ba (g i)))).card +
          (if iv i = none then 1 else 0) * Q5.card) := Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i : Fin N, (Q5.filter (Gate5 p CrtGen.tables (ba (g i)))).card +
          (∑ i : Fin N, (if iv i = none then 1 else 0)) * Q5.card := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ Q5.card * (1 + (collPairs g).card) + nNone iv N * Q5.card := by
        refine add_le_add hsum (le_of_eq ?_)
        rw [Fin.sum_univ_eq_sum_range (fun i => if iv i = none then 1 else 0) N, ind_none_sum]

/-- **A pair overlaps only if an `iv` is absent or the blocks share their middle bytes.** -/
lemma ovE_le_ind (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16) (hiv : IvsOf iv g)
    (i j : Fin N) :
    ovE (iv i) (iv j) ≤ (if iv i = none then 1 else 0) + (if iv j = none then 1 else 0) +
      (if midB (g i) = midB (g j) then 1 else 0) := by
  have h1 := ovE_le_one (iv i) (iv j)
  rcases hiv i with hi | hi
  · rw [hi] at h1 ⊢; simp only [↓reduceIte]; omega
  rcases hiv j with hj | hj
  · rw [hj] at h1 ⊢; simp only [↓reduceIte]; omega
  rw [hi, hj]
  by_cases hm : midB (g i) = midB (g j) <;> simp [ovE, hm, blk_ba]

lemma ov5_le_ovE (iv iv' : Option ByteArray) : ov5 iv iv' ≤ ovE iv iv' := by
  unfold ov5 ovE
  rcases iv with _ | a <;> rcases iv' with _ | b
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · by_cases h : a.size = 16 ∧ b.size = 16 ∧ midB (blk 16 a) ≠ midB (blk 16 b)
    · have h' : a.size = 16 ∧ b.size = 16 ∧ a ≠ b :=
        ⟨h.1, h.2.1, fun e => h.2.2 (by rw [e])⟩
      simp [h, h']
    · simp only [h, ↓reduceIte]; split_ifs <;> omega

/-- The ordered pairs of distinct slots with equal middle bytes are twice the unordered ones. -/
lemma sum_midB_eq_le (g : Fin N → Bytes 16) :
    ∑ i : Fin N, ∑ j ∈ univ.erase i, (if midB (g i) = midB (g j) then 1 else 0) ≤
      2 * (collPairs g).card := by
  classical
  have e : ∑ i : Fin N, ∑ j ∈ univ.erase i, (if midB (g i) = midB (g j) then 1 else 0) =
      (univ.filter fun ij : Fin N × Fin N => ij.1 ≠ ij.2 ∧ midB (g ij.1) = midB (g ij.2)).card := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => j ≠ i)]
    have h1 : univ.filter (fun j => j ≠ i) = univ.erase i := by ext; simp
    have h2 : ∑ x ∈ univ.filter (fun j => ¬ j ≠ i),
        (if i ≠ x ∧ midB (g i) = midB (g x) then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        simp only [ne_eq, not_not, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hj]
    rw [h1, h2, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : i ≠ j := fun e => (Finset.mem_erase.1 hj).1 e.symm
    simp [hji]
  rw [e]
  -- each unordered pair counts twice
  have hsplit : (univ.filter fun ij : Fin N × Fin N => ij.1 ≠ ij.2 ∧ midB (g ij.1) = midB (g ij.2)) ⊆
      collPairs g ∪ (collPairs g).map (Equiv.prodComm _ _).toEmbedding := by
    intro ij hij
    obtain ⟨hne, hm⟩ := (Finset.mem_filter.1 hij).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, hlt, hm⟩)
    · refine Finset.mem_union_right _ (Finset.mem_map.2 ⟨(ij.2, ij.1), ?_, by simp⟩)
      exact Finset.mem_filter.2 ⟨mem_univ _, hgt, hm.symm⟩
  refine (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_map]; omega

/-- **The pairwise overlaps of all slots.** -/
theorem sum_ovE_le (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16) (hiv : IvsOf iv g) :
    ∑ i ∈ range N, ∑ j ∈ (range N).erase i, ovE (iv i) (iv j) ≤
      2 * (collPairs g).card + 2 * N * nNone iv N := by
  classical
  have e : ∑ i ∈ range N, ∑ j ∈ (range N).erase i, ovE (iv i) (iv j) =
      ∑ i : Fin N, ∑ j ∈ univ.erase i, ovE (iv i) (iv j) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (range N).erase i.val = (univ.erase i).map Fin.valEmbedding := by
      ext j
      constructor
      · intro hj
        obtain ⟨hji, hjN⟩ := Finset.mem_erase.1 hj
        exact Finset.mem_map.2 ⟨⟨j, Finset.mem_range.1 hjN⟩,
          Finset.mem_erase.2 ⟨fun e => hji (by rw [← e]), mem_univ _⟩, rfl⟩
      · intro hj
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hj
        exact Finset.mem_erase.2 ⟨fun e => (Finset.mem_erase.1 hj').1 (Fin.ext e),
          Finset.mem_range.2 j'.isLt⟩
    rw [this, Finset.sum_map]
    rfl
  rw [e]
  have hN : ∑ i : Fin N, (if iv i = none then 1 else 0) = nNone iv N := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if iv i = none then 1 else 0) N, ind_none_sum]
  calc ∑ i : Fin N, ∑ j ∈ univ.erase i, ovE (iv i) (iv j)
      ≤ ∑ i : Fin N, ∑ j ∈ univ.erase i, ((if iv i = none then 1 else 0) +
          (if iv j = none then 1 else 0) + (if midB (g i) = midB (g j) then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ovE_le_ind iv g hiv i j
    _ ≤ ∑ i : Fin N, (∑ j : Fin N, ((if iv i = none then 1 else 0) +
          (if iv j = none then 1 else 0)) +
          ∑ j ∈ univ.erase i, (if midB (g i) = midB (g j) then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => by
          rw [Finset.sum_add_distrib]
          exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset (f := fun j : Fin N =>
            (if iv i = none then 1 else 0) + (if iv j = none then 1 else 0))
            (Finset.erase_subset i univ)) _
    _ = ∑ i : Fin N, ∑ j : Fin N, ((if iv i = none then 1 else 0) + (if iv j = none then 1 else 0))
          + ∑ i : Fin N, ∑ j ∈ univ.erase i, (if midB (g i) = midB (g j) then 1 else 0) :=
        Finset.sum_add_distrib
    _ ≤ 2 * N * nNone iv N + 2 * (collPairs g).card := by
        refine add_le_add (le_of_eq ?_) (sum_midB_eq_le g)
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, hN, ← Finset.mul_sum]
        ring
    _ = 2 * (collPairs g).card + 2 * N * nNone iv N := by ring

theorem sum_ov5_le (iv : ℕ → Option ByteArray) (g : Fin N → Bytes 16) (hiv : IvsOf iv g) :
    ∑ i ∈ range N, ∑ j ∈ (range N).erase i, ov5 (iv i) (iv j) ≤
      2 * (collPairs g).card + 2 * N * nNone iv N :=
  (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => ov5_le_ovE _ _).trans
    (sum_ovE_le iv g hiv)

end Count

end VoleMole.Theft
