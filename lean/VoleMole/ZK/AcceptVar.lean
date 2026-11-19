import VoleMole.ZK.AcceptVarData

/-!
# The grinding acceptance set by the second moment (`lean/docs/zk.md` §10.1)

`ZK/AcceptCount.lean` proves `|A| ≥ 2¹¹¹` by Markov on the box `S = [0, 120)¹⁷`. Here the same
box with Chebyshev's inequality instead:

    2¹¹⁴ ≤ |A|                                                  (`card_accSet_ge_114`)

(`≈ 2¹¹⁴·²`; the true value is `≈ 0.397·2¹²⁰ ≈ 2¹¹⁸·⁶⁷` by sampling).

**The off count.** On `S` the `17` hidden leaves are distinct, so the open count is
`2287 − Z`, where `Z` is the number of internal nodes off every hidden path
(`openCount_add_Z`: each internal node with exactly one hidden child is counted once by
`N(2n+1) + N(2n+2) − 2N(n)`, `N` the indicator of being off; the sum telescopes to the
`2304 − 17` leaves that are off).

**The moments.** `Σ_S Z = Σ_v U(v)` (`sum_Z`) and `Σ_S Z² = Σ_{v,w} U2(v, w)` (`sum_Z2`), where
`U2(v, w) = Π_i (120 − c_i(v ∪ w))` counts the tuples with both `v` and `w` off (`card_off2`).
Two nodes are either related (one descends from the other: `U2 = U(ancestor)`) or have disjoint
subtrees (`c(v ∪ w) = c v + c w`; `desc_chain`: the ancestors of a node form a chain). So
`Σ U2 + Σ_v (P(c v) − P(2 c v)) = Σ_{v,w} P(c v + c w) + 2 Σ_{v, w below v} (P(c v) − P(c v + c w))`
(`sum_U2`), and the kernel evaluates the right-hand side (`ZK/AcceptVarData.lean`).

**Chebyshev.** With the centre `Z = 2197` (open count `90`, close to the optimal centre of
Cantelli's inequality): a rejected tuple has `Z ≤ 2181`, so `(Z − 2197)² ≥ 256`, and
`256·#rejected ≤ Σ (Z − 2197)²`. The mean open count on `S` is `≈ 104.28` and its variance
`≈ 24.29`, so at least `≈ 0.108·120¹⁷ ≈ 2¹¹⁴·²` tuples of `S` are accepted.

The remaining gap to `≈ 2¹¹⁸·⁷` is the box (`120¹⁷ ≈ 2¹¹⁷·⁴`; on all `2¹²⁰` tuples the mean
`≈ 106.38` exceeds `105`, so no moment bound applies there) and the slack of a second-moment bound
at a threshold `0.35 σ` above the mean (the accepted fraction of `S` is `≈ 0.56` by sampling). An
exact count needs the subset of vectors below each node as state (`2¹⁷` states, subset
convolutions at the top of the tree), out of the kernel's reach.
-/

open Finset

namespace VoleMole.ZK.Accept

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

/-! ## Ancestors form a chain -/

lemma desc_trans {u v w : ℕ} (h1 : Desc u v) (h2 : Desc v w) : Desc u w := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  exact ⟨s + t, by rw [← div_pow_add, hs, ht]⟩

/-- **Two ancestors of a node are related.** -/
lemma desc_chain {v w x : ℕ} (h1 : Desc v x) (h2 : Desc w x) : Desc v w ∨ Desc w v := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  rcases le_total t s with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inr ⟨k, by rw [← ht, div_pow_add, hs]⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inl ⟨k, by rw [← hs, div_pow_add, ht]⟩

lemma desc_antisymm {v w : ℕ} (h1 : Desc v w) (h2 : Desc w v) : v = w :=
  le_antisymm (desc_le h1) (desc_le h2)

/-- The internal nodes below an internal node: itself and those below its children. -/
lemma filter_desc_internal {v : ℕ} (hv : v < 2303) :
    (range 2303).filter (Desc v) =
      insert v ((range 2303).filter (Desc (2 * v + 1)) ∪ (range 2303).filter (Desc (2 * v + 2))) := by
  ext n
  simp only [mem_filter, mem_range, mem_insert, mem_union]
  rw [desc_iff]
  constructor
  · rintro ⟨hn, h | h | h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hn, h⟩)
    · exact Or.inr (Or.inr ⟨hn, h⟩)
  · rintro (rfl | ⟨hn, h⟩ | ⟨hn, h⟩)
    · exact ⟨hv, Or.inl rfl⟩
    · exact ⟨hn, Or.inr (Or.inl h)⟩
    · exact ⟨hn, Or.inr (Or.inr h)⟩

lemma not_mem_desc_children {v : ℕ} (hv : v < 2303) :
    v ∉ (range 2303).filter (Desc (2 * v + 1)) ∪ (range 2303).filter (Desc (2 * v + 2)) := by
  simp only [mem_union, mem_filter, not_or, not_and]
  exact ⟨fun _ h => by have := desc_le h; omega, fun _ h => by have := desc_le h; omega⟩

lemma disj_desc_children (v : ℕ) :
    Disjoint ((range 2303).filter (Desc (2 * v + 1))) ((range 2303).filter (Desc (2 * v + 2))) := by
  rw [Finset.disjoint_filter]
  intro n _ h1 h2
  exact desc_disj v _ ⟨h1, h2⟩

lemma filter_desc_leaf {v : ℕ} (hv : 2303 ≤ v) : (range 2303).filter (Desc v) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro n hn h
  have := desc_le h
  rw [mem_range] at hn
  omega

/-! ## Count vectors -/

lemma V17.ext_get {a b : V17} (h : ∀ i < 17, a.get i = b.get i) : a = b := by
  cases a
  cases b
  simp only [V17.mk.injEq]
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num),
    h 9 (by norm_num), h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num),
    h 13 (by norm_num), h 14 (by norm_num), h 15 (by norm_num), h 16 (by norm_num)⟩

lemma V17.beq_eq {a b : V17} (h : V17.beq a b = true) : a = b := by
  cases a
  cases b
  have key : ∀ x y : ℕ, Nat.beq x y = true ↔ x = y :=
    fun x y => ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩
  simp only [V17.beq, Bool.and_eq_true, key] at h
  simp only [V17.mk.injEq]
  tauto

lemma V17.add_comm' (a b : V17) : a.add b = b.add a :=
  V17.ext_get fun i hi => by rw [V17.get_add _ _ hi, V17.get_add _ _ hi, Nat.add_comm]

lemma V17.u_add_le (a b : V17) : (a.add b).u ≤ a.u := by
  rw [V17.u_eq, V17.u_eq]
  refine Finset.prod_le_prod fun i _ => ?_
  rw [V17.get_add _ _ i.isLt]
  omega

/-- The counts of node `v`. -/
def cv (v : ℕ) : V17 := (go 13 v).1

lemma cv_get {v : ℕ} (hv : v < 4607) (i : Fin BAVC.tau) : (cv v).get i = cnt i v :=
  (go_spec 13 v hv (by have := Nat.one_le_two_pow (n := 13); nlinarith)).1 i

lemma cv_eq_of {v : ℕ} (hv : v < 4607) {a : V17} (h : ∀ i : Fin BAVC.tau, a.get i = cnt i v) :
    a = cv v :=
  V17.ext_get fun i hi => by rw [h ⟨i, hi⟩, cv_get hv ⟨i, hi⟩]

lemma U_eq_cv {v : ℕ} (hv : v < 4607) : U v = (cv v).u := by
  rw [V17.u_eq, U]
  exact Finset.prod_congr rfl fun i _ => by rw [cv_get hv i]

/-- `P(c v + c w)`. -/
def pu (v w : ℕ) : ℕ := ((cv v).add (cv w)).u

lemma pu_comm (v w : ℕ) : pu v w = pu w v := by rw [pu, pu, V17.add_comm']

/-! ## The kernel's second pass -/

/-- The related pairs' term of the internal node `w'`. -/
def D (w' : ℕ) : ℕ := ∑ w ∈ (range 2303).filter (Desc w'), ((cv w').u - pu w' w)

theorem go2_spec : ∀ f v, v < 4607 → 4608 ≤ (v + 1) * 2 ^ f →
    (go2 f v).1 = cv v ∧
    (∀ g : V17 → ℕ, ((go2 f v).2.1.map g).sum = ∑ w ∈ (range 2303).filter (Desc v), g (cv w)) ∧
    (go2 f v).2.2 = ∑ w' ∈ (range 2303).filter (Desc v), D w' := by
  intro f
  induction f with
  | zero =>
    intro v hv hf
    simp at hf
    omega
  | succ f ih =>
    intro v hv hf
    by_cases hi : v < 2303
    · obtain ⟨h1c, h1l, h1s⟩ := ih (2 * v + 1) (by omega) (by rw [pow_succ] at hf; nlinarith)
      obtain ⟨h2c, h2l, h2s⟩ := ih (2 * v + 2) (by omega) (by rw [pow_succ] at hf; nlinarith)
      rcases hga : go2 f (2 * v + 1) with ⟨a, la, s⟩
      rcases hgb : go2 f (2 * v + 2) with ⟨b, lb, t⟩
      rw [hga] at h1c h1l h1s
      rw [hgb] at h2c h2l h2s
      simp only at h1c h1l h1s h2c h2l h2s
      have hc : a.add b = cv v := cv_eq_of hv fun i => by
        rw [V17.get_add _ _ i.isLt, h1c, h2c, cv_get (by omega) i, cv_get (by omega) i,
          cnt_internal i hi]
      have hl : ∀ g : V17 → ℕ, ((a.add b :: (la ++ lb)).map g).sum =
          ∑ w ∈ (range 2303).filter (Desc v), g (cv w) := by
        intro g
        rw [filter_desc_internal hi, Finset.sum_insert (not_mem_desc_children hi),
          Finset.sum_union (disj_desc_children v), List.map_cons, List.sum_cons, List.map_append,
          List.sum_append, h1l, h2l, hc]
      have hDv : ∑ w ∈ (range 2303).filter (Desc v), ((cv v).u - ((cv v).add (cv w)).u) = D v :=
        rfl
      simp only [go2, hi, ite_true, hga, hgb]
      refine ⟨hc, hl, ?_⟩
      rw [hl, hc, hDv, h1s, h2s, filter_desc_internal hi,
        Finset.sum_insert (not_mem_desc_children hi), Finset.sum_union (disj_desc_children v)]
      ring
    · simp only [go2, hi, ite_false, List.map_nil, List.sum_nil]
      refine ⟨cv_eq_of hv fun i => ?_, fun g => ?_, ?_⟩
      · rw [leafVec_get _ i.isLt, cnt_leaf i (by omega) hv]
      · rw [filter_desc_leaf (by omega), Finset.sum_empty]
      · rw [filter_desc_leaf (by omega), Finset.sum_empty]

lemma go2_root :
    (∀ g : V17 → ℕ, (L0.map g).sum = ∑ w ∈ range 2303, g (cv w)) ∧
    (go2 13 0).2.2 = ∑ w' ∈ range 2303, D w' := by
  have h := go2_spec 13 0 (by norm_num) (by norm_num)
  have e : (range 2303).filter (Desc 0) = range 2303 :=
    Finset.filter_true_of_mem fun n _ => desc_zero n
  rw [e] at h
  exact ⟨h.2.1, h.2.2⟩

/-! ## Histograms -/

lemma hins_sum (g : V17 → ℕ) (a : V17) :
    ∀ h : List (V17 × ℕ), ((hins a h).map fun p => p.2 * g p.1).sum =
      g a + (h.map fun p => p.2 * g p.1).sum
  | [] => by simp [hins]
  | (x, n) :: t => by
    simp only [hins]
    split_ifs with hb
    · rw [V17.beq_eq hb]
      simp only [List.map_cons, List.sum_cons]
      ring
    · simp only [List.map_cons, List.sum_cons]
      rw [hins_sum g a t]
      ring

lemma foldl_hins_sum (g : V17 → ℕ) :
    ∀ (L : List V17) (h : List (V17 × ℕ)),
      ((L.foldl (fun h a => hins a h) h).map fun p => p.2 * g p.1).sum =
        (h.map fun p => p.2 * g p.1).sum + (L.map g).sum
  | [], h => by simp
  | a :: L, h => by
    rw [List.foldl_cons, foldl_hins_sum g L, hins_sum, List.map_cons, List.sum_cons]
    ring

/-- **A histogram has the list's sums.** -/
theorem hist_sum (g : V17 → ℕ) (L : List V17) :
    ((hist L).map fun p => p.2 * g p.1).sum = (L.map g).sum := by
  rw [hist, foldl_hins_sum]
  simp

lemma sum_L0 (g : V17 → ℕ) :
    ((hist L0).map fun p => p.2 * g p.1).sum = ∑ w ∈ range 2303, g (cv w) := by
  rw [hist_sum, go2_root.1]

/-! ## The sums over the internal nodes -/

lemma sumU_val : ∑ v ∈ range 2303, U v = 484259924132640697798742136587093743952 := by
  rw [← sz_val, sum_L0]
  exact Finset.sum_congr rfl fun v hv => U_eq_cv (by rw [mem_range] at hv; omega)

lemma sumPU_val : ∑ v ∈ range 2303, ∑ w ∈ range 2303, pu v w =
    1056881111883048691624339931618558395936896 := by
  rw [← aAll_val, aAll]
  have : (fun p : V17 × ℕ => p.2 * ((hist L0).map fun q => q.2 * (p.1.add q.1).u).sum) =
      fun p => p.2 * (fun x => ∑ w ∈ range 2303, (x.add (cv w)).u) p.1 := by
    funext p
    rw [sum_L0 fun y => (p.1.add y).u]
  rw [this, sum_L0 fun x => ∑ w ∈ range 2303, (x.add (cv w)).u]
  rfl

lemma sumD_val : ∑ v ∈ range 2303, D v = 72875678509543480965805498961646914158 := by
  rw [← rd_val, go2_root.2]

lemma sumDiag_val : ∑ v ∈ range 2303, ((cv v).u - pu v v) =
    19311176279936440689791419079891556688 := by
  rw [← rs_val, sum_L0 fun x => x.u - (x.add x).u]
  rfl

/-! ## Pairs of nodes on the box -/

/-- The number of leaves `j < 120` of vector `i` below `v` or `w`. -/
def cnt2 (i : Fin BAVC.tau) (v w : ℕ) : ℕ :=
  #((inS i).filter fun j => Desc v (BAVC.treePos i j.val) ∨ Desc w (BAVC.treePos i j.val))

/-- The number of tuples in `S` for which `v` and `w` are off every hidden path. -/
def U2 (v w : ℕ) : ℕ := ∏ i, (120 - cnt2 i v w)

lemma card_off2 (v w : ℕ) :
    #(S.filter fun d => (∀ i : Fin BAVC.tau, ¬ Desc v (BAVC.treePos i (d i).val)) ∧
      ∀ i : Fin BAVC.tau, ¬ Desc w (BAVC.treePos i (d i).val)) = U2 v w := by
  have h : (S.filter fun d => (∀ i : Fin BAVC.tau, ¬ Desc v (BAVC.treePos i (d i).val)) ∧
      ∀ i : Fin BAVC.tau, ¬ Desc w (BAVC.treePos i (d i).val)) =
      Fintype.piFinset fun i => (inS i).filter fun j =>
        ¬ (Desc v (BAVC.treePos i j.val) ∨ Desc w (BAVC.treePos i j.val)) := by
    ext d; simp [S, Fintype.mem_piFinset, forall_and, not_or]
  rw [h, Fintype.card_piFinset, U2]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := Finset.card_filter_add_card_filter_not (s := inS i)
    (fun j => Desc v (BAVC.treePos i j.val) ∨ Desc w (BAVC.treePos i j.val))
  rw [card_inS] at this
  rw [cnt2]
  omega

lemma cnt2_of_desc {v w : ℕ} (h : Desc v w) (i : Fin BAVC.tau) : cnt2 i v w = cnt i v := by
  rw [cnt2, cnt]
  congr 1
  refine Finset.filter_congr fun j _ => ⟨fun h' => h'.elim id (desc_trans h), Or.inl⟩

lemma cnt2_comm (i : Fin BAVC.tau) (v w : ℕ) : cnt2 i v w = cnt2 i w v := by
  rw [cnt2, cnt2]
  simp only [or_comm]

lemma cnt2_disj {v w : ℕ} (h1 : ¬ Desc v w) (h2 : ¬ Desc w v) (i : Fin BAVC.tau) :
    cnt2 i v w = cnt i v + cnt i w := by
  rw [cnt2, cnt, cnt, ← Finset.card_union_of_disjoint, Finset.filter_or]
  rw [Finset.disjoint_filter]
  intro j _ ha hb
  rcases desc_chain ha hb with h | h
  · exact h1 h
  · exact h2 h

lemma U2_of_desc {v w : ℕ} (h : Desc v w) : U2 v w = U v := by
  rw [U2, U]
  exact Finset.prod_congr rfl fun i _ => by rw [cnt2_of_desc h]

lemma U2_comm (v w : ℕ) : U2 v w = U2 w v := by
  rw [U2, U2]
  exact Finset.prod_congr rfl fun i _ => by rw [cnt2_comm]

lemma U2_disj {v w : ℕ} (hv : v < 4607) (hw : w < 4607) (h1 : ¬ Desc v w) (h2 : ¬ Desc w v) :
    U2 v w = pu v w := by
  rw [U2, pu, V17.u_eq]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cnt2_disj h1 h2, V17.get_add _ _ i.isLt, cv_get hv, cv_get hw]

/-- **The pair count, split**: the disjoint-subtree formula plus a correction on related pairs. -/
lemma U2_split {v w : ℕ} (hv : v < 4607) (hw : w < 4607) :
    U2 v w = pu v w + (if Desc v w then (cv v).u - pu v w else 0) +
      (if Desc w v ∧ ¬ Desc v w then (cv w).u - pu v w else 0) := by
  by_cases h1 : Desc v w
  · have := V17.u_add_le (cv v) (cv w)
    simp only [h1, ite_true, not_true_eq_false, and_false, ite_false, add_zero]
    rw [U2_of_desc h1, U_eq_cv hv, pu]
    omega
  · by_cases h2 : Desc w v
    · have := V17.u_add_le (cv w) (cv v)
      simp only [h1, h2, ite_false, not_false_eq_true, and_self, ite_true]
      rw [U2_comm, U2_of_desc h2, U_eq_cv hw, pu_comm, pu]
      omega
    · simp only [h1, h2, ite_false, false_and, add_zero]
      exact U2_disj hv hw h1 h2

/-- **The sum of the pair counts**, in the kernel's terms. -/
theorem sum_U2 :
    (∑ v ∈ range 2303, ∑ w ∈ range 2303, U2 v w) + ∑ v ∈ range 2303, ((cv v).u - pu v v) =
      (∑ v ∈ range 2303, ∑ w ∈ range 2303, pu v w) + 2 * ∑ v ∈ range 2303, D v := by
  set R := range 2303
  have hR : ∀ v ∈ R, v < 4607 := fun v hv => by rw [mem_range] at hv; omega
  -- The correction on `w` below `v`, and on `v` below `w`.
  set F1 : ℕ → ℕ → ℕ := fun v w => if Desc v w then (cv v).u - pu v w else 0
  set F2 : ℕ → ℕ → ℕ := fun v w => if Desc w v ∧ ¬ Desc v w then (cv w).u - pu v w else 0
  have hsplit : ∑ v ∈ R, ∑ w ∈ R, U2 v w =
      ∑ v ∈ R, ∑ w ∈ R, pu v w + ∑ v ∈ R, ∑ w ∈ R, F1 v w + ∑ v ∈ R, ∑ w ∈ R, F2 v w := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w hw => U2_split (hR v hv) (hR w hw)
  have hF1 : ∀ v, ∑ w ∈ R, F1 v w = D v := by
    intro v
    rw [D, Finset.sum_filter]
  -- `F2` is `F1` transposed, off the diagonal.
  have hF2 : ∑ v ∈ R, ∑ w ∈ R, F2 v w + ∑ v ∈ R, ((cv v).u - pu v v) =
      ∑ v ∈ R, ∑ w ∈ R, F1 v w := by
    rw [Finset.sum_comm (f := F2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have e : ∀ w ∈ R, F1 v w = F2 w v + (if w = v then (cv v).u - pu v v else 0) := by
      intro w _
      simp only [F1, F2]
      by_cases h1 : Desc v w
      · by_cases h2 : Desc w v
        · have := desc_antisymm h1 h2
          subst this
          simp [h1]
        · have hne : w ≠ v := fun e => h2 (e ▸ desc_self w)
          simp [h1, h2, hne, pu_comm]
      · have hne : w ≠ v := fun e => h1 (e ▸ desc_self v)
        simp [h1, hne]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' R v]
    simp only [hv, ↓reduceIte]
  simp only [hF1] at hF2
  rw [hsplit]
  simp only [hF1] at *
  omega

/-! ## The off count on the box -/

-- (Elaboration otherwise unfolds membership in this concrete subset, as for `accSet`.)
attribute [local irreducible] S

lemma mem_S {d : Idx} : d ∈ S ↔ ∀ i, (d i).val < 120 := by
  unfold S
  rw [Fintype.mem_piFinset]
  exact forall_congr' fun i => by rw [inS, Finset.mem_filter]; simp

lemma ite_mul_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) * (if q then 1 else 0) : ℕ) = if p ∧ q then 1 else 0 := by
  by_cases p <;> by_cases q <;> simp [*]

/-- The number of internal nodes off every hidden path. -/
def Z (d : Idx) : ℕ := ∑ v ∈ range 2303, if hid (ba (enc d)) v = false then 1 else 0

lemma sum_Z : ∑ d ∈ S, Z d = ∑ v ∈ range 2303, U v := by
  simp only [Z]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v hv =>
    sum_off (by rw [mem_range] at hv; rw [numNodes_val]; omega)

lemma sum_Z2 : ∑ d ∈ S, Z d ^ 2 = ∑ v ∈ range 2303, ∑ w ∈ range 2303, U2 v w := by
  simp only [Z, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [mem_range] at hv hw
  rw [← card_off2, Finset.card_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ite_mul_ite]
  exact if_congr (and_congr (hid_false_enc d (show v < BAVC.numNodes by rw [numNodes_val]; omega))
    (hid_false_enc d (show w < BAVC.numNodes by rw [numNodes_val]; omega))) rfl rfl

lemma sum_pairs (f : ℕ → ℕ) :
    ∀ k, (∑ n ∈ range k, (f (2 * n + 1) + f (2 * n + 2))) + f 0 = ∑ v ∈ range (2 * k + 1), f v
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ← sum_pairs f k]
    ring_nf

lemma treePos_box {i : Fin BAVC.tau} {j : ℕ} (hj : j < 120) :
    BAVC.treePos i j = 2303 + 17 * j + i := by
  simp only [BAVC.treePos, numLeaves_val, BAVC.tau, show j < 128 by omega, ite_true]
  omega

/-- **On the box, `17` leaves are hidden.** -/
lemma sum_leaves {d : Idx} (hd : d ∈ S) :
    ∑ x ∈ range 2304, (if hid (ba (enc d)) (2303 + x) = false then 1 else 0) = 2287 := by
  have hd' : ∀ i, (d i).val < 120 := mem_S.1 hd
  set I : Finset ℕ := univ.image fun i : Fin BAVC.tau => 17 * (d i).val + i.val with hI
  have hIc : #I = 17 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_fin]; rfl
    · intro i i' h
      have := hd' i
      have := hd' i'
      have := i.isLt
      have := i'.isLt
      simp only [BAVC.tau] at *
      exact Fin.ext (by omega)
  have hIs : I ⊆ range 2304 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.1 hx
    have := hd' i
    have := i.isLt
    simp only [BAVC.tau] at *
    rw [mem_range]
    omega
  have e : ∀ x ∈ range 2304, (if hid (ba (enc d)) (2303 + x) = false then 1 else 0) =
      if x ∈ I then 0 else 1 := by
    intro x hx
    rw [mem_range] at hx
    have hl : ∀ i : Fin BAVC.tau, Desc (2303 + x) (BAVC.treePos i (d i).val) ↔
        BAVC.treePos i (d i).val = 2303 + x := fun i =>
      desc_leaf (by rw [numLeaves_val]; omega) (treePos_lt i.isLt (d i).isLt)
    have hm : x ∈ I ↔ ∃ i : Fin BAVC.tau, BAVC.treePos i (d i).val = 2303 + x := by
      rw [hI, mem_image]
      refine exists_congr fun i => ?_
      rw [treePos_box (hd' i)]
      simp only [mem_univ, true_and]
      omega
    have key : hid (ba (enc d)) (2303 + x) = false ↔ x ∉ I := by
      rw [hid_false_enc d (show 2303 + x < BAVC.numNodes by rw [numNodes_val]; omega), hm]
      simp only [hl, not_exists]
    by_cases hx' : x ∈ I
    · have : ¬ hid (ba (enc d)) (2303 + x) = false := fun h => key.1 h hx'
      simp [this, hx']
    · have : hid (ba (enc d)) (2303 + x) = false := key.2 hx'
      simp only [this, hx', ↓reduceIte]
  have hf : (range 2304).filter (fun x => x ∈ I) = I := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hIs]
  have hc := Finset.card_filter_add_card_filter_not (s := range 2304) (fun x => x ∈ I)
  rw [hf, hIc, card_range] at hc
  rw [Finset.sum_congr rfl e, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
    smul_eq_mul, mul_one, zero_add]
  omega

lemma hid_root (d : Idx) : hid (ba (enc d)) 0 = true := by
  rw [hid_enc d (by rw [numNodes_val]; norm_num)]
  exact ⟨⟨0, by simp [BAVC.tau]⟩, desc_zero _⟩

/-- **The open count is `2287` minus the off count**, on the box. -/
theorem openCount_add_Z {d : Idx} (hd : d ∈ S) : openCount (ba (enc d)) + Z d = 2287 := by
  let N : ℕ → ℕ := fun v => if hid (ba (enc d)) v = false then 1 else 0
  have hZ : Z d = ∑ v ∈ range 2303, N v := by simp only [Z, N]
  have h1 : openCount (ba (enc d)) + 2 * Z d =
      ∑ n ∈ range 2303, (N (2 * n + 1) + N (2 * n + 2)) := by
    rw [openCount_eq_sum, numLeaves_val, hZ, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [mem_range] at hn
    have := xor_count (hid (ba (enc d)) (2 * n + 1)) (hid (ba (enc d)) (2 * n + 2))
    rw [← hid_internal _ (show n < BAVC.numLeaves - 1 by rw [numLeaves_val]; omega)] at this
    exact this
  have h2 := sum_pairs N 2303
  have h0 : N 0 = 0 := by simp [N, hid_root]
  rw [show 2 * 2303 + 1 = 2303 + 2304 by norm_num, Finset.sum_range_add, h0, add_zero] at h2
  have h3 : ∑ x ∈ range 2304, N (2303 + x) = 2287 := sum_leaves hd
  omega

/-! ## Chebyshev -/

lemma cheb_point (z : ℕ) (b : Prop) [Decidable b] (hb : b → z ≤ 2181) :
    256 * (if b then 1 else 0) + 4394 * z ≤ z ^ 2 + 2197 ^ 2 := by
  split_ifs with h
  · have hz := hb h
    have : (16 : ℤ) ≤ 2197 - z := by omega
    have key : (256 : ℤ) + 4394 * z ≤ z ^ 2 + 2197 ^ 2 := by nlinarith
    exact_mod_cast key
  · have key : (4394 : ℤ) * z ≤ z ^ 2 + 2197 ^ 2 := by nlinarith [sq_nonneg ((z : ℤ) - 2197)]
    simp only [mul_zero, zero_add]
    exact_mod_cast key

/-- **Chebyshev for the open count** on a set `S'` of index tuples where it is `2287` minus `Zf`
(generic in `S'`, so that the kernel never unfolds the box). -/
lemma cheb (S' : Finset Idx) (Zf : Idx → ℕ)
    (hX : ∀ d ∈ S', openCount (ba (enc d)) + Zf d = 2287) :
    256 * #(S'.filter fun d => ¬ openCount (ba (enc d)) ≤ 105) + 4394 * ∑ d ∈ S', Zf d ≤
      ∑ d ∈ S', Zf d ^ 2 + 2197 ^ 2 * #S' ∧
    #(S'.filter fun d => openCount (ba (enc d)) ≤ 105) +
      #(S'.filter fun d => ¬ openCount (ba (enc d)) ≤ 105) = #S' := by
  have hpt : ∀ d ∈ S', 256 * (if ¬ openCount (ba (enc d)) ≤ 105 then 1 else 0) + 4394 * Zf d ≤
      Zf d ^ 2 + 2197 ^ 2 := fun d hd =>
    cheb_point _ _ fun h => by have := hX d hd; omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, ← Finset.card_filter] at hsum
  exact ⟨by linarith, Finset.card_filter_add_card_filter_not _⟩

/-- **`2¹¹⁴ ≤ |A|`**: at least `2¹¹⁴` of the `2¹²⁸` values of `Δ` are accepted by
`grind_and_open`. By Chebyshev on `S` with the second moment of the off count. -/
theorem card_accSet_ge_114 : 2 ^ 114 ≤ #accSet := by
  obtain ⟨hc, hgb⟩ := cheb S Z fun d hd => openCount_add_Z hd
  rw [sum_Z, sum_Z2, card_S, sumU_val] at hc
  have hU2 := sum_U2
  rw [sumPU_val, sumD_val, sumDiag_val] at hU2
  rw [card_S] at hgb
  have hg := card_good_le S accSet enc_mem
  have h4 : (120 : ℕ) ^ 17 = 221861110674043699200000000000000000 := by norm_num
  have h5 : (2 : ℕ) ^ 114 = 20769187434139310514121985316880384 := by norm_num
  rw [h4] at hc hgb
  rw [h5]
  omega

end VoleMole.ZK.Accept
