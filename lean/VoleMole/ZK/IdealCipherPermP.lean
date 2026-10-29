import VoleMole.ZK.IdealCipherPerm
import VoleMole.ZK.IdealCipherP

/-!
# Puncturing a GGM tree with permutation rows when part of the table is fixed in advance

`IC.puncturePm` (`ZK/IdealCipherPerm.lean`) replaces the permutations of the secret nodes by
independent uniform permutations, against a distinguisher that reads the uniform permutation table
`π`. Here the table the tree and the distinguisher see is `π` **patched** on a fixed set `P` of keys
(`patchT P W π`: the permutations `W k` at `k ∈ P`, `π` elsewhere): the table conditioned on its
rows at `P`, as when an earlier adversary read the cipher at `P` before the tree was built
(`ZK/AdaptRO.lean`). This is `ZK/IdealCipherP.lean` for permutation rows.

* `hopPmP`: replacing node `n` costs `(N + q + |P|) / (|K| − s)`: as in `IC.hopPm`, the node's value
  is its parent's (replaced) permutation at a fresh input, and programming the table at it is
  perfect **unless** the value is in `P` (where the patched table is not uniform) or a candidate.
* `puncturePmP`: the hybrid over the secret nodes, `|secret| · (N + q + |P|) / (|K| − s)`.
* `experPmP_empty`, `experPmP_close`: the real experiment, and a fully replaced experiment whose
  output is `ε`-close to `F` of a uniform `h` for every table, with the patched table.
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

section HopPmP

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {x : ℕ → K} {N : ℕ} {O : Type}

/-- **The experiment with permutation rows and the table patched on `P`**: `experPm`, with the tree
and `A` on `patchT P W π`. -/
noncomputable def experPmP (x : ℕ → K) (N : ℕ) (rep : Finset ℕ) (Φ : (ℕ → K → K) → O)
    (A : O → (K → Equiv.Perm K) → Prop) (P : Finset K) (W : K → Equiv.Perm K) : ℝ :=
  pr (PCoins K N × (K → Equiv.Perm K))
    (fun p => A (Φ (rowAt x N rep (cf (patchT P W p.2)) (cf p.1.2) p.1.1)) (patchT P W p.2))

/-- The candidates on the patched table, and the patched keys. -/
noncomputable def candsPmP (x : ℕ → K) (N : ℕ) (ins : Finset ℕ) (Φ : (ℕ → K → K) → O)
    (Q : O → (K → Equiv.Perm K) → Finset K) (P : Finset K) (W : K → Equiv.Perm K)
    (p : PCoins K N × (K → Equiv.Perm K)) : Finset K :=
  candsPm x N ins Φ Q (p.1, patchT P W p.2) ∪ P

omit [Fintype K] [Nonempty K] in
lemma candsPmP_card (ins : Finset ℕ) (Φ : (ℕ → K → K) → O)
    (Q : O → (K → Equiv.Perm K) → Finset K) (P : Finset K) (W : K → Equiv.Perm K) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (p : PCoins K N × (K → Equiv.Perm K)) :
    (candsPmP x N ins Φ Q P W p).card ≤ N + q + P.card :=
  (card_union_le _ _).trans (Nat.add_le_add_right (candsPm_card ins Φ Q hq _) _)

/-- **The secret value is guessed with probability `≤ (N + q + |P|) / (|K| − s)`** (patched
table). -/
lemma pr_secretPm_mem_candsP {rep : Finset ℕ} {n : ℕ} (hN : n < N)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (rd : Finset K) {s : ℕ} (hrd : rd.card ≤ s)
    (hs : s < Fintype.card K) (hxn : n ≠ 0 → x n ∉ rd)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ∈ rd)
    (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (Q : O → (K → Equiv.Perm K) → Finset K) {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q)
    (P : Finset K) (W : K → Equiv.Perm K) :
    pr (PCoins K N × (K → Equiv.Perm K)) (fun p => secretVal (x := x) n hN (p.1.1, cf p.1.2) ∈
      candsPmP x N (insert n rep) Φ Q P W p) ≤
      (N + q + P.card : ℕ) / (Fintype.card K - s : ℕ) := by
  have hin : n ∈ insert n rep := Finset.mem_insert_self _ _
  have hden : (0 : ℝ) < (Fintype.card K - s : ℕ) := by
    exact_mod_cast (by omega : 0 < Fintype.card K - s)
  by_cases h0 : n = 0
  · subst h0
    have hT : ∀ (p : PCoins K N × (K → Equiv.Perm K)) (k : K),
        candsPmP x N (insert 0 rep) Φ Q P W ((k, p.1.2), p.2) =
          candsPmP x N (insert 0 rep) Φ Q P W p := by
      intro p k
      have hrow := fun m => (rowAt_seed_indep (x := x) hin hN (cf (patchT P W p.2)) (cf p.1.2) k
        p.1.1 m)
      unfold candsPmP candsPm
      congr 2
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ 0 := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hrow m).2 hm'
      · simp only
        rw [show rowAt x N (insert 0 rep) (cf (patchT P W p.2)) (cf p.1.2) k =
          rowAt x N (insert 0 rep) (cf (patchT P W p.2)) (cf p.1.2) p.1.1 from
            funext fun m => (hrow m).1]
    have h := pr_mem_reset_le (α := PCoins K N × (K → Equiv.Perm K)) (fun p => p.1.1)
      (fun p k => ((k, p.1.2), p.2)) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      (candsPmP x N (insert 0 rep) Φ Q P W) hT (candsPmP_card _ Φ Q P W hq)
    refine (le_of_eq (pr_congr fun p => ?_)).trans (h.trans ?_)
    · simp only [secretVal, ↓reduceIte]
    · exact div_le_div_of_nonneg_left (by positivity) hden (by exact_mod_cast Nat.sub_le _ _)
  · have hp : (n - 1) / 2 ∈ insert n rep := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    let st : PCoins K N × (K → Equiv.Perm K) → Equiv.Perm K → PCoins K N × (K → Equiv.Perm K) :=
      fun p σ => ((p.1.1, Function.update p.1.2 pf σ), p.2)
    have hT : ∀ p σ σ', (∀ y ∈ rd, σ y = σ' y) →
        candsPmP x N (insert n rep) Φ Q P W (st p σ) =
          candsPmP x N (insert n rep) Φ Q P W (st p σ') := by
      intro p σ σ' hσ
      have hind := rowAt_congr_par (x := x) hin hN hp rd (hsib h0) (cf (patchT P W p.2))
        (cf (Function.update p.1.2 pf σ)) (cf (Function.update p.1.2 pf σ')) p.1.1
        (fun j hj => by
          have : j ≠ pf := fun e => hj (by rw [e])
          simp only [cf, Function.update_of_ne this])
        (fun _ y hy => by simp only [cf, pf, Function.update_self]; exact hσ y hy)
      unfold candsPmP candsPm
      congr 2
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ n := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hind m).2 hm'
      · simp only [st]
        rw [hΦ h0 _ _ (fun m hm => (hind m).1 hm) (fun y hy => by
          rw [rowAt_of_mem hp hpN, rowAt_of_mem hp hpN]
          simp only [cf, pf, Function.update_self]; exact hσ y hy)]
    have h := pr_perm_reset_le (α := PCoins K N × (K → Equiv.Perm K)) (fun p => p.1.2 pf) st
      (fun p σ => by simp [st]) (fun p σ σ' => by simp [st]) (fun p => by simp [st])
      (x n) rd (hxn h0) (candsPmP x N (insert n rep) Φ Q P W) hT (candsPmP_card _ Φ Q P W hq)
    refine (le_of_eq (pr_congr fun p => ?_)).trans (h.trans ?_)
    · simp only [secretVal, h0, ↓reduceIte]
      rfl
    · exact div_le_div_of_nonneg_left (by positivity) hden
        (by exact_mod_cast Nat.sub_le_sub_left hrd _)

/-- **One hop with permutation rows and the table patched on `P`**: replacing node `n` costs
`(N + q + |P|) / (|K| − s)`. -/
theorem hopPmP (rep : Finset ℕ) (n : ℕ) (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (rd : Finset K) {s : ℕ} (hrd : rd.card ≤ s)
    (hs : s < Fintype.card K) (hxn : n ≠ 0 → x n ∉ rd)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ∈ rd)
    (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → Equiv.Perm K) → Prop) (Q : O → (K → Equiv.Perm K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset K) (W : K → Equiv.Perm K) :
    |experPmP x N rep Φ A P W - experPmP x N (insert n rep) Φ A P W| ≤
      (N + q + P.card : ℕ) / (Fintype.card K - s : ℕ) := by
  classical
  let v : PCoins K N → K := fun c => secretVal (x := x) n hN (c.1, cf c.2)
  let ins := insert n rep
  -- Programming the (unpatched) table at the secret value is perfect.
  have h1 : experPmP x N rep Φ A P W =
      pr (PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K))) (fun p =>
        A (Φ (rowAt x N rep (cf (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)))
          (cf p.1.2) p.1.1)) (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1))) :=
    pr_program_eq (ι := Unit) (x := fun c _ => v c) (fun _ _ _ _ => rfl)
      (fun c _ g => A (Φ (rowAt x N rep (cf (patchT P W g)) (cf c.2) c.1)) (patchT P W g))
  -- The experiment with `n` replaced by the answer.
  let B : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) → Prop := fun p =>
    A (Φ (rowAt x N ins (cf (patchT P W p.2.1)) (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())))
      p.1.1)) (patchT P W p.2.1)
  have h2 : pr _ B = experPmP x N ins Φ A P W := by
    have e := pr_equiv (swapRowPm (K := K) hN)
      (fun p => A (Φ (rowAt x N ins (cf (patchT P W p.2.1)) (cf p.1.2) p.1.1)) (patchT P W p.2.1))
    rw [pr_add_answers (fun p : PCoins K N × (K → Equiv.Perm K) =>
      A (Φ (rowAt x N ins (cf (patchT P W p.2)) (cf p.1.2) p.1.1)) (patchT P W p.2))] at e
    exact e
  -- The bad event: the secret value is a candidate or a patched key.
  let bad : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) → Prop := fun p =>
    v p.1 ∈ candsPmP x N ins Φ Q P W ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1)
  have h3 : pr _ bad ≤ (N + q + P.card : ℕ) / (Fintype.card K - s : ℕ) := by
    have e := pr_equiv (swapRowPm (K := K) hN)
      (fun p => v p.1 ∈ candsPmP x N ins Φ Q P W (p.1, p.2.1))
    rw [pr_add_answers (fun p : PCoins K N × (K → Equiv.Perm K) =>
      v p.1 ∈ candsPmP x N ins Φ Q P W p)] at e
    have e2 : pr _ bad = pr (PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)))
        (fun a => (fun p : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) =>
          v p.1 ∈ candsPmP x N ins Φ Q P W (p.1, p.2.1)) (swapRowPm hN a)) :=
      pr_congr fun a => by
        show v a.1 ∈ _ ↔ v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) ∈ _
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from by
          show secretVal (x := x) n hN (a.1.1, cf (Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ()))) =
            secretVal (x := x) n hN (a.1.1, cf a.1.2)
          rw [cf_update]
          exact secretVal_update hN (a.1.1, cf a.1.2) _]
        rfl
    rw [e2, e]
    exact pr_secretPm_mem_candsP hN hpar rd hrd hs hxn hsib Φ hΦ Q hq P W
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAt x N rep (cf (patchT P W (programAt (fun _ : Unit => v p.1)
      p.2.2 p.2.1))) (cf p.1.2) p.1.1)) (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2
        p.2.1))) ↔ B p) := by
    intro p hp
    have hvP : v p.1 ∉ P := fun h => hp (Finset.mem_union_right _ h)
    have hcom : patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1) =
        programAt (fun _ : Unit => v p.1) p.2.2 (patchT P W p.2.1) :=
      patchT_programAt W p.2.2 p.2.1 fun _ => hvP
    rw [hcom]
    have hgood : ∀ m < N, m ∉ ins → keyAt x N ins (cf (patchT P W p.2.1))
        (Function.update (cf p.1.2) ⟨n, hN⟩ (cf p.2.2 ())) p.1.1 m ≠
          secretVal (x := x) n hN (p.1.1, cf p.1.2) := fun m hm hmi e => hp (by
      show v p.1 ∈ candsPmP x N ins Φ Q P W _
      unfold candsPmP candsPm
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨m,
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hmi⟩, ?_⟩))
      show keyAt x N ins (cf (patchT P W p.2.1)) (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())))
        p.1.1 m = v p.1
      rw [cf_update]
      exact e)
    have hrows := rowAt_program (x := x) hN hnr hpar (cf (patchT P W p.2.1)) (p.1.1, cf p.1.2)
      (cf p.2.2) hgood
    rw [cf_programAt, hΦN _ _ fun m hm => (hrows m hm).1]
    have hnq : v p.1 ∉ Q (Φ (rowAt x N ins (cf (patchT P W p.2.1))
        (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ()))) p.1.1)) (patchT P W p.2.1) :=
      fun h => hp (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    show A (Φ (rowAt x N ins (cf (patchT P W p.2.1))
        (Function.update (cf p.1.2) ⟨n, hN⟩ ⇑(p.2.2 ())) p.1.1))
      (programAt (fun _ : Unit => v p.1) p.2.2 (patchT P W p.2.1)) ↔ B p
    rw [← cf_update]
    exact (hQ _ _ _ fun k hk =>
      (programAt_apply_of_ne _ _ fun _ e => hnq (by rw [e]; exact hk)).symm).symm
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-- **The hybrid over the secret nodes with permutation rows and the table patched on `P`**:
`|sec| · (N + q + |P|) / (|K| − s)`. -/
theorem puncturePmP (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (rd : ℕ → Finset K) {s : ℕ} (hrd : ∀ n, (rd n).card ≤ s) (hs : s < Fintype.card K)
    (hxn : ∀ n < N, sec n → n ≠ 0 → x n ∉ rd n)
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 →
      x m ∈ rd n)
    (Φ : (ℕ → K → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd n, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → Equiv.Perm K) → Prop) (Q : O → (K → Equiv.Perm K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset K) (W : K → Equiv.Perm K) :
    |experPmP x N ∅ Φ A P W - experPmP x N ((range N).filter sec) Φ A P W| ≤
      ((range N).filter sec).card * ((N + q + P.card : ℕ) / (Fintype.card K - s : ℕ)) := by
  have key : ∀ j ≤ N, |experPmP x N ∅ Φ A P W - experPmP x N ((range j).filter sec) Φ A P W| ≤
      ((range j).filter sec).card * ((N + q + P.card : ℕ) / (Fintype.card K - s : ℕ)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hsj
      · have hnot : j ∉ (range j).filter sec := by simp
        have h := hopPmP ((range j).filter sec) j (by omega) hnot (fun h0 => Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hup j (by omega) hsj h0⟩) (rd j) (hrd j) hs
          (hxn j (by omega) hsj) (hsib j (by omega) hsj) Φ (hΦ j (by omega) hsj) hΦN A Q hQ hq P W
        rw [Finset.card_insert_of_notMem hnot, Nat.cast_succ, add_mul, one_mul]
        have := abs_sub_le (experPmP x N ∅ Φ A P W) (experPmP x N ((range j).filter sec) Φ A P W)
          (experPmP x N (insert j ((range j).filter sec)) Φ A P W)
        linarith
      · exact ih
  exact key N le_rfl

omit [Nonempty K] in
/-- **The real experiment with the patched table** (nothing replaced). -/
theorem experPmP_empty (Φ : (ℕ → K → K) → O) (A : O → (K → Equiv.Perm K) → Prop) (P : Finset K)
    (W : K → Equiv.Perm K) :
    experPmP x N ∅ Φ A P W = pr (K × (K → Equiv.Perm K)) (fun p =>
      A (Φ (rowAt x N ∅ (cf (patchT P W p.2)) (fun _ _ => p.1) p.1)) (patchT P W p.2)) := by
  let e : PCoins K N × (K → Equiv.Perm K) ≃ (K × (K → Equiv.Perm K)) × (Fin N → Equiv.Perm K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun c => A (Φ (rowAt x N ∅ (cf (patchT P W c.1.2)) (fun _ _ => c.1.1)
    c.1.1)) (patchT P W c.1.2))
  rw [pr_prod_fst (fun p : K × (K → Equiv.Perm K) =>
    A (Φ (rowAt x N ∅ (cf (patchT P W p.2)) (fun _ _ => p.1) p.1)) (patchT P W p.2))] at h
  rw [← h]
  refine pr_congr fun c => ?_
  show A (Φ (rowAt x N ∅ (cf (patchT P W c.2)) (cf c.1.2) c.1.1)) (patchT P W c.2) ↔ _
  rw [rowAt_empty (cf (patchT P W c.2)) (cf c.1.2) (fun _ _ => c.1.1) c.1.1]
  exact Iff.rfl

omit [Nonempty K] in
/-- **A fully replaced experiment whose output is `ε`-close to `F` of a uniform `h`, for every
table, is `ε`-close to the ideal experiment**, with the patched table. -/
theorem experPmP_close {H : Type} [Fintype H] (rep : Finset ℕ) (Φ : (ℕ → K → K) → O) (F : H → O)
    {ε : ℝ} (hE : ∀ π : K → Equiv.Perm K,
      Close ε (fun c : PCoins K N => Φ (rowAt x N rep (cf π) (cf c.2) c.1)) F)
    (A : O → (K → Equiv.Perm K) → Prop) (P : Finset K) (W : K → Equiv.Perm K) :
    |experPmP x N rep Φ A P W - pr (H × (K → Equiv.Perm K)) (fun h => A (F h.1) (patchT P W h.2))| ≤
      ε :=
  abs_pr_prod_sub_le' (fun p : PCoins K N × (K → Equiv.Perm K) =>
      A (Φ (rowAt x N rep (cf (patchT P W p.2)) (cf p.1.2) p.1.1)) (patchT P W p.2))
    (fun h : H × (K → Equiv.Perm K) => A (F h.1) (patchT P W h.2))
    fun π => hE (patchT P W π) fun o => A o (patchT P W π)

end HopPmP

end VoleMole.ZK.IC
