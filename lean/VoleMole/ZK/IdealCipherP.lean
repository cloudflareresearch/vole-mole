import VoleMole.ZK.IdealCipher

/-!
# Puncturing a GGM tree when part of the cipher table is fixed in advance

`IC.puncture` (`ZK/IdealCipher.lean`) replaces the rows of the secret nodes by independent uniform
rows, against a distinguisher that reads the uniform table `E`. Here the table the tree and the
distinguisher see is `E` **patched** on a fixed set `P` of keys (`patchT P W E`: the rows `W k` at
`k ∈ P`, `E` elsewhere): the table conditioned on its rows at `P`, as when an earlier adversary
read the cipher at `P` before the tree was built (`ZK/AdaptRO.lean`).

* `hopP`: replacing node `n` costs `(N + q + |P|) / |K|`: as in `IC.hop`, the node's value is
  uniform and independent, and programming the table at it is perfect **unless** the value is in
  `P` (where the patched table is not uniform), or read as a key elsewhere.
* `punctureP`: the hybrid over the secret nodes, `|secret| · (N + q + |P|) / |K|`.
* `experP_empty`, `experP_eq_of_close`: the real and the fully replaced experiments, as
  `exper_empty` and `exper_eq_of_close` with the patched table.
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-- **The patched table**: the rows `W k` at the keys `k ∈ P`, `E` elsewhere. -/
def patchT {K Y : Type*} [DecidableEq K] (P : Finset K) (W : K → Y) (E : K → Y) : K → Y :=
  fun k => if k ∈ P then W k else E k

lemma patchT_of_not_mem {K Y : Type*} [DecidableEq K] {P : Finset K} (W E : K → Y) {k : K}
    (hk : k ∉ P) : patchT P W E k = E k := by
  simp only [patchT, hk, ↓reduceIte]

lemma patchT_of_mem {K Y : Type*} [DecidableEq K] {P : Finset K} (W E : K → Y) {k : K}
    (hk : k ∈ P) : patchT P W E k = W k := by
  simp only [patchT, hk, ↓reduceIte]

/-- Patching commutes with programming off the patched keys. -/
lemma patchT_programAt {K Y ι : Type*} [DecidableEq K] {P : Finset K} (W : K → Y) {x : ι → K}
    (u : ι → Y) (E : K → Y) (hx : ∀ i, x i ∉ P) :
    patchT P W (programAt x u E) = programAt x u (patchT P W E) := by
  classical
  funext k
  by_cases hk : k ∈ P
  · rw [patchT_of_mem _ _ hk, programAt_apply_of_ne _ _ fun i hi => hx i (by rw [hi]; exact hk),
      patchT_of_mem _ _ hk]
  · rw [patchT_of_not_mem _ _ hk]
    unfold programAt
    rw [Function.extend_def, Function.extend_def]
    split_ifs
    · rfl
    · rw [patchT_of_not_mem _ _ hk]

section Hop

variable {K X : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X]
  {x : ℕ → X} {N : ℕ} {O : Type}

/-- **The experiment with the patched table**: `exper`, with the tree and `A` on `patchT P W E`. -/
noncomputable def experP (x : ℕ → X) (N : ℕ) (rep : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (A : O → (K → X → K) → Prop) (P : Finset K) (W : K → X → K) : ℝ :=
  pr (Coins K X N × (K → X → K)) (fun p =>
    A (Φ (rowAt x N rep (patchT P W p.2) p.1.2 p.1.1)) (patchT P W p.2))

/-- The candidates on the patched table, and the patched keys. -/
noncomputable def candsP (x : ℕ → X) (N : ℕ) (ins : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset K) (P : Finset K) (W : K → X → K)
    (p : Coins K X N × (K → X → K)) : Finset K :=
  cands x N ins Φ Q (p.1, patchT P W p.2) ∪ P

omit [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X] in
lemma candsP_card (ins : Finset ℕ) (Φ : (ℕ → X → K) → O) (Q : O → (K → X → K) → Finset K)
    (P : Finset K) (W : K → X → K) {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q)
    (p : Coins K X N × (K → X → K)) :
    (candsP x N ins Φ Q P W p).card ≤ N + q + P.card :=
  (card_union_le _ _).trans (Nat.add_le_add_right (cands_card ins Φ Q hq _) _)

/-- **The secret value is guessed with probability `≤ (N + q + |P|) / |K|`.** -/
lemma pr_secret_mem_candsP {rep : Finset ℕ} {n : ℕ} (hN : n < N)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (Q : O → (K → X → K) → Finset K) {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q)
    (P : Finset K) (W : K → X → K) :
    pr (Coins K X N × (K → X → K)) (fun p => secretVal (x := x) n hN p.1 ∈
      candsP x N (insert n rep) Φ Q P W p) ≤ (N + q + P.card : ℕ) / Fintype.card K := by
  have hin : n ∈ insert n rep := Finset.mem_insert_self _ _
  by_cases h0 : n = 0
  · subst h0
    refine pr_mem_reset_le (α := Coins K X N × (K → X → K)) (fun p => p.1.1)
      (fun p k => ((k, p.1.2), p.2)) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      (candsP x N (insert 0 rep) Φ Q P W) (fun p k => ?_) (candsP_card _ Φ Q P W hq)
    have hrow := fun m => (rowAt_seed_indep (x := x) hin hN (patchT P W p.2) p.1.2 k p.1.1 m)
    unfold candsP cands
    congr 2
    · refine Finset.image_congr fun m hm => ?_
      have hm' : m ≠ 0 := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
      exact (hrow m).2 hm'
    · simp only
      rw [show rowAt x N (insert 0 rep) (patchT P W p.2) p.1.2 k =
          rowAt x N (insert 0 rep) (patchT P W p.2) p.1.2 p.1.1 from funext fun m => (hrow m).1]
  · have hp : (n - 1) / 2 ∈ insert n rep := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    let st : Coins K X N × (K → X → K) → K → Coins K X N × (K → X → K) := fun p k =>
      ((p.1.1, Function.update p.1.2 pf (Function.update (p.1.2 pf) (x n) k)), p.2)
    have hf : ∀ p k, (st p k).1.2 pf (x n) = k := fun p k => by simp [st]
    have hss : ∀ p k k', st (st p k) k' = st p k' := fun p k k' => by simp [st]
    have hsf : ∀ p, st p (p.1.2 pf (x n)) = p := fun p => by simp [st]
    have hT : ∀ p k, candsP x N (insert n rep) Φ Q P W (st p k) =
        candsP x N (insert n rep) Φ Q P W p := by
      intro p k
      have hind := rowAt_point_indep (x := x) hin hN hp (hsib h0) (patchT P W p.2) p.1.2 p.1.1 k
      unfold candsP cands
      congr 2
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ n := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hind m).2 hm'
      · simp only [st]
        have hρ : rowAt x N (insert n rep) (patchT P W p.2) (Function.update p.1.2 pf
            (Function.update (p.1.2 pf) (x n) k)) p.1.1 =
            Function.update (rowAt x N (insert n rep) (patchT P W p.2) p.1.2 p.1.1) ((n - 1) / 2)
              (Function.update (rowAt x N (insert n rep) (patchT P W p.2) p.1.2 p.1.1
                ((n - 1) / 2)) (x n) k) := by
          funext m
          by_cases hm : m = (n - 1) / 2
          · subst hm
            rw [Function.update_self, rowAt_of_mem hp hpN, rowAt_of_mem hp hpN, Function.update_self]
          · rw [Function.update_of_ne hm, (hind m).1 hm]
        rw [hρ, hΦ h0]
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_le (α := Coins K X N × (K → X → K))
      (fun p => p.1.2 pf (x n)) st hf hss hsf (candsP x N (insert n rep) Φ Q P W) hT
      (candsP_card _ Φ Q P W hq))
    simp only [secretVal, h0, ↓reduceIte]
    rfl

/-- **One hop with the patched table**: replacing node `n` costs `(N + q + |P|) / |K|`. -/
theorem hopP (rep : Finset ℕ) (n : ℕ) (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset K) (W : K → X → K) :
    |experP x N rep Φ A P W - experP x N (insert n rep) Φ A P W| ≤
      (N + q + P.card : ℕ) / Fintype.card K := by
  classical
  let v : Coins K X N → K := secretVal (x := x) n hN
  let ins := insert n rep
  -- Programming the (unpatched) table at the secret value is perfect.
  have h1 : experP x N rep Φ A P W = pr (Coins K X N × ((K → X → K) × (Unit → X → K))) (fun p =>
      A (Φ (rowAt x N rep (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) p.1.2 p.1.1))
        (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1))) :=
    pr_program_eq (ι := Unit) (x := fun c _ => v c) (fun _ _ _ _ => rfl)
      (fun c _ g => A (Φ (rowAt x N rep (patchT P W g) c.2 c.1)) (patchT P W g))
  -- The experiment with `n` replaced by the answer.
  let B : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    A (Φ (rowAt x N ins (patchT P W p.2.1) (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1))
      (patchT P W p.2.1)
  have h2 : pr _ B = experP x N ins Φ A P W := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => A (Φ (rowAt x N ins (patchT P W p.2.1) p.1.2 p.1.1)) (patchT P W p.2.1))
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) =>
      A (Φ (rowAt x N ins (patchT P W p.2) p.1.2 p.1.1)) (patchT P W p.2))] at e
    exact e
  -- The bad event: the secret value is a candidate or a patched key.
  let bad : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    v p.1 ∈ candsP x N ins Φ Q P W ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1)
  have h3 : pr _ bad ≤ (N + q + P.card : ℕ) / Fintype.card K := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => v p.1 ∈ candsP x N ins Φ Q P W (p.1, p.2.1))
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) =>
      v p.1 ∈ candsP x N ins Φ Q P W p)] at e
    have e2 : pr _ bad = pr (Coins K X N × ((K → X → K) × (Unit → X → K)))
        (fun a => (fun p : Coins K X N × ((K → X → K) × (Unit → X → K)) =>
          v p.1 ∈ candsP x N ins Φ Q P W (p.1, p.2.1)) (swapRow hN a)) :=
      pr_congr fun a => by
        show v a.1 ∈ _ ↔ v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) ∈ _
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from
          secretVal_update hN a.1 _]
        rfl
    rw [e2, e]
    exact pr_secret_mem_candsP hN hpar hsib Φ hΦ Q hq P W
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAt x N rep (patchT P W (programAt (fun _ : Unit => v p.1)
      p.2.2 p.2.1)) p.1.2 p.1.1)) (patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1))) ↔
      B p) := by
    intro p hp
    have hvP : v p.1 ∉ P := fun h => hp (Finset.mem_union_right _ h)
    have hcom : patchT P W (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1) =
        programAt (fun _ : Unit => v p.1) p.2.2 (patchT P W p.2.1) :=
      patchT_programAt W p.2.2 p.2.1 fun _ => hvP
    rw [hcom]
    have hgood : ∀ m < N, m ∉ ins → keyAt x N ins (patchT P W p.2.1)
        (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1 m ≠ secretVal (x := x) n hN p.1 :=
      fun m hm hmi e => hp (by
        show v p.1 ∈ candsP x N ins Φ Q P W _
        unfold candsP cands
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨m,
          Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hmi⟩, e⟩)))
    have hrows := rowAt_program hN hnr hpar (patchT P W p.2.1) p.1 p.2.2 hgood
    rw [hΦN _ _ fun m hm => (hrows m hm).1]
    have hnq : v p.1 ∉ Q (Φ (rowAt x N ins (patchT P W p.2.1)
        (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1)) (patchT P W p.2.1) :=
      fun h => hp (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    exact (hQ _ _ _ fun k hk =>
      (programAt_apply_of_ne _ _ fun _ e => hnq (by rw [e]; exact hk)).symm).symm
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-- **The hybrid over the secret nodes with the patched table**: `|sec| · (N + q + |P|) / |K|`. -/
theorem punctureP (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset K) (W : K → X → K) :
    |experP x N ∅ Φ A P W - experP x N ((range N).filter sec) Φ A P W| ≤
      ((range N).filter sec).card * ((N + q + P.card : ℕ) / Fintype.card K) := by
  have key : ∀ j ≤ N, |experP x N ∅ Φ A P W - experP x N ((range j).filter sec) Φ A P W| ≤
      ((range j).filter sec).card * ((N + q + P.card : ℕ) / Fintype.card K) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hs
      · have hnot : j ∉ (range j).filter sec := by simp
        have h := hopP ((range j).filter sec) j (by omega) hnot (fun h0 => Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hup j (by omega) hs h0⟩) (hsib j (by omega) hs) Φ
          (hΦ j (by omega) hs) hΦN A Q hQ hq P W
        rw [Finset.card_insert_of_notMem hnot, Nat.cast_succ, add_mul, one_mul]
        have := abs_sub_le (experP x N ∅ Φ A P W) (experP x N ((range j).filter sec) Φ A P W)
          (experP x N (insert j ((range j).filter sec)) Φ A P W)
        linarith
      · exact ih
  exact key N le_rfl

/-- **The real experiment with the patched table** (nothing replaced). -/
theorem experP_empty (Φ : (ℕ → X → K) → O) (A : O → (K → X → K) → Prop) (P : Finset K)
    (W : K → X → K) :
    experP x N ∅ Φ A P W = pr (K × (K → X → K)) (fun p =>
      A (Φ (rowAt x N ∅ (patchT P W p.2) (fun _ _ => p.1) p.1)) (patchT P W p.2)) := by
  let e : Coins K X N × (K → X → K) ≃ (K × (K → X → K)) × (Fin N → X → K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun c => A (Φ (rowAt x N ∅ (patchT P W c.1.2) (fun _ _ => c.1.1) c.1.1))
    (patchT P W c.1.2))
  rw [pr_prod_fst (fun p : K × (K → X → K) =>
    A (Φ (rowAt x N ∅ (patchT P W p.2) (fun _ _ => p.1) p.1)) (patchT P W p.2))] at h
  rw [← h]
  refine pr_congr fun c => ?_
  show A (Φ (rowAt x N ∅ (patchT P W c.2) c.1.2 c.1.1)) (patchT P W c.2) ↔ _
  rw [rowAt_empty (patchT P W c.2) c.1.2 (fun _ _ => c.1.1) c.1.1]
  exact Iff.rfl

/-- **An experiment whose output has, for every table, the law of `F` of a uniform `h`** is the
ideal experiment, with the patched table. -/
theorem experP_eq_of_close {H : Type} [Fintype H] (rep : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (F : H → O) (hE : ∀ E : K → X → K, Close 0 (fun c : Coins K X N => Φ (rowAt x N rep E c.2 c.1)) F)
    (A : O → (K → X → K) → Prop) (P : Finset K) (W : K → X → K) :
    experP x N rep Φ A P W = pr (H × (K → X → K)) (fun h => A (F h.1) (patchT P W h.2)) := by
  have h := Close.prod_left (X := fun (c : Coins K X N) (E : K → X → K) =>
      (Φ (rowAt x N rep (patchT P W E) c.2 c.1), patchT P W E))
    (Y := fun (h : H) (E : K → X → K) => (F h, patchT P W E))
    (fun E => (hE (patchT P W E)).map fun o => (o, patchT P W E)) (fun o => A o.1 o.2)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

end Hop

end VoleMole.ZK.IC
