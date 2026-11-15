import VoleMole.ROM.OneMoreClsSim

/-!
# The wrapped forger's budget

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). The wrapper of U1^cls (`wrapE`) adds, before each
`H₂¹` query of the forger, one `H₂⁴` query, one `H₄` query and at most `NdC` `H₅` queries
(`decIns_length_le`), and no cipher or `hash_to_target` query. So a forger within `qA`, `nA`, `qE`,
`Q_T` gives a wrapped forger within `qW qA NdC`, `nW nA qA NdC`, `qE`, `Q_T`
(`forgerBound_wrapE`), and Theorem U1^cls (`pomfrit_U1_cls_sim`) needs only the forger's budget
(`pomfrit_U1_cls_sim'`).

`NdC = 17·255·2¹³⁶·242·312` is a crude count (every tree, every leftover tree at `2⁸` blocks); the
decoder's actual work is at most `255·2⁸·242` points for the one class it decodes (two classes of
width `≥ 51` leave at most one tree, `pomfrit-lemmap-tight.md` §6A.2). It enters the bound only
through the total number of hash queries, in the term `n'·2⁻⁴⁴⁸`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge VoleMole.PomFRIT

/-- A crude bound on the decoder's `H₅` inputs at one `H₂¹` query. -/
def NdC : ℕ := 17 * (255 * (2 ^ 8) ^ 17 * 242 * 312)

lemma length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [Nat.succ_mul]; omega

/-- **The decoder's `H₅` inputs at one `H₂¹` query are at most `NdC`.** -/
theorem decIns_length_le (lr : Bool) (E : CTable) (Lb : QueryLog specIC) (x1 iv : ByteArray) :
    (decIns lr E Lb x1 iv).length ≤ NdC := by
  classical
  let _ : HasPrg := icPrg E.cipher
  unfold decIns NdC
  refine (length_flatMap_le _ _ (255 * (2 ^ 8) ^ 17 * 242 * 312) fun i _ => ?_).trans ?_
  · refine (length_flatMap_le _ _ 312 fun Δ _ => ?_).trans ?_
    · simp [IC.gateIns, gateInputs_length]
    · rw [Finset.length_toList]
      refine Nat.mul_le_mul_right _ ((card_clsPts_le _ _ _ _ _).trans ?_)
      refine Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) ?_) (by simp [nGen]; decide)
      refine (Finset.prod_le_pow_card _ _ (2 ^ 8) fun k _ => ?_).trans ?_
      · rw [card_block]; exact Nat.pow_le_pow_right (by norm_num) (width_le_eight k)
      · exact Nat.pow_le_pow_right (by norm_num) ((Finset.card_le_univ _).trans (by simp; decide))
  · rw [Finset.length_toList]
    exact Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans (by simp; decide))

/-! ## Query bounds through the forger's oracles -/

section Bounds

variable {α β : Type}

theorem isKindQueryBoundU_bind {oa : OracleComp specU α} {ob : α → OracleComp specU β}
    {q₁ q₂ : Kind → ℕ} (h₁ : IsKindQueryBoundU oa q₁) (h₂ : ∀ a, IsKindQueryBoundU (ob a) q₂) :
    IsKindQueryBoundU (oa >>= ob) (q₁ + q₂) := by
  refine isQueryBound_bind (combine := (· + ·)) (fun t b₁ b₂ b hb => ?_) (fun t b₁ b₂ b hb => ?_)
    h₁ h₂
  · rcases t with (d | x) | x
    · simp only [Pi.add_apply] at hb ⊢; omega
    · exact ⟨trivial, trivial⟩
    · exact ⟨trivial, trivial⟩
  · rcases t with (d | x) | x
    · constructor <;> funext k <;> by_cases hk : k = d.1 <;>
        simp [hk, Function.update_of_ne, Pi.add_apply] <;> omega
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

theorem IsKindQueryBoundU.mono {oa : OracleComp specU α} {q q' : Kind → ℕ}
    (h : IsKindQueryBoundU oa q) (hle : q ≤ q') : IsKindQueryBoundU oa q' := by
  induction oa using OracleComp.inductionOn generalizing q q' with
  | pure _ => trivial
  | query_bind t k ih =>
    unfold IsKindQueryBoundU at h ⊢
    rw [isQueryBound_query_bind_iff] at h ⊢
    obtain ⟨hc, hk⟩ := h
    rcases t with (d | x) | x
    · refine ⟨lt_of_lt_of_le hc (hle d.1), fun u => ih u (hk u) fun k' => ?_⟩
      show Function.update q d.1 (q d.1 - 1) k' ≤ Function.update q' d.1 (q' d.1 - 1) k'
      by_cases hk' : k' = d.1
      · rw [hk', Function.update_self, Function.update_self]
        exact Nat.sub_le_sub_right (hle d.1) 1
      · rw [Function.update_of_ne hk', Function.update_of_ne hk']; exact hle k'
    · exact ⟨trivial, fun u => ih u (hk u) hle⟩
    · exact ⟨trivial, fun u => ih u (hk u) hle⟩

lemma isKindQueryBoundU_toU (m : OracleComp specIC α) :
    ∀ q, IsKindQueryBoundIC m q → IsKindQueryBoundU (toU m) q := by
  induction m using OracleComp.inductionOn with
  | pure a => intro q _; trivial
  | query_bind t k ih =>
    intro q h
    simp only [toU, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    unfold IsKindQueryBoundIC at h
    unfold IsKindQueryBoundU
    rw [isQueryBound_query_bind_iff] at h
    erw [isQueryBound_query_bind_iff]
    rcases t with d | x
    · exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · exact ⟨trivial, fun u => ih u _ (h.2 u)⟩

lemma isQueryBoundP_toU (m : OracleComp specIC α) (P : DomIC ⊕ (ByteArray ⊕ TG) → Prop)
    (P' : DomIC → Prop) [DecidablePred P] [DecidablePred P'] (hPP : ∀ t, P (.inl t) ↔ P' t) :
    ∀ n, IsQueryBoundP m P' n → IsQueryBoundP (toU m) P n := by
  induction m using OracleComp.inductionOn with
  | pure a => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n h
    simp only [toU, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    rw [isQueryBoundP_query_bind_iff] at h
    erw [isQueryBoundP_query_bind_iff]
    by_cases ht : P' t
    · have ht' : P (.inl t) := (hPP t).2 ht
      simp only [ht, ht', ite_true, not_true_eq_false, false_or] at h ⊢
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · have ht' : ¬P (.inl t) := fun h' => ht ((hPP t).1 h')
      simp only [ht, ht', ite_false, not_false_eq_true, true_or, true_and] at h ⊢
      exact fun u => ih u _ (h u)

/-- The `H₅` queries of the wrapper cost `H₅` queries only. -/
lemma kinds_mapM_h5E (l : List ByteArray) :
    IsKindQueryBoundIC (l.mapM h5E) (Function.update 0 .h5 l.length) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    simp only [List.mapM_cons]
    refine (isKindQueryBoundIC_bind (isKindQueryBoundIC_map_hash (.h5, a) _) fun _ =>
      isKindQueryBoundIC_bind (q₂ := 0) ih fun xs =>
        (show IsKindQueryBoundIC (pure _ : OracleComp specIC (QueryLog specIC)) 0 from trivial)).mono
      fun k => ?_
    by_cases hk : k = .h5
    · subst hk; simp; omega
    · simp [Function.update_of_ne hk]

lemma left_mapM_h5E (l : List ByteArray) :
    IsQueryBoundP (l.mapM h5E) (fun t => t.isLeft = true) l.length := by
  induction l with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a l ih =>
    simp only [List.mapM_cons, List.length_cons]
    refine (isQueryBoundP_bind (n := 1) (m := l.length) ?_ fun _ _ =>
      (isQueryBoundP_bind (n := l.length) (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _)).mono
      (by omega)
    exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)

lemma right_mapM_h5E (l : List ByteArray) :
    IsQueryBoundP (l.mapM h5E) (fun t => t.isRight = true) 0 := by
  induction l with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a l ih =>
    simp only [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ =>
      (isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _))
    exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 (by simp))

lemma kinds_queryIC (d : Dom) :
    IsKindQueryBoundIC (liftM (specIC.query (.inl d)) : OracleComp specIC (Ans d))
      (Function.update 0 d.1 1) := by
  simpa using isKindQueryBoundIC_map_hash d id

variable (lr : Bool) (E : CTable)

lemma kinds_coverIC (L : QueryLog specIC) (x1 : ByteArray) :
    IsKindQueryBoundIC (coverIC lr E L x1) (wrapQueries NdC) := by
  unfold coverIC
  refine (isKindQueryBoundIC_bind (kinds_queryIC muCell) fun um =>
    isKindQueryBoundIC_bind (show IsKindQueryBoundIC _ (Function.update 0 .h4 1) from
      kinds_queryIC (ivCell lr x1 um.ba)) fun ui =>
      isKindQueryBoundIC_bind (q₁ := Function.update 0 .h5 NdC) (q₂ := 0)
        (show IsKindQueryBoundIC (List.mapM h5E _) _ from
          (kinds_mapM_h5E (decIns lr E L x1 ui.ba)).mono fun k => by
            by_cases hk : k = .h5
            · subst hk; simpa using decIns_length_le lr E L x1 ui.ba
            · simp [Function.update_of_ne hk]) fun _ =>
        (show IsKindQueryBoundIC (pure _ : OracleComp specIC (QueryLog specIC)) 0 from
          trivial)).mono fun k => ?_
  by_cases h1 : k = .muDelayed
  · subst h1; simp [muCell, wrapQueries]
  by_cases h2 : k = .h4
  · subst h2; simp [muCell, wrapQueries]
  by_cases h3 : k = .h5
  · subst h3; simp [muCell, wrapQueries]
  simp [muCell, wrapQueries, h1, h2, h3]

lemma left_coverIC (L : QueryLog specIC) (x1 : ByteArray) :
    IsQueryBoundP (coverIC lr E L x1) (fun t => t.isLeft = true) (NdC + 2) := by
  unfold coverIC
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by simp), fun um => ?_⟩
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by simp), fun ui => ?_⟩
  exact (isQueryBoundP_bind (n := NdC) (m := 0)
    ((show IsQueryBoundP (List.mapM h5E _) _ _ from left_mapM_h5E _).mono
      (decIns_length_le lr E L x1 ui.ba)) fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)

lemma right_coverIC (L : QueryLog specIC) (x1 : ByteArray) :
    IsQueryBoundP (coverIC lr E L x1) (fun t => t.isRight = true) 0 := by
  unfold coverIC
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp), fun um => ?_⟩
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp), fun ui => ?_⟩
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (show IsQueryBoundP (List.mapM h5E _) _ _ from right_mapM_h5E _) fun _ _ =>
      isQueryBoundP_pure _ _ _

/-- The wrapper's hash queries before the query `d`, per kind. -/
noncomputable def cvq : DomIC → Kind → ℕ
  | .inl (k, _) => if k = .h21 then wrapQueries NdC else 0
  | .inr _ => 0

lemma kinds_coverAt (L : QueryLog specIC) (d : DomIC) :
    IsKindQueryBoundIC (coverAt lr E L d) (cvq d) := by
  rcases d with ⟨k, x1⟩ | c
  · by_cases hk : k = .h21
    · subst hk; simpa [coverAt, cvq] using kinds_coverIC lr E L x1
    · simp only [coverAt, cvq, hk, ite_false]; trivial
  · trivial

lemma left_coverAt (L : QueryLog specIC) (d : DomIC) :
    IsQueryBoundP (coverAt lr E L d) (fun t => t.isLeft = true)
      (match d with | .inl (k, _) => if k = .h21 then NdC + 2 else 0 | .inr _ => 0) := by
  rcases d with ⟨k, x1⟩ | c
  · by_cases hk : k = .h21
    · subst hk; simpa [coverAt] using left_coverIC lr E L x1
    · simp only [coverAt, hk, ite_false]; exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

lemma right_coverAt (L : QueryLog specIC) (d : DomIC) :
    IsQueryBoundP (coverAt lr E L d) (fun t => t.isRight = true) 0 := by
  rcases d with ⟨k, x1⟩ | c
  · by_cases hk : k = .h21
    · subst hk; simpa [coverAt] using right_coverIC lr E L x1
    · simp only [coverAt, hk, ite_false]; exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

lemma kinds_queryU_bind {γ : Type} (d : Dom) (f : Ans d → OracleComp specU γ) (B : Kind → ℕ)
    (h : ∀ u, IsKindQueryBoundU (f u) B) :
    IsKindQueryBoundU ((liftM (specU.query (.inl (.inl d))) : OracleComp specU (Ans d)) >>= f)
      (Function.update (0 : Kind → ℕ) d.1 1 + B) := by
  unfold IsKindQueryBoundU
  erw [isQueryBound_query_bind_iff]
  refine ⟨by simp, fun u => (h u).mono fun k => ?_⟩
  show B k ≤ Function.update (Function.update (0 : Kind → ℕ) d.1 1 + B) d.1
    ((Function.update (0 : Kind → ℕ) d.1 1 + B) d.1 - 1) k
  by_cases hk : k = d.1
  · subst hk; simp
  · simp [Function.update_of_ne hk]

lemma budget_h21 (q : Kind → ℕ) (d : Dom) (hq : 0 < q d.1) :
    cvq (.inl d) + (Function.update (0 : Kind → ℕ) d.1 1 + qW (Function.update q d.1 (q d.1 - 1)) NdC) ≤
      qW q NdC := by
  intro k
  obtain ⟨kd, x1⟩ := d
  simp only at hq
  by_cases h21 : kd = .h21
  · subst h21
    obtain ⟨c, hc⟩ : ∃ c, q .h21 = c + 1 := ⟨q .h21 - 1, by omega⟩
    by_cases hk : k = .h21
    · subst hk; simp [cvq, qW, wrapQueries, hc]; omega
    · simp only [cvq, ite_true, qW, Pi.add_apply, Function.update_of_ne hk, Function.update_self,
        hc, Pi.zero_apply, zero_add, Nat.add_sub_cancel]
      rw [Nat.succ_mul]; omega
  · by_cases hk : k = kd
    · subst hk
      simp only [cvq, h21, ite_false, qW, Pi.add_apply, Function.update_self, Pi.zero_apply,
        Function.update_of_ne (Ne.symm h21)]
      omega
    · simp [cvq, h21, qW, Function.update_of_ne hk, Function.update_of_ne (Ne.symm h21)]

theorem kinds_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (q : Kind → ℕ) (L : QueryLog specIC), IsKindQueryBoundU oa q →
      IsKindQueryBoundU ((simulateQ (clsW lr E) oa).run L) (qW q NdC) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro q L _; trivial
  | query_bind t cont ih =>
    intro q L hq
    unfold IsKindQueryBoundU at hq
    rw [isQueryBound_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (d | c) | x
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      refine (isKindQueryBoundU_bind (isKindQueryBoundU_toU _ _ (kinds_coverAt lr E L (.inl d)))
        fun cv => kinds_queryU_bind d _ _ fun u => ih u _ _ (hq.2 u)).mono
        (budget_h21 q d hq.1)
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      refine (isKindQueryBoundU_bind (q₁ := 0) (q₂ := qW q NdC) (isKindQueryBoundU_toU _ _
        (kinds_coverAt lr E L (.inr c))) fun cv => ?_).mono (by simp)
      unfold IsKindQueryBoundU
      erw [isQueryBound_query_bind_iff]
      exact ⟨trivial, fun u => ih u _ _ (hq.2 u)⟩
    · simp only [clsW, StateT.run_mk, bind_map_left]
      unfold IsKindQueryBoundU
      erw [isQueryBound_query_bind_iff]
      rcases x with x | x <;> exact ⟨trivial, fun u => ih u _ _ (hq.2 u)⟩

theorem hashes_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (q : Kind → ℕ) (n : ℕ) (L : QueryLog specIC), IsKindQueryBoundU oa q →
      IsQueryBoundP oa (fun t => isHashU t = true) n →
      IsQueryBoundP ((simulateQ (clsW lr E) oa).run L) (fun t => isHashU t = true)
        (n + q .h21 * (NdC + 2)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro q n L _ _; exact isQueryBoundP_pure _ _ _
  | query_bind t cont ih =>
    intro q n L hq hn
    unfold IsKindQueryBoundU at hq
    rw [isQueryBound_query_bind_iff] at hq
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (d | c) | x
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      have hn0 : 0 < n := hn.1.resolve_left (by simp [isHashU])
      have hc := isQueryBoundP_toU (coverAt lr E L (.inl d)) (fun t => isHashU t = true)
        (fun t => t.isLeft = true) (fun t => by cases t <;> rfl) _ (left_coverAt lr E L (.inl d))
      refine (isQueryBoundP_bind
        (m := 1 + (n - 1 + (Function.update q d.1 (q d.1 - 1)) .h21 * (NdC + 2))) hc
        fun cv _ => ?_).mono ?_
      · erw [isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        have h1 : isHashU (Sum.inl (Sum.inl d) : DomIC ⊕ (ByteArray ⊕ TG)) = true := rfl
        rw [ite_eq_left h1, Nat.add_sub_cancel_left]
        exact ih u _ (n - 1) _ (hq.2 u) (hn.2 u)
      · obtain ⟨kd, x1⟩ := d
        have hq0 : 0 < q kd := hq.1
        by_cases h21 : kd = .h21
        · subst h21
          obtain ⟨c, hc⟩ : ∃ c, q .h21 = c + 1 := ⟨q .h21 - 1, by omega⟩
          simp only [ite_true, Function.update_self, hc, Nat.add_sub_cancel]
          rw [Nat.succ_mul]
          generalize c * (NdC + 2) = X
          omega
        · simp only [h21, ite_false, Function.update_of_ne (Ne.symm h21)]
          generalize q .h21 * (NdC + 2) = X
          omega
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      have hc := isQueryBoundP_toU (coverAt lr E L (.inr c)) (fun t => isHashU t = true)
        (fun t => t.isLeft = true) (fun t => by cases t <;> rfl) 0 (left_coverAt lr E L (.inr c))
      refine (isQueryBoundP_bind (n := 0) (m := n + q .h21 * (NdC + 2)) hc fun cv _ => ?_).mono
        (by omega)
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [isHashU]), fun u => ih u _ n _ (hq.2 u) (hn.2 u)⟩
    · simp only [clsW, StateT.run_mk, bind_map_left]
      erw [isQueryBoundP_query_bind_iff]
      rcases x with x | x <;>
        exact ⟨Or.inl (by simp [isHashU]), fun u => ih u _ n _ (hq.2 u) (hn.2 u)⟩

theorem cipher_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (m : ℕ) (L : QueryLog specIC), IsQueryBoundP oa (fun t => isCipherU t = true) m →
      IsQueryBoundP ((simulateQ (clsW lr E) oa).run L) (fun t => isCipherU t = true) m := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro m L _; exact isQueryBoundP_pure _ _ _
  | query_bind t cont ih =>
    intro m L hm
    rw [isQueryBoundP_query_bind_iff] at hm
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with d | x
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      have hc := isQueryBoundP_toU (coverAt lr E L d) (fun t => isCipherU t = true)
        (fun t => t.isRight = true) (fun t => by cases t <;> rfl) 0 (right_coverAt lr E L d)
      refine (isQueryBoundP_bind (n := 0) (m := m) hc fun cv _ => ?_).mono (by omega)
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨hm.1, fun u => ih u _ _ (hm.2 u)⟩
    · simp only [clsW, StateT.run_mk, bind_map_left]
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨hm.1, fun u => ih u _ _ (hm.2 u)⟩

theorem ht_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (k : ℕ) (L : QueryLog specIC), IsQueryBoundP oa (fun t => isHT t = true) k →
      IsQueryBoundP ((simulateQ (clsW lr E) oa).run L) (fun t => isHT t = true) k := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro k L _; exact isQueryBoundP_pure _ _ _
  | query_bind t cont ih =>
    intro k L hk
    rw [isQueryBoundP_query_bind_iff] at hk
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with d | x
    · simp only [clsW, StateT.run_mk, bind_assoc, pure_bind]
      have hc : IsQueryBoundP (toU (coverAt lr E L d)) (fun t => isHT t = true) 0 :=
        isQueryBoundP_toU _ (fun t => isHT t = true) (fun _ => False) (fun t => by simp [isHT]) 0
          (OracleComp.isQueryBoundP_false _ 0)
      refine (isQueryBoundP_bind (n := 0) (m := k) hc fun cv _ => ?_).mono (by omega)
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨hk.1, fun u => ih u _ _ (hk.2 u)⟩
    · simp only [clsW, StateT.run_mk, bind_map_left]
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨hk.1, fun u => ih u _ _ (hk.2 u)⟩

/-- **The wrapped forger's budget**: a forger within `qA`, `nA`, `qE`, `Q_T` gives a wrapped forger
within `qW qA NdC`, `nW nA qA NdC`, `qE`, `Q_T`, for every cipher table. -/
theorem forgerBound_wrapE {A : Forger} {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) : ForgerBound (wrapE lr E A) (qW qA NdC) (nW nA qA NdC) qE QT := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · unfold wrapE IsKindQueryBoundU
    rw [StateT.run'_eq, isQueryBound_map_iff]
    exact kinds_clsW lr E (A pk) qA [] (hA.kinds pk)
  · unfold wrapE
    rw [StateT.run'_eq, isQueryBoundP_map_iff]
    exact hashes_clsW lr E (A pk) qA nA [] (hA.kinds pk) (hA.hashes pk)
  · unfold wrapE
    rw [StateT.run'_eq, isQueryBoundP_map_iff]
    exact cipher_clsW lr E (A pk) qE [] (hA.cipher pk)
  · unfold wrapE
    rw [StateT.run'_eq, isQueryBoundP_map_iff]
    exact ht_clsW lr E (A pk) QT [] (hA.ht pk)

end Bounds

section Thm

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (ℓ : ℕ) (lr : Bool)

/-- **Theorem U1^cls with simultaneous extraction, the forger's budget only** (gap G8-cls): for a
key generation with 32-byte key digests, any Issuer and a forger with budget `qA`, `nA`, `qE`, `Q_T`,

    Pr[PomWin] ≤ Adv^{ompr}(red (wrapE, E₁^cls); Q_T + ℓ + 1, ℓ) + clsSimEps(q', q_E', n', ℓ),

`q' = qP (qW qA NdC) Q_T ℓ`, `q_E' = eP qE ℓ`, `n' = nP (nW nA qA NdC) Q_T ℓ`: the wrapper adds an
`H₂⁴`, an `H₄` and at most `NdC` `H₅` queries per `H₂¹` query, which enter only `n'`. -/
theorem pomfrit_U1_cls_sim' (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint
          (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      clsSimEps (qP (qW qA NdC) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA NdC) QT ℓ) ℓ :=
  pomfrit_U1_cls_sim KG pre ℓ lr A hdig hA fun E => forgerBound_wrapE lr E hA

/-- **Theorem U1^cls, union over the forgeries, the forger's budget only.** -/
theorem pomfrit_U1_cls' (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint
          (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      (ℓ + 1) * clsFailEps (qP (qW qA NdC) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA NdC) QT ℓ) :=
  pomfrit_U1_cls KG pre ℓ lr A hdig hA fun E => forgerBound_wrapE lr E hA

end Thm

end VoleMole.ROM.OneMore.Pomfrit
