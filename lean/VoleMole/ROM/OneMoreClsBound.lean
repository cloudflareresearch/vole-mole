import VoleMole.ROM.OneMoreClsFail

/-!
# U1^cls's term in the one-more game, bounded (gap G8-cls)

`lean/docs/security/pomfrit.md` §6.4. The reduction of Theorem U1^cls runs the forger `A` wrapped
(`wrapE`, `ROM/OneMoreCls.lean`; it reads the cipher table) with the hint `E₁^cls` (`e1C`). The
derived prover of the wrapped forger (`proverP … (wrapE E A) … i`) depends on `E` through the
wrapper's `H₅` queries; Lemma P^cls's bound is applied per cipher table
(`prEvent_accept_le_adaptive_pomfritC_E`), and its three cipher terms (binding, an opened dead leaf,
Post) are transferred, table by table, to the derived prover of `A` (`proverP … A … i`, which does
not read `E`): both have the same proof, statement and cipher log, and joint logs that agree up to the
wrapper's `H₂⁴`, `H₄`, `H₅` entries (`eval_proverP_wrapE`).

* Filters: `cipherLog_filter_keepK`, `postTargets_filter_keepK`, `postJ_of_filter`.
* `bindFailA_wrapE`, `deadOpenA_wrapE`, `postOut_wrapE`: the transfer, table by table.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## Filters -/

section Filter

lemma cipherLog_filter_keepK (L : QueryLog specIC) : cipherLog (L.filter keepK) = cipherLog L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      by_cases h : keepK ⟨.inl d, u⟩ = true
      · rw [List.filter_cons_of_pos h]; exact ih
      · rw [List.filter_cons_of_neg h]; exact ih
    | inr c =>
      rw [List.filter_cons_of_pos rfl]
      exact congrArg (List.cons _) ih

lemma kindIns_h1_filter_keepK (L : QueryLog specIC) :
    kindIns .h1 (hashLog (L.filter keepK)) = kindIns .h1 (hashLog L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      by_cases h : keepK ⟨.inl d, u⟩ = true
      · simp only [List.filter_cons, h, ite_true]
        simp only [hashLog, List.filterMap_cons, kindIns, List.filter_cons] at ih ⊢
        split_ifs <;> simp_all
      · have hd : d.1 ≠ .h1 := by
          intro hd; simp [keepK, hd] at h
        simp only [List.filter_cons, h, Bool.false_eq_true, ite_false]
        simp only [hashLog, List.filterMap_cons, kindIns, List.filter_cons] at ih ⊢
        simp [hd, ih]
    | inr c =>
      simp only [List.filter_cons, keepK, ite_true]
      simp only [hashLog, List.filterMap_cons, kindIns] at ih ⊢
      exact ih

lemma postTargets_filter_keepK (L : QueryLog specIC) :
    postTargets (L.filter keepK) = postTargets L := by
  unfold postTargets; rw [kindIns_h1_filter_keepK]

lemma mem_inr_filter_keepK (L : QueryLog specIC) (c : Cell) :
    (.inr c : DomIC) ∈ (L.filter keepK).map Sigma.fst ↔ (.inr c : DomIC) ∈ L.map Sigma.fst := by
  constructor
  · intro h
    obtain ⟨e, he, he1⟩ := List.mem_map.1 h
    exact List.mem_map.2 ⟨e, (List.mem_filter.1 he).1, he1⟩
  · intro h
    obtain ⟨e, he, he1⟩ := List.mem_map.1 h
    refine List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, ?_⟩, he1⟩
    obtain ⟨t, u⟩ := e
    simp only at he1
    subst he1
    rfl

lemma split_of_filter {α : Type*} {p : α → Bool} :
    ∀ (L : List α) {A B : List α} {e : α}, L.filter p = A ++ e :: B →
      ∃ pre post, L = pre ++ e :: post ∧ pre.filter p = A
  | [], A, B, e, h => by cases A <;> simp at h
  | x :: L, A, B, e, h => by
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx] at h
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨[], L, rfl, rfl⟩
      | cons a A =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h'⟩ := h
        obtain ⟨pre, post, h1, h2⟩ := split_of_filter L h'
        exact ⟨x :: pre, post, by simp [h1], by simp [List.filter_cons_of_pos hx, h2]⟩
    · rw [List.filter_cons_of_neg hx] at h
      obtain ⟨pre, post, h1, h2⟩ := split_of_filter L h
      exact ⟨x :: pre, post, by simp [h1], by simp [List.filter_cons_of_neg hx, h2]⟩

/-- **Post reads the cipher entries and the `H₁` inputs only.** -/
lemma postJ_of_filter (E : CTable) {J J' : QueryLog specIC} (h : J'.filter keepK = J.filter keepK)
    (hp : PostJ E J') : PostJ E J := by
  obtain ⟨pre, e, post, hJ, κ, w, he, w', hw', h1, h2, ht⟩ := hp
  have hke : keepK e = true := by obtain ⟨t, u⟩ := e; simp only at he; subst he; rfl
  have hf : J.filter keepK = pre.filter keepK ++ e :: post.filter keepK := by
    rw [← h, hJ, List.filter_append, List.filter_cons_of_pos hke]
  obtain ⟨pre', post', hJ', hpre⟩ := split_of_filter J hf
  refine ⟨pre', e, post', hJ', κ, w, he, w', hw', ?_, ?_, ?_⟩
  · rw [← mem_inr_filter_keepK, hpre, mem_inr_filter_keepK]; exact h1
  · rw [← mem_inr_filter_keepK, hpre, mem_inr_filter_keepK]; exact h2
  · rw [← postTargets_filter_keepK, hpre, postTargets_filter_keepK]; exact ht

end Filter

/-! ## The cipher events of the wrapped forger's derived game are the forger's -/

section Transfer

variable (g : Table) (E : CTable) (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (i : ℕ)

/-- **Binding failure, an opened dead leaf and Post of the wrapped forger's derived game are those
of the forger's**, table by table. -/
theorem events_wrapE :
    let r' := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre (wrapE lr E A) Lst i) E)
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst i) E)
    (bindFailA (stG lr pk) E r' → bindFailA (stG lr pk) E r) ∧
      (deadOpenA (stG lr pk) E r' → deadOpenA (stG lr pk) E r) ∧
      (PostOut E r' → PostOut E r) := by
  intro r' r
  set P' := proverP lr pk pre (wrapE lr E A) Lst i
  set P := proverP lr pk pre A Lst i
  obtain ⟨e1, e2, e3⟩ := eval_proverP_wrapE g E lr pk pre A Lst i
  obtain ⟨a1, a2, a3⟩ := gameA_out CrtGen.tables (stG lr pk) P' E g
  obtain ⟨b1, b2, b3⟩ := gameA_out CrtGen.tables (stG lr pk) P E g
  have hJ : (jOf g P' E).filter keepK = (jOf g P E).filter keepK := e3
  have hC : cipherLog (jOf g P' E) = cipherLog (jOf g P E) := by
    rw [← cipherLog_filter_keepK, hJ, cipherLog_filter_keepK]
  have hsA : sA g P' E = sA g P E := e2
  have hπ : πOf g P' E = πOf g P E := e1
  have h1 : r'.1 = r.1 := by rw [a1, b1]; exact e1
  have hs : stOut r' = stOut r := by rw [a2, b2]; exact e2
  have h3 : r'.2.2 = r.2.2 := by rw [a3, b3, e1, e2]
  have hk : r'.2.1.keys = r.2.1.keys := by
    rw [(gameA_keys_known g CrtGen.tables E (stG lr pk) P').1,
      (gameA_keys_known g CrtGen.tables E (stG lr pk) P).1, hC]
    simp only [ivE, hsA, hπ]
  have hx' : r'.2.1.aux.2 = jOf g P' E := by
    simp only [r', evalWithAnswerFn_gameA]; exact aux_gameIC _ _ _ _ _
  have hx : r.2.1.aux.2 = jOf g P E := by
    simp only [r, evalWithAnswerFn_gameA]; exact aux_gameIC _ _ _ _ _
  refine ⟨fun hb => ?_, fun hd => ?_, fun hp => ?_⟩
  · simp only [bindFailA, bindFail, Binds] at hb ⊢
    rw [← h1, ← hs, ← h3, ← hk]; exact hb
  · simp only [deadOpenA, DeadOpenOut] at hd ⊢
    rw [← h1, ← hs, ← h3, hx, ← hC, ← hx']; exact hd
  · simp only [PostOut] at hp ⊢
    rw [hx] at ⊢; rw [hx'] at hp
    exact postJ_of_filter E hJ hp

end Transfer

end VoleMole.ROM.OneMore.Pomfrit
