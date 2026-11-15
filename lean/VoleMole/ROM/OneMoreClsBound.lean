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

/-! ## Lemma P^cls for a prover that reads the cipher table through the reduction -/

section Dep

/-- **Comparison of two families of games over the cipher table, table by table.** -/
lemma prEvent_transfer {X Y : Type} (oa : CTable → OracleComp spec X) (ob : CTable → OracleComp spec Y)
    (P : CTable → X → Prop) (Q : CTable → Y → Prop)
    (h : ∀ E g, P E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) →
      Q E (evalWithAnswerFn (QueryImpl.ofFn g) (ob E))) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[P E r] ≤
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (ob E)).run' ∅}[Q E r] :=
  (prEvent_bind_le_sum_of_table ($ᵗ CTable) oa (Finset.univ : Finset Unit) (fun _ E => ob E) P
    (fun _ => Q) fun E g hP => ⟨(), Finset.mem_univ _, h E g hP⟩).trans (by simp)

variable {ι β β₀ : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Lemma P^cls, adaptive form, for a prover `PE E` that depends on the cipher table**, whose
binding failure, opened dead leaf and Post events imply, table by table, those of a prover `P₀`
that does not: the bound of `pomfritT_accept_le_cls`, with `PE`'s hash budget for the chain terms
and `P₀`'s cipher budget for the cipher terms. -/
theorem pomfritT_accept_le_cls_dep (PE : CTable → OracleComp specIC (ByteArray × (ι × β)))
    (P₀ : OracleComp specIC (ByteArray × (ι × β₀)))
    (htr : ∀ E g,
      let r' := evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stT pk hF b1F b2F lr) (PE E) E)
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stT pk hF b1F b2F lr) P₀ E)
      (bindFailA (stT pk hF b1F b2F lr) E r' → bindFailA (stT pk hF b1F b2F lr) E r) ∧
        (deadOpenA (stT pk hF b1F b2F lr) E r' → deadOpenA (stT pk hF b1F b2F lr) E r) ∧
        (PostOut E r' → PostOut E r))
    (qE : ℕ) (hqE : IsQueryBoundP P₀ (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : ∀ E, IsQueryBoundP (PE E) (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : ∀ E, IsKindQueryBoundIC (PE E) q) (hq₀ : IsKindQueryBoundIC P₀ q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (stT pk hF b1F b2F lr) (PE E) E)).run' ∅}[
        r.2.2.accept = true ∧
          ClsCovered E (stT pk hF b1F b2F lr (stOut r)) CrtGen.tables r ∧
          ¬ClsExtracted E (stT pk hF b1F b2F lr (stOut r)) CrtGen.tables
            (witKT pk hF (some (stOut r))) r] ≤
      (q .h21 + 1) * ((2 ^ 150 : ℝ≥0∞)⁻¹ + (2 ^ 134 : ℝ≥0∞)⁻¹) +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 ^ 50 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 + stmtBindEpsD q := by
  classical
  set stF := stT pk hF b1F b2F lr
  set T := CrtGen.tables
  have hE := fun E => prEvent_accept_le_adaptive_pomfritC_E pk hF b1F b2F lr T (PE E) E
    liftInvOk_tables (2 ^ 50) (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun s => combDetC_pomfritT pk hF b1F b2F lr E s) (fun r => PostOut E r)
    (fun s g h => keysPre_of_not_postOut T (stF s) (PE E) E g h) n (hn E) q (hq E)
  have hdo := prEvent_joint_deadOpen_le_A T stF P₀ (pomfritParams lr) (fun _ => rfl) q hq₀
  have hb := prEvent_transfer (fun E => gameA T stF (PE E) E) (fun E => gameA T stF P₀ E)
    (fun E r => bindFailA stF E r) (fun E r => bindFailA stF E r) fun E g h => (htr E g).1 h
  have hd := prEvent_transfer (fun E => gameA T stF (PE E) E) (fun E => gameA T stF P₀ E)
    (fun E r => deadOpenA stF E r) (fun E r => deadOpenA stF E r) fun E g h => (htr E g).2.1 h
  have hp := prEvent_transfer (fun E => gameA T stF (PE E) E) (fun E => gameA T stF P₀ E)
    (fun E r => PostOut E r) (fun E r => PostOut E r) fun E g h => (htr E g).2.2 h
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA stF E r) (fun E r => deadOpenA stF E r)
    (fun E r => PostOut E r) _ hE).trans ?_
  have hj := add_le_add (add_le_add (add_le_add (le_refl (
      (q + extractorQueries + verifierQueries) .h21 * (epsKOS #chal3Blocks
          (Chain.kosL (stKT pk hF b1F b2F lr none)) + parEps (Chain.kosL (stKT pk hF b1F b2F lr none))) +
        (q + extractorQueries + verifierQueries) .h22 *
          (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q + extractorQueries + verifierQueries) .h23 * (((2 ^ 50 : ℕ) : ℝ≥0∞) / 2 ^ 128) +
        hitSum (q + extractorQueries + verifierQueries)
          (hitEps (q + extractorQueries + verifierQueries)
            (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries))) +
        (q + extractorQueries + verifierQueries) .mu *
          stmtEpsD (q + extractorQueries + verifierQueries) .mu))
    ((hb.trans (prEvent_joint_bindFail_le_A T stF P₀ qE hqE)).trans (add_le_add le_rfl hdo)))
    (hd.trans hdo)) (hp.trans (prEvent_joint_postOut_le_A T stF P₀ qE hqE q hq₀))
  refine hj.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q 45 rfl, stmtEpsD_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
      (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
  have hpar : parEps (Chain.kosL (stKT pk hF b1F b2F lr none)) ≤ (2 ^ 134 : ℝ≥0∞)⁻¹ :=
    parEps_le (by
      cases lr <;>
        norm_num [Chain.kosL, stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams,
          Params.correctionRows, Params.witnessBits])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * ((2 ^ 150 : ℝ≥0∞)⁻¹ + (2 ^ 134 : ℝ≥0∞)⁻¹) +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((2 ^ 50 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45 +
          stmtBindEpsD q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

end Dep

end VoleMole.ROM.OneMore.Pomfrit
