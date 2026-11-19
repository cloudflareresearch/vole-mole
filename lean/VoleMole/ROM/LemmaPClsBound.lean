import VoleMole.ROM.LemmaPCls

/-!
# Lemma P^cls: the adaptive bound into the class extractor's output

`lean/docs/security/pomfrit-lemmap-tight.md` §6A.3. `ROM/LemmaP.lean`'s adaptive bound
(`pomfritT_accept_le_major`) with the class extractor: for PomFRIT redemption with an adaptively
chosen statement whose target is any function of `chal1`, and a prover whose log covers the
decoder's `H₅` evaluations (`ClsCovered`),

    Pr[accept ∧ covered ∧ ¬ClsExtracted] ≤ … + (q₁ + 1)·2⁻¹³⁴ + (Q₃ + 1)·2⁻⁷⁸,

where `…` are `pomfritT_accept_le_major`'s other terms. `ClsExtracted`
(`ROM/LemmaPCls.lean`): a fully alive tree whose candidate is in the relation has the prefix that
the class extractor outputs, the extractor reading the witness and label rows of the alive trees,
`ũ`, the committed dead leaves, and the check value at the decoder's points with the gate hash
read off the prover's log.

* `parBadA`, `pomBadC`, `pomEpsC`: Lemma P's per-query bad event (`pomBad`) with the parallelism
  event at `H₂¹`, and its charge.
* `pomBadC_trace` (deterministic step), `prEvent_pomBadC_le` (per-query bound).
* `prEvent_accept_le_adaptive_pomfritC_E`, `prEvent_accept_le_adaptive_pomfritC`,
  `combDetC_pomfritT` (`pomfritT_extract_class_chain` as the per-chain step),
  `pomfritT_accept_le_cls`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

set_option maxRecDepth 8000

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.PomFRIT

section PomUnionC

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)

/-- **The parallelism bad query of the adaptive game**: at an `H₂¹` query, the answer is not good
for parallelism for the responses committed there (the reference statement's data, as `pomBad`
at `H₂¹`). -/
def parBadA (t : Dom) (g : Table) : Prop :=
  @parBad (icPrg E.cipher) (stKT pk hF b1F b2F lr none)
    (preOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr none)) T t g

/-- **Lemma P^cls's per-query bad event**: `pomBad` or the parallelism event. -/
def pomBadC (N : ℕ) (t : Dom) (g : Table) : Prop :=
  pomBad pk hF b1F b2F lr T P E N t g ∨ parBadA pk hF b1F b2F lr T P E t g

/-- **The per-query charge of `pomBadC`**. -/
noncomputable def pomEpsC (n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) (n'' : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  pomEps pk hF b1F b2F lr n' εc ntot N n'' k + @parEpsK (stKT pk hF b1F b2F lr none) k

lemma pomEpsC_eq_zero (n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) (n'' : Kind → ℕ) (k : Kind)
    (hk : k ∉ adaptKinds) : pomEpsC pk hF b1F b2F lr n' εc ntot N n'' k = 0 := by
  unfold pomEpsC
  rw [pomEps_eq_zero pk hF b1F b2F lr n' εc ntot N n'' k hk, zero_add]
  cases k <;> simp_all [adaptKinds, parEpsK]

/-- At the verifier's `H₂¹` input: the reference data's parallelism event. -/
theorem pomfritT_convXpar (g : Table) (x : ByteArray) :
    @parBad (icPrg E.cipher) (stT pk hF b1F b2F lr (sA g P E))
      (cFixT pk hF b1F b2F lr T P E g).preOf T (.h21, x) g →
    parBadA pk hF b1F b2F lr T P E (.h21, x) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  have h1 := (parBad_congr (cFixT pk hF b1F b2F lr T P E g).preOf
    (preOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr none)) T g x
    (preOf_fixT_eq pk hF b1F b2F lr T P E g none x)).1 hb
  exact (parBad_transport (st := stT pk hF b1F b2F lr (sA g P E))
    (st' := stKT pk hF b1F b2F lr none) rfl _ T (.h21, x) g).1 h1

set_option maxRecDepth 8000 in
/-- **Lemma P^cls's deterministic step, per table**: if the verifier accepts the prover's proof,
the prover's log covers the decoder and Lemma P^cls's extraction fails, without binding failure,
opened dead leaf or `cf`, a query of the game's log is bad (`pomBadC`). -/
theorem pomBadC_trace (hT : liftInvOk T = true) (N : ℕ)
    (hdet : ∀ s, @CombDetC (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (@GoalC (icPrg E.cipher) (witKT pk hF (some s)) (stT pk hF b1F b2F lr s) T))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (g : Table)
    (h₀ : let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T (stT pk hF b1F b2F lr) P E)
      (r.2.2.accept = true ∧ ClsCovered E (stT pk hF b1F b2F lr (stOut r)) T r ∧
        ¬ClsExtracted E (stT pk hF b1F b2F lr (stOut r)) T (witKT pk hF (some (stOut r))) r) ∧
      ¬bindFailA (stT pk hF b1F b2F lr) E r ∧ ¬deadOpenA (stT pk hF b1F b2F lr) E r ∧ ¬cf r) :
    ∃ e ∈ tableQueryLog (gameA T (stT pk hF b1F b2F lr) P E) g,
      pomBadC pk hF b1F b2F lr T P E N e.1 g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  let cb : Option (ℕ × ByteArray) := some (45, dstP)
  let sel : QueryLog spec → Dom → Option (Option ι) := stmtAtD (decT pk hF b1F b2F lr) none
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ClsCovered E (stF (stOut r)) T r ∧
      ¬ClsExtracted E (stF (stOut r)) T (witKT pk hF (some (stOut r))) r
  let bad : Dom → Table → Prop := fun t g =>
    combBadF T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF) (witKT pk hF) dstP
      sel N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨ stmtHitD (tableQueryLog oa) t g
  show ∃ e ∈ tableQueryLog oa g, bad e.1 g ∨ parBadA pk hF b1F b2F lr T P E e.1 g
  have h : (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬cf r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) := h₀
  simp only [ev, bindFailA, deadOpenA, oa, evalWithAnswerFn_gameA, stOut_gameIC] at h
  obtain ⟨⟨hacc, hcov, hnex⟩, hnb, hnd, hnp⟩ := h
  have hlog : tableQueryLog oa g = gLog T (stF (sA g P E)) P E g :=
    tableQueryLog_gameA T stF P E g
  by_cases hh : NoHit (gameIC T (stF (sA g P E)) P E) (chainHit T (stF (sA g P E)) P E) g
  swap
  · simp only [NoHit, not_forall, not_not] at hh
    obtain ⟨e, he, hhit⟩ := hh
    refine ⟨e, hlog ▸ he, Or.inl (Or.inr (Or.inl ?_))⟩
    unfold chainHitL
    rw [hlog]
    exact hhit
  by_cases hs : NoStmtHitD T (stF (sA g P E)) P E g
  swap
  · simp only [NoStmtHitD, not_forall, not_not] at hs
    obtain ⟨e, he, hhit⟩ := hs
    refine ⟨e, hlog ▸ he, Or.inl (Or.inr (Or.inr ?_))⟩
    unfold stmtHitD
    rw [hlog]
    exact hhit
  obtain ⟨leaves, hr, hacc', hbad⟩ := combBad_trace_icDC hT (stF (sA g P E))
    (sysKT pk hF (some (sA g P E))) (witKT pk hF (some (sA g P E))) dstP rfl N
    (@GoalC (icPrg E.cipher) (witKT pk hF (some (sA g P E))) (stF (sA g P E)) T)
    (fun c1 v w => by
      show (OneMore.Pomfrit.pomfritRedeemT pk (hF (sA g P E)) (b1F (sA g P E)) (b2F (sA g P E))
        lr).values c1 v.ba w = _
      rw [OneMore.Pomfrit.pomfritRedeemT_values, ofArr_combinationOf_ba]; rfl)
    P E (hdet (sA g P E)) cf (hcf (sA g P E)) g hacc _
    (dead_of_not_mem_aliveR T (stF (sA g P E)) P E g hh hacc)
    (fun leaves hrec hG => hnex (clsExtracted_of_goalC T (stF (sA g P E)) P E g
      (witKT pk hF (some (sA g P E))) hh hacc hcov leaves hrec hG)) hnp hnb hnd hh
  set keys := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC (stF (sA g P E)) E P)).2.keys
  set ch := runChain (Hashes.ofTable g) T (stF (sA g P E)) (πOf g P E) leaves keys
  obtain ⟨s', hdec, hmuEq⟩ := decT_spec pk hF b1F b2F lr ch.chal1 (sA g P E)
  obtain ⟨h2, h3⟩ := stmtAtD_ident (decT pk hF b1F b2F lr) none T (stF (sA g P E)) P E g rfl hh hs
    keys hacc' hr hdec
  obtain ⟨-, -, hF3, hF4, hO3, hO4⟩ := chain_ident T (stF (sA g P E)) P E g hh keys hacc' hr
  have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨(stF (sA g P E)).params, πOf g P E⟩
      ((stF (sA g P E)).mu1 (Hashes.ofTable g))) (Proof.opening ⟨(stF (sA g P E)).params, πOf g P E⟩)
      (Proof.delta ⟨(stF (sA g P E)).params, πOf g P E⟩) = some leaves := hr
  obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T (stF (sA g P E)) (πOf g P E) hacc' hr0 keys
  have hc1s : ch.chal1.size = 136 := Prob.Bytes.size_ba _
  have hyc1 : yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch) = ch.chal1 := by
    rw [runY, yChal1_chal2Input _ hc1s]
  have htgt : hF (sA g P E) (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) =
      hF s' (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) := by
    rw [hyc1]; exact (target_eq_of_muInD_T pk lr hmuEq).symm
  have hgl : gLogA T stF P E g = gLog T (stF (sA g P E)) P E g := gLogA_eq T stF P E g
  have hF3' : firstIn .h21 (fun _ => true)
      (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch))
      (logBefore (.h22, runY (Hashes.ofTable g) (stF (sA g P E)) ch) (gLogA T stF P E g)) =
      some (runX (Hashes.ofTable g) (stF (sA g P E)) (πOf g P E) leaves) := by
    rw [hgl]; exact hF3
  have hF4' : firstIn .h22 (fun _ => true) (zChal2 (runZ (stF (sA g P E)) ch))
      (logBefore (.h23, runZ (stF (sA g P E)) ch) (gLogA T stF P E g)) =
      some (runY (Hashes.ofTable g) (stF (sA g P E)) ch) := by
    rw [hgl]; exact hF4
  have hF3'' : firstIn .h21 (fun _ => true)
      (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch))
      (logBefore (.h22, runY (Hashes.ofTable g) (stF (sA g P E)) ch)
        (logBefore (.h23, runZ (stF (sA g P E)) ch) (gLogA T stF P E g))) =
      some (runX (Hashes.ofTable g) (stF (sA g P E)) (πOf g P E) leaves) := by
    rw [hgl, logBefore_logBefore hO4]; exact hF3
  have hmk : ∀ (t : Dom) (o : Option ι), InLog (verifyQ T (stF (sA g P E)) (πOf g P E)) g t →
      sel (gLog T (stF (sA g P E)) P E g) t = some o →
      @combBad (icPrg E.cipher) _ _ (cDT pk hF b1F b2F lr T P E o) T chal3Blocks N t g →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g ∨ parBadA pk hF b1F b2F lr T P E e.1 g := by
    intro t o ht hst hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T (stF (sA g P E)) P E g ht)
    refine ⟨e, hlog ▸ he, Or.inl (Or.inl ⟨o, ?_, hb⟩)⟩
    show sel (tableQueryLog oa g) e.1 = some o
    rw [hlog]
    exact hst
  rcases hbad with hb | hpb | hb | hb
  · exact hmk _ none hxL (by simp only [sel, stmtAtD]) (pomfritT_convX pk hF b1F b2F lr T P E N g _ hb)
  · obtain ⟨e, he, he1⟩ := List.mem_map.1 (inLog_gLog T (stF (sA g P E)) P E g hxL)
    refine ⟨e, hlog ▸ he, Or.inr ?_⟩
    rw [he1]
    exact pomfritT_convXpar pk hF b1F b2F lr T P E g _ hpb
  · exact hmk _ (some s') hyL h2 (pomfritT_convY pk hF b1F b2F lr T P E N g _ _ s' hF3' htgt hb)
  · exact hmk _ (some s') hzL h3
      (pomfritT_convZ pk hF b1F b2F lr T P E N g _ _ _ s' hF4' hF3'' htgt hb)

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **Lemma P^cls's per-query bound** (cache form): `prEvent_pomBad_le` with the parallelism event,
`pomEpsC = pomEps + parEps` at `H₂¹`. -/
theorem prEvent_pomBadC_le (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) (K : Finset Dom)
    [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey 45 dstP u ∈ K) (ntot : ℕ)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      pomBadC pk hF b1F b2F lr T P E N t.val (extendTable K (completeTable c g))] ≤
      pomEpsC pk hF b1F b2F lr n' εc ntot N (q + extractorQueries + verifierQueries) t.val.1 := by
  classical
  unfold pomBadC pomEpsC
  refine (prEvent_or_le _ _ _).trans (add_le_add
    (prEvent_pomBad_le pk hF b1F b2F lr T P E hT N hn' hεc q hq K hK ntot c t hc hcard) ?_)
  refine prEvent_completeTable_cell_le c _ hc
    (fun t G => parBadA pk hF b1F b2F lr T P E t.val (extendTable K G)) _ fun G => ?_
  simp only [extendTable_update]
  exact @prEvent_parBad_update_le (icPrg E.cipher) _ _
    (preOfA_committed T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr none)) T _ _

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 8000 in
/-- **The adaptive union bound for Lemma P^cls, per cipher table**:
`prEvent_accept_le_adaptive_pomfritT_E` with the class extractor's goal, for provers whose log
covers the decoder, and the parallelism term `n₂₁·ε_par`. -/
theorem prEvent_accept_le_adaptive_pomfritC_E (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ s, @CombDetC (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (@GoalC (icPrg E.cipher) (witKT pk hF (some s)) (stT pk hF b1F b2F lr s) T))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (n : ℕ) (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ClsCovered E (stT pk hF b1F b2F lr (stOut r)) T r ∧
          ¬ClsExtracted E (stT pk hF b1F b2F lr (stOut r)) T (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * (epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
          parEps (Chain.kosL (stKT pk hF b1F b2F lr none))) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          bindFailA (stT pk hF b1F b2F lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          deadOpenA (stT pk hF b1F b2F lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          cf r] := by
  classical
  intro n''
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  set mx := (simulateQ randomOracle oa).run' ∅
  set ntot := n + 2 + verifierTotal
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ClsCovered E (stF (stOut r)) T r ∧
      ¬ClsExtracted E (stF (stOut r)) T (witKT pk hF (some (stOut r))) r
  let ε : Kind → ℝ≥0∞ := pomEpsC pk hF b1F b2F lr n' εc ntot N n''
  have hKε : ∀ k ∉ adaptKinds, ε k = 0 := pomEpsC_eq_zero pk hF b1F b2F lr n' εc ntot N n''
  let K : Finset Dom := possibleQueryKeys oa ∪ Finset.univ.image (combKey 45 dstP)
  have hK : ∀ u, combKey 45 dstP u ∈ K := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hS : AllQueriesSatisfy oa (· ∈ K) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d h => Finset.mem_union_left _ h
  let : SampleableType ((d : K) → Ans d.val) := SampleableType.piOfFintype _
  have hq'' := isKindQueryBound_gameA T stF P E hq
  have hgood := prEvent_randomOracle_le_of_fresh_bad_queries oa K hS (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound oa adaptKinds ε hKε n'' hq'') ntot
    (isTotalQueryBound_gameA T stF E hn)
    (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r)
    (pomBadC pk hF b1F b2F lr T P E N)
    (fun c t hc hcard => prEvent_pomBadC_le pk hF b1F b2F lr T P E hT N hn' hεc q hq K hK ntot c t
      hc hcard)
    (fun g h => pomBadC_trace pk hF b1F b2F lr T P E hT N hdet cf hcf g h)
  have hsum : ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k =
      n'' .h21 * (epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
          parEps (Chain.kosL (stKT pk hF b1F b2F lr none))) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) +
        n'' .mu * stmtEpsD n'' .mu := by
    simp only [adaptKinds, ε, pomEpsC, pomEps, parEpsK]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [chainEps, hitEps, stmtEpsD, hitSum, reduceCtorEq, ite_true, ite_false, zero_add,
      add_zero, mul_add, ntot]
    ring
  calc Pr{let r ← mx}[ev r]
      ≤ Pr{let r ← mx}[(ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r) ∨
          (bindFailA stF E r ∨ (deadOpenA stF E r ∨ cf r))] :=
        prEvent_mono mx _ _ fun r h => by tauto
    _ ≤ Pr{let r ← mx}[ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r] +
          (Pr{let r ← mx}[bindFailA stF E r] +
            (Pr{let r ← mx}[deadOpenA stF E r] + Pr{let r ← mx}[cf r])) :=
        (prEvent_or_le mx _ _).trans (add_le_add le_rfl ((prEvent_or_le mx _ _).trans
          (add_le_add le_rfl (prEvent_or_le mx _ _))))
    _ ≤ _ := by
        rw [← hsum]
        refine (add_le_add hgood le_rfl).trans_eq ?_
        ring
end PomUnionC

/-! ## The joint experiment and the theorem -/

section PomJointC

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool) (T : CrtTables) (P : OracleComp specIC (ByteArray × (ι × β)))

/-- **Lemma P^cls's adaptive bound in the joint experiment** (the cipher table uniform). -/
theorem prEvent_accept_le_adaptive_pomfritC (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ (E : CTable) s, @CombDetC (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (@GoalC (icPrg E.cipher) (witKT pk hF (some s)) (stT pk hF b1F b2F lr s) T))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ClsCovered E (stT pk hF b1F b2F lr (stOut r)) T r ∧
          ¬ClsExtracted E (stT pk hF b1F b2F lr (stOut r)) T (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * (epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
          parEps (Chain.kosL (stKT pk hF b1F b2F lr none))) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n''
  have hE := fun E => prEvent_accept_le_adaptive_pomfritC_E pk hF b1F b2F lr T P E hT N hn' hεc
    (hdet E) (fun r => PostOut E r)
    (fun s g h => keysPre_of_not_postOut T (stT pk hF b1F b2F lr s) P E g h) n hn q hq
  have hdo := prEvent_joint_deadOpen_le_A T (stT pk hF b1F b2F lr) P (pomfritParams lr)
    (fun _ => rfl) q hq
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA (stT pk hF b1F b2F lr) E r)
    (fun E r => deadOpenA (stT pk hF b1F b2F lr) E r) (fun E r => PostOut E r) _ hE).trans ?_
  gcongr
  · exact (prEvent_joint_bindFail_le_A T (stT pk hF b1F b2F lr) P qE hqE).trans
      (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T (stT pk hF b1F b2F lr) P qE hqE q hq

/-- The per-chain step of Lemma P^cls for the family (`pomfritT_extract_class_chain`). -/
theorem combDetC_pomfritT (E : CTable) (s : ι) :
    @CombDetC (icPrg E.cipher) 45 CrtGen.tables (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) (2 ^ 50)
      (@GoalC (icPrg E.cipher) (witKT pk hF (some s)) (stT pk hF b1F b2F lr s) CrtGen.tables) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro ch known dead acc l c1 hch1 hv A hA hAS hkos hpar hQS hcb hP hhide hne
  subst hch1
  exact PomFRIT.pomfritT_extract_class_chain pk (stT pk hF b1F b2F lr s) lr rfl ch
    (tgtOf (hF s ch.chal1)) l hv hA hAS hkos hpar (hdOf dead)
    (fun Δ hΔ i hi => eq_hdOf_of_hides (hhide Δ hΔ) (hne i hi)) hQS hcb preB admissible
    deltaBlocks deltaBlocks_injOn acc hP.2

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Lemma P^cls, adaptive form, every term explicit.** As `pomfritT_accept_le_major`, for a
prover whose log covers the decoder's evaluations (`ClsCovered`). The verifier accepts and **no
fully alive tree whose candidate `(r, σ)` satisfies `P(σ) = h(chal1) ⊕ r` has the prefix that the
class extractor outputs** (`ClsExtracted`) with probability at most the bound of
`pomfritT_accept_le_major` with the `H₂³` term `(Q₃+1)·2⁵⁰·2⁻¹²⁸` (`2⁻⁷⁸` per query) in place of
`(Q₃+1)·2⁵⁷·2⁻¹²⁸`, plus the parallelism term `(q₁+1)·2⁻¹³⁴`. -/
theorem pomfritT_accept_le_cls (labelRows : Bool) (P : OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (stT pk hF b1F b2F labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧
          ClsCovered E (stT pk hF b1F b2F labelRows (stOut r)) CrtGen.tables r ∧
          ¬ClsExtracted E (stT pk hF b1F b2F labelRows (stOut r)) CrtGen.tables
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
  have h := prEvent_accept_le_adaptive_pomfritC pk hF b1F b2F labelRows CrtGen.tables P
    liftInvOk_tables (2 ^ 50) (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun E s => combDetC_pomfritT pk hF b1F b2F labelRows E s)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q 45 rfl, stmtEpsD_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F labelRows none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
      (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
  have hpar : parEps (Chain.kosL (stKT pk hF b1F b2F labelRows none)) ≤ (2 ^ 134 : ℝ≥0∞)⁻¹ :=
    parEps_le (by
      cases labelRows <;>
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

end PomJointC

end VoleMole.ROM.IC
