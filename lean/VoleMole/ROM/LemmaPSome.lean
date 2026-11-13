import VoleMole.ROM.LemmaP

/-!
# Lemma P without the `Shift` term: some alive tree extracts (for Theorem U2)

`lean/docs/security/pomfrit.md` §5, §6.2, §6.4 (gap G8). For Theorem U2 the reduction submits the
prefixes of **all** alive trees as shifts, so Lemma P's goal weakens to: **some fully alive tree has
a candidate in the relation** (its prefix is then one of the shifts). Lemma P's step 6 (the
`Shift` event, `2⁵⁷` accepted `chal3`) is not needed; the per-chain step is `extract_or_few` with
`N = 2`, as for `pomfritRedeem`.

* **A general goal on an output** (`GoalOut`): the goal at the output's `chal1`, the candidates of
  its chain and its alive trees (`aliveR`). `MajorExtracted` is `GoalOut GoalP`, `SomeExtracted` is
  `GoalOut GoalS` (`GoalS`: some tree of the set satisfies the relation).
* **The deterministic step and the union bound with any goal** (`pomBad_traceG`,
  `prEvent_accept_le_adaptive_pomfritT_EG`, `prEvent_accept_le_adaptive_pomfritTG`): the proofs of
  `pomBad_trace`, `prEvent_accept_le_adaptive_pomfritT_E`, `prEvent_accept_le_adaptive_pomfritT`
  (`ROM/LemmaP.lean`) with `GoalP` replaced by a parameter; they read the goal only through the
  per-chain hypothesis `hdet`. The per-query bound `prEvent_pomBad_le` does not read the goal and is
  reused.
* **The per-chain step** (`pomfritT_extract_some_chain`, `combDetG_pomfritT_some`): for the target
  family `pomfritRedeemT`, some tree outside the fixed ones extracts, or at most `2` admissible
  `chal3` are accepted.
* **The bound** (`pomfritT_accept_le_some`): `pomfritRedeem_accept_le_adaptive`'s bound, with the
  `H₂³` term `(Q₃ + 1)·2·2⁻¹²⁸`, for the target family and the goal `SomeExtracted`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

/-! ## The per-chain step with `N = 2` for the target family -/

namespace VoleMole.PomFRIT

open VoleMole.SeedExtraction VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.EndToEnd

variable [HasPrg]

set_option maxRecDepth 8000 in
/-- **Some tree extracts, at a chain of the executable verifier, for any target** (as
`pomfritRedeem_extract_chain`, for a statement with PomFRIT's parameters whose constraint evaluator
is PomFRIT's system at a target `h` and a combination `l`): with every tree outside `S` fixed on
`A`, some tree of `S` has a candidate encoding `(ρ, σ)` with `P(σ) = h + ρ`, or at most `2`
admissible `chal3` are accepted. -/
theorem pomfritT_extract_some_chain {Ch : Type*} (pk : UovPk)
    (st : Statement) (lr : Bool) (hp : st.params = pomfritParams lr) (ch : Chain)
    (h : Fin 45 → GF256) (l : Fin 45 → GF128)
    (hvals : ∀ x, ch.vals x =
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).values x)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {Sb : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ Sb)
    (hkos : Seed.KOSGood ch.kosCh Sb (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {S : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ S, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩
        (valVec (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l)
          (wStar uStar (ch.dc st))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      pomfritWit GF256.ofBits 119 45 pk.map h (wStar uStar (ch.dc st)))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ S, pomfritWit GF256.ofBits 119 45 pk.map h
        (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
      #{x ∈ Z | acc x} ≤ 2 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  dsimp only at hp
  subst hp
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables _ ch _ hvals
    (PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) hA hAS hkos hL2
  exact pomfrit_extract_gf128 119 45 _ _ _ hK _ _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end VoleMole.PomFRIT

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Goals on an output -/

section Goals

/-- An extraction goal: a predicate of the relation, `chal1`, the trees' candidates and a set of
trees (`GoalP`, `GoalS`). -/
abbrev GoalT := (ByteArray → (ℕ → GF128) → Prop) → ByteArray → (Fin BAVC.tau → ℕ → GF128) →
  Finset (Fin BAVC.tau) → Prop

/-- **U2's goal**: some tree of `S` has a candidate in the relation. -/
def GoalS : GoalT := fun wit c1 cand S => ∃ i ∈ S, wit c1 (cand i)

variable {β : Type}

/-- **A goal on an output**: at the output's `chal1`, the candidates of its chain (`candOut`, the
extractor's keys) and its alive trees (`aliveR`). -/
def GoalOut (Goal : GoalT) (E : CTable) (st : Statement) (wit : ByteArray → (ℕ → GF128) → Prop)
    (r : Out (β × QueryLog specIC)) : Prop :=
  Goal wit r.2.2.chal1 (@candOut (icPrg E.cipher) _ st r) (aliveR E r)

/-- **Lemma P's goal without `Shift`**: some fully alive tree has a candidate in the relation. -/
def SomeExtracted (E : CTable) (st : Statement) (wit : ByteArray → (ℕ → GF128) → Prop)
    (r : Out (β × QueryLog specIC)) : Prop :=
  GoalOut GoalS E st wit r

lemma majorExtracted_eq (E : CTable) (st : Statement) (wit : ByteArray → (ℕ → GF128) → Prop)
    (r : Out (β × QueryLog specIC)) : MajorExtracted E st wit r = GoalOut GoalP E st wit r := rfl

/-- Lemma P's goal implies U2's. -/
lemma someExtracted_of_major {E : CTable} {st : Statement} {wit : ByteArray → (ℕ → GF128) → Prop}
    {r : Out (β × QueryLog specIC)} (h : MajorExtracted E st wit r) : SomeExtracted E st wit r := by
  obtain ⟨i, hi, hw, -⟩ := h
  exact ⟨i, hi, hw⟩

end Goals

/-! ## The deterministic step and the union bound with any goal -/

section PomUnionG

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool) (T : CrtTables) (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)
  (Goal : GoalT)

set_option maxRecDepth 4000 in
/-- **Lemma P's deterministic step, per table, any goal** (`pomBad_trace` with `GoalP` a parameter):
if the verifier accepts the prover's proof and the goal fails on its output, without binding failure, opened dead leaf or `cf`, a query of the game's log is
bad (`pomBad`). -/
theorem pomBad_traceG (hT : liftInvOk T = true) (N : ℕ)
    (hdet : ∀ s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (Goal (witKT pk hF (some s))))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (g : Table)
    (h₀ : let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T (stT pk hF b1F b2F lr) P E)
      (r.2.2.accept = true ∧ ¬GoalOut Goal E (stT pk hF b1F b2F lr (stOut r))
        (witKT pk hF (some (stOut r))) r) ∧
      ¬bindFailA (stT pk hF b1F b2F lr) E r ∧ ¬deadOpenA (stT pk hF b1F b2F lr) E r ∧ ¬cf r) :
    ∃ e ∈ tableQueryLog (gameA T (stT pk hF b1F b2F lr) P E) g,
      pomBad pk hF b1F b2F lr T P E N e.1 g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  let cb : Option (ℕ × ByteArray) := some (45, dstP)
  let sel : QueryLog spec → Dom → Option (Option ι) := stmtAtD (decT pk hF b1F b2F lr) none
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬GoalOut Goal E (stF (stOut r)) (witKT pk hF (some (stOut r))) r
  let bad : Dom → Table → Prop := fun t g =>
    combBadF T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF) (witKT pk hF) dstP
      sel N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨ stmtHitD (tableQueryLog oa) t g
  show ∃ e ∈ tableQueryLog oa g, bad e.1 g
  have h : (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬cf r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) := h₀
  simp only [ev, bindFailA, deadOpenA, oa, evalWithAnswerFn_gameA, stOut_gameIC] at h
  obtain ⟨⟨hacc, hnex⟩, hnb, hnd, hnp⟩ := h
  have hlog : tableQueryLog oa g = gLog T (stF (sA g P E)) P E g :=
    tableQueryLog_gameA T stF P E g
  by_cases hh : NoHit (gameIC T (stF (sA g P E)) P E) (chainHit T (stF (sA g P E)) P E) g
  swap
  · simp only [NoHit, not_forall, not_not] at hh
    obtain ⟨e, he, hhit⟩ := hh
    refine ⟨e, hlog ▸ he, Or.inr (Or.inl ?_)⟩
    unfold chainHitL
    rw [hlog]
    exact hhit
  by_cases hs : NoStmtHitD T (stF (sA g P E)) P E g
  swap
  · simp only [NoStmtHitD, not_forall, not_not] at hs
    obtain ⟨e, he, hhit⟩ := hs
    refine ⟨e, hlog ▸ he, Or.inr (Or.inr ?_)⟩
    unfold stmtHitD
    rw [hlog]
    exact hhit
  obtain ⟨leaves, hr, hacc', hbad⟩ := combBad_trace_icDG hT (stF (sA g P E))
    (sysKT pk hF (some (sA g P E))) (witKT pk hF (some (sA g P E))) dstP rfl N
    (Goal (witKT pk hF (some (sA g P E))))
    (fun c1 v w => by
      show (OneMore.Pomfrit.pomfritRedeemT pk (hF (sA g P E)) (b1F (sA g P E)) (b2F (sA g P E))
        lr).values c1 v.ba w = _
      rw [OneMore.Pomfrit.pomfritRedeemT_values, ofArr_combinationOf_ba]; rfl)
    P E (hdet (sA g P E)) cf (hcf (sA g P E)) g hacc _
    (dead_of_not_mem_aliveR T (stF (sA g P E)) P E g hh hacc) hnex hnp hnb hnd hh
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
      ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
    intro t o ht hst hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T (stF (sA g P E)) P E g ht)
    refine ⟨e, hlog ▸ he, Or.inl ⟨o, ?_, hb⟩⟩
    show sel (tableQueryLog oa g) e.1 = some o
    rw [hlog]
    exact hst
  rcases hbad with hb | hb | hb
  · exact hmk _ none hxL (by simp only [sel, stmtAtD]) (pomfritT_convX pk hF b1F b2F lr T P E N g _ hb)
  · exact hmk _ (some s') hyL h2 (pomfritT_convY pk hF b1F b2F lr T P E N g _ _ s' hF3' htgt hb)
  · exact hmk _ (some s') hzL h3
      (pomfritT_convZ pk hF b1F b2F lr T P E N g _ _ _ s' hF4' hF3'' htgt hb)

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The adaptive union bound for PomFRIT, per cipher table, any goal**
(`prEvent_accept_le_adaptive_pomfritT_E` with `GoalP` a parameter): as
`prEvent_accept_le_adaptive_comb_E`, with the statement committed at `H₂²` (`stmtAtD`) and the
statement hits of delayed binding (`stmtHitD`, `(n₂₂ + n₀)·2⁻²⁵⁶` per `H₂⁰` query). No injectivity
is needed: the `H₂⁰` input determines the target (`pomfritTarget_eq_of_muInD`), which is all the
system and the relation read. -/
theorem prEvent_accept_le_adaptive_pomfritT_EG (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (Goal (witKT pk hF (some s))))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (n : ℕ) (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬GoalOut Goal E (stT pk hF b1F b2F lr (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
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
    r.2.2.accept = true ∧ ¬GoalOut Goal E (stF (stOut r)) (witKT pk hF (some (stOut r))) r
  let ε : Kind → ℝ≥0∞ := pomEps pk hF b1F b2F lr n' εc ntot N n''
  have hKε : ∀ k ∉ adaptKinds, ε k = 0 := pomEps_eq_zero pk hF b1F b2F lr n' εc ntot N n''
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
    (pomBad pk hF b1F b2F lr T P E N)
    (fun c t hc hcard => prEvent_pomBad_le pk hF b1F b2F lr T P E hT N hn' hεc q hq K hK ntot c t
      hc hcard)
    (fun g h => pomBad_traceG pk hF b1F b2F lr T P E Goal hT N hdet cf hcf g h)
  have hsum : ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k =
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) +
        n'' .mu * stmtEpsD n'' .mu := by
    simp only [adaptKinds, ε, pomEps]
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

end PomUnionG

/-! ## The joint experiment and the bound for U2's goal -/

section PomJointG

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool) (T : CrtTables) (P : OracleComp specIC (ByteArray × (ι × β))) (Goal : GoalT)

/-- **Lemma P's adaptive bound in the joint experiment, any goal** (the cipher table uniform). -/
theorem prEvent_accept_le_adaptive_pomfritTG (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ (E : CTable) s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (Goal (witKT pk hF (some s))))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬GoalOut Goal E (stT pk hF b1F b2F lr (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n''
  have hE := fun E => prEvent_accept_le_adaptive_pomfritT_EG pk hF b1F b2F lr T P E Goal hT N hn' hεc
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


/-- **The per-chain step for U2's goal** (`pomfritT_extract_some_chain`), `N = 2`. -/
theorem combDetG_pomfritT_some (E : CTable) (s : ι) :
    @CombDetG (icPrg E.cipher) 45 CrtGen.tables (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) 2
      (GoalS (witKT pk hF (some s))) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro ch known acc l c1 hch1 hv A hA hAS hkos hQS hcb hP
  subst hch1
  exact PomFRIT.pomfritT_extract_some_chain pk (stT pk hF b1F b2F lr s) lr rfl ch
    (tgtOf (hF s ch.chal1)) l hv hA hAS hkos hP.1 hQS hcb admissible deltaBlocks
    deltaBlocks_injOn acc hP.2

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Lemma P without `Shift`, adaptive form, every term explicit** (for Theorem U2). For the
issuer's key `pk` and a prover that outputs a proof and the index `s` of its statement (target
function `hF s`, binders `b1F s`, `b2F s`): the verifier accepts and **no fully alive tree has a
candidate `(r, σ)` with `P(σ) = h(chal1) ⊕ r`** (`SomeExtracted`) with probability at most the bound
of `pomfritRedeem_accept_le_adaptive`, with its `H₂³` term `(Q₃+1)·2·2⁻¹²⁸`: no `2⁻⁷¹`. -/
theorem pomfritT_accept_le_some (labelRows : Bool) (P : OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (stT pk hF b1F b2F labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬SomeExtracted E (stT pk hF b1F b2F labelRows (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 + stmtBindEpsD q := by
  classical
  have h := prEvent_accept_le_adaptive_pomfritTG pk hF b1F b2F labelRows CrtGen.tables P
    GoalS liftInvOk_tables 2 (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun E s => combDetG_pomfritT_some pk hF b1F b2F labelRows E s)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q 45 rfl, stmtEpsD_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F labelRows none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
      (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45 +
          stmtBindEpsD q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring


end PomJointG

end VoleMole.ROM.IC
