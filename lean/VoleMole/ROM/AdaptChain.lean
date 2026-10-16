import VoleMole.ROM.StmtBind

/-!
# Adaptively chosen statements: the union bound with the statement read off the log (issue relations)

The fixed-statement bound (`prEvent_accept_le_chain_terms`, at the joint game) charges every
`H₂¹`, `H₂²`, `H₂³` query with the bad event of *the* statement's chain data. With the statement
chosen by the prover at the end, the charge of a query must not depend on that choice: here it is
the bad event of the statement **committed at the query** (`stmtAt`, `ROM/StmtBind.lean`), a
function of the log before the query, so the per-query bounds are unchanged
(`prEvent_chainBadA_le`). The identification of the accepted chain's statement with the committed
one costs the statement hits (`stmtHit`), one more family of per-query bad events.

* `ChainDet T st cs N Wit`: the per-chain deterministic theorem of an issue relation
  (`*_extract_chain`), as `prEvent_accept_le_chain_terms`' `hdet`.
* `chainBad_trace_ic`: the deterministic step of `prEvent_accept_le_chain_terms` at the joint
  game, for a fixed statement: an accepted proof from which extraction fails, outside Post,
  binding failure, an opened dead leaf and chain hits, makes the verifier's `H₂¹`, `H₂²` or `H₂³`
  query bad.
* `chainBadA`: the bad event of the chain data of the statement committed at the query;
  `chainHitL`: the chain hits of `ROM/CipherChain.lean` against any log.
* **`prEvent_accept_le_adaptive_E`**: for a family of non-delayed statements with common
  parameters and combination, an injective encoding (`dec (muIn (stF s)) = some s`), per cipher
  table: `Pr[accept ∧ ¬Extracted] ≤` the chain terms + the hits + the statement hits
  `n₀·(n₂₁ + n₀)·2⁻²⁵⁶` + `Pr[bindFail] + Pr[DeadOpenOut] + Pr[Post]`, all at the statement of the
  output.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The per-chain deterministic theorem -/

/-- **The per-chain deterministic theorem of an issue relation** with system `cs` (the `hdet` of
`prEvent_accept_le_chain_terms`). -/
def ChainDet [HasPrg] (T : CrtTables) (st : Statement) (cs : System GF128) (N : ℕ)
    (Wit : ByteArray → (ℕ → GF128) → Prop) : Prop :=
  ∀ (ch : Chain) (known : Finset (Fin BAVC.tau)) (acc : Prob.Bytes 16 → Prop),
    (∀ w, ch.vals w = cs.values w) →
    ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
    Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      ¬cs.Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec cs (wStar uStar (ch.dc st))) ≠ 0) →
    ChainHyps A known acc →
    (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
      (open Classical in #{x ∈ admissible | acc x} ≤ N)

/-! ## The deterministic step at the joint game, for a fixed statement -/

section Trace

variable {β : Type} {T : CrtTables}

set_option maxRecDepth 4000 in
/-- **The deterministic step at the joint game** (`prEvent_accept_le_chain_terms`' `htrace`, with
the chain data, hits and failure events of `ROM/CipherChain.lean`): an accepted proof from which
extraction fails, outside Post, a binding failure, an opened dead leaf and chain hits, makes one
of the verifier's `H₂¹`, `H₂²`, `H₂³` queries bad. -/
theorem chainBad_trace_ic (hT : liftInvOk T = true) (st : Statement) (cs : System GF128) (N : ℕ)
    (Wit : ByteArray → (ℕ → GF128) → Prop) (hvals : ∀ c1 lb w, st.values c1 lb w = cs.values w)
    (P : OracleComp specIC (ByteArray × β)) (E : CTable)
    (hdet : @ChainDet (icPrg E.cipher) T st cs N Wit) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (hnex : ¬@Extracted (icPrg E.cipher) _ st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnc : ¬PostOut E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnb : ¬@bindFail (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnd : ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) :
    letI := icPrg E.cipher
    ∃ leaves, BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves ∧
      (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true ∧
      let C := ChainData.ofSys (st := st) (preOf T st P E) (midOf T st P E) cs (accOf T st P E)
      let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
      chainBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) g ∨
        chainBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
        chainBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set C := ChainData.ofSys (st := st) (preOf T st P E) (midOf T st P E) cs (accOf T st P E)
  have hs := sameChainHyp_ic T st P E g
  have hl := deadHiddenHyp_ic T st P E g
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬PostOut E r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys
    SameChain st T C.preOf C.midOf C.accOf (deadOf T st P E g) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch) ∧
      ∀ i ∉ r.2.1.known, (deadOf T st P E g i).Nonempty at hs
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬PostOut E r → ¬DeadOpenOut st E r →
    NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ i : Fin BAVC.tau, ∀ j ∈ deadOf T st P E g i,
      BAVC.deltaIndex (Proof.delta ⟨st.params, r.1⟩) i = j at hl
  change (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.2.accept = true
    at hacc
  change ¬Extracted st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnex
  change ¬PostOut E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnc
  change ¬bindFail st (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnb
  change ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnd
  have hπ : (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 = πOf g P E :=
    proverIC_fst g st E P
  simp only [evalWithAnswerFn_game, hπ] at hs hl hacc hnex hnc hnb hnd
  set π := πOf g P E
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  obtain ⟨hsc, hL2c⟩ := hs hacc hnc hh leaves hr'
  have hbad := chainBad_of_accept hT C N Wit (fun _ _ c1 lb w => hvals c1 lb w)
    (fun _ _ ch known acc hv => hdet ch known acc hv) hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) hsc hL2c (hl hacc hnc hnd hh)
    (by
      rintro ⟨i, hi, hw⟩
      refine hnex ⟨i, hi, ?_⟩
      simp only [huc.1, huc.2, hc1]
      exact hw)
  exact ⟨leaves, hr, hacc, hbad⟩

end Trace

/-! ## Hits against any log -/

section HitL

/-- **A chain hit against the log `L`** (`chainHit` with the log a parameter). -/
def chainHitL (cb : Option (ℕ × ByteArray)) (L : Table → QueryLog spec) (t : Dom) (g : Table) :
    Prop :=
  (g t).ba ∈ hitTargets cb (logBefore t (L g)) t.1

/-- **A hit has probability `≤ hitEps n` when its cell alone is resampled** (`prEvent_chainHit_le`
for any computation with at most `n k` queries of each kind). -/
theorem prEvent_chainHitL_le {α : Type} (cb : Option (ℕ × ByteArray)) (oa : OracleComp spec α)
    (n : Kind → ℕ) (hn : IsKindQueryBound oa n) (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[chainHitL cb (tableQueryLog oa) t (Function.update g t u)] ≤
      hitEps n (combCount cb n) t.1 := by
  have h : ∀ u : Ans t, chainHitL cb (tableQueryLog oa) t (Function.update g t u) ↔
      u.ba ∈ hitTargets cb (logBefore t (tableQueryLog oa g)) t.1 := fun u => by
    simp only [chainHitL, Function.update_self, logBefore_tableQueryLog_update]
  simp_rw [h]
  refine (prEvent_ba_mem_le t.1.outLen _).trans
    (length_hitTargets_le cb _ n (fun k => ?_) t.1)
  exact (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
    (length_kindIns_tableQueryLog_le _ hn g k)

end HitL

/-! ## The adaptive union bound -/

section Adapt

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (sys : ι → System GF128) (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)

/-- The chain data of the statement `s` (`ROM/CipherChain.lean`'s, at `stF s`). -/
def chainDataA (s : ι) : ChainData (stF s) :=
  ChainData.ofSys (preOf T (stF s) P E) (midOf T (stF s) P E) (sys s) (accOf T (stF s) P E)

/-- **A bad chain query at the statement committed there.** -/
def chainBadA (N : ℕ) (t : Dom) (g : Table) : Prop :=
  ∃ s, stmtAt dec (tableQueryLog (gameA T stF P E) g) t = some s ∧
    @chainBad (icPrg E.cipher) (stF s) (chainDataA T stF sys P E s) T chal3Blocks N t g

lemma chainEps_congr {st st' : Statement} (h : st.params = st'.params) (S : Finset Blocks)
    (n N : ℕ) : chainEps st S n N = chainEps st' S n N := by
  funext k
  have hk : Chain.kosL st = Chain.kosL st' := by simp only [Chain.kosL, h]
  cases k <;> simp only [chainEps, hk]

/-- **The per-query bound of a bad chain query at its committed statement**: the statement does
not read the query's cell, and each statement's chain data are committed. -/
theorem prEvent_chainBadA_le (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[chainBadA T stF dec sys P E N t (Function.update g t u)] ≤
      chainEps st₀ chal3Blocks n N t.1 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  have h : ∀ u, chainBadA T stF dec sys P E N t (Function.update g t u) ↔
      ∃ s, stmtAt dec (tableQueryLog (gameA T stF P E) g) t = some s ∧
        chainBad (chainDataA T stF sys P E s) T chal3Blocks N t (Function.update g t u) :=
    fun u => by unfold chainBadA; rw [stmtAt_update]
  simp_rw [h]
  rcases hσ : stmtAt dec (tableQueryLog (gameA T stF P E) g) t with _ | s
  · simp only [reduceCtorEq, false_and, exists_false]
    rw [prEvent_false]
    exact bot_le
  · have h' : ∀ u, (∃ s', some s = some s' ∧
        chainBad (chainDataA T stF sys P E s') T chal3Blocks N t (Function.update g t u)) ↔
        chainBad (chainDataA T stF sys P E s) T chal3Blocks N t (Function.update g t u) :=
      fun u => ⟨fun ⟨s', hs', hb⟩ => (Option.some.inj hs') ▸ hb, fun hb => ⟨s, rfl, hb⟩⟩
    simp_rw [h']
    refine (prEvent_chainBad_update_le hT (chainDataA T stF sys P E s)
      (chainData_committed T (stF s) P E (sys s)) chal3Blocks (fun _ _ => hn s) N t g).trans_eq ?_
    rw [chainEps_congr (hparams s)]

/-- The kinds charged by the adaptive union bound: the chain's, and `H₂⁰`. -/
def adaptKinds : Finset Kind := {.h1, .h21, .h22, .h23, .mu}

/-- **The adaptive union bound for the issue relations, per cipher table.** A family `stF` of
non-delayed statements with common parameters (those of `st₀`) and combination `cb`, an encoding
that determines the statement (`dec (muIn (stF s)) = some s`), systems `sys s` of a common
length `n` and per-chain deterministic theorems for each statement. Against the lazy hash
oracle, the adaptive game (`P` with `q k` hash queries of kind `k`; `n' = q + extractorQueries +
verifierQueries` with the extractor's and the verifier's) accepts with extraction failing at the
statement `P` chose with probability at most

    n'₂₁·ε_KOS + n'₂₂·ε_QS(n) + n'₂₃·N·2⁻¹²⁸ + hitSum n' (hitEps n') + n'₀·(n'₂₁ + n'₀)·2⁻²⁵⁶
      + Pr[bindFail] + Pr[DeadOpenOut] + Pr[Post],

the failure events at the statement of the output. -/
theorem prEvent_accept_le_adaptive_E (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    let n' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n' .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        n' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + hitSum n' (hitEps n' (combCount cb n')) +
        n' .mu * stmtEps n' .mu +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[bindFailA stF E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[deadOpenA stF E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[PostOut E r] := by
  classical
  intro n'
  let _ : HasPrg := icPrg E.cipher
  set oa := gameA T stF P E
  set mx := (simulateQ randomOracle oa).run' ∅
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬Extracted (stF (stOut r)) (Wit (stOut r)) r
  let bad : Dom → Table → Prop := fun t g =>
    chainBadA T stF dec sys P E N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨
      stmtHit (tableQueryLog oa) t g
  let ε : Kind → ℝ≥0∞ := fun k =>
    chainEps st₀ chal3Blocks n N k + (hitEps n' (combCount cb n') k + stmtEps n' k)
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := by
    intro k hk
    cases k <;> simp_all [adaptKinds, ε, chainEps, hitEps, stmtEps]
  have hbad : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[bad t (Function.update g t u)] ≤ ε t.1 := fun t g =>
    (prEvent_or_le _ _ _).trans (add_le_add
      (prEvent_chainBadA_le T stF dec sys P E hT st₀ hparams hn N t g)
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_chainHitL_le cb oa n' (isKindQueryBound_gameA T stF P E hq) t g)
        (prEvent_stmtHit_le oa n' (isKindQueryBound_gameA T stF P E hq) t g))))
  have htrace : ∀ g : Table, (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬PostOut E r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
    intro g h
    simp only [ev, bindFailA, deadOpenA, oa, evalWithAnswerFn_gameA, stOut_gameIC] at h
    obtain ⟨⟨hacc, hnex⟩, hnb, hnd, hnp⟩ := h
    set s := sA g P E
    set st := stF s
    have hlog : tableQueryLog oa g = gLog T st P E g := tableQueryLog_gameA T stF P E g
    by_cases hh : NoHit (gameIC T st P E) (chainHit T st P E) g
    swap
    · simp only [NoHit, not_forall, not_not] at hh
      obtain ⟨e, he, hhit⟩ := hh
      refine ⟨e, hlog ▸ he, Or.inr (Or.inl ?_)⟩
      unfold chainHitL
      rw [hlog, ← hcomb s]
      exact hhit
    by_cases hs : NoStmtHit T st P E g
    swap
    · simp only [NoStmtHit, not_forall, not_not] at hs
      obtain ⟨e, he, hhit⟩ := hs
      refine ⟨e, hlog ▸ he, Or.inr (Or.inr ?_)⟩
      unfold stmtHit
      rw [hlog]
      exact hhit
    obtain ⟨leaves, hr, hacc', hbad⟩ := chainBad_trace_ic hT st (sys s) N (Wit s) (hvals s) P E
      (hdet s) g hacc hnex hnp hnb hnd hh
    set keys := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
    obtain ⟨h1, h2, h3⟩ := stmtAt_ident dec T st P E g (hdel s) (hdec s) hh hs keys hacc' hr
    have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩
        (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr
    obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T st (πOf g P E) hacc' hr0 keys
    have hmk : ∀ t, InLog (verifyQ T st (πOf g P E)) g t → stmtAt dec (gLog T st P E g) t = some s →
        chainBad (chainDataA T stF sys P E s) T chal3Blocks N t g →
        ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
      intro t ht hst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T st P E g ht)
      refine ⟨e, hlog ▸ he, Or.inl ⟨s, ?_, hb⟩⟩
      rw [hlog]
      exact hst
    rcases hbad with hb | hb | hb
    · exact hmk _ hxL h1 hb
    · exact hmk _ hyL h2 hb
    · exact hmk _ hzL h3 hb
  have hgood := prEvent_exists_bad_query_le oa n' (isKindQueryBound_gameA T stF P E hq)
    (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r) bad
    adaptKinds ε hK hbad htrace
  have hsum : ∑ k ∈ adaptKinds, (n' k : ℝ≥0∞) * ε k =
      n' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n' .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        n' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + hitSum n' (hitEps n' (combCount cb n')) +
        n' .mu * stmtEps n' .mu := by
    simp only [adaptKinds, ε]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [chainEps, hitEps, stmtEps, hitSum, zero_add, add_zero, mul_add]
    ring
  calc Pr{let r ← mx}[ev r]
      ≤ Pr{let r ← mx}[(ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r) ∨
          (bindFailA stF E r ∨ (deadOpenA stF E r ∨ PostOut E r))] :=
        prEvent_mono mx _ _ fun r h => by tauto
    _ ≤ Pr{let r ← mx}[ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r] +
          (Pr{let r ← mx}[bindFailA stF E r] +
            (Pr{let r ← mx}[deadOpenA stF E r] + Pr{let r ← mx}[PostOut E r])) :=
        (prEvent_or_le mx _ _).trans (add_le_add le_rfl ((prEvent_or_le mx _ _).trans
          (add_le_add le_rfl (prEvent_or_le mx _ _))))
    _ ≤ _ := by
        rw [← hsum]
        refine (add_le_add hgood le_rfl).trans_eq ?_
        ring

end Adapt

end VoleMole.ROM.IC
