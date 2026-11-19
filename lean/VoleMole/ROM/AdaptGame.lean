import VoleMole.ROM.CipherFull

/-!
# The soundness game with an adaptively chosen statement (plan M6, statement binding)

`ROM/CipherFull.lean` bounds `Pr[accept ∧ ¬Extracted]` for a *fixed* statement. Here the prover
chooses the statement: a family `stF : ι → Statement` of statements, and a prover
`P : OracleComp specIC (ByteArray × (ι × β))` whose output is a proof together with the index
`s : ι` of the statement it proves (and arbitrary data `β`).

* `extractIC st E r`: the part of `proverIC` after `P` (the straight-line extractor at the
  statement `st`); `proverIC st E P = runE E P >>= extractIC st E` (`proverIC_eq_bind`).
* `proverA stF E P`: `P`, then the extractor at the statement `P` output; `gameA T stF P E`: then
  the verifier on that statement. The statement index of an output is `stOut r` (in `aux`).
* **Per table, the adaptive game is the fixed game at the statement chosen at that table**
  (`evalWithAnswerFn_gameA`, `tableQueryLog_gameA`): against a hash table `g` and a cipher table
  `E`, `gameA T stF P E` has the output and the log of `gameIC T (stF (sA g P E)) P E`, where
  `sA g P E` is `P`'s statement against `g` and `E`. So every deterministic (per-table) lemma of
  the fixed-statement development applies at `stF (sA g P E)`; only the union bounds (whose
  per-query predicates must not depend on the statement chosen at the end) are redone here.
* The query bounds (`isKindQueryBound_gameA`): the prover's, the extractor's and the verifier's,
  as for `gameIC`.
* The failure events with explicit bounds, adaptively: Post (`prEvent_joint_postOut_le_A`),
  binding (`pr_bindFail_le_table_A`, `prEvent_joint_bindFail_le_A`), an opened dead leaf
  (`prEvent_joint_deadOpen_le_A`, through the hash ladder `prEvent_leafUnqueried_le_A`, the fresh
  `H₂³` answer `prEvent_zUnqueried_le_A` and the two fresh cipher cells
  `prEvent_deadQueried_le_A`). The bounds are those of the fixed statement: their bad events
  read the prover's log and the proof, and the per-table facts hold at every statement of the
  family sharing the same parameters (`hparams`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The extractor as a continuation, and the adaptive game -/

section Defs

variable {ι β : Type}

/-- **The straight-line extractor at the statement `st`**, on `P`'s output and joint log `r`: the
part of `proverIC` after `runE E P`. -/
def extractIC (st : Statement) (E : CTable) (r : (ByteArray × β) × QueryLog specIC) :
    OracleComp spec (ByteArray × ExtData (β × QueryLog specIC)) := do
  let pf : Proof := { params := st.params, bytes := r.1.1 }
  let mu1 ← mu1Q st
  let iv ← hashQ .h4 ((pf.ivPre ++ mu1).push 4)
  pure (r.1.1,
    { keys := keysOf (cipherLog r.2) E iv pf.opening pf.delta
      known := knownOf (cipherLog r.2) E iv pf.opening
      aux := (r.1.2, r.2) })

lemma proverIC_eq_bind (st : Statement) (E : CTable) (P : OracleComp specIC (ByteArray × β)) :
    proverIC st E P = runE E P >>= extractIC st E := rfl

lemma gameIC_eq_bind (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
    (E : CTable) : gameIC T st P E = proverIC st E P >>= fun r =>
      (fun t => (r.1, r.2, t)) <$> @verifyQ (icPrg E.cipher) T st r.1 := rfl

variable (T : CrtTables) (stF : ι → Statement)

/-- **The adaptive prover with the straight-line extractor**: `P` (with the cipher answered by
`E`), then the extractor at the statement `P` chose. -/
def proverA (E : CTable) (P : OracleComp specIC (ByteArray × (ι × β))) :
    OracleComp spec (ByteArray × ExtData ((ι × β) × QueryLog specIC)) :=
  runE E P >>= fun r => extractIC (stF r.1.2.1) E r

/-- **The adaptive game**: `proverA`, then the verifier at the statement `P` chose. -/
def gameA (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) :
    OracleComp spec (Out ((ι × β) × QueryLog specIC)) :=
  proverA stF E P >>= fun r =>
    (fun t => (r.1, r.2, t)) <$> @verifyQ (icPrg E.cipher) T (stF r.2.aux.1.1) r.1

/-- The statement index of an output of the adaptive game. -/
def stOut (r : Out ((ι × β) × QueryLog specIC)) : ι := r.2.1.aux.1.1

/-- **`P`'s statement** against the hash table `g` and the cipher table `E`. -/
def sA (g : Table) (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) : ι :=
  (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1

end Defs

/-! ## Per table, the adaptive game is the fixed game -/

section PerTable

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) (g : Table)

lemma evalWithAnswerFn_extractIC_aux (st : Statement) (r : (ByteArray × (ι × β)) × QueryLog specIC) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E r)).2.aux = (r.1.2, r.2) := by
  simp only [extractIC, evalWithAnswerFn_bind, evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_pure]

lemma evalWithAnswerFn_extractIC_fst (st : Statement) (r : (ByteArray × (ι × β)) × QueryLog specIC) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E r)).1 = r.1.1 := by
  simp only [extractIC, evalWithAnswerFn_bind, evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_pure]

/-- **Per table, the adaptive prover is the fixed prover at the chosen statement.** -/
theorem evalWithAnswerFn_proverA :
    evalWithAnswerFn (QueryImpl.ofFn g) (proverA stF E P) =
      evalWithAnswerFn (QueryImpl.ofFn g) (proverIC (stF (sA g P E)) E P) := by
  rw [proverA, proverIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_runE]
  rfl

theorem tableQueryLog_proverA :
    tableQueryLog (proverA stF E P) g = tableQueryLog (proverIC (stF (sA g P E)) E P) g := by
  rw [proverA, proverIC_eq_bind, tableQueryLog_bind, tableQueryLog_bind, evalWithAnswerFn_runE]
  rfl

lemma proverIC_aux_fst (st : Statement) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.aux.1.1 = sA g P E := by
  rw [proverIC_aux]; rfl

/-- **Per table, the adaptive game is the fixed game at the chosen statement.** -/
theorem evalWithAnswerFn_gameA :
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E) =
      evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF (sA g P E)) P E) := by
  rw [gameA, gameIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_proverA, proverIC_aux_fst]

theorem tableQueryLog_gameA :
    tableQueryLog (gameA T stF P E) g = tableQueryLog (gameIC T (stF (sA g P E)) P E) g := by
  rw [gameA, gameIC_eq_bind, tableQueryLog_bind, tableQueryLog_bind, tableQueryLog_proverA,
    evalWithAnswerFn_proverA, proverIC_aux_fst]

/-- The statement index of the adaptive game's output is `P`'s statement. -/
theorem stOut_gameA :
    stOut (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) = sA g P E := by
  rw [evalWithAnswerFn_gameA, stOut, gameIC_eq_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_map, proverIC_aux_fst]

/-- **Any statement-indexed event of the adaptive game's output, per table**, is the event at the
chosen statement of the fixed game's output. -/
theorem gameA_event_iff (ev : ι → Out ((ι × β) × QueryLog specIC) → Prop) :
    (let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E); ev (stOut r) r) ↔
      ev (sA g P E) (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF (sA g P E)) P E)) := by
  simp only [stOut_gameA]
  rw [evalWithAnswerFn_gameA]

end PerTable

/-! ## Query bounds -/

section Bounds

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement)

theorem isKindQueryBound_extractIC (st : Statement) (E : CTable)
    (r : (ByteArray × β) × QueryLog specIC) :
    IsKindQueryBound (extractIC st E r) extractorQueries := by
  unfold extractIC
  have h4 : ∀ k : Kind, k ≠ .h4 → ∀ mu1 : ByteArray,
      IsKindQueryBound (hashQ .h4 ((Proof.ivPre ⟨st.params, r.1.1⟩ ++ mu1).push 4) >>= fun iv =>
        (pure (r.1.1,
          { keys := keysOf (cipherLog r.2) E iv (Proof.opening ⟨st.params, r.1.1⟩)
              (Proof.delta ⟨st.params, r.1.1⟩)
            known := knownOf (cipherLog r.2) E iv (Proof.opening ⟨st.params, r.1.1⟩)
            aux := (r.1.2, r.2) }) :
          OracleComp spec (ByteArray × ExtData (β × QueryLog specIC))))
        (Function.update extractorQueries k (extractorQueries k - 1)) := by
    intro k hk mu1
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨?_, fun _ => trivial⟩
    rw [Function.update_of_ne (Ne.symm hk)]
    simp [extractorQueries]
  unfold mu1Q
  split
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .muDelayed (by decide) u.ba⟩
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .mu (by decide) u.ba⟩

theorem isKindQueryBound_proverA (E : CTable) {P : OracleComp specIC (ByteArray × (ι × β))}
    {q : Kind → ℕ} (hq : IsKindQueryBoundIC P q) :
    IsKindQueryBound (proverA stF E P) (q + extractorQueries) :=
  isKindQueryBound_bind (isKindQueryBound_runE E hq) fun r => isKindQueryBound_extractIC _ E r

/-- **The adaptive game's hash queries per kind**: the prover's, the extractor's two and the
verifier's. -/
theorem isKindQueryBound_gameA (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)
    {q : Kind → ℕ} (hq : IsKindQueryBoundIC P q) :
    IsKindQueryBound (gameA T stF P E) (q + extractorQueries + verifierQueries) :=
  isKindQueryBound_bind (isKindQueryBound_proverA stF E hq) fun r =>
    (isQueryBound_map_iff _ _ _ _ _).2 (@isKindQueryBound_verifyQ (icPrg E.cipher) T _ r.1)

end Bounds

/-! ## The failure events, adaptively -/

section Fails

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement)
  (P : OracleComp specIC (ByteArray × (ι × β)))

/-- The statement index of the fixed game's output is `P`'s statement. -/
lemma stOut_gameIC (st : Statement) (g : Table) (E : CTable) :
    stOut (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) = sA g P E := by
  rw [stOut, gameIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map, proverIC_aux_fst]

/-- The binding failure at the statement of the output. -/
def bindFailA (E : CTable) (r : Out ((ι × β) × QueryLog specIC)) : Prop :=
  @bindFail (icPrg E.cipher) _ (stF (stOut r)) r

/-- An opened dead leaf at the statement of the output. -/
def deadOpenA (E : CTable) (r : Out ((ι × β) × QueryLog specIC)) : Prop :=
  DeadOpenOut (stF (stOut r)) E r

/-- **Post, adaptively**: `≤ 1024·q_E·q₁·2⁻²⁵⁶` (Post reads `P`'s joint log only). -/
theorem prEvent_joint_postOut_le_A (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        PostOut E r] ≤
      ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  have h := prEvent_joint_le_add (gameA T stF P) (fun E r => PostOut E r) (fun _ _ => False)
    (((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostOut, evalWithAnswerFn_gameA, gameIC_aux]
      exact prEvent_postJ_le P g qE hqE q hq
  rwa [prEvent_joint_false, add_zero] at h

/-- **The binding failure, per table** (the pointwise step of `pr_bindFail_le_table`): a fresh
collision query of `P`'s cipher run, or an opened dead leaf. -/
theorem bindFail_imp {β' : Type} (st : Statement) (P' : OracleComp specIC (ByteArray × β'))
    (h : Table) (E : CTable)
    (hb : @bindFail (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P' E))) :
    freshBadC (runH h P') ∅ E collBad ∨
      DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P' E)) := by
  let _ : HasPrg := icPrg E.cipher
  obtain ⟨hacc, hnb⟩ := hb
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC] at hacc hnb ⊢
  set π := (evalWithAnswerFn (QueryImpl.ofFn (join h E)) P').1
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, -⟩ := verify_iv_chal1 _ T st π hacc hr
  rcases binds_or_coll_or_dead (runH h P') E (ivOf (Hashes.ofTable h) ⟨st.params, π⟩
      (st.mu1 (Hashes.ofTable h))) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) with hB | hC | hD
  · exact absurd (fun leaves' hr' => hB leaves' (hiv ▸ hr')) hnb
  · exact Or.inl hC
  · refine Or.inr ⟨hacc, ?_⟩
    show DeadOpen (cipherLog (tableQueryLog P' (join h E))) E _ _ _
    rw [cipherLog_tableQueryLog, hiv]
    exact hD

/-- **The binding failure for a fixed hash table, adaptively**: `≤ 2·q_E²·2⁻²⁵⁶` plus an opened
dead leaf, over the cipher table. -/
theorem pr_bindFail_le_table_A (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE)
    (h : Table) :
    Pr{let E ← $ᵗ CTable}[bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn h) (gameA T stF P E))] ≤
      2 * qE ^ 2 * (2 ^ 256)⁻¹ + Pr{let E ← $ᵗ CTable}[deadOpenA stF E
        (evalWithAnswerFn (QueryImpl.ofFn h) (gameA T stF P E))] := by
  have hn := isTotalQueryBound_runH h hqE
  have hpt : ∀ E : CTable, bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn h) (gameA T stF P E)) →
      freshBadC (runH h P) ∅ E collBad ∨
        deadOpenA stF E (evalWithAnswerFn (QueryImpl.ofFn h) (gameA T stF P E)) := by
    intro E hb
    simp only [bindFailA, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at hb ⊢
    exact bindFail_imp T _ P h E hb
  refine (prEvent_mono _ _ _ hpt).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  exact prEvent_coll_le (runH h P) qE hn (fun E => freshBadC (runH h P) ∅ E collBad) fun _ h => h

/-- **The binding failure in the joint experiment, adaptively.** -/
theorem prEvent_joint_bindFail_le_A (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        bindFailA stF E r] ≤
      2 * qE ^ 2 * (2 ^ 256)⁻¹ +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
          deadOpenA stF E r] :=
  prEvent_joint_le_add (gameA T stF P) (fun E r => bindFailA stF E r)
    (fun E r => deadOpenA stF E r) _ (pr_bindFail_le_table_A T stF P qE hqE)

/-- Updating the hash table at a cell `P` did not query changes neither `P`'s run nor its log. -/
lemma jOf_update_of_not_mem {g : Table} {E : CTable} {d : Dom} (hd : d ∉ hashLog (jOf g P E))
    (u : Ans d) :
    evalWithAnswerFn (QueryImpl.ofFn (join (Function.update g d u) E)) P =
        evalWithAnswerFn (QueryImpl.ofFn (join g E)) P ∧
      jOf (Function.update g d u) P E = jOf g P E :=
  tableQueryLog_congr P (join g E) (join (Function.update g d u) E) fun _ ht =>
    join_update_inl_of_ne g E d u fun h => mem_hashLog.not.1 hd (h ▸ ht)

/-- **The hash ladder, adaptively** (`prEvent_accept_leafUnqueried_z_le`): the verifier accepts,
one of its leaf-hash inputs is not among `P`'s hash queries but its `H₂³` input is, with
probability at most `(q₁+18)·ladderEps₁ + (q₂₁+1)·ladderEps₂₁ + (q₂₂+1)·ladderEps₂₂`. The bad
answers read `P`'s log and `Δ` only. -/
theorem prEvent_leafUnqueried_z_le_A (p : Params) (hparams : ∀ s, (stF s).params = p)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) (E : CTable) :
    Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧
          @LeafUnqueried (icPrg E.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
          ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2] ≤
      (q .h1 + 18) * ladderEps q .h1 + (q .h21 + 1) * ladderEps q .h21 +
        (q .h22 + 1) * ladderEps q .h22 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set PQ : Table → List Dom := fun g => hashLog (jOf g P E)
  set δ : Table → ByteArray := fun g => Proof.delta ⟨p, πOf g P E⟩
  let bad : Dom → Table → Prop := fun t g => t.1 ≠ .h23 ∧ ladderBad PQ δ t g
  let ε : Kind → ℝ≥0∞ := fun k => if k = .h23 then 0 else ladderEps q k
  have hε : ∀ k ∉ ladderKinds', ε k = 0 := by
    intro k hk
    cases k <;> simp_all [ladderKinds', ε, ladderEps]
  have hbad : ∀ (t : Dom) (g : Table),
      Pr{let u ← $ᵗ (Ans t)}[bad t (Function.update g t u)] ≤ ε t.1 := by
    rintro ⟨k, w⟩ g
    by_cases h23 : k = .h23
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hu.1 h23).trans ?_
      rw [prEvent_false]
      exact bot_le
    have hε' : ε k = ladderEps q k := ite_eq_right_of_eq_false _ _ (eq_false h23)
    show _ ≤ ε k
    rw [hε']
    by_cases ht : ((k, w) : Dom) ∈ PQ g
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hu.2.1 ?_).trans (by simp)
      show ((k, w) : Dom) ∈ hashLog (jOf (Function.update g (k, w) u) P E)
      rw [mem_hashLog] at ht ⊢
      exact mem_tableQueryLog_congr P _ _ _ (fun t ht' => join_update_inl_of_ne g E _ u ht') ht
    have hfx : ∀ u : Ans (k, w), PQ (Function.update g (k, w) u) = PQ g ∧
        δ (Function.update g (k, w) u) = δ g := fun u => by
      obtain ⟨h1, h2⟩ := jOf_update_of_not_mem P ht u
      exact ⟨by simp only [PQ, h2], by simp only [δ, πOf, h1]⟩
    by_cases hk : k ∈ ladderKinds
    · refine (prEvent_mono _ _ (fun u : Prob.Bytes k.outLen => u.ba ∈ ladderTargets (δ g) (PQ g) k)
        fun u hu => ?_).trans ((prEvent_ba_mem_le k.outLen _).trans
          (length_ladderTargets_le (δ g) (PQ g) q
            (fun k' => length_kindIns_hashLog_le P hq (join g E) k') k))
      have h2 := hu.2.2
      rw [(hfx u).1, (hfx u).2, Function.update_self] at h2
      exact h2
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => ?_).trans (by simp)
      have h2 := hu.2.2
      rw [ladderTargets_of_not_mem _ _ hk] at h2
      exact List.not_mem_nil h2
  have htrace : ∀ g : Table, (fun r : Out ((ι × β) × QueryLog specIC) => r.2.2.accept = true ∧
      @LeafUnqueried (icPrg E.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
        ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2)
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) →
      ∃ e ∈ tableQueryLog (gameA T stF P E) g, bad e.1 g := by
    intro g h
    simp only [evalWithAnswerFn_gameA, stOut_gameIC] at h
    rw [tableQueryLog_gameA]
    set st := stF (sA g P E)
    have e : (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.1 =
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2 := by rw [evalWithAnswerFn_game]
    obtain ⟨hacc, hL, hz⟩ := h
    change (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.2.accept = true
      at hacc
    change LeafUnqueried st (hashLog (evalWithAnswerFn (QueryImpl.ofFn g)
      (game T st (proverIC st E P))).2.1.aux.2)
      (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hL
    change ((.h23, zOut st (evalWithAnswerFn (QueryImpl.ofFn g)
      (game T st (proverIC st E P)))) : Dom) ∈ hashLog (evalWithAnswerFn (QueryImpl.ofFn g)
      (game T st (proverIC st E P))).2.1.aux.2 at hz
    rw [e] at hL hz
    rcases ladder_walk T st (proverIC st E P) (fun aux => hashLog aux.2) g hacc hL with
      hz' | ⟨e, he, hk, hb⟩
    · exact absurd hz hz'
    · refine ⟨e, he, hk, ?_⟩
      have hp : st.params = p := hparams _
      simp only [ladderBad, proverIC_aux, proverIC_fst, hp] at hb
      exact hb
  refine (prEvent_exists_bad_query_le (gameA T stF P E) (q + extractorQueries + verifierQueries)
    (isKindQueryBound_gameA T stF P E hq) _ bad ladderKinds' ε hε hbad htrace).trans_eq ?_
  simp [ladderKinds', verifierQueries, extractorQueries, Pi.add_apply, add_assoc, ε]

/-- **The verifier's `H₂³` input unqueried by `P`, adaptively** (`prEvent_accept_zUnqueried_le`):
acceptance needs one fresh answer to be `Δ`, `≤ 2⁻¹²⁸`. Updating the table at that cell changes
neither `P`'s run (so neither the statement) nor the verifier's chain. -/
theorem prEvent_zUnqueried_le_A (E : CTable) :
    Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  let _ : HasPrg := icPrg E.cipher
  let st : Table → Statement := fun g => stF (sA g P E)
  let π : Table → ByteArray := fun g => πOf g P E
  let lv : Table → BAVC.Leaves := fun g =>
    (BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨(st g).params, π g⟩
      ((st g).mu1 (Hashes.ofTable g))) (Proof.opening ⟨(st g).params, π g⟩)
      (Proof.delta ⟨(st g).params, π g⟩)).getD ⟨.empty, .empty⟩
  let zz : Table → ByteArray := fun g =>
    runZ (st g) (runChain (Hashes.ofTable g) T (st g) (π g) (lv g) fun _ _ => ByteArray.empty)
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2
  have hgame : ∀ g, evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E) =
      (π g, (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC (st g) E P)).2,
        verify (Hashes.ofTable g) T (st g) (π g)) := fun g => by
    rw [evalWithAnswerFn_gameA]
    exact (evalWithAnswerFn_game g T _ _).trans (by rw [proverIC_fst]; rfl)
  have hst : ∀ g, stOut (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) = sA g P E :=
    fun g => stOut_gameA T stF P E g
  have hfacts : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) →
      BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨(st g).params, π g⟩
        ((st g).mu1 (Hashes.ofTable g))) (Proof.opening ⟨(st g).params, π g⟩)
        (Proof.delta ⟨(st g).params, π g⟩) = some (lv g) ∧
      (verify (Hashes.ofTable g) T (st g) (π g)).accept = true ∧
      ((.h23, zz g) : Dom) ∉ hashLog (jOf g P E) := by
    intro g hg
    obtain ⟨hacc, hz⟩ := hg
    rw [hst] at hz
    rw [hgame] at hacc hz
    rw [proverIC_aux] at hz
    obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T (st g) (π g)).1 hacc
    have hlv : lv g = leaves := by simp only [lv, hr, Option.getD_some]
    refine ⟨hlv ▸ hr, hacc, ?_⟩
    rw [zOut_eq_runZ _ T (st g) (π g) _ hacc hr (fun _ _ => ByteArray.empty)] at hz
    simpa only [zz, hlv, jOf] using hz
  have hP' : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) → ∀ u,
      π (Function.update g (.h23, zz g) u) = π g ∧ st (Function.update g (.h23, zz g) u) = st g :=
    fun g hg u => by
      have h1 := (jOf_update_of_not_mem P (hfacts g hg).2.2 u).1
      exact ⟨by simp only [π, πOf, h1], by simp only [st, sA, h1]⟩
  have hlv' : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) → ∀ u,
      lv (Function.update g (.h23, zz g) u) = lv g := fun g hg u => by
    obtain ⟨hπ, hs⟩ := hP' g hg u
    simp only [lv, hπ, hs, ivOf_ofTable_update_h23]
  have hzz : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) → ∀ u,
      zz (Function.update g (.h23, zz g) u) = zz g := fun g hg u => by
    obtain ⟨hπ, hs⟩ := hP' g hg u
    simp only [zz, hπ, hs, hlv' g hg u, runChain_ofTable_update_h23]
  have h := prEvent_fresh_guess_le (gameA T stF P E) ev (fun g => (.h23, zz g)) .h23 1
    (fun _ => rfl)
    (fun g hg => by
      obtain ⟨hr, hacc, -⟩ := hfacts g hg
      rw [tableQueryLog_gameA]
      exact inLog_gLog T (st g) P E g
        (inLog_verifyQ g T (st g) (π g) hacc hr (fun _ _ => ByteArray.empty)).2.2)
    (fun g hg u => by
      show ((.h23, zz (Function.update g (.h23, zz g) u)) : Dom) = (.h23, zz g)
      rw [hzz g hg u])
    (fun g hg => by
      refine ⟨finOf fun u : Prob.Bytes 16 => u.ba = Proof.delta ⟨(st g).params, π g⟩,
        Finset.card_le_one.2 fun a ha b hb =>
          Bytes.ba_injective ((mem_finOf.1 ha).trans (mem_finOf.1 hb).symm), fun u hu => ?_⟩
      refine mem_finOf.2 ?_
      obtain ⟨hacc', -⟩ := hu
      rw [hgame] at hacc'
      obtain ⟨hπ, hs⟩ := hP' g hg u
      obtain ⟨-, leaves', hr', -, h3⟩ :=
        (accept_iff _ T (st (Function.update g (.h23, zz g) u))
          (π (Function.update g (.h23, zz g) u))).1 hacc'
      have hlv'' : lv (Function.update g (.h23, zz g) u) = leaves' := by
        simp only [lv, hr', Option.getD_some]
      have hz' := hzz g hg u
      simp only [zz, hlv''] at hz'
      have h3' : (Function.update g (.h23, zz g) u
          (.h23, runZ (st (Function.update g (.h23, zz g) u))
            (runChain (Hashes.ofTable (Function.update g (.h23, zz g) u)) T
              (st (Function.update g (.h23, zz g) u))
              (π (Function.update g (.h23, zz g) u)) leaves' fun _ _ => ByteArray.empty))).ba =
          Proof.delta ⟨(st (Function.update g (.h23, zz g) u)).params,
            π (Function.update g (.h23, zz g) u)⟩ := h3
      rw [hz', Function.update_self, hπ, hs] at h3'
      exact h3')
  refine h.trans (le_of_eq ?_)
  norm_num [Kind.outLen]

/-- **A dead leaf whose leaf hashes `P` queried, adaptively**, for a fixed hash table: `≤ q₁·2⁻²⁵⁶`
over the cipher table. The dead leaf's cells are not in `P`'s cipher log, so setting them changes
neither `P`'s run nor its statement (`prEvent_deadQueried_le` at the statement of each table). -/
theorem prEvent_deadQueried_le_A (g : Table) (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable}[DeadQueried g (stF (sA g P E)) P E] ≤ q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hinvS : ∀ E, (∃ p, DeadAt g (stF (sA g P E)) P E p) → ∀ w,
      sA g P (upd2 E (dc g (stF (sA g P E)) P E 0) (dc g (stF (sA g P E)) P E 1) w) =
        sA g P E := by
    intro E hE w
    set st := stF (sA g P E)
    obtain ⟨-, -, -, hnc⟩ := deadAt_deadPt g st P hE
    set E' := upd2 E (dc g st P E 0) (dc g st P E 1) w
    have hnot : ∀ c, c < 2 → dc g st P E c ∉ (cipherLog (jOf g P E)).map Sigma.fst := by
      intro c hc h
      obtain ⟨q, hq, hqe⟩ := List.mem_map.1 h
      refine hnc ⟨q, hq, ?_⟩
      interval_cases c
      · exact Or.inl hqe
      · exact Or.inr hqe
    have hJ : ∀ t ∈ (jOf g P E).map Sigma.fst, join g E' t = join g E t := by
      intro t ht
      cases t with
      | inl d => rw [join_inl, join_inl]
      | inr x =>
        have hx := mem_cipherLog.2 ht
        rw [join_inr, join_inr]
        exact upd2_apply_of_ne E (fun h => hnot 0 (by norm_num) (by rw [← h]; exact hx))
          (fun h => hnot 1 (by norm_num) (by rw [← h]; exact hx)) w
    have hP := (tableQueryLog_congr P (join g E) (join g E') hJ).1
    simp only [sA, hP]
  refine prEvent_two_cells_le _ (fun E => dc g (stF (sA g P E)) P E 0)
    (fun E => dc g (stF (sA g P E)) P E 1) (fun E => deadTargets g (stF (sA g P E)) P E) (q .h1)
    (fun E _ h => ?_) (fun E hE w => ?_) (fun E _ => ?_)
    (fun E hE => deadQueried_mem g _ P hE)
  · have h2 := congrArg Prod.snd h
    simp only [dc_snd] at h2
    exact lp_ne _ _ h2
  · rw [hinvS E hE.2 w]
    exact deadQueried_inv g _ P hE.2 w
  · refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map]
    exact length_kindIns_hashLog_le P hq (join g E) .h1

/-- **`ε_open`, adaptively**: an accepted proof opens a dead leaf with probability at most
`openHashEps q + q₁·2⁻²⁵⁶`, the bound of `prEvent_joint_deadOpen_le`. -/
theorem prEvent_joint_deadOpen_le_A (p : Params) (hparams : ∀ s, (stF s).params = p)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        deadOpenA stF E r] ≤ openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let m : CTable → ProbComp (Out ((ι × β) × QueryLog specIC)) := fun E =>
    (simulateQ randomOracle (gameA T stF P E)).run' ∅
  let A : CTable → Out ((ι × β) × QueryLog specIC) → Prop := fun E r =>
    r.2.2.accept = true ∧
      @LeafUnqueried (icPrg E.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r
  have hA : ∀ E, Pr{let r ← m E}[A E r] ≤ openHashEps q := fun E => by
    refine (prEvent_mono _ _ (fun r => (r.2.2.accept = true ∧
        @LeafUnqueried (icPrg E.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
          ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2) ∨
        (r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2))
        fun r h => (em (((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2)).elim
          (fun hz => Or.inl ⟨h.1, h.2, hz⟩) fun hz => Or.inr ⟨h.1, hz⟩).trans
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_leafUnqueried_z_le_A T stF P p hparams q hq E)
        (prEvent_zUnqueried_le_A T stF P E)))
  have h1 : Pr{let E ← $ᵗ CTable; let r ← m E}[A E r] ≤ openHashEps q := by
    have h := prEvent_avg_le_add m A (fun _ _ => False) (openHashEps q) fun E =>
      (hA E).trans le_self_add
    rwa [prEvent_joint_false, add_zero] at h
  have h2 : Pr{let E ← $ᵗ CTable; let r ← m E}[deadOpenA stF E r ∧ ¬A E r] ≤
      q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    have h := prEvent_joint_le_add (gameA T stF P) (fun E r => deadOpenA stF E r ∧ ¬A E r)
      (fun _ _ => False) (q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) fun g =>
        ((prEvent_mono _ _ _ fun E h => by
          simp only [A, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at h
          exact deadQueried_of_deadOpen T _ P g E h.1 fun hL => h.2 ⟨h.1.1, hL⟩).trans
          (prEvent_deadQueried_le_A stF P g q hq)).trans le_self_add
    rwa [prEvent_joint_false, add_zero] at h
  calc Pr{let E ← $ᵗ CTable; let r ← m E}[deadOpenA stF E r]
      ≤ Pr{let E ← $ᵗ CTable; let r ← m E}[A E r ∨ (deadOpenA stF E r ∧ ¬A E r)] :=
        prEvent_joint_mono m _ _ fun E r h => (em (A E r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_joint_or_le m _ _).trans (add_le_add h1 h2)

end Fails

end VoleMole.ROM.IC
