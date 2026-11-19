import VoleMole.Assumptions.PermLinks
import VoleMole.ROM.MoussakaOMUFSimPerm

/-!
# Moussaka down to OMPR with AES and `Com` both random permutations with inverse queries

`ROM/MoussakaOMUFSimPerm.lean` (`omuf_le_num_simP`: AES as random permutations, the adversary with
forward and inverse cipher queries, simultaneous extraction) with its forgery term made the
standalone CT-UF^open advantage of an explicit forger, and then `Assumptions/PermLinks.lean`'s
permutation model of `Com` (`advCTUFPermAt_le_ompr`).

* **Logs** (`tableQueryLog_liftP`, `tableQueryLog_normJ`): the hash-and-cipher log of a lifted
  computation, and of a jointly normalized one, is a function of the original's log.
* **The forger** `ctufForgerP lr pk qI A`: a CT-UF^open forger whose common randomness is the
  permutation table `π`; it runs the permutation-model game and every extraction with the signers
  as its oracle (`extAllP`) and outputs `ctufOut` at the forward table. It reads its signers only
  on its signing log (`gameP_congr`, through `runIssP_congr` and the log lemmas).
* `ctOpenWin_of_forgeP`, `win_imp_openP`: per table, a win of the permutation-model game is an
  extraction failure, a `Com` collision or a CT-UF^open win of `ctufForgerP`.
* **`omuf_le_open_simP`**, **`omuf_le_num_open_simP`**, **`omuf_le_num_ompr_simP`**:

      Pr[Win] ≤ εIR^simP(q', q'_E, n', qI, qR) + Pr[Coll]
                + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j}) + permEps,

  under the modelling hypothesis `hmodelP` for `ctufForgerP` (as in `omuf_le_num_ompr_perm`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM

/-! ## Logs of lifted and normalized computations -/

section Logs

variable {α : Type}

/-- A cipher query of the PRF view as a forward query of the permutation model. -/
def liftQ : DomIC → DomP
  | .inl d => .inl d
  | .inr c => .inr (true, c)

/-- **The log of a lifted computation** is the original's log, each query lifted. -/
theorem tableQueryLog_liftP (h : Table) (π : PTable) (X : OracleComp specIC α) :
    tableQueryLog (liftP X) (joinP h π) =
      (tableQueryLog X (join h π.fwd)).map fun e => ⟨liftQ e.1, joinP h π (liftQ e.1)⟩ := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with d | c
    · rw [liftP_inl, tableQueryLog_query_bind, tableQueryLog_query_bind, List.map_cons]
      exact congrArg₂ List.cons rfl (ih (h d))
    · rw [liftP_inr, tableQueryLog_query_bind, tableQueryLog_query_bind, List.map_cons]
      exact congrArg₂ List.cons rfl (ih _)

/-- The queries of the PRF view that the joint normalization makes for one query of the
permutation model. -/
def normQs (pI pR : Params) (π : PTable) : DomP → List DomIC
  | .inl d => if d.1 = .h21 then [.inl (.h4, ivIn pR d.2), .inl (.h4, ivIn pI d.2), .inl d]
      else [.inl d]
  | .inr (true, c) => [.inr c]
  | .inr (false, c) => [.inr (c.1, (π c.1).symm c.2)]

/-- **The log of a jointly normalized computation** is a function of the original's log. -/
theorem tableQueryLog_normJ (pI pR : Params) (h : Table) (π : PTable) (P : OracleComp specP α) :
    tableQueryLog (normJ pI pR π P) (join h π.fwd) =
      (tableQueryLog P (joinP h π)).flatMap fun e =>
        (normQs pI pR π e.1).map fun t => ⟨t, join h π.fwd t⟩ := by
  induction P using OracleComp.inductionOn with
  | pure a => simp [normJ]
  | query_bind t k ih =>
    rcases t with d | ⟨_ | _, c⟩
    · simp only [normJ] at ih ⊢
      rw [addIV_inl]
      by_cases hd : d.1 = .h21
      · simp only [hd, ite_true]
        rw [normP_inl, ite_eq_right_of_eq_false _ _ (by simp), tableQueryLog_query_bind, normP_inl,
          ite_eq_left_of_eq_true _ _ (eq_true hd),
          tableQueryLog_query_bind, tableQueryLog_query_bind, tableQueryLog_query_bind]
        simp only [List.flatMap_cons, normQs, hd, ite_true, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append]
        exact congrArg₂ List.cons rfl (congrArg₂ List.cons rfl (congrArg₂ List.cons rfl (ih (h d))))
      · simp only [hd, ite_false]
        rw [normP_inl, ite_eq_right_of_eq_false _ _ (eq_false hd), tableQueryLog_query_bind,
          tableQueryLog_query_bind]
        simp only [List.flatMap_cons, normQs, hd, ite_false, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append]
        exact congrArg₂ List.cons rfl (ih (h d))
    · simp only [normJ] at ih ⊢
      rw [addIV_inr, normP_inv, tableQueryLog_query_bind, tableQueryLog_query_bind]
      simp only [List.flatMap_cons, normQs, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      exact congrArg₂ List.cons rfl (ih _)
    · simp only [normJ] at ih ⊢
      rw [addIV_inr, normP_fwd, tableQueryLog_query_bind, tableQueryLog_query_bind]
      simp only [List.flatMap_cons, normQs, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      exact congrArg₂ List.cons rfl (ih _)

end Logs

end VoleMole.ROM.IC

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim
open VoleMole.ROM.IC.OMUF CTUFOpen CTUFPerm

/-! ## The permutation-model game reads the signers only on its signing log -/

section CongrP

variable {K qR : ℕ} (lr : Bool) (g : Table) (π : PTable)

/-- **The lifted Anchor reads its signer only at an accepted query.** -/
theorem liftP_anchor_congr (sk sk' : Fin K → Spec.Signer) (q : IssQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (anchorIC lr sk q)).2 = true →
      (sk' q.k).derivePreimage (toL q.t) = (sk q.k).derivePreimage (toL q.t)) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (liftP (anchorIC lr sk' q)) =
        evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (liftP (anchorIC lr sk q)) ∧
      tableQueryLog (liftP (anchorIC lr sk' q)) (joinP g π) =
        tableQueryLog (liftP (anchorIC lr sk q)) (joinP g π) := by
  have ha := anchorIC_congr lr (join g π.fwd) sk sk' q h
  rw [evalWithAnswerFn_liftP, evalWithAnswerFn_liftP, tableQueryLog_liftP, tableQueryLog_liftP,
    ha.1, ha.2]
  exact ⟨rfl, rfl⟩

variable {A : AdversaryP K qR}

/-- **The Issue rounds of the permutation model read the signers only at their accepted
queries.** -/
theorem runIssP_congr (sk sk' : Fin K → Spec.Signer) :
    ∀ (n : ℕ) (s : A.σ),
      (∀ p ∈ sigLog (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (runIssP lr sk A n s)).2,
        (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) →
      evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (runIssP lr sk' A n s) =
          evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (runIssP lr sk A n s) ∧
        tableQueryLog (runIssP lr sk' A n s) (joinP g π) =
          tableQueryLog (runIssP lr sk A n s) (joinP g π)
  | 0, s, _ => by simp [runIssP]
  | n + 1, s, h => by
    have ha := liftP_anchor_congr lr g π sk sk'
      (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).2 fun hb => h _ (by
        simp only [runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLog,
          evalWithAnswerFn_liftP]
        exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_cons_self, hb⟩, rfl⟩)
    have hr := runIssP_congr sk sk' n
      (A.absorb (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).1
        (evalWithAnswerFn (QueryImpl.ofFn (joinP g π))
          (liftP (anchorIC lr sk (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).2))).1)
      fun p hp => h p (by
        simp only [runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLog,
          List.filter_cons] at hp ⊢
        split_ifs <;> simp_all)
    simp only [runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
      tableQueryLog_pure, ha.1, ha.2, hr.1, hr.2, and_self]

variable (pk : Fin K → UovPk) (qI : ℕ) (A)

/-- **The permutation-model OMUF game reads the signers only at the accepted Issue queries.** -/
theorem gameP_congr (sk sk' : Fin K → Spec.Signer)
    (h : ∀ p ∈ sigLog (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUF.gameP lr pk sk qI A)).1,
      (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUF.gameP lr pk sk' qI A) =
        evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUF.gameP lr pk sk qI A) ∧
      tableQueryLog (OMUF.gameP lr pk sk' qI A) (joinP g π) =
        tableQueryLog (OMUF.gameP lr pk sk qI A) (joinP g π) := by
  have hr := runIssP_congr lr g π sk sk' qI (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) A.init)
    (by simpa only [OMUF.gameP, evalWithAnswerFn_bind, evalWithAnswerFn_map] using h)
  simp only [OMUF.gameP, evalWithAnswerFn_bind, evalWithAnswerFn_map, tableQueryLog_bind,
    tableQueryLog_map', hr.1, hr.2, and_self]

end CongrP

/-! ## The CT-UF^open forger of the permutation model -/

section ForgerP

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (qI : ℕ) (A : AdversaryP K qR)

/-- **The CT-UF^open forger `B₂` of the permutation model**: it runs the permutation-model OMUF
game and every extraction with the signers as its oracle, the permutation table `π` its common
randomness, and outputs `ctufOut` at the forward table. -/
noncomputable def ctufForgerP :
    CTForger Ans PTable K Spec.Bytes (Option Spec.Bytes) Spec.Bytes Opening where
  run σ π := ctufOut lr pk π.fwd <$> extAllP lr pk (skOf σ) qI A π
  reads σ σ' π g hs _ := by
    simp only [evalWithAnswerFn_map, ctufOut] at hs ⊢
    rw [extAllP_eval] at hs
    have hg0 := game_congr lr (join g π.fwd) (A := A.toIC lr π) pk qI (skOf σ) (skOf σ')
      fun p hp => hs p hp
    have hgP := gameP_congr lr g π A pk qI (skOf σ) (skOf σ') (by
      rw [gameP_eval]; exact fun p hp => hs p hp)
    have h1 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk (skOf σ') qI A j)) π.fwd) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk (skOf σ) qI A j)) π.fwd) := fun j =>
      gameA_congr _ _ π.fwd g
        (by simp only [nJ, evalWithAnswerFn_normJ, PIP, evalWithAnswerFn_map, hgP.1])
        (by simp only [nJ, PIP, normJ_map, tableQueryLog_map', tableQueryLog_normJ, hgP.2])
    have h2 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk (skOf σ') qI A j)) π.fwd) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk (skOf σ) qI A j)) π.fwd) := fun j =>
      gameA_congr _ _ π.fwd g
        (by simp only [nJ, evalWithAnswerFn_normJ, PRP, evalWithAnswerFn_map, hgP.1])
        (by simp only [nJ, PRP, normJ_map, tableQueryLog_map', tableQueryLog_normJ, hgP.2])
    rw [extAllP_eval, extAllP_eval, hg0.1]
    simp only [h1, h2]

variable (sk : Fin K → Spec.Signer)

/-- **Per table: a forgery, with every accepted issuance proof extracted, is a CT-UF^open win of
`ctufForgerP`** (`ctOpenWin_of_forge` in the permutation model). -/
theorem ctOpenWin_of_forgeP (g : Table) (π : PTable)
    (hI : ∀ j ∈ Finset.range qI, ¬BadI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd)))
    (hF : Forge lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π))) :
    CTOpenWin (verK pk) comO WFO
      (ctufOut lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π))) := by
  classical
  set E := π.fwd with hE
  set v := evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π) with hv
  obtain ⟨x, hx, hn⟩ := hF
  have hx' := hx
  obtain ⟨-, -, -, -, -, -, -, -, -, s, u, k, -, he, -⟩ := hx'
  have h : ∃ p : Fin K × Opening × Spec.Bytes, p.2.1 ∈ SR lr pk E v ∧
      comO p.2.1 ∉ (issL v.1).map (·.1) ∧ (pk p.1).toSpec.eval p.2.2 = comO p.2.1 :=
    ⟨(k, x, s), hx, hn, he⟩
  obtain ⟨hs1, hs2, hs3⟩ := Classical.choose_spec h
  refine ⟨⟨(Classical.choose h).1, (Classical.choose h).2.1, (Classical.choose h).2.2,
    by simp only [ctufOut]; unfold forgeOf; exact dite_eq_left h, wfo_of_SR lr pk hs1, hs3, ?_⟩, ?_⟩
  · intro q hq hqe
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLog hq
    refine hs2 (List.mem_map.2 ⟨(toL p.1.t, toL p.1.ctx), ?_, ?_⟩)
    · exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa using hb⟩, rfl⟩
    · exact hqe
  · intro q hq
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLog hq
    obtain ⟨hlI, -, -, -⟩ := game_eval g E lr pk sk (A.toIC lr π) qI
    have hv1 : v.1 = evalWithAnswerFn (QueryImpl.ofFn (join g E))
        (OMUF.game lr pk sk qI (A.toIC lr π)) := by
      rw [hv, extAllP_eval]
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    rw [hv1] at hj
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        (OMUF.game lr pk sk qI (A.toIC lr π))).1[j]? = some (p.1, true) := by
      rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_IP lr pk sk qI A g π hj'
    have hext : ExtI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) E)) := by
      by_contra hne
      exact hI j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
    obtain ⟨x, hx, hxc, -⟩ := opI_of_ext E lr hext
    have hxS : x ∈ SI lr E v := by
      refine ⟨j, p.1, _, ?_, ?_, hx⟩
      · rw [hv1]; exact hj'
      · rw [hv, extAllP_eval]; simp [hjl, hE]
    have h' : ∃ x ∈ SI lr E v, comO x = toL p.1.t := ⟨x, hxS, by rw [hxc, hst]⟩
    obtain ⟨hy1, hy2⟩ := Classical.choose_spec h'
    refine ⟨Classical.choose h', ?_, wfo_of_SI lr hy1, hy2⟩
    simp only [ctufOut, opensOf]
    exact List.mem_filterMap.2 ⟨(p.1.k, toL p.1.t), hq, by simp [h']⟩

/-- **The per-table core in the permutation model, with CT-UF^open**: a win means that some
accepted proof is not extracted, or `B₁` finds a `Com` collision, or `ctufForgerP` wins
CT-UF^open. -/
theorem win_imp_openP (g : Table) (π : PTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUF.gameP lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qR, BadR π.fwd lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) π.fwd))) ∨
    Coll lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π)) ∨
    CTOpenWin (verK pk) comO WFO
      (ctufOut lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π))) := by
  by_cases hI : ∃ j ∈ Finset.range qI, BadI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd))
  · exact Or.inl hI
  push Not at hI
  rcases win_impP lr pk sk qI A g π hwin with h | h | h | h
  · exact absurd h (by push Not; exact hI)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (ctOpenWin_of_forgeP lr pk qI A sk g π hI h)))

/-- **`ctufForgerP`'s CT-UF^open advantage** against the Anchors' signers is the probability of its
win in the reductions' run of the permutation model. -/
theorem advCTUFOpenAt_ctufForgerP :
    advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerP lr pk qI A) =
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        CTOpenWin (verK pk) comO WFO (ctufOut lr pk π.fwd v)] := by
  unfold advCTUFOpenAt semAdv
  refine prEvent_bind_congr_of_support _ _ _ fun π _ => ?_
  simp only [ctufForgerP, skOf_signers, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **Theorem 1 in the permutation model with `B₂`'s standalone CT-UF^open advantage,
simultaneous extraction events.** -/
theorem omuf_le_open_simP :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (OMUF.gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimIR lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerP lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForgerP]
  have h := prEvent_bind_le_sum4_of_table ($ᵗ PTable) (fun π => runP π (OMUF.gameP lr pk sk qI A))
    (fun _ r => Win r) {0} ∅ (fun _ π => extAllP lr pk sk qI A π)
    (fun π v => SimIR lr pk π.fwd v) (fun _ π => extAllP lr pk sk qI A π) (fun _ _ => False)
    (fun π => extAllP lr pk sk qI A π) (fun π v => Coll lr pk π.fwd v)
    (fun π v => CTOpenWin (verK pk) comO WFO (ctufOut lr pk π.fwd v)) fun π g hw => by
      rw [evalWithAnswerFn_runP] at hw
      rcases win_imp_openP lr pk qI A sk g π hw with ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton, Finset.sum_empty, add_zero] using h

variable {q : Kind → ℕ} {qE n : ℕ}

/-- **Theorem 1 with simultaneous extraction, AES as random permutations, with
`Adv^{ct-uf-open}_K(ctufForgerP)`.** -/
theorem omuf_le_num_open_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (OMUF.gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      epsIRsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerP lr pk qI A) :=
  (omuf_le_open_simP lr pk qI A sk).trans (add_le_add (add_le_add
    (prEvent_simIR_leP hA hdig hdinj) le_rfl) le_rfl)

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T Z S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [DecidableEq Z] [Inhabited T]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] [Fintype Xc]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) {qf qi qS : ℕ}

/-- **Theorem 1 down to OMPR with AES and `Com` both random permutations with inverse queries**
(simultaneous extraction). `hmodelP` is **the modelling step, a hypothesis**, as in
`omuf_le_num_ompr_perm`, for the forger `ctufForgerP` of the permutation model of AES:

    Pr[Win] ≤ εIR^simP(q', q'_E, n', qI, qR) + Pr[Coll]
              + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
              + permEps(q_f + q_i + q_S + 1, q_i, |Xc|, |T × Z|),

`n = (q_f + q_S + 1) + 2q_S + 1`. -/
theorem omuf_le_num_ompr_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) {emb : Xc → T × Z}
    (hemb : Function.Injective emb)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CPBudget qf qi qS f)
    (hmodelP : advCTUFOpenAt (verK pk) comO WFO
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerP lr pk qI A) ≤
      advCTUFPermAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) emb F) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (OMUF.gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      epsIRsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      (∑ j : Fin K, (advOMPR (tr.atKey (ks j)) ((qf + qS + 1) + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> permRed emb F) +
        (((qf + qS + 1) + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) +
        permEps (qf + qi + qS + 1) qi (Fintype.card Xc) (Fintype.card (T × Z))) :=
  (omuf_le_num_open_simP lr pk qI A sk hA hdig hdinj).trans
    (add_le_add le_rfl (hmodelP.trans (advCTUFPermAt_le_ompr tr ks hemb F hF)))

end ForgerP

end VoleMole.Assumptions.UOV.Links
