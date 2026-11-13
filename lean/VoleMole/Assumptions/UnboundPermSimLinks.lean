import VoleMole.Assumptions.PermSimLinks
import VoleMole.ROM.MoussakaUnboundOMUFSimPerm

/-!
# Unbound Moussaka down to OMPR with AES and `Com ∪ UCom` random permutations

`ROM/MoussakaUnboundOMUFSimPerm.lean` (`omufU_le_num_simP`: AES as random permutations, the
adversary with forward and inverse cipher queries, simultaneous extraction) with its forgery term
made the standalone CT-UF^open advantage (over `Com ∪ UCom`, as in `Assumptions/UnboundLinks.lean`)
of an explicit forger, and then `Assumptions/PermLinks.lean`'s permutation model of `Com`
(`advCTUFPermAt_le_ompr`), as `Assumptions/PermSimLinks.lean` does for Moussaka.

* `tableQueryLog_normP`: the log of a normalized computation is a function of the original's
  (`tableQueryLog_normJ` without the added `iv` queries; the bound issuance provers run through
  `normP`).
* `gameUP_congr`: the permutation-model OMUF-U game reads the signers only at its accepted Issue
  queries (`runIssUP_congr`, `liftP_anchorU_congr`).
* **The forger** `ctufForgerUP lr pk qI A`: a CT-UF^open forger over `Com ∪ UCom` whose common
  randomness is the permutation table `π`; it runs the permutation-model game and every
  extraction (`OMUFU.extAllP`) and outputs `ctufOutU` at the forward table.
* `ctOpenWin_of_forgeUP`, `win_imp_openUP`: per table, a win is an extraction failure, a
  collision of `Com ∪ UCom` or a CT-UF^open win of `ctufForgerUP`.
* `omufU_le_open_simP`, `omufU_le_num_open_simP`, **`omufU_le_num_ompr_simP`**:

      Pr[Win] ≤ εI^simP + εU^simP + Pr[Coll]
                + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j}) + permEps,

  under the modelling hypothesis `hmodelP` for `ctufForgerUP` (as in `omufU_le_num_ompr_perm`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM

/-! ## The log of a normalized computation -/

section Logs

variable {α : Type}

/-- The queries of the PRF view that the normalization makes for one query of the permutation
model. -/
def normQsP (p : Params) (π : PTable) : DomP → List DomIC
  | .inl d => if d.1 = .h21 then [.inl (.h4, ivIn p d.2), .inl d] else [.inl d]
  | .inr (true, c) => [.inr c]
  | .inr (false, c) => [.inr (c.1, (π c.1).symm c.2)]

/-- **The log of a normalized computation** is a function of the original's log. -/
theorem tableQueryLog_normP (p : Params) (h : Table) (π : PTable) (P : OracleComp specP α) :
    tableQueryLog (normP p π P) (join h π.fwd) =
      (tableQueryLog P (joinP h π)).flatMap fun e =>
        (normQsP p π e.1).map fun t => ⟨t, join h π.fwd t⟩ := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with d | ⟨_ | _, c⟩
    · by_cases hd : d.1 = .h21
      · rw [normP_inl, ite_eq_left_of_eq_true _ _ (eq_true hd), tableQueryLog_query_bind,
          tableQueryLog_query_bind, tableQueryLog_query_bind]
        simp only [List.flatMap_cons, normQsP, hd, ite_true, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append]
        exact congrArg₂ List.cons rfl (congrArg₂ List.cons rfl (ih (h d)))
      · rw [normP_inl, ite_eq_right_of_eq_false _ _ (eq_false hd), tableQueryLog_query_bind,
          tableQueryLog_query_bind]
        simp only [List.flatMap_cons, normQsP, hd, ite_false, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append]
        exact congrArg₂ List.cons rfl (ih (h d))
    · rw [normP_inv, tableQueryLog_query_bind, tableQueryLog_query_bind]
      simp only [List.flatMap_cons, normQsP, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      exact congrArg₂ List.cons rfl (ih _)
    · rw [normP_fwd, tableQueryLog_query_bind, tableQueryLog_query_bind]
      simp only [List.flatMap_cons, normQsP, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      exact congrArg₂ List.cons rfl (ih _)

end Logs

end VoleMole.ROM.IC

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim
open CTUFOpen CTUFPerm

section UnboundP

open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU

attribute [local irreducible] Spec.Moussaka.com Spec.MoussakaUnbound.ucom
  Spec.MoussakaUnbound.derive

variable {K qR : ℕ}

/-! ## The permutation-model OMUF-U game reads the signers only on its signing log -/

section CongrP

variable (lr : Bool) (g : Table) (π : PTable)

/-- **The lifted Anchor of either variant reads its signer only at an accepted query.** -/
theorem liftP_anchorU_congr (sk sk' : Fin K → Spec.Signer) (q : IQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (anchorU lr sk q)).2 = true →
      (sk' q.q.k).derivePreimage (toL q.q.t) = (sk q.q.k).derivePreimage (toL q.q.t)) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (liftP (anchorU lr sk' q)) =
        evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (liftP (anchorU lr sk q)) ∧
      tableQueryLog (liftP (anchorU lr sk' q)) (joinP g π) =
        tableQueryLog (liftP (anchorU lr sk q)) (joinP g π) := by
  have ha := anchorU_congr lr (join g π.fwd) sk sk' q h
  rw [evalWithAnswerFn_liftP, evalWithAnswerFn_liftP, tableQueryLog_liftP, tableQueryLog_liftP,
    ha.1, ha.2]
  exact ⟨rfl, rfl⟩

variable {A : OMUFU.AdversaryP K qR}

/-- **The Issue rounds of the permutation model read the signers only at their accepted
queries.** -/
theorem runIssUP_congr (sk sk' : Fin K → Spec.Signer) :
    ∀ (n : ℕ) (s : A.σ),
      (∀ p ∈ sigLogU (evalWithAnswerFn (QueryImpl.ofFn (joinP g π))
          (OMUFU.runIssP lr sk A n s)).2,
        (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) →
      evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUFU.runIssP lr sk' A n s) =
          evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUFU.runIssP lr sk A n s) ∧
        tableQueryLog (OMUFU.runIssP lr sk' A n s) (joinP g π) =
          tableQueryLog (OMUFU.runIssP lr sk A n s) (joinP g π)
  | 0, s, _ => by simp [OMUFU.runIssP]
  | n + 1, s, h => by
    have ha := liftP_anchorU_congr lr g π sk sk'
      (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).2 fun hb => h _ (by
        simp only [OMUFU.runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLogU,
          evalWithAnswerFn_liftP]
        exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_cons_self, hb⟩, rfl⟩)
    have hr := runIssUP_congr sk sk' n
      (A.absorb (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).1
        (evalWithAnswerFn (QueryImpl.ofFn (joinP g π))
          (liftP (anchorU lr sk (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.query s)).2))).1)
      fun p hp => h p (by
        simp only [OMUFU.runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLogU,
          List.filter_cons] at hp ⊢
        split_ifs <;> simp_all)
    simp only [OMUFU.runIssP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
      tableQueryLog_pure, ha.1, ha.2, hr.1, hr.2, and_self]

variable (pk : Fin K → UovPk) (qI : ℕ) (A)

/-- **The permutation-model OMUF-U game reads the signers only at the accepted Issue
queries.** -/
theorem gameUP_congr (sk sk' : Fin K → Spec.Signer)
    (h : ∀ p ∈ sigLogU (evalWithAnswerFn (QueryImpl.ofFn (joinP g π))
        (OMUFU.gameP lr pk sk qI A)).1,
      (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUFU.gameP lr pk sk' qI A) =
        evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (OMUFU.gameP lr pk sk qI A) ∧
      tableQueryLog (OMUFU.gameP lr pk sk' qI A) (joinP g π) =
        tableQueryLog (OMUFU.gameP lr pk sk qI A) (joinP g π) := by
  have hr := runIssUP_congr lr g π sk sk' qI
    (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) A.init)
    (by simpa only [OMUFU.gameP, evalWithAnswerFn_bind, evalWithAnswerFn_map] using h)
  simp only [OMUFU.gameP, evalWithAnswerFn_bind, evalWithAnswerFn_map, tableQueryLog_bind,
    tableQueryLog_map', hr.1, hr.2, and_self]

end CongrP

/-! ## The CT-UF^open forger of the permutation model -/

section ForgerP

variable (lr : Bool) (pk : Fin K → UovPk) (qI : ℕ) (A : OMUFU.AdversaryP K qR)

/-- **The CT-UF^open forger `B₂` over `Com ∪ UCom` of the permutation model**: it runs the
permutation-model OMUF-U game and every extraction with the signers as its oracle, the
permutation table `π` its common randomness, and outputs `ctufOutU` at the forward table. -/
noncomputable def ctufForgerUP :
    CTForger Ans PTable K Spec.Bytes (Option Spec.Bytes) Spec.Bytes XOp where
  run σ π := ctufOutU lr pk π.fwd <$> OMUFU.extAllP lr pk (skOf σ) qI A π
  reads σ σ' π g hs _ := by
    simp only [evalWithAnswerFn_map, ctufOutU] at hs ⊢
    rw [OMUFU.extAllP_eval] at hs
    have hg0 := gameU_congr lr (join g π.fwd) (A.toIC lr π) pk qI (skOf σ) (skOf σ')
      fun p hp => hs p hp
    have hgP := gameUP_congr lr g π A pk qI (skOf σ) (skOf σ') (by
      rw [OMUFU.gameP_eval]; exact fun p hp => hs p hp)
    have h1 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk (skOf σ') qI A j)) π.fwd) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk (skOf σ) qI A j)) π.fwd) := fun j =>
      gameA_congr _ _ π.fwd g
        (by simp only [nB, evalWithAnswerFn_normP, PBIP, evalWithAnswerFn_map, hgP.1])
        (by simp only [nB, PBIP, normP_map, tableQueryLog_map', tableQueryLog_normP, hgP.2])
    have h2 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk (skOf σ') qI A j)) π.fwd) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk (skOf σ) qI A j)) π.fwd) :=
      fun j => gameA_congr _ _ π.fwd g
        (by simp only [nU, evalWithAnswerFn_normJ, PUIP, evalWithAnswerFn_map, hgP.1])
        (by simp only [nU, PUIP, normJ_map, tableQueryLog_map', tableQueryLog_normJ, hgP.2])
    have h3 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk (skOf σ') qI A j)) π.fwd) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk (skOf σ) qI A j)) π.fwd) :=
      fun j => gameA_congr _ _ π.fwd g
        (by simp only [nU, evalWithAnswerFn_normJ, PURP, evalWithAnswerFn_map, hgP.1])
        (by simp only [nU, PURP, normJ_map, tableQueryLog_map', tableQueryLog_normJ, hgP.2])
    rw [OMUFU.extAllP_eval, OMUFU.extAllP_eval, hg0.1]
    simp only [h1, h2, h3]

variable (sk : Fin K → Spec.Signer)

/-- **Per table: a forgery, with every accepted issuance proof of either variant extracted, is a
CT-UF^open win of `ctufForgerUP`** (`ctOpenWin_of_forgeU` in the permutation model). -/
theorem ctOpenWin_of_forgeUP (g : Table) (π : PTable)
    (hB : ∀ j ∈ Finset.range qI, ¬BadBI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd)))
    (hU : ∀ j ∈ Finset.range qI, ¬BadUI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd)))
    (hF : OMUFU.Forge lr pk π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAllP lr pk sk qI A π))) :
    CTOpenWin (verK pk) comX WFX
      (ctufOutU lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g)
        (OMUFU.extAllP lr pk sk qI A π))) := by
  classical
  set E := π.fwd with hE
  set v := evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAllP lr pk sk qI A π) with hv
  obtain ⟨y, hy, hn⟩ := hF
  have hy' := hy
  obtain ⟨-, -, -, -, -, -, -, -, s, u, k, -, he, -⟩ := hy'
  have h : ∃ p : Fin K × UOpening × Spec.Bytes, p.2.1 ∈ SUR lr pk E v ∧
      ucomO p.2.1 ∉ sigT v.1 ∧ (pk p.1).toSpec.eval p.2.2 = ucomO p.2.1 :=
    ⟨(k, y, s), hy, hn, he⟩
  obtain ⟨hs1, hs2, hs3⟩ := Classical.choose_spec h
  have hv1 : v.1 = evalWithAnswerFn (QueryImpl.ofFn (join g E))
      (OMUFU.game lr pk sk qI (A.toIC lr π)) := by
    rw [hv, OMUFU.extAllP_eval]
  refine ⟨⟨(Classical.choose h).1, .inr (Classical.choose h).2.1, (Classical.choose h).2.2,
    by simp only [ctufOutU]; unfold forgeOfU; exact dite_eq_left h, ?_, ?_, ?_⟩, ?_⟩
  · rcases hs1 with ⟨j, rq, r, h1, h2, hxo⟩
    exact hxo.1
  · show (pk _).toSpec.eval _ = comX (Sum.inr _)
    rw [hs3]; simp only [comX, Sum.elim_inr]
  · intro q hq hqe
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLogU hq
    have e : comX (Sum.inr (Classical.choose h).2.1) = ucomO (Classical.choose h).2.1 := by
      simp only [comX, Sum.elim_inr]
    refine hs2 ?_
    rw [← e, ← hqe]
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, hb⟩, rfl⟩
  · intro q hq
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLogU hq
    obtain ⟨hlI, -, -, -⟩ := OMUFU.game_eval g E lr pk sk (A.toIC lr π) qI
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    rw [hv1] at hj
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hex : ∃ x ∈ SIX lr E v, comX x = toL p.1.q.t := by
      rcases p with ⟨p | p, b⟩
      · have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E))
            (OMUFU.game lr pk sk qI (A.toIC lr π))).1[j]? = some (.inl p, true) := by
          rw [hj]; simp_all
        obtain ⟨hacc, hst⟩ := accepted_BIP lr pk sk qI A g π hj'
        have hext : ExtBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) E)) := by
          by_contra hne
          exact hB j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
        obtain ⟨x, hx, hxc, -⟩ := opBI_of_ext E lr hext
        refine ⟨.inl x, Or.inl ⟨x, ⟨j, p, _, ?_, ?_, hx⟩, rfl⟩, ?_⟩
        · rw [hv1]; exact hj'
        · rw [hv, OMUFU.extAllP_eval]; simp [hjl, hE]
        · simp only [comX, Sum.elim_inl, IQ.q]; rw [hxc, hst]; rfl
      · have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E))
            (OMUFU.game lr pk sk qI (A.toIC lr π))).1[j]? = some (.inr p, true) := by
          rw [hj]; simp_all
        obtain ⟨hacc, hst⟩ := accepted_UIP lr pk sk qI A g π hj'
        have hext : ExtUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) E)) := by
          by_contra hne
          exact hU j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
        obtain ⟨y, hy, hyc, -⟩ := opUI_of_ext E lr hext
        refine ⟨.inr y, Or.inr ⟨y, ⟨j, p, _, ?_, ?_, hy⟩, rfl⟩, ?_⟩
        · rw [hv1]; exact hj'
        · rw [hv, OMUFU.extAllP_eval]; simp [hjl, hE]
        · simp only [comX, Sum.elim_inr, IQ.q]; rw [hyc, hst]; rfl
    obtain ⟨hy1, hy2⟩ := Classical.choose_spec hex
    refine ⟨Classical.choose hex, ?_, wfx_of_SIX lr hy1, hy2⟩
    simp only [ctufOutU, opensOfU]
    exact List.mem_filterMap.2 ⟨(p.1.q.k, toL p.1.q.t), hq, by simp [hex]⟩

/-- **The per-table core of Theorem U1 in the permutation model with CT-UF^open**: a win means
that some accepted proof is not extracted, or `B₁` finds a collision of `Com ∪ UCom`, or
`ctufForgerUP` wins CT-UF^open over the union domain. -/
theorem win_imp_openUP (g : Table) (π : PTable)
    (hwin : OMUFU.Win (evalWithAnswerFn (QueryImpl.ofFn (joinP g π))
      (OMUFU.gameP lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadBI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qI, BadUI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qR, BadUR π.fwd lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) π.fwd))) ∨
    OMUFU.Coll lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAllP lr pk sk qI A π)) ∨
    CTOpenWin (verK pk) comX WFX (ctufOutU lr pk π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAllP lr pk sk qI A π))) := by
  by_cases hB : ∃ j ∈ Finset.range qI, BadBI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd))
  · exact Or.inl hB
  by_cases hU : ∃ j ∈ Finset.range qI, BadUI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd))
  · exact Or.inr (Or.inl hU)
  push Not at hB hU
  rcases OMUFU.win_impP lr pk sk qI A g π hwin with h | h | h | h | h
  · exact absurd h (by push Not; exact hB)
  · exact absurd h (by push Not; exact hU)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (ctOpenWin_of_forgeUP lr pk qI A sk g π hB hU h))))

/-- **`ctufForgerUP`'s CT-UF^open advantage** against the Anchors' signers is the probability of
its win in the reductions' run of the permutation model. -/
theorem advCTUFOpenAt_ctufForgerUP :
    advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerUP lr pk qI A) =
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
          (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[
        CTOpenWin (verK pk) comX WFX (ctufOutU lr pk π.fwd v)] := by
  unfold advCTUFOpenAt semAdv
  refine prEvent_bind_congr_of_support _ _ _ fun π _ => ?_
  simp only [ctufForgerUP, skOf_signers, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **Theorem U1 in the permutation model with `ctufForgerUP`'s standalone CT-UF^open advantage,
simultaneous extraction events.** -/
theorem omufU_le_open_simP :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (runP π (OMUFU.gameP lr pk sk qI A))).run' ∅}[OMUFU.Win r] ≤
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
        (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[SimBI lr π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
        (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[SimU lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
        (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[OMUFU.Coll lr pk π.fwd v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerUP lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForgerUP]
  have h := prEvent_bind_le_sum4_of_table ($ᵗ PTable)
    (fun π => runP π (OMUFU.gameP lr pk sk qI A))
    (fun _ r => OMUFU.Win r) {0} {0} (fun _ π => OMUFU.extAllP lr pk sk qI A π)
    (fun π v => SimBI lr π.fwd v) (fun _ π => OMUFU.extAllP lr pk sk qI A π)
    (fun π v => SimU lr pk π.fwd v) (fun π => OMUFU.extAllP lr pk sk qI A π)
    (fun π v => OMUFU.Coll lr pk π.fwd v)
    (fun π v => CTOpenWin (verK pk) comX WFX (ctufOutU lr pk π.fwd v)) fun π g hw => by
      rw [evalWithAnswerFn_runP] at hw
      rcases win_imp_openUP lr pk qI A sk g π hw with
        ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [OMUFU.extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [OMUFU.extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [OMUFU.extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

variable {q : Kind → ℕ} {qE n : ℕ}

/-- **Theorem U1 with simultaneous extraction, AES as random permutations, with
`Adv^{ct-uf-open}_K(ctufForgerUP)` over `Com ∪ UCom`.** -/
theorem omufU_le_num_open_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (runP π (OMUFU.gameP lr pk sk qI A))).run' ∅}[OMUFU.Win r] ≤
      epsIsimP (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsimP (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
        (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[OMUFU.Coll lr pk π.fwd v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerUP lr pk qI A) :=
  (omufU_le_open_simP lr pk qI A sk).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_leP hA) (prEvent_simU_leP hA hdig hdinj)) le_rfl) le_rfl)

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T Z S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [DecidableEq Z] [Inhabited T]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] [Fintype Xc]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) {qf qi qS : ℕ}

/-- **Theorem U1 down to OMPR with AES and `Com ∪ UCom` random permutations with inverse
queries** (simultaneous extraction). `hmodelP` is **the modelling step, a hypothesis**, as in
`omufU_le_num_ompr_perm`, for the forger `ctufForgerUP` of the permutation model of AES:

    Pr[Win] ≤ εI^simP + εU^simP + Pr[Coll]
              + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
              + permEps(q_f + q_i + q_S + 1, q_i, |Xc|, |T × Z|),

`n = (q_f + q_S + 1) + 2q_S + 1`. -/
theorem omufU_le_num_ompr_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) {emb : Xc → T × Z}
    (hemb : Function.Injective emb)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CPBudget qf qi qS f)
    (hmodelP : advCTUFOpenAt (verK pk) comX WFX
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerUP lr pk qI A) ≤
      advCTUFPermAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) emb F) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (runP π (OMUFU.gameP lr pk sk qI A))).run' ∅}[OMUFU.Win r] ≤
      epsIsimP (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsimP (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle
        (OMUFU.extAllP lr pk sk qI A π)).run' ∅}[OMUFU.Coll lr pk π.fwd v] +
      (∑ j : Fin K, (advOMPR (tr.atKey (ks j)) ((qf + qS + 1) + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> permRed emb F) +
        (((qf + qS + 1) + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) +
        permEps (qf + qi + qS + 1) qi (Fintype.card Xc) (Fintype.card (T × Z))) :=
  (omufU_le_num_open_simP lr pk qI A sk hA hdig hdinj).trans
    (add_le_add le_rfl (hmodelP.trans (advCTUFPermAt_le_ompr tr ks hemb F hF)))

end ForgerP

end UnboundP

end VoleMole.Assumptions.UOV.Links
