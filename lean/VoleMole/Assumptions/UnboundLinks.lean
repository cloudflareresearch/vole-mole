import VoleMole.Assumptions.UOVLinks
import VoleMole.ROM.MoussakaUnboundOMUFSim

/-!
# Unbound Moussaka Theorem U1: the UOV term as a CT-UF^open advantage, and down to OMPR

`Assumptions/UOVLinks.lean` and `Assumptions/SimLinks.lean` for the unbound game
(`ROM/MoussakaUnboundOMUF.lean`, `moussaka-unbound.md` §3.3, §4). The CT-UF^open game is the one
of `Assumptions/UOV.lean` over the **union domain**: openings are inputs of `Com ∪ UCom`
(`OMUFU.XOp`), `Com` is `OMUFU.comX` (`KP800(·)[0..45)` on either input space), the domain is
`OMUFU.WFX`.

* `ctufForgerU` (`B₂`): runs the OMUF-U game and every extraction with the signers as its oracle
  (`reads`: its output depends on them only at the accepted Issue queries `(k, t)` of either
  variant, its signing log, `game_congr`), and outputs the forgery of `OMUFU.Forge` and, for every
  signed target, an extracted issuance input: a `Com` input for a bound issuance, a `UCom` input
  for an unbound one. If an accepted issuance proof is not extracted an opening may be missing;
  that case is already a term of the bound (`BadBI`, `BadUI`), so nothing is added
  (`win_imp_open`).
* `omufU_le_open`, `omufU_le_num_open`: Theorem U1 with `Adv^{ct-uf-open}_K(B₂)`.
* **`omufU_le_num_ompr`**: under the modelling hypothesis `hmodel` (`B₂`'s CT-UF^open advantage
  with the concrete `Com ∪ UCom` is at most the ideal-`Com` advantage of some forger `F` within a
  budget; not provable, since `Com` and `UCom` are fixed functions; the same step as
  `omuf_le_num_ompr`, with `Com` ideal in the standalone game only), the term is at most
  `Σ_j (Adv^{ompr}_{key j} + (q_f + 2q_S + 1)·failPr_{key j})` (`advCTUFIdealAt_le_ompr`).
* With simultaneous extraction: `omufU_le_open_sim`, `omufU_le_num_open_sim`,
  **`omufU_le_num_ompr_sim`**.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim

section Unbound

open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU

attribute [local irreducible] Spec.Moussaka.com Spec.MoussakaUnbound.ucom
  Spec.MoussakaUnbound.derive

variable {K qR : ℕ}

/-- **The signing log of an OMUF-U Issue record list**: the accepted queries' `(k, t)`, of either
variant (the Anchor calls its signer exactly on these, `anchorU`). -/
def sigLogU (l : List (IQ K × Bool)) : List (Fin K × Spec.Bytes) :=
  (l.filter (·.2)).map fun p => (p.1.q.k, toL p.1.q.t)

section Congr

variable (lr : Bool) (f : (d : DomIC) → AnsIC d)

/-- **The unbound Anchor reads its signer only at an accepted query.** -/
theorem uanchorIC_congr (sk sk' : Fin K → Spec.Signer) (q : IssQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn f) (uanchorIC lr sk q)).2 = true →
      (sk' q.k).derivePreimage (toL q.t) = (sk q.k).derivePreimage (toL q.t)) :
    evalWithAnswerFn (QueryImpl.ofFn f) (uanchorIC lr sk' q) =
        evalWithAnswerFn (QueryImpl.ofFn f) (uanchorIC lr sk q) ∧
      tableQueryLog (uanchorIC lr sk' q) f = tableQueryLog (uanchorIC lr sk q) f := by
  unfold uanchorIC at h ⊢
  by_cases hw : uWFI lr q
  · simp only [hw, ite_true, evalWithAnswerFn_map, tableQueryLog_map', and_true] at h ⊢
    by_cases ha : (evalWithAnswerFn (QueryImpl.ofFn f)
        (verifyIC CrtGen.tables (ustmtI lr q) q.pf)).accept = true
    · simp only [ha, ite_true] at h ⊢
      rw [h trivial]
    · simp [ha]
  · simp [hw]

/-- **The Anchor of either variant reads its signer only at an accepted query.** -/
theorem anchorU_congr (sk sk' : Fin K → Spec.Signer) (q : IQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn f) (anchorU lr sk q)).2 = true →
      (sk' q.q.k).derivePreimage (toL q.q.t) = (sk q.q.k).derivePreimage (toL q.q.t)) :
    evalWithAnswerFn (QueryImpl.ofFn f) (anchorU lr sk' q) =
        evalWithAnswerFn (QueryImpl.ofFn f) (anchorU lr sk q) ∧
      tableQueryLog (anchorU lr sk' q) f = tableQueryLog (anchorU lr sk q) f := by
  rcases q with q | q
  · exact anchorIC_congr lr f sk sk' q h
  · exact uanchorIC_congr lr f sk sk' q h

variable {A : OMUFU.Adversary K qR}

/-- **The Issue rounds read the signers only at their accepted queries.** -/
theorem runIssU_congr (sk sk' : Fin K → Spec.Signer) :
    ∀ (n : ℕ) (s : A.σ),
      (∀ p ∈ sigLogU (evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.runIss lr sk A n s)).2,
        (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) →
      evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.runIss lr sk' A n s) =
          evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.runIss lr sk A n s) ∧
        tableQueryLog (OMUFU.runIss lr sk' A n s) f = tableQueryLog (OMUFU.runIss lr sk A n s) f
  | 0, s, _ => by simp [OMUFU.runIss]
  | n + 1, s, h => by
    have ha := anchorU_congr lr f sk sk'
      (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).2 fun hb => h _ (by
        simp only [OMUFU.runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLogU]
        exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_cons_self, hb⟩, rfl⟩)
    have hr := runIssU_congr sk sk' n (A.absorb (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).1
      (evalWithAnswerFn (QueryImpl.ofFn f)
        (anchorU lr sk (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).2)).1) fun p hp => h p (by
        simp only [OMUFU.runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLogU,
          List.filter_cons] at hp ⊢
        split_ifs <;> simp_all)
    simp only [OMUFU.runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
      tableQueryLog_pure, ha.1, ha.2, hr.1, hr.2, and_self]

variable (pk : Fin K → UovPk) (qI : ℕ) (A)

/-- **The OMUF-U game reads the signers only at the accepted Issue queries.** -/
theorem gameU_congr (sk sk' : Fin K → Spec.Signer)
    (h : ∀ p ∈ sigLogU (evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.game lr pk sk qI A)).1,
      (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) :
    evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.game lr pk sk' qI A) =
        evalWithAnswerFn (QueryImpl.ofFn f) (OMUFU.game lr pk sk qI A) ∧
      tableQueryLog (OMUFU.game lr pk sk' qI A) f = tableQueryLog (OMUFU.game lr pk sk qI A) f := by
  have hr := runIssU_congr lr f sk sk' qI (evalWithAnswerFn (QueryImpl.ofFn f) A.init) (by
    simpa only [OMUFU.game, evalWithAnswerFn_bind, evalWithAnswerFn_map] using h)
  simp only [OMUFU.game, evalWithAnswerFn_bind, evalWithAnswerFn_map, tableQueryLog_bind,
    tableQueryLog_map', hr.1, hr.2, and_self]

end Congr

section Forger

variable (lr : Bool) (pk : Fin K → UovPk) (qI : ℕ) (A : OMUFU.Adversary K qR)

/-- The inputs extracted from the accepted issuance proofs of either variant. -/
def SIX (E : CTable) (v : OMUFU.View K) : Set XOp :=
  Sum.inl '' SBI lr E v ∪ Sum.inr '' SUI lr E v

open Classical in
/-- `B₂`'s forgery: an extracted redemption input `y` with an honest key `k` and a preimage `s`,
`P_k(s) = UCom(y)`, whose commitment was never signed (`OMUFU.Forge`), if there is one. -/
noncomputable def forgeOfU (E : CTable) (v : OMUFU.View K) : Option (Fin K × XOp × Spec.Bytes) :=
  if h : ∃ p : Fin K × UOpening × Spec.Bytes, p.2.1 ∈ SUR lr pk E v ∧
      ucomO p.2.1 ∉ sigT v.1 ∧ (pk p.1).toSpec.eval p.2.2 = ucomO p.2.1
  then some ((Classical.choose h).1, .inr (Classical.choose h).2.1, (Classical.choose h).2.2)
  else none

open Classical in
/-- `B₂`'s openings: for every signed target, an extracted issuance input of it, if there is
one. -/
noncomputable def opensOfU (E : CTable) (v : OMUFU.View K) : List XOp :=
  (sigLogU v.1.1).filterMap fun q =>
    if h : ∃ x ∈ SIX lr E v, comX x = q.2 then some (Classical.choose h) else none

/-- `B₂`'s output from the view. -/
noncomputable def ctufOutU (E : CTable) (v : OMUFU.View K) :
    CTOut K Spec.Bytes XOp × List (Fin K × Spec.Bytes) × List (Fin K × Spec.Bytes) :=
  ((forgeOfU lr pk E v, opensOfU lr E v), sigLogU v.1.1, [])

/-- **The CT-UF^open forger `B₂` over `Com ∪ UCom`**: it runs the OMUF-U game and every
extraction with the signers as its oracle, and outputs `ctufOutU`. Its signing log is the
accepted Issue queries `(k, t)` of either variant. -/
noncomputable def ctufForgerU :
    CTForger Ans CTable K Spec.Bytes (Option Spec.Bytes) Spec.Bytes XOp where
  run σ E := ctufOutU lr pk E <$> OMUFU.extAll lr pk (skOf σ) qI A E
  reads σ σ' E g hs _ := by
    simp only [evalWithAnswerFn_map, ctufOutU] at hs ⊢
    rw [OMUFU.extAll_eval] at hs
    have hg := gameU_congr lr (join g E) A pk qI (skOf σ) (skOf σ') fun p hp => hs p hp
    have h1 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk (skOf σ') qI A j) E) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (PBI lr pk (skOf σ) qI A j) E) := fun j =>
      gameA_congr _ _ E g (by simp only [PBI, evalWithAnswerFn_map, hg.1])
        (by simp only [PBI, tableQueryLog_map', hg.2])
    have h2 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk (skOf σ') qI A j) E) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUI lr) (PUI lr pk (skOf σ) qI A j) E) := fun j =>
      gameA_congr _ _ E g (by simp only [PUI, evalWithAnswerFn_map, hg.1])
        (by simp only [PUI, tableQueryLog_map', hg.2])
    have h3 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk (skOf σ') qI A j) E) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUR lr pk) (PUR lr pk (skOf σ) qI A j) E) := fun j =>
      gameA_congr _ _ E g (by simp only [PUR, evalWithAnswerFn_map, hg.1])
        (by simp only [PUR, tableQueryLog_map', hg.2])
    rw [OMUFU.extAll_eval, OMUFU.extAll_eval, hg.1]
    simp only [h1, h2, h3]

end Forger

section Win

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  (A : OMUFU.Adversary K qR)

theorem mem_sigLogU {l : List (IQ K × Bool)} {q : Fin K × Spec.Bytes} (hq : q ∈ sigLogU l) :
    ∃ p ∈ l, p.2 = true ∧ q = (p.1.q.k, toL p.1.q.t) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  obtain ⟨hp, hb⟩ := List.mem_filter.1 hp
  exact ⟨p, hp, by simpa using hb, rfl⟩

theorem wfx_of_SIX {E : CTable} {v : OMUFU.View K} {x : XOp} (hx : x ∈ SIX lr E v) : WFX x := by
  rcases hx with ⟨x, ⟨j, q, r, -, -, hxo⟩, rfl⟩ | ⟨y, ⟨j, q, r, -, -, hyo⟩, rfl⟩
  · exact hxo.1
  · exact hyo.1

/-- **Per table: a forgery, with every accepted issuance proof of either variant extracted, is a
CT-UF^open win of `B₂` over `Com ∪ UCom`.** -/
theorem ctOpenWin_of_forgeU (g : Table) (E : CTable)
    (hB : ∀ j ∈ Finset.range qI, ¬BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)))
    (hU : ∀ j ∈ Finset.range qI, ¬BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)))
    (hF : OMUFU.Forge lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E))) :
    CTOpenWin (verK pk) comX WFX
      (ctufOutU lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E))) := by
  classical
  set v := evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E) with hv
  obtain ⟨y, hy, hn⟩ := hF
  have hy' := hy
  obtain ⟨-, -, -, -, -, -, -, -, s, u, k, -, he, -⟩ := hy'
  have h : ∃ p : Fin K × UOpening × Spec.Bytes, p.2.1 ∈ SUR lr pk E v ∧
      ucomO p.2.1 ∉ sigT v.1 ∧ (pk p.1).toSpec.eval p.2.2 = ucomO p.2.1 :=
    ⟨(k, y, s), hy, hn, he⟩
  obtain ⟨hs1, hs2, hs3⟩ := Classical.choose_spec h
  have hv1 : v.1 = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUFU.game lr pk sk qI A) := by
    rw [hv, OMUFU.extAll_eval]
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
    obtain ⟨hlI, -, -, -⟩ := OMUFU.game_eval g E lr pk sk A qI
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    rw [hv1] at hj
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    -- an extracted issuance input of `t`, of the variant of the query
    have hex : ∃ x ∈ SIX lr E v, comX x = toL p.1.q.t := by
      rcases p with ⟨p | p, b⟩
      · have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUFU.game lr pk sk qI A)).1[j]? =
            some (.inl p, true) := by rw [hj]; simp_all
        obtain ⟨hacc, hst⟩ := accepted_BI g E lr pk sk qI A hj'
        have hext : ExtBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)) := by
          by_contra hne
          exact hB j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
        obtain ⟨x, hx, hxc, -⟩ := opBI_of_ext E lr hext
        refine ⟨.inl x, Or.inl ⟨x, ⟨j, p, _, ?_, ?_, hx⟩, rfl⟩, ?_⟩
        · rw [hv1]; exact hj'
        · rw [hv, OMUFU.extAll_eval]; simp [hjl]
        · simp only [comX, Sum.elim_inl, IQ.q]; rw [hxc, hst]; rfl
      · have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUFU.game lr pk sk qI A)).1[j]? =
            some (.inr p, true) := by rw [hj]; simp_all
        obtain ⟨hacc, hst⟩ := accepted_UI g E lr pk sk qI A hj'
        have hext : ExtUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)) := by
          by_contra hne
          exact hU j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
        obtain ⟨y, hy, hyc, -⟩ := opUI_of_ext E lr hext
        refine ⟨.inr y, Or.inr ⟨y, ⟨j, p, _, ?_, ?_, hy⟩, rfl⟩, ?_⟩
        · rw [hv1]; exact hj'
        · rw [hv, OMUFU.extAll_eval]; simp [hjl]
        · simp only [comX, Sum.elim_inr, IQ.q]; rw [hyc, hst]; rfl
    obtain ⟨hy1, hy2⟩ := Classical.choose_spec hex
    refine ⟨Classical.choose hex, ?_, wfx_of_SIX lr hy1, hy2⟩
    simp only [ctufOutU, opensOfU]
    exact List.mem_filterMap.2 ⟨(p.1.q.k, toL p.1.q.t), hq, by simp [hex]⟩

/-- **The per-table core of Theorem U1 with CT-UF^open**: a win means that some accepted proof is
not extracted, or `B₁` finds a collision of `Com ∪ UCom`, or `B₂` wins CT-UF^open over the union
domain. -/
theorem win_imp_openU (g : Table) (E : CTable)
    (hwin : OMUFU.Win (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUFU.game lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadUR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))) ∨
    OMUFU.Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E)) ∨
    CTOpenWin (verK pk) comX WFX
      (ctufOutU lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E))) := by
  by_cases hB : ∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))
  · exact Or.inl hB
  by_cases hU : ∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))
  · exact Or.inr (Or.inl hU)
  push Not at hB hU
  rcases OMUFU.win_imp lr pk sk qI A g E hwin with h | h | h | h | h
  · exact absurd h (by push Not; exact hB)
  · exact absurd h (by push Not; exact hU)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (ctOpenWin_of_forgeU lr pk sk qI A g E hB hU h))))

/-- **`B₂`'s CT-UF^open advantage** against the Anchors' signers is the probability of its win in
the reductions' run. -/
theorem advCTUFOpenAt_ctufForgerU :
    advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) =
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (OMUFU.extAll lr pk sk qI A E)).run' ∅}[
        CTOpenWin (verK pk) comX WFX (ctufOutU lr pk E v)] := by
  unfold advCTUFOpenAt semAdv
  refine prEvent_bind_congr_of_support _ _ _ fun E _ => ?_
  simp only [ctufForgerU, skOf_signers, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **Theorem U1 with `B₂`'s standalone CT-UF^open advantage** (over `Com ∪ UCom`): for every
OMUF-U adversary, honest Anchors with any public keys and signers, either layout,

    Pr[Win] ≤ Σ_{j<qI} Pr[BadBI_j] + Σ_{j<qI} Pr[BadUI_j] + Σ_{j<qR} Pr[BadUR_j]
              + AdvBind(B₁) + Adv^{ct-uf-open}_K(B₂),

`B₂ = ctufForgerU lr pk qI A` against the signers `(k, t) ↦ derive_preimage(sk_k, t)`. -/
theorem omufU_le_open :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)).run' ∅}[BadBI E lr r] +
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)).run' ∅}[BadUI E lr r] +
      ∑ j ∈ Finset.range qR, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E)).run' ∅}[BadUR E lr pk r] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForgerU]
  refine prEvent_bind_le_sum5_of_table ($ᵗ CTable) (fun E => runE E (OMUFU.game lr pk sk qI A))
    (fun _ r => OMUFU.Win r.1) (Finset.range qI) (Finset.range qI) (Finset.range qR)
    _ _ _ _ _ _ _ _ (fun E v => CTOpenWin (verK pk) comX WFX (ctufOutU lr pk E v)) fun E g hw => ?_
  rw [evalWithAnswerFn_runE] at hw
  exact win_imp_openU lr pk sk qI A g E hw

/-- **Theorem U1 with `B₂`'s standalone CT-UF^open advantage, simultaneous extraction events**
(`omufU_le_open` with `omufU_le_sim`'s events). -/
theorem omufU_le_open_sim :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[SimBI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[SimU lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForgerU]
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (OMUFU.game lr pk sk qI A))
    (fun _ r => OMUFU.Win r.1) {0} {0} (fun _ E => OMUFU.extAll lr pk sk qI A E)
    (fun E v => SimBI lr E v) (fun _ E => OMUFU.extAll lr pk sk qI A E) (fun E v => SimU lr pk E v)
    (fun E => OMUFU.extAll lr pk sk qI A E) (fun E v => OMUFU.Coll lr pk E v)
    (fun E v => CTOpenWin (verK pk) comX WFX (ctufOutU lr pk E v)) fun E g hw => by
      rw [evalWithAnswerFn_runE] at hw
      rcases win_imp_openU lr pk sk qI A g E hw with
        ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

end Win

section Num

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  {A : OMUFU.Adversary K qR} {q : Kind → ℕ} {qE n : ℕ}

/-- **Theorem U1 (`omufU_le_num`) with `Adv^{ct-uf-open}_K` over `Com ∪ UCom` in place of
`AdvCTUF(B₂)`**: for an adversary within its budget and honest Anchors with distinct 32-byte key
digests,

    Pr[Win] ≤ qI·εI + qI·εUI + qR·εUR + AdvBind(B₁) + Adv^{ct-uf-open}_K(B₂). -/
theorem omufU_le_num_open (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      qI * epsI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) +
      qI * epsUI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) +
      qR * epsUR (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) := by
  refine (omufU_le_open lr pk sk qI A).trans
    (add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl) le_rfl)
  · refine (Finset.sum_le_card_nsmul _ _ (epsI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaIssue_accept_le_adaptive_spec (ι := ιI) (β := OMUFU.GOut K) (fun s => s.1)
      (fun s => s.2.1) (fun s => s.2.2) lr (hinjI lr) (PBI lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (OMUFU.game_e lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (OMUFU.game_k lr pk sk hA qI))
  · refine (Finset.sum_le_card_nsmul _ _ (epsUI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaUnboundIssue_accept_le_adaptive_spec (ι := ιI) (β := OMUFU.GOut K) (stUI lr) lr
      (fun s => s.1) (fun s => Unbound.moussakaUnboundIssue_stmt _ _ lr) (fun s => s.2.1)
      (hinjUI lr) (PUI lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (OMUFU.game_e lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (OMUFU.game_k lr pk sk hA qI))
  · refine (Finset.sum_le_card_nsmul _ _
      (epsUR (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaUnboundRedeem_accept_le_adaptive_spec (ι := ιR K) (β := OMUFU.GOut K)
      (stUR lr pk) lr (fun s => ancR pk s) (fun s => by simpa using s.2.1) (fun s => s.1.2.1)
      (fun s => s.1.2.2.1) (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2)
      (fun s => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ lr) (fun s => s.2.2.1)
      (hinjUR lr pk hdig hdinj) (PUR lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (OMUFU.game_e lr pk sk hA qI)) _
      ((isQueryBoundP_map_iff _ _ _).2 (OMUFU.game_h lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (OMUFU.game_k lr pk sk hA qI))

/-- **Theorem U1 (`omufU_le_num_sim`) with `Adv^{ct-uf-open}_K` over `Com ∪ UCom`.** -/
theorem omufU_le_num_open_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      epsIsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) :=
  (omufU_le_open_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_le hA) (prEvent_simU_le hA hdig hdinj)) le_rfl) le_rfl)

end Num

section OMPR

open CTUFOpen

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  {A : OMUFU.Adversary K qR} {q : Kind → ℕ} {qE n : ℕ}
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T] [SampleableType T]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) (qf qS : ℕ)

/-- **Theorem U1 with the UOV term down to OMPR** (`moussaka-unbound.md` §3.3: Lemma U over the
union domain), at fixed keys. `hmodel` is **the modelling step, a hypothesis**: the CT-UF^open
advantage of `B₂ = ctufForgerU` with the concrete `Com ∪ UCom` (`KP800(·)[0..45)` on both input
spaces) is at most the ideal advantage (`Com` a random function in the standalone game only,
`advCTUFIdealAt`) of some forger `F` within the budget `(q_f, q_S)` against the signers of keys
`ks` of a trapdoor `tr`. It is not provable: `Com` and `UCom` are fixed functions. Under it,

    Pr[Win] ≤ qI·εI + qI·εUI + qR·εUR + AdvBind(B₁)
              + Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_{key j}). -/
theorem omufU_le_num_ompr (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest)
    (F : ProbComp (OracleComp (specCI AR K Xc T S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CIBudget qf qS f)
    (hmodel : advCTUFOpenAt (verK pk) comX WFX
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerU lr pk qI A) ≤
      advCTUFIdealAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) F) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      qI * epsI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) +
      qI * epsUI (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) +
      qR * epsUR (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      ∑ j : Fin K, (advOMPR (tr.atKey (ks j)) (qf + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> F) +
        ((qf + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) :=
  (omufU_le_num_open lr pk sk qI hA hdig hdinj).trans
    (add_le_add le_rfl (hmodel.trans (advCTUFIdealAt_le_ompr tr qf qS ks F hF)))

/-- **Theorem U1 down to OMPR with simultaneous extraction** (`omufU_le_num_ompr` with
`εI^sim + εU^sim` in place of `qI·εI + qI·εUI + qR·εUR`; the same modelling hypothesis):

    Pr[Win] ≤ εI^sim + εU^sim + AdvBind(B₁)
              + Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_{key j}). -/
theorem omufU_le_num_ompr_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest)
    (F : ProbComp (OracleComp (specCI AR K Xc T S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CIBudget qf qS f)
    (hmodel : advCTUFOpenAt (verK pk) comX WFX
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerU lr pk qI A) ≤
      advCTUFIdealAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) F) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      epsIsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      ∑ j : Fin K, (advOMPR (tr.atKey (ks j)) (qf + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> F) +
        ((qf + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) :=
  (omufU_le_num_open_sim lr pk sk qI hA hdig hdinj).trans
    (add_le_add le_rfl (hmodel.trans (advCTUFIdealAt_le_ompr tr qf qS ks F hF)))

end OMPR

end Unbound

end VoleMole.Assumptions.UOV.Links
