import VoleMole.Theft.PlainUnboundPerm
import VoleMole.Theft.PlainUnboundManyRom
import VoleMole.Theft.PlainMousManyPerm

/-!
# Unbound non-malleability for `U` tokens, permutation rows and inverse queries

`nmUN_lean_rom'` (`Theft/PlainUnboundManyRom.lean`, function rows, forward queries) restated with
**permutation rows** (`ZKRow.perm`) and an adversary over `specP` with **forward and inverse**
cipher queries, on the `N = U + M` slices (`ansPNQ`), as `noRedirectN_lean_romP'` for bound
Moussaka:

* **`plainSENL_romUP`**: `plainSEL_romUP` with the slices as advice, for `FreshKNU kt`.
* `progQUmP`, `hpatchUmP`, `hlogUmP`, `qBudP_redQNu`: the forward-only patches.
* `romRowsUP`, `eRomUP_congr`, **`stageBudgetNX_extRomUNP`**: the extractor's read budget.
* **`nmUN_lean_romP`**, **`nmUN_lean_romP'`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Verifier
  VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Moussaka (KeysBy preOf outPre_preOf)
open VoleMole.Theft.Ratatouille (qPre qPre_h3 qPre_h5 advEquiv fnRows filterMap_decE_toIC
  map_toIC_congr)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

variable {U M L : ℕ}

/-! ## Plain extraction from `ROM/`'s permutation-model bound -/

section Plain

/-- **`ROM/`'s straight-line extractor with `N` slices and inverse queries**: `eRomUP`. -/
noncomputable def eRomUNP (N : ℕ) : Log → UOp → List DomP → (Fin N → Tab3) →
    (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ op qs _ b => eRomUP none none op qs zT zT b

lemma eRomUP_cLog (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : UOp) {qs qs' : List DomP} (g₁ g₂ g₁' g₂' : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M)
    (h : cLog (PTable.fwd b.1.2) (qs.map (toIC b.1.2)) =
      cLog (PTable.fwd b.1.2) (qs'.map (toIC b.1.2))) :
    eRomUP p₁ p₂ op qs g₁ g₂ b = eRomUP p₁ p₂ op qs' g₁' g₂' b :=
  eRomU_cLog p₁ p₂ op g₁ g₂ g₁' g₂' ((b.1.1, fnRows b.1.2), b.2) h

set_option maxHeartbeats 1000000 in
/-- **Plain extraction for `U` tokens and `M` redemptions from `ROM/`'s permutation-model bound**
(unbound Moussaka, permutation rows, inverse queries, `L ≥ 9749`): `PlainSENL` for `eRomUNP`
against `QBudP q qE`, for `FreshKNU kt`, error `epsRomUP q qE (totK Moussaka.M q)`. -/
theorem plainSENL_romUP (kt : Bytes → UOVKey) (hL : LminU ≤ L) (N : ℕ) (q : Kind → ℕ) {qE : ℕ}
    (hqE : qE + 4607 < 2 ^ 128) :
    PlainSENL N (ansPNQ (p := Privacy.Moussaka.pI) (L := L) (M := Arith.Moussaka.M))
      (AccOp (verILUX hbX) (verRLUX hbX)) (FreshKNU kt) RelOp (eRomUNP (L := L) N) (QBudP q qE)
      (epsRomUP q qE (totK Arith.Moussaka.M q)).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_romUP (L := L) kt hL q hqE (α × (Fin N → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locNQ b.2 (oa b.1)) fun b => qBudP_locHQ _ _ (hoa b.1)
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α N
    (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, hfr, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) z.2.2.2.1.2
  refine ⟨?_, ?_, ?_⟩
  · show AccOp _ _ (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show FreshKU kt none none (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
    rw [hr]
    exact ⟨hfr.1.wf, hfr.2⟩
  · show ¬ RelOp (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
      (eRomUP none none (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
        (qlog (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRomUP_cLog none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches, and the reduction's budget -/

section Patch

/-- **The patch of a simulated proof of either unbound relation, by forward queries.** -/
noncomputable abbrev progQUmP : UI → SimCoins pI × SimCoins pR →
    OracleComp specP (K2 Privacy.Moussaka.pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => liftP (progQUm xi c)

/-- **The patch's queries, from a log entry**: the prefix computation's forward queries, on the
tables with `H₂³` zero (none for no proof). -/
noncomputable def logQUmP {N : ℕ} (e : Option (UI × Bytes)) (_ : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) : List DomP :=
  qlog (ansQ zT zT ((fun _ => 0, b) :
    ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))) (liftP (vQUm e))

lemma qBudP_progQUmP (xi : UI) (c : SimCoins pI × SimCoins pR) :
    QBudP qPre (verifyCellBound pR) (progQUmP xi c) :=
  qBudP_liftP (qBudT_progQUm xi c).1

lemma progQUmP_ansPNQ {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPNQ g t) (progQUmP xi c) = qlog (ansQ zT zT t) (progQUmP xi c) ∧
      runT (ansPNQ g t) (progQUmP xi c) = runT (ansQ zT zT t) (progQUmP xi c) :=
  noH3_ansPNQ _ g zT zT t (noH3_of_kindP (qBudP_progQUmP xi c).1 qPre_h3 _)

lemma hlogUmP {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPNQ g t) (progQUmP xi c) =
      logQUmP (pairO (some xi) (simU (leanSim pI) (leanSim pR) xi c)) g t.2 := by
  rw [(progQUmP_ansPNQ xi c g t).1]
  unfold logQUmP
  rw [qlog_liftP, qlog_liftP]
  refine congrArg (List.map embIC) ?_
  rcases xi with x | x
  · show qlog _ (progQIU x c.1) = _
    rw [progQIU, qlog_map, ← qlog_vPreIC_G2 zT zT t (fun _ => 0)]
    rfl
  · show qlog _ (progQRU x c.2) = _
    rw [progQRU, qlog_map, ← qlog_vPreIC_G2 zT zT t (fun _ => 0)]
    rfl

lemma hpatchIUP (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansP g₁ g₂ (leanProgIUX hbX x c t) d =
      patch2 Privacy.Moussaka.pI (runT (ansP g₁ g₂ t) (progQIU x c)) d (ansP g₁ g₂ t d) := by
  rw [progQIU, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.MoussakaUnbound.stI x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchRUP (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansP g₁ g₂ (leanProgRUX hbX x c t) d =
      patch2 Privacy.Moussaka.pI (runT (ansP g₁ g₂ t) (progQRU x c)) d (ansP g₁ g₂ t d) := by
  rw [progQRU, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.MoussakaUnbound.stR x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchUmP {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomP) :
    ansPNQ g (progU (leanProgIUX hbX) (leanProgRUX hbX) xi c t) d =
      patch2P Privacy.Moussaka.pI (runT (ansPNQ g t) (progQUmP xi c)) d (ansPNQ g t d) := by
  rw [(progQUmP_ansPNQ xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPNQ_slPt _ _ hs, ansPNQ_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne (p := Privacy.Moussaka.pI) (runT (ansQ zT zT t) (progQUmP xi c))
      (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPNQ_eq g _ zT zT hd, ansPNQ_eq g t zT zT hd]
    rcases d with d | c'
    · rw [runT_liftP]
      rcases xi with x | x
      · exact hpatchIUP x c.1 zT zT t (.inl d)
      · exact hpatchRUP x c.2 zT zT t (.inl d)
    · have h2 := progU_sndX (Hb := hbX) xi c t
      show pans (progU (leanProgIUX hbX) (leanProgRUX hbX) xi c t).2.1.2 c' =
        pans t.2.1.2 c'
      rw [h2]

lemma logQUmP_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) :
    logQUmP none g b = [] := rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches** (permutation model). -/
theorem qBudP_redQNu {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specP α}
    (h : QBudP q qE oa) :
    ∀ ys : List (Option UI × (SimCoins pI × SimCoins pR)),
      QBudP (q + ys.length • qPre) (qE + ys.length * verifyCellBound pR)
        (redQN progQUmP (patch2P Privacy.Moussaka.pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudP_redQNu h ys
    have h₁ := Ratatouille.qBudP_progQO (fun x c => qBudP_progQUmP x c) y.1 y.2
    refine ⟨?_, ?_⟩
    · refine IsKindQueryBoundP.mono (isKindQueryBoundP_bind h₁.1 fun m =>
        isQueryBound_simP _ ih.1) fun k => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, List.length_cons]
      exact le_of_eq (by ring)
    · refine (isQueryBoundP_bind h₁.2 fun m _ => isQueryBoundP_simP _ ih.2).mono ?_
      simp only [List.length_cons]
      exact le_of_eq (by ring)

end Patch

/-! ## The rows `eRomUP` reads -/

section Rows

/-- **The rows `eRomUP` reads**: the keys of the cipher queries, the reconstruction's rows and the
zero key's row. -/
noncomputable def romRowsUP (op : UOp) (qs : List DomP) (π : PTable)
    (x : XTab L Arith.Moussaka.M) : Finset Blk :=
  romRowsU op (qs.map (toIC π)) (fnRows π) x

lemma romRowsUP_eq (op : UOp) (qs : List DomP) (π : PTable) (x : XTab L Arith.Moussaka.M) :
    romRowsUP op qs π x = insert zeroRow ((qs.filterMap decEP).toFinset ∪
      treeRows (fnRows π) (ivOf (hbX x) ⟨(fdU op).1.params, (fdU op).2⟩ ((fdU op).1.mu1 (hbX x)))
        (Proof.opening ⟨(fdU op).1.params, (fdU op).2⟩)
        (Proof.delta ⟨(fdU op).1.params, (fdU op).2⟩)) := by
  unfold romRowsUP romRowsU
  rw [filterMap_decE_toIC]

lemma card_romRowsUP_le (op : UOp) (qs : List DomP) (π : PTable) (x : XTab L Arith.Moussaka.M) :
    (romRowsUP op qs π x).card ≤ (qs.filterMap decEP).toFinset.card + 4608 := by
  have h := card_romRowsU_le op (qs.map (toIC π)) (fnRows π) x
  rw [filterMap_decE_toIC] at h
  exact h

/-- **`eRomUP` reads neither the slices nor `H₅`, and the permutations only in `romRowsUP`.** -/
theorem eRomUP_congr (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : UOp) (qs : List DomP) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {π π' : PTable}
    (x : XTab L Arith.Moussaka.M) (h : ∀ k ∈ romRowsUP op qs π x, π k = π' k) :
    eRomUP p₁ p₂ op qs g₁' g₂' ((G5', π'), x) = eRomUP p₁ p₂ op qs g₁ g₂ ((G5, π), x) := by
  have hq : qs.map (toIC π') = qs.map (toIC π) := map_toIC_congr fun k hk =>
    h k (by rw [romRowsUP_eq]; exact mem_insert_of_mem (mem_union_left _ hk))
  show eRomU p₁ p₂ op (qs.map (toIC π')) g₁' g₂' ((G5', fnRows π'), x) =
    eRomU p₁ p₂ op (qs.map (toIC π)) g₁ g₂ ((G5, fnRows π), x)
  rw [hq]
  exact eRomU_congr p₁ p₂ op _ g₁ g₂ g₁' g₂' G5 G5' x fun k hk =>
    congrArg (fun σ : Equiv.Perm Blk => (σ : Blk → Blk)) (h k hk)

end Rows

/-! ## The extractor's read budget -/

section Reads

/-- The extractor's query list on the tables `t`: the patches' prefixes, then the last stage's. -/
noncomputable def qsNUP {α : Type} {N : ℕ} (ls : List (Option (UI × Bytes)))
    (oa : OracleComp specP α) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) : List DomP :=
  (ls.flatMap fun e => qlog (ansQ zT zT ((fun _ => 0, t.2) :
    ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))) (liftP (vQUm e))) ++
    qlog (ansPNQ g t) oa

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices and inverse queries** (unbound
Moussaka): each slice at `q h3` keys, `H₅` at `q h5 + N·312`, the permutation table at
`qE + N·cells(pR) + 4608` rows. -/
theorem stageBudgetNX_extRomUNP {N : ℕ} {q : Kind → ℕ} {qE : ℕ}
    {F : (Fin N → Tab3) → ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) →
      UOp}
    (hF : AdmLN (QBudP q qE) ansPNQ F) (l : Log) :
    StageBudgetNX (extLN ansPNQ (QBudP q qE) logQUmP (eRomUNP N) l F) (q .h3)
      (q .h5 + N * 312) (qE + N * verifyCellBound pR + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQUmP) (e := eRomUNP N) hF
  set ls := (l.take N).reverse
  have hlen : ls.length ≤ N := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPNQ (QBudP q qE) logQUmP (eRomUNP N) l F = fun g t =>
      eRomUP none none (runT (ansPNQ g t) oa) (qsNUP ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomUNP qsNUP logsL
    rfl
  rw [hfun]
  intro x
  have hS : ∀ e, QBudP qPre (verifyCellBound pR) (liftP (vQUm e)) :=
    fun e => qBudP_liftP (qBud_vQUm e)
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPNQ (Function.update g j u) (atX s x)) oa).filterMap
        (dec3NQ j)).toFinset,
      fun u => card_dec_leG _ _ _ _ (isQueryBoundP_kindP hb.1 .h3) fun _ _ => dec3NQ_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPNQ (Function.update g j u) (atX s x))
      (ansPNQ (Function.update g j u') (atX s x)) fun d hd =>
        ansPNQ_h3 g j u u' _ d fun k hk => hg k (mem_decG hd hk)
    show eRomUP none none _ (qsNUP ls oa _ _) zT zT _ =
      eRomUP none none _ (qsNUP ls oa _ _) zT zT _
    unfold qsNUP
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsNUP ls oa g (atX s x)).filterMap dec5P).toFinset,
      fun s => (card_runsN_leG dec5P (kindBP .h5) (fun _ _ => dec5P_kind) _ _
        (fun e => isQueryBoundP_kindP (hS e).1 .h5) (isQueryBoundP_kindP hb.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congrG dec5P _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
      (f' := ansPNQ g (atX (s.1, G5, s.2.2) x)) (fun e => liftP (vQUm e)) ls oa subset_rfl
      (fun d hd => ansQ_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) G5 d
          fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_h5 g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomUP none none _ (qsNUP ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRomUP none none _ (qsNUP ls oa g (atX s x)) zT zT _
    unfold qsNUP
    rw [e1, e2]
    exact eRomUP_congr none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the permutations
    refine ⟨fun s => romRowsUP (runT (ansPNQ g (atX s x)) oa) (qsNUP ls oa g (atX s x)) s.2.2 x,
      fun s => (card_romRowsUP_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_leG decEP (fun d => d.isRight) (fun _ _ => decEP_right)
        (ansQ zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (ansPNQ g (atX s x)) (fun e => (hS e).2) hb.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pR) hlen
      unfold qsNUP
      generalize verifyCellBound pR = c at this h2 ⊢
      omega
    have hsub : ((qsNUP ls oa g (atX s x)).filterMap decEP).toFinset ⊆
        romRowsUP (runT (ansPNQ g (atX s x)) oa) (qsNUP ls oa g (atX s x)) s.2.2 x := by
      rw [romRowsUP_eq]
      exact fun k hk => mem_insert_of_mem (mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := runsN_congrG decEP _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
      (f' := ansPNQ g (atX (s.1, s.2.1, E) x)) (fun e => liftP (vQUm e)) ls oa hsub
      (fun d hd => ansQ_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) E d
          fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_E g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomUP none none (runT (ansPNQ g (atX (s.1, s.2.1, E) x)) oa)
        (qsNUP ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRomUP none none (runT (ansPNQ g (atX s x)) oa) (qsNUP ls oa g (atX s x)) zT zT _
    have e1' : qsNUP ls oa g (atX (s.1, s.2.1, E) x) = qsNUP ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRomUP_congr none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## Unbound non-malleability for `U` tokens with permutation rows -/

section Theorem

/-- **The extractor**: `eRomUNP` on the reduction's queries. -/
noncomputable def extRomUNP (q : Kind → ℕ) (qE : ℕ) :
    ExtN U M Tab3 (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :=
  extLN ansPNQ (QBudP q qE) logQUmP (eRomUNP (U + M))

variable (A : ThiefN U M Tab3
  (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability and no squatting for `U` tokens and `M` redemptions with
permutation rows, inverse cipher queries and `ROM/`'s plain extraction** (`M = Moussaka.M`,
`L ≥ 9749`): as `nmUN_lean_rom`, with `ZKRow.perm`, an adversary over `specP` within
`QBudP q q_E` (no total hash budget) and the extractor `extRomUNP`;
`ε_rom = epsRomUP (q + N·qPre) (q_E + N·cells(pR)) (totK Moussaka.M (q + N·qPre))`. The PRF bound
(`hprf`) stays a hypothesis. -/
theorem nmUN_lean_romP (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hqE : qE + (U + M) * verifyCellBound pR + 4607 < 2 ^ 128)
    (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUNP q qE) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUNP q qE))) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Equiv.Perm Blk) pR (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomUP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUNP q qE) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUNP q qE) h)) := by
  have hSB : ∀ reqs reds, StageBudgetNX (A.out reqs reds) (q .h3) (q .h5) qE := fun reqs reds => by
    obtain ⟨oa, hb, hF⟩ := hA reqs reds
    rw [hF]
    exact stageBudgetNX_runTNQ hb
  have hX : ∀ l, StageBudgetNX (extRomUNP q qE l (opN A l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pR + 4608) :=
    fun l => stageBudgetNX_extRomUNP (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) →
      ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) → UOp,
      AdmLN (QBudP q qE) ansPNQ F →
      Hit.AdmHitN (R := Equiv.Perm Blk) (p := Privacy.Moussaka.pI) (L := L)
        (M := Arith.Moussaka.M) (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTNQ hb
  have hmv := ((progMovesN_hitU (U := U) (M := M) (R := Equiv.Perm Blk) hL (q .mu) (q .h21)
    (q .h22)).mono hAH).fresh_mono (Fresh' := FreshKNU kt) fun _ _ h => h.1
  exact nmUN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIUX hbX) (leanPRUX hbX)
    (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX) (verILUX hbX) (verRLUX hbX)
    (extRomUNP q qE) (leanPIUX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRUX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPN_budgetUXI' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPN_budgetUXR' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_okKU A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
      (verILUX hbX) (verRLUX hbX) (extRomUNP q qE) hw hk
      (weakSEN_of_plainL progQUmP (patch2P Privacy.Moussaka.pI) logQUmP
        (plainSENL_romUP kt hL _ _ hqE) hmv progU_sndX hpatchUmP hlogUmP logQUmP_none
        fun oa ys hl h => hl ▸ qBudP_redQNu h ys)
      fun _ => hA _ _) pts hpts hprf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens with permutation rows**, the hops' budgets
simplified (`cells(pR) = 101372`), for `q_E + N·101372 + 4607 < 2¹²⁸`:

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·105979 + 4608),   N = U + M. -/
theorem nmUN_lean_romP' (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE : ℕ} (hqE : qE + (U + M) * 101372 + 4607 < 2 ^ 128)
    (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUNP q qE) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUNP q qE))) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        M * ZKRow.εz (Equiv.Perm Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomUP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUNP q qE) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUNP q qE) h)) := by
  have hq : qE + (U + M) * verifyCellBound pR + 4607 < 2 ^ 128 := by
    rw [verifyCellBound_pRU]; exact hqE
  have h := nmUN_lean_romP A hw hk hL hq hA pts hpts hprf
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 105979 + 4608 := by
    rw [verifyCellBound_pRU]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

end VoleMole.Theft.MoussakaUnbound
