import VoleMole.Theft.PlainUnboundRom
import VoleMole.Theft.PlainMousManyRom

/-!
# Unbound Moussaka for `U` tokens and `M` redemptions with plain extraction from `ROM/`

`nmUN_leanX_hit` (`Theft/MoussakaUnboundHit.lean`) keeps plain extraction `PlainSEN` as a
hypothesis. Here it is replaced by `PlainSENL` (`Theft/ManyPlainLog.lean`) and proved from
`ROM/`'s simultaneous extraction (`plainSEL_romU`, `Theft/PlainUnboundRom.lean`), as
`noRedirectN_lean_rom'` (`Theft/PlainMousManyRom.lean`) does for bound Moussaka
(`docs/security/moussaka-unbound.md` §5.3):

* **`FreshKNU kt`**: the freshness of the bound: `FreshOkN` and, for a redemption, Anchor keys that
  are the keys `kt d` of their digests (`KeysOpU`). In the game, for adversaries whose output
  redemptions have the keys of `kt` (`KeysOutNU`), the game's freshness is `FreshKNU kt`
  (`sim_se_leN_okKU`).
* **`plainSENL_romU`**: `PlainSENL` for `eRomUN` (the one-operation `eRomU`) against
  `QBudT q qE nG`, for `FreshKNU kt`, with the error `epsRomU q qE nG` (the slices as advice).
* `progQIU`, `progQRU`, `progQUm`, `logQUm`: the patches of the two unbound simulators, by queries
  (`hlogUm`, `hpatchUm`). `qBudT_redQNu`: the reduction for `N` patches is within
  `QBudT (q + N·qPre) (qE + N·cells(pR)) (nG + N·338)`, `cells(pR) = 101372` for the unbound
  redemption relation (`verifyCellBound_pRU`).
* `romRowsU`, **`eRomU_congr`**: `eRomU` reads neither the slices nor `H₅`, and the cipher only in
  the cells' rows of its query list, the reconstruction's rows and the zero key's row.
* **`stageBudgetNX_extRomUN`**: the extractor's read budget: each slice at `q h3` keys, `H₅` at
  `q h5 + N·312`, the cipher at `qE + N·cells(pR) + 4608` rows.
* **`nmUN_lean_rom`**, **`nmUN_lean_rom'`**: the theorem, and **`nmUN_lean_rom_one`** for one
  token and one redemption (`U = M = 1`).
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
open VoleMole.Theft.Moussaka (KeysBy preOf outPre_preOf ansPN_h5M ansPN_EM)
open VoleMole.Theft.Ratatouille (qPre qBud_mono_cells flatMap_qlog_congr runsN_congr
  card_runsN_le advEquiv qPre_h3 qPre_h5)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

variable {U M L : ℕ}

/-! ## The freshness of the bound, in the game -/

/-- **The freshness of `ROM/`'s bound** for `U + M` simulated unbound proofs: `FreshOkN` and the
Anchor keys of `kt`. -/
def FreshKNU (kt : Bytes → UOVKey) (l : Log) (op : UOp) : Prop := FreshOkN l op ∧ KeysOpU kt op

section Game

variable {G S : Type} (A : ThiefN U M G S)

/-- **The adversary's output redemptions have the Anchor keys of `kt`.** -/
def KeysOutNU (kt : Bytes → UOVKey) : Prop := ∀ reqs reds g s, KeysOpU kt (A.out reqs reds g s)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : ExtN U M G S) [Nonempty CI] [Nonempty CR] [Fintype CI] [Fintype CR] [Fintype G]
  [Fintype S] [Nonempty G]

/-- **`sim_se_leN_ok` for `FreshKNU kt`**, for `HitWfN` adversaries with the keys of `kt`. -/
theorem sim_se_leN_okKU (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) (FreshKNU kt)
      RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤ εSE := by
  have h := simGN_le_of_weakSEN (Ω := SecN U) (ρ := Coins proveSeedBytes) hse
    (fun ω l => xN A (pubOf A ω) l) (fun _ l => opN A l) fun _ l => hAE l
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  exact ⟨hz.1, ⟨freshOkN_of_sim A simI progI simR progR verI verR hw _ _ _ _ _ hz.1 hz.2.1,
    hk _ _ _ _⟩, hz.2.2⟩

end Game

/-! ## Plain extraction from `ROM/`'s bound -/

section Plain

/-- **`ROM/`'s straight-line extractor with `N` slices**: the one-operation extractor `eRomU`. -/
noncomputable def eRomUN (N : ℕ) : Log → UOp → List DomIC → (Fin N → Tab3) →
    (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ op qs _ b => eRomU none none op qs zT zT b

/-- `eRomU` reads the query list only through its cipher entries, and not the slices. -/
lemma eRomU_cLog (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : UOp) {qs qs' : List DomIC} (g₁ g₂ g₁' g₂' : Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M)
    (h : cLog (Ratatouille.ctOf b.1.2) qs = cLog (Ratatouille.ctOf b.1.2) qs') :
    eRomU p₁ p₂ op qs g₁ g₂ b = eRomU p₁ p₂ op qs' g₁' g₂' b := by
  simp only [eRomU, h]

set_option maxHeartbeats 1000000 in
/-- **Plain extraction for `U` tokens and `M` redemptions from `ROM/`'s bound** (unbound Moussaka,
function rows, `M = Moussaka.M`, `L ≥ 9749`): `PlainSENL` holds for `eRomUN` against the last
stages within `QBudT q qE nG`, for the freshness `FreshKNU kt`, with the one-operation error
`epsRomU q qE nG`. -/
theorem plainSENL_romU (kt : Bytes → UOVKey) (hL : LminU ≤ L) (N : ℕ) (q : Kind → ℕ)
    (qE nG : ℕ) :
    PlainSENL N (ansPN (R := Blk → Blk) (p := Privacy.Moussaka.pI) (L := L)
        (M := Arith.Moussaka.M))
      (AccOp (verILUX hbX) (verRLUX hbX)) (FreshKNU kt) RelOp (eRomUN (L := L) N) (QBudT q qE nG)
      (epsRomU q qE nG).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_romU (L := L) kt hL q qE nG (α × (Fin N → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locN b.2 (oa b.1)) fun b => qBudT_locN (hoa b.1) b.2
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α N
    (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, hfr, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) (Ratatouille.ctOf z.2.2.2.1.2)
  refine ⟨?_, ?_, ?_⟩
  · show AccOp _ _ (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show FreshKU kt none none (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
    rw [hr]
    exact ⟨hfr.1.wf, hfr.2⟩
  · show ¬ RelOp (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
      (eRomU none none (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
        (qlog (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRomU_cLog none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches of the two unbound simulators, and the reduction's budget -/

section Patch

/-- **The unbound issuance simulator's patch, by queries.** -/
noncomputable def progQIU (x : IssueInstance) (c : SimCoins pI) :
    OracleComp specIC (K2 Privacy.Moussaka.pI → Option (ZK.Sim.Bytes 16)) :=
  (fun pre => mOf Privacy.Moussaka.pI (preOf c pre) c.1.2.1) <$>
    vPreIC CrtGen.tables (Privacy.MoussakaUnbound.stI x) (toBA (leanSim pI x c))

/-- **The unbound redemption simulator's patch, by queries.** -/
noncomputable def progQRU (x : RedeemInstance) (c : SimCoins pR) :
    OracleComp specIC (K2 Privacy.Moussaka.pI → Option (ZK.Sim.Bytes 16)) :=
  (fun pre => mOf Privacy.Moussaka.pI (preOf c pre) c.1.2.1) <$>
    vPreIC CrtGen.tables (Privacy.MoussakaUnbound.stR x) (toBA (leanSim pR x c))

/-- **The patch of a simulated proof of either unbound relation, by queries.** -/
noncomputable abbrev progQUm : UI → SimCoins pI × SimCoins pR →
    OracleComp specIC (K2 Privacy.Moussaka.pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => match xi with
    | .inl x => progQIU x c.1
    | .inr x => progQRU x c.2

/-- The prefix computation of a log entry (none for no proof). -/
noncomputable def vQUm : Option (UI × Bytes) → OracleComp specIC ByteArray
  | some (.inl x, π) => vPreIC CrtGen.tables (Privacy.MoussakaUnbound.stI x) (toBA π)
  | some (.inr x, π) => vPreIC CrtGen.tables (Privacy.MoussakaUnbound.stR x) (toBA π)
  | none => pure ByteArray.empty

/-- **The patch's queries, from a log entry**: the prefix computation's, on the tables with
`H₂³` zero (none for no proof). -/
noncomputable def logQUm {N : ℕ} (e : Option (UI × Bytes)) (_ : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M) : List DomIC :=
  qlog (ansP zT zT ((fun _ => 0, b) :
    ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))) (vQUm e)

set_option maxRecDepth 100000 in
lemma verifyCellBound_pIU : verifyCellBound pI = 55292 := by
  rw [verifyCellBound_eq]; decide

set_option maxRecDepth 100000 in
lemma verifyCellBound_pRU : verifyCellBound pR = 101372 := by
  rw [verifyCellBound_eq]; decide

lemma cells_pIU_le_pRU : verifyCellBound pI ≤ verifyCellBound pR := by
  rw [verifyCellBound_pIU, verifyCellBound_pRU]; norm_num

lemma qBud_vQUm (e : Option (UI × Bytes)) : QBud qPre (verifyCellBound pR) (vQUm e) := by
  rcases e with _ | ⟨x | x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact qBud_mono_cells ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩
      cells_pIU_le_pRU
  · exact ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩

set_option maxHeartbeats 4000000 in
/-- **The patch's budget**: `qPre` hash queries, at most `338` in all, and `cells(pR)` cells. -/
lemma qBudT_progQUm : ∀ (xi : UI) (c : SimCoins pI × SimCoins pR),
    QBudT qPre (verifyCellBound pR) 338 (progQUm xi c)
  | .inl _, _ => ⟨qBud_mono_cells ⟨isQueryBound_map_iff _ _ _ _ _ |>.2
        (isKindQueryBoundIC_vPreIC _ _ _),
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩ cells_pIU_le_pRU,
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_vPreIC _ _ _)⟩
  | .inr _, _ => ⟨⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (isKindQueryBoundIC_vPreIC _ _ _),
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩,
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_vPreIC _ _ _)⟩

/-- **The patch's queries on the `N` slices are its queries on two.** -/
lemma progQUm_ansPN {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPN g t) (progQUm xi c) = qlog (ansP zT zT t) (progQUm xi c) ∧
      runT (ansPN g t) (progQUm xi c) = runT (ansP zT zT t) (progQUm xi c) :=
  noH3_ansPN _ g zT zT t (noH3_of_kind (qBudT_progQUm xi c).1.1 qPre_h3 _)

lemma hlogUm {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPN g t) (progQUm xi c) =
      logQUm (pairO (some xi) (simU (leanSim pI) (leanSim pR) xi c)) g t.2 := by
  rw [(progQUm_ansPN xi c g t).1]
  rcases xi with x | x
  · show qlog _ (progQIU x c.1) = _
    rw [progQIU, qlog_map, ← qlog_vPreIC_G2 zT zT t (fun _ => 0)]
    rfl
  · show qlog _ (progQRU x c.2) = _
    rw [progQRU, qlog_map, ← qlog_vPreIC_G2 zT zT t (fun _ => 0)]
    rfl

lemma hpatchIU (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansP g₁ g₂ (leanProgIUX hbX x c t) d =
      patch2 Privacy.Moussaka.pI (runT (ansP g₁ g₂ t) (progQIU x c)) d (ansP g₁ g₂ t d) := by
  rw [progQIU, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.MoussakaUnbound.stI x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchRU (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansP g₁ g₂ (leanProgRUX hbX x c t) d =
      patch2 Privacy.Moussaka.pI (runT (ansP g₁ g₂ t) (progQRU x c)) d (ansP g₁ g₂ t d) := by
  rw [progQRU, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.MoussakaUnbound.stR x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchUm {N : ℕ} (xi : UI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansPN g (progU (leanProgIUX hbX) (leanProgRUX hbX) xi c t) d =
      patch2 Privacy.Moussaka.pI (runT (ansPN g t) (progQUm xi c)) d (ansPN g t d) := by
  rw [(progQUm_ansPN xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne _ (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd, ansPN_eq g t zT zT hd]
    rcases xi with x | x
    · exact hpatchIU x c.1 zT zT t d
    · exact hpatchRU x c.2 zT zT t d

lemma logQUm_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M) : logQUm none g b = [] := rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches.** -/
theorem qBudT_redQNu {α : Type} {q : Kind → ℕ} {qE nG : ℕ} {oa : OracleComp specIC α}
    (h : QBudT q qE nG oa) :
    ∀ ys : List (Option UI × (SimCoins pI × SimCoins pR)),
      QBudT (q + ys.length • qPre) (qE + ys.length * verifyCellBound pR) (nG + ys.length * 338)
        (redQN progQUm (patch2 Privacy.Moussaka.pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudT_redQNu h ys
    have h₁ := Ratatouille.qBud_progQO (fun x c => (qBudT_progQUm x c).1) y.1 y.2
    have h₁' := Ratatouille.left_progQO (fun x c => (qBudT_progQUm x c).2) y.1 y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (isKindQueryBoundIC_bind h₁.1 fun m => isQueryBound_simP _ ih.1.1).mono fun k => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, List.length_cons]
      exact le_of_eq (by ring)
    · refine (isQueryBoundP_bind h₁.2 fun m _ => isQueryBoundP_simP _ ih.1.2).mono ?_
      simp only [List.length_cons]
      exact le_of_eq (by ring)
    · refine (isQueryBoundP_bind h₁' fun m _ => isQueryBoundP_simP _ ih.2).mono ?_
      simp only [List.length_cons]
      exact le_of_eq (by ring)

end Patch

/-! ## The rows `eRomU` reads -/

section Rows

/-- **The rows `eRomU` reads**: the cells' rows of the query list, the reconstruction's rows of the
operation's proof, and the zero key's row. -/
noncomputable def romRowsU (op : UOp) (qs : List DomIC) (E : Blk → Blk → Blk)
    (x : XTab L Arith.Moussaka.M) : Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    treeRows E (ivOf (hbX x) ⟨(fdU op).1.params, (fdU op).2⟩ ((fdU op).1.mu1 (hbX x)))
      (Proof.opening ⟨(fdU op).1.params, (fdU op).2⟩)
      (Proof.delta ⟨(fdU op).1.params, (fdU op).2⟩))

lemma card_romRowsU_le (op : UOp) (qs : List DomIC) (E : Blk → Blk → Blk)
    (x : XTab L Arith.Moussaka.M) :
    (romRowsU op qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (card_treeRows_le E
      (ivOf (hbX x) ⟨(fdU op).1.params, (fdU op).2⟩ ((fdU op).1.mu1 (hbX x)))
      (Proof.opening ⟨(fdU op).1.params, (fdU op).2⟩)
      (Proof.delta ⟨(fdU op).1.params, (fdU op).2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

/-- **`eRomU` reads neither the slices nor `H₅`, and the cipher only in `romRowsU`.** -/
theorem eRomU_congr (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : UOp) (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F)
    {E E' : Blk → Blk → Blk} (x : XTab L Arith.Moussaka.M)
    (h : ∀ k ∈ romRowsU op qs E x, E k = E' k) :
    eRomU p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRomU p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  show pickU _ _ _ = pickU _ _ _
  dsimp only
  have hc : cLog (Ratatouille.ctOf E') qs = cLog (Ratatouille.ctOf E) qs :=
    (Ratatouille.cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      rw [h c.1 (mem_insert_of_mem (mem_union_left _ (mem_dec hc rfl)))]).symm
  rw [hc]
  unfold romRowsU at h
  generalize fdU op = f at h ⊢
  generalize cLog (Ratatouille.ctOf E) qs = log at hc ⊢
  have hsub : logKeys log ⊆ (qs.filterMap decE).toFinset :=
    hc ▸ Ratatouille.logKeys_cLog_subset _ _
  have hrows : ∀ c : Cell, c.1 ∈ extractRows log (Ratatouille.ctOf E).cipher
      (ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))) (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) → Ratatouille.ctOf E c = Ratatouille.ctOf E' c := by
    intro c hc
    show E c.1 c.2 = E' c.1 c.2
    refine congrFun (h c.1 ?_) c.2
    rcases mem_insert.1 hc with hc | hc
    · exact hc ▸ mem_insert_self _ _
    · rcases mem_union.1 hc with hc | hc
      · exact mem_insert_of_mem (mem_union_left _ (hsub hc))
      · exact mem_insert_of_mem (mem_union_right _ hc)
  obtain ⟨hk, hkn, hu⟩ := extract_congr_rows hrows
  have hr : Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E') log =
      Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E) log := by
    unfold Ratatouille.rOut
    rw [← hk, ← hkn]
  rw [hr]
  generalize hR : Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E) log = r
  have hu' : ∀ (i : Fin BAVC.tau) (j : ℕ),
      @uBit (icPrg (Ratatouille.ctOf E').cipher) f.1.params (outChain r).iv
        ((outChain r).corr f.1) (outChain r).keys i j =
      @uBit (icPrg (Ratatouille.ctOf E).cipher) f.1.params (outChain r).iv ((outChain r).corr f.1)
        (outChain r).keys i j := by
    intro i j
    subst hR
    have := hu f.1.params (ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x)))
      ((outChain (Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E) log)).corr f.1) i j
    rw [← hk] at this
    exact this.symm
  have hcand : candOf (Ratatouille.ctOf E') f.1 r = candOf (Ratatouille.ctOf E) f.1 r := by
    funext i
    unfold candOf Chain.u
    simp only [hu']
  rw [hcand]

end Rows

/-! ## The extractor's read budget -/

section Reads

lemma logQUm_eq {N : ℕ} (e : Option (UI × Bytes)) (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M) :
    logQUm e g b = qlog (ansP zT zT ((fun _ => 0, b) :
      ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))) (vQUm e) := rfl

/-- The extractor's query list on the tables `t`: the patches' prefixes, then the last stage's. -/
noncomputable def qsNU {α : Type} {N : ℕ} (ls : List (Option (UI × Bytes)))
    (oa : OracleComp specIC α) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) : List DomIC :=
  (ls.flatMap fun e => qlog (ansP zT zT ((fun _ => 0, t.2) :
    ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))) (vQUm e)) ++
    qlog (ansPN g t) oa

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices** (unbound Moussaka): each slice at
`q h3` keys, `H₅` at `q h5 + N·312`, the cipher at `qE + N·cells(pR) + 4608` rows. -/
theorem stageBudgetNX_extRomUN {N : ℕ} {q : Kind → ℕ} {qE nG : ℕ}
    {F : (Fin N → Tab3) → ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) → UOp}
    (hF : AdmLN (QBudT q qE nG) ansPN F) (l : Log) :
    StageBudgetNX (extLN ansPN (QBudT q qE nG) logQUm (eRomUN N) l F) (q .h3)
      (q .h5 + N * 312) (qE + N * verifyCellBound pR + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQUm) (e := eRomUN N) hF
  set ls := (l.take N).reverse
  have hlen : ls.length ≤ N := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPN (QBudT q qE nG) logQUm (eRomUN N) l F = fun g t =>
      eRomU none none (runT (ansPN g t) oa) (qsNU ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomUN qsNU logsL
    congr 2
  rw [hfun]
  intro x
  have hS := qBud_vQUm
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPN (Function.update g j u) (atX s x)) oa).filterMap
        (dec3N j)).toFinset,
      fun u => card_dec_le _ _ _ _ (isQueryBoundP_kind hb.1.1 .h3) fun _ _ => dec3N_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPN (Function.update g j u) (atX s x))
      (ansPN (Function.update g j u') (atX s x)) fun d hd =>
        ansPN_h3 g j u u' _ d fun k hk => hg k (mem_dec hd hk)
    show eRomU none none _ (qsNU ls oa _ _) zT zT _ = eRomU none none _ (qsNU ls oa _ _) zT zT _
    unfold qsNU
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsNU ls oa g (atX s x)).filterMap dec5).toFinset,
      fun s => (card_runsN_le dec5 (kindB .h5) (fun _ _ => dec5_kind) _ _
        (fun e => isQueryBoundP_kind (hS e).1 .h5) (isQueryBoundP_kind hb.1.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congr dec5 _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
      (f' := ansPN g (atX (s.1, G5, s.2.2) x)) vQUm ls oa subset_rfl
      (fun d hd => ansP_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) G5 d
          fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_h5M g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomU none none _ (qsNU ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRomU none none _ (qsNU ls oa g (atX s x)) zT zT _
    unfold qsNU
    rw [e1, e2]
    exact eRomU_congr none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the cipher
    refine ⟨fun s => romRowsU (runT (ansPN g (atX s x)) oa) (qsNU ls oa g (atX s x)) s.2.2 x,
      fun s => (card_romRowsU_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_le decE (fun d => d.isRight) (fun _ _ => decE_right)
        (ansP zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (ansPN g (atX s x)) (fun e => (hS e).2) hb.1.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pR) hlen
      unfold qsNU
      generalize verifyCellBound pR = c at this h2 ⊢
      omega
    obtain ⟨e1, e2⟩ := runsN_congr decE _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
      (f' := ansPN g (atX (s.1, s.2.1, E) x)) vQUm ls oa
      (fun k hk => mem_insert_of_mem (mem_union_left _ hk))
      (fun d hd => ansP_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) E d
          fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_EM g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomU none none (runT (ansPN g (atX (s.1, s.2.1, E) x)) oa)
        (qsNU ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRomU none none (runT (ansPN g (atX s x)) oa) (qsNU ls oa g (atX s x)) zT zT _
    have e1' : qsNU ls oa g (atX (s.1, s.2.1, E) x) = qsNU ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRomU_congr none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## The hop budgets for any extractor on the tables with the extra table -/

section Hops

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)
  (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI X))
  (ext : ExtN U M Tab3 (ShX R Privacy.Moussaka.pI X)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The bad event at a value of the extra table reads what the last stage, the extractor and
the verifiers read** (`bad_budgetN` for an extractor on the tables with the extra table). -/
theorem bad_budgetNXu (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (x : X) (ω : SecN U) (l : Log) :
    StageBudgetN (fun g s => BadN A (verILUX Hb) (verRLUX Hb) ext ω l g (atX s x))
      (a3 + x3) (a5 + (x5 + 312)) (aE + (xE + 4607)) := by
  have h := (show StageBudgetN (fun g s => opN A l g (atX s x)) a3 a5 aE from hA _ _ x).event
    (V := AccOp (verILUH (Hb x)) (verRLUH (Hb x)))
    (fun op w acc => acc ∧ FreshOpN l op ∧
      (¬ RelOp op w ∨ ∃ h, HitOp (tOfN A ω h) (List.ofFn (ω h).1) op w))
    (hX l x) (accOp_rd5 _ _ (verILUH_rd5 (Hb x)) (verRLUH_rd5 (Hb x)))
    (accOp_rdE _ _ (verILUH_rdE (Hb x)) (verRLUH_rdE (Hb x)))
  have e : (fun g s => BadN A (verILUX Hb) (verRLUX Hb) ext ω l g (atX s x)) =
      fun g s => (AccOp (verILUH (Hb x)) (verRLUH (Hb x)) (opN A l g (atX s x)) s ∧
        FreshOpN l (opN A l g (atX s x)) ∧
        (¬ RelOp (opN A l g (atX s x)) (ext l (opN A l) g (atX s x)) ∨
          ∃ h, HitOp (tOfN A ω h) (List.ofFn (ω h).1) (opN A l g (atX s x))
            (ext l (opN A l) g (atX s x)))) := by
    funext g s
    simp only [BadN, accN, freshN, relN, hitN, accOp_atXU]
    rfl
  rw [e]
  exact h

/-- **The budget of every hop's distinguisher, for any extractor on the tables with the extra
table** (`distN_budgetUX` for `ext`). -/
theorem distN_budgetUX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX Privacy.Moussaka.pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
      (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIUX Hb) (leanPRUX Hb))
        (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω))
        (BadN A (verILUX Hb) (verRLUX Hb) ext) i ω τ) :=
  (distN_budgetX (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun x => PN (atTN A x) (leanPIUH (Hb x)) (leanPRUH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIUH (Hb x)) (leanProgRUH (Hb x)) (pubOf A ω))
    (fun x ω l g s => BadN A (verILUX Hb) (verRLUX Hb) ext ω l g (atX s x))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf A ω) l c s)
    (fun _ _ _ _ _ => rfl)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIUH_rd5 (Hb x)) (leanPRUH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIUH_rdE (hHb x)) (leanPRUH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIUH_isProg (Hb x))
      (leanProgRUH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetNXu Hb A ext hA hX x ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, for any extractor on the tables with the extra table. -/
theorem distPN_budgetUXI' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
        (leanProgRUX Hb) (verILUX Hb) (verRLUX Hb) ext i ω τ) := by
  have h := (distN_budgetUX' Hb A ext hHb hA hX i ω τ).comp
    (fun o : Bytes => pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω)) ω (tapeC τ) i).1)
      (some o))
  -- (the unbound parameters have the `H₂³` table type of the shared tables)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

/-- **The budget of a redemption hop**, for any extractor on the tables with the extra table. -/
theorem distPN_budgetUXR' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
        (leanProgRUX Hb) (verILUX Hb) (verRLUX Hb) ext i ω τ) := by
  have h := distPN_budgetUXI' Hb A ext hHb hA hX i ω τ
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

end Hops

/-! ## Unbound non-malleability for `U` tokens and `M` redemptions with `ROM/`'s plain
extraction -/

section Theorem

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomUN` on the reduction's queries. -/
noncomputable def extRomUN (q : Kind → ℕ) (qE nG : ℕ) :
    ExtN U M Tab3 (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :=
  extLN ansPN (QBudT q qE nG) logQUm (eRomUN (U + M))

variable (A : ThiefN U M Tab3 (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability and no squatting for `U` tokens and `M` redemptions with `ROM/`'s
plain extraction** (function rows, `M = Moussaka.M`, `L ≥ 9749`): as `nmUN_leanX_hit`, for a
`HitWfN` adversary whose output redemptions have the Anchor keys of `kt` (`hk`) and whose last
stage is the run on the `N = U + M` slices and the tables of an oracle computation with at most
`q k` hash queries of kind `k`, `nG` in all and `q_E` cipher cells (`hA`), and `ROM/`'s
straight-line extractor on the reduction's queries (`extRomUN`); plain extraction is no longer a
hypothesis, and the extractor's read budget is proved (`stageBudgetNX_extRomUN`):

    Pr[BadN] ≤ U·εz(pI; q') + M·εz(pR; q') + Σ_i δ_i + ε_rom
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶)
      + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)),

`ε_rom = epsRomU (q + N·qPre) (q_E + N·cells(pR)) (nG + N·338)` and `q' = (q h3 + q h3,
q h5 + (q h5 + N·312) + 312 + (N − 1)·624, q_E + (q_E + N·cells(pR) + 4608) + N·4607)`. The PRF
bound (`hprf`) stays a hypothesis, as in `nmUN_leanX_hit`. -/
theorem nmUN_lean_rom (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE nG) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) ≤
      U * ZKRow.εz (Blk → Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Blk → Blk) pR (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE nG) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE nG) h)) := by
  have hSB : ∀ reqs reds, StageBudgetNX (A.out reqs reds) (q .h3) (q .h5) qE := fun reqs reds => by
    obtain ⟨oa, hb, hF⟩ := hA reqs reds
    rw [hF]
    exact stageBudgetNX_runTN hb.1
  have hX : ∀ l, StageBudgetNX (extRomUN q qE nG l (opN A l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pR + 4608) :=
    fun l => stageBudgetNX_extRomUN (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) →
      ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) → UOp,
      AdmLN (QBudT q qE nG) ansPN F →
      Hit.AdmHitN (R := Blk → Blk) (p := Privacy.Moussaka.pI) (L := L) (M := Arith.Moussaka.M)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTN hb.1
  have hmv := ((progMovesN_hitU (U := U) (M := M) (R := Blk → Blk) hL (q .mu) (q .h21)
    (q .h22)).mono hAH).fresh_mono (Fresh' := FreshKNU kt) fun _ _ h => h.1
  exact nmUN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIUX hbX) (leanPRUX hbX)
    (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX) (verILUX hbX) (verRLUX hbX)
    (extRomUN q qE nG) (leanPIUX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRUX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPN_budgetUXI' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPN_budgetUXR' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_okKU A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
      (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG) hw hk
      (weakSEN_of_plainL progQUm (patch2 Privacy.Moussaka.pI) logQUm
        (plainSENL_romU kt hL _ _ _ _) hmv progU_sndX hpatchUm hlogUm logQUm_none
        fun oa ys hl h => hl ▸ qBudT_redQNu h ys)
      fun _ => hA _ _) pts hpts hprf

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions with `ROM/`'s plain
extraction**, the hops' budgets simplified (`cells(pR) = 101372`): `nmUN_lean_rom` with

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·105979 + 4608),   N = U + M. -/
theorem nmUN_lean_rom' (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE nG) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        M * ZKRow.εz (Blk → Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE nG) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE nG) h)) := by
  have h := nmUN_lean_rom A hw hk hL hA pts hpts hprf
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 105979 + 4608 := by
    rw [verifyCellBound_pRU]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

/-! ## One token and one redemption -/

section One

variable (A : ThiefN 1 1 Tab3 (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for one token and one redemption with `ROM/`'s plain extraction**
(`nmUN_lean_rom'` at `U = M = 1`): the programming term is
`2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)` (`two_epsHitN`), and

    q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 216566),
    ε_rom = epsRomU (q + 2·qPre) (q_E + 2·cells(pR)) (nG + 676). -/
theorem nmUN_lean_rom_one (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (1 + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE nG) h) pts b) ≤ εprf) :
    pr (TapeN 1 1 (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) ≤
      ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 216566) +
        ZKRow.εz (Blk → Blk) pR (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 216566) +
        ∑ i, pr (TapeN 1 1 (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomU (q + 2 • qPre) (qE + 2 * verifyCellBound pR) (nG + 676)).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin 1, (εprf + (1 + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE nG) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE nG) h)) := by
  have h := nmUN_lean_rom' A hw hk hL hA pts hpts hprf
  have e5 : 2 * q .h5 + (1 + 1) * 312 + 312 + (1 + 1 - 1) * 624 = 2 * q .h5 + 1560 := by omega
  have eE : 2 * qE + (1 + 1) * 105979 + 4608 = 2 * qE + 216566 := by omega
  have eN : (1 + 1 : ℕ) = 2 := rfl
  rw [e5, eE, two_epsHitN] at h
  simpa only [Nat.cast_one, one_mul, eN, show (2 : ℕ) * 338 = 676 from rfl] using h

end One

end VoleMole.Theft.MoussakaUnbound
