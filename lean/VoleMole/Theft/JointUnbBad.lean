import VoleMole.Theft.JointBad
import VoleMole.Theft.PlainUnboundManyRom

/-!
# The unbound non-malleability event as one game reader's event

As `Theft/JointBad.lean` does for Ratatouille's theft event, the event `BadN` of the unbound game
NM-U^{U,M} (`Theft/MoussakaUnboundMany.lean`) with `ROM/`'s extractor `extRomUN` is shown to be
read by one **consistent game reader** (`GRd`), for an adversary whose last stage is the run of an
oracle computation (`AdmLN`):

* **`fdPts`, `fd_congrP`** (any forged statement and proof `f : Hit.FD`, any `M`): `ROM/`'s
  extraction (`rOut`, `candOf`) reads the cipher only at the query list's cells and at the CTR
  blocks of `f`'s `iv` of the zero key, the cells' keys and the reconstruction's nodes; the
  Ratatouille `eRom_congrP` (`Theft/JointExt.lean`) is this at `Hit.Rata.fd A op`;
* **`eRomU_congrP`**, `romPtsU_congr`: the same for the unbound extractor `eRomU` at `fdU op`;
* `oaN`, **`qsJ`**, `extRomUN_eq`: the extractor's query list as runs on `ansPN` (the patches'
  prefix computations `vQUm`, then the last stage);
* **`runsGRd`** (the runs), **`chkGRd`** (the verifier on the operation, issuance at `pI` and
  redemption at `pR` on the tables of Moussaka's `pI`, and the extractor), **`badGRd`**: consistent
  (`badGRd_cons`), and **`badGRd_reads`**: it reads `BadN` with `extRomUN`, the hit of an honest
  token included (`HitOp` is a function of the secrets, the operation and the extracted witness);
* the budgets (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`): each slice and all slices together at
  `q h3` keys (`T₃`); `H₅` at `N·312 + q h5 + 312`; the cipher at
  `2·(N·cells(pR) + q_E) + 9215` keys and classes (`c_E`), `cells(pR) = 101372`.
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## `ROM/`'s extraction at points, for any forged statement and proof -/

section Fd

open VoleMole.Theft.Ratatouille (rOut ctOf cLog_congr logKeys_cLog_subset decE_of_decC)

variable {L M : ℕ}

/-- The `iv` of a forged statement and proof (with the extra table's `H₄`, `μ₁`). -/
noncomputable def fdIv (f : Hit.FD) (x : XTab L M) : ByteArray :=
  ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))

/-- **The keys the extraction reads at the forged `iv`**: the zero key, the query list's cells'
keys, the reconstruction's nodes. -/
noncomputable def fdKeysP (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    rdKeys E (fdIv f x) (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩))

/-- **The points the extraction reads**: the query list's cells, and `fdKeysP` at the CTR blocks
of the forged `iv`. -/
noncomputable def fdPts (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    Finset (Blk × Blk) :=
  (qs.filterMap decC).toFinset ∪ ptsOf (fdKeysP f qs E x) (fdIv f x)

lemma card_fdKeysP_le (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    (fdKeysP f qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (rdKeys_card E (fdIv f x)
      (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

set_option maxHeartbeats 1000000 in
/-- **The extraction reads the cipher only at `fdPts`**: the extraction's output (`rOut`) and its
candidates (`candOf`) agree on tables that agree there. -/
theorem fd_congrP (f : Hit.FD) (qs : List DomIC) {E E' : Blk → Blk → Blk} (x : XTab L M)
    (h : ∀ kz ∈ fdPts f qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    rOut f.1 f.2 (hbX x) (ctOf E') (cLog (ctOf E') qs) =
        rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs) ∧
      candOf (ctOf E') f.1 (rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs)) =
        candOf (ctOf E) f.1 (rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs)) := by
  have hc : cLog (ctOf E') qs = cLog (ctOf E) qs :=
    (cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      exact h c (mem_union_left _ (mem_dec hc rfl))).symm
  rw [hc]
  have hP : ∀ k ∈ fdKeysP f qs E x, PtsAgree E E' k (fdIv f x) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨hk, c, t, rfl⟩))
  unfold fdKeysP fdIv at hP
  generalize cLog (ctOf E) qs = log at hc ⊢
  have hsub : logKeys log ⊆ (qs.filterMap decE).toFinset := hc ▸ logKeys_cLog_subset _ _
  set iv := ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))
  have hk : keysOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) =
      keysOf log (ctOf E') iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) :=
    keysOf_congrP (E := ctOf E) (E' := ctOf E') (iv := iv) fun k hk' => by
      rcases mem_union.1 hk' with hk' | hk'
      · exact hP k (mem_insert_of_mem (mem_union_left _ (hsub hk')))
      · exact hP k (mem_insert_of_mem (mem_union_right _ hk'))
  have hkn : knownOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩) =
      knownOf log (ctOf E') iv (Proof.opening ⟨f.1.params, f.2⟩) :=
    knownOf_congrP (E := ctOf E) (E' := ctOf E') (iv := iv)
      (fun k hk' => hP k (mem_insert_of_mem (mem_union_left _ (hsub hk')))) _
  have hr : rOut f.1 f.2 (hbX x) (ctOf E') log = rOut f.1 f.2 (hbX x) (ctOf E) log := by
    unfold rOut
    rw [← hk, ← hkn]
  refine ⟨hr, ?_⟩
  have hu0 : ∀ (i : Fin BAVC.tau) (j : ℕ) (corr : ℕ → ByteArray),
      @uBit (icPrg (ctOf E').cipher) f.1.params iv corr (keysOf log (ctOf E) iv
        (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) i j =
      @uBit (icPrg (ctOf E).cipher) f.1.params iv corr (keysOf log (ctOf E) iv
        (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) i j := by
    intro i j corr
    refine (uBit_congrP (E := (ctOf E).cipher) (E' := (ctOf E').cipher) j fun j' _ _ => ?_).symm
    have hrow := keysOf_row log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) i j'
    have hmem : blk 16 (keysOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩)
        (Proof.delta ⟨f.1.params, f.2⟩) i j') ∈ insert zeroRow ((qs.filterMap decE).toFinset ∪
          rdKeys E iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) := by
      rcases mem_insert.1 hrow with hz | hl
      · rw [hz]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (hsub hl))
    exact hP _ hmem
  have ek : (outChain (rOut f.1 f.2 (hbX x) (ctOf E) log)).keys = keysOf log (ctOf E) iv
      (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) := rfl
  have ei : (outChain (rOut f.1 f.2 (hbX x) (ctOf E) log)).iv = iv := rfl
  funext i
  unfold candOf Chain.u
  simp only [ek, ei, hu0]

/-- **Tables that agree at `fdPts` have the same points.** -/
theorem fdPts_congr (f : Hit.FD) (qs : List DomIC) {E E' : Blk → Blk → Blk} (x : XTab L M)
    (h : ∀ kz ∈ fdPts f qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    fdPts f qs E' x = fdPts f qs E x := by
  have hA : RecAgreeP E E' (fdIv f x) (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨mem_insert_of_mem (mem_union_right _ hk), c, t, rfl⟩))
  unfold fdPts fdKeysP
  rw [rdKeys_ic_congrP hA]

end Fd

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Ratatouille (qPre qPre_h3 qPre_h5 card_runsN_le image_decC_subset
  countP_flatMap_qlog_le)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## `eRomU` at points -/

section ERomU

variable {L : ℕ}

/-- **The points `eRomU` reads**: `fdPts` of the operation's statement and proof. -/
noncomputable def romPtsU (op : UOp) (qs : List DomIC) (E : Blk → Blk → Blk)
    (x : XTab L Arith.Moussaka.M) : Finset (Blk × Blk) :=
  fdPts (fdU op) qs E x

/-- **`eRomU` reads neither the slices nor `H₅`, and the cipher only at `romPtsU`.** -/
theorem eRomU_congrP (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : UOp) (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {E E' : Blk → Blk → Blk}
    (x : XTab L Arith.Moussaka.M) (h : ∀ kz ∈ romPtsU op qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    eRomU p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRomU p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  obtain ⟨h1, h2⟩ := fd_congrP (fdU op) qs x h
  show pickU _ _ _ = pickU _ _ _
  dsimp only
  rw [h1, h2]

theorem romPtsU_congr (op : UOp) (qs : List DomIC) {E E' : Blk → Blk → Blk}
    (x : XTab L Arith.Moussaka.M) (h : ∀ kz ∈ romPtsU op qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    romPtsU op qs E' x = romPtsU op qs E x :=
  fdPts_congr (fdU op) qs x h

end ERomU

/-! ## The extractor's query list as runs on `ansPN` -/

section Bad

variable {U M L : ℕ}

/-- The unbound games' shared tables (function rows). -/
abbrev TabU (L : ℕ) := ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)

/-- **The patches' prefix computations do not read `H₂³`.** -/
lemma qlog_vQUm_G2 (e : Option (UI × Bytes)) (t : TabU L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabU L)) (vQUm e) = qlog (ansP zT zT t) (vQUm e) := by
  have h0 : ∀ f : (d : DomIC) → AnsIC d,
      qlog f (pure ByteArray.empty : OracleComp specIC ByteArray) = [] := fun _ => rfl
  rcases e with _ | ⟨x | x, π⟩
  · exact (h0 _).trans (h0 _).symm
  · simp only [vQUm]
    exact qlog_vPreIC_G2 zT zT t (fun _ => 0) CrtGen.tables (Privacy.MoussakaUnbound.stI x)
      (toBA π)
  · simp only [vQUm]
    exact qlog_vPreIC_G2 zT zT t (fun _ => 0) CrtGen.tables (Privacy.MoussakaUnbound.stR x)
      (toBA π)

/-- **The patches' prefix computations are runs on the game's answers.** -/
lemma qlog_vQUm_N {N : ℕ} (e : Option (UI × Bytes)) (gs : Fin N → Tab3) (t : TabU L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabU L)) (vQUm e) = qlog (ansPN gs t) (vQUm e) := by
  rw [qlog_vQUm_G2, (noH3_ansPN (vQUm e) gs zT zT t (noH3_of_kind (qBud_vQUm e).1 qPre_h3 _)).1]

variable (A : ThiefN U M Tab3 (TabU L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds))

include hA in
lemma admLN_opN (l : Log) : AdmLN (QBudT q qE nG) ansPN (opN A l) :=
  hA _ _

/-- **The last stage's computation**, as `extLN` chooses it. -/
noncomputable def oaN (l : Log) : OracleComp specIC UOp :=
  (admLN_opN A hA l).choose

lemma oaN_bud (l : Log) : QBudT q qE nG (oaN A hA l) :=
  (admLN_opN A hA l).choose_spec.1

/-- **The operation is the run of `oaN`.** -/
lemma opN_eq (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    opN A l gs t = runT (ansPN gs t) (oaN A hA l) :=
  congrFun (congrFun (admLN_opN A hA l).choose_spec.2 gs) t

/-- **The extractor's query list**, as runs on `ansPN`: the patches' prefixes of the first `N` log
entries (most recent first), then the last stage's queries. -/
noncomputable def qsJ (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) : List DomIC :=
  ((l.take (U + M)).reverse.flatMap fun e => qlog (ansPN gs t) (vQUm e)) ++
    qlog (ansPN gs t) (oaN A hA l)

/-- **`extRomUN` is `eRomU` on the run and `qsJ`.** -/
lemma extRomUN_eq (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    extRomUN q qE nG l (opN A l) gs t =
      eRomU none none (runT (ansPN gs t) (oaN A hA l)) (qsJ A hA l gs t) zT zT t.2 := by
  classical
  unfold extRomUN extLN
  simp only [dite_eq_left (admLN_opN A hA l)]
  unfold eRomUN
  rw [opN_eq A hA l gs t]
  congr 1
  unfold qsJ logsL
  congr 1
  exact List.flatMap_congr fun e _ => (logQUm_eq e gs t.2).trans (qlog_vQUm_N e gs t)

/-! ## The runs' reader -/

/-- **The reader of the extractor's query list**: the slice keys, `H₅` keys and cells of `qsJ`. -/
noncomputable def runsGRd :
    GRd (SecN U) (Option (UI × Bytes)) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) (U + M) where
  Q3 _ l gs t j := ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset
  Q5 _ l gs t := ((qsJ A hA l gs t).filterMap dec5).toFinset
  QE _ l gs t := ((qsJ A hA l gs t).filterMap decC).toFinset

/-- **Agreement at the runs' reads gives the same query list and operation.** -/
lemma runsGRd_agree {ω : SecN U} {l : Log} {gs gs' : Fin (U + M) → Tab3} {t t' : TabU L}
    (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    qsJ A hA l gs' t' = qsJ A hA l gs t ∧
      runT (ansPN gs' t') (oaN A hA l) = runT (ansPN gs t) (oaN A hA l) := by
  have hd : ∀ d ∈ qsJ A hA l gs t, ansPN gs t d = ansPN gs' t' d := fun d hd =>
    ansPN_agree gs gs' t t' h.1 h.2.1 d (fun j k hk => h.2.2.1 j k (mem_dec hd hk))
      (fun k hk => h.2.2.2.1 k (mem_dec hd hk)) (fun kz hkz => h.2.2.2.2 kz (mem_dec hd hkz))
  have e1 := flatMap_qlog_congr' vQUm (ansPN gs t) (ansPN gs' t') ((l.take (U + M)).reverse)
    fun d hd' => hd d (List.mem_append_left _ hd')
  have e2 := runT_congr (oaN A hA l) (ansPN gs t) (ansPN gs' t')
    fun d hd' => hd d (List.mem_append_right _ hd')
  refine ⟨?_, e2.2⟩
  unfold qsJ
  rw [e1, e2.1]

/-- **The runs' reader is consistent.** -/
theorem runsGRd_cons : (runsGRd A hA).Cons := by
  intro ω l gs t gs' t' h
  have e := (runsGRd_agree A hA h).1
  refine ⟨?_, ?_, ?_⟩
  · funext j
    show ((qsJ A hA l gs' t').filterMap (dec3N j)).toFinset = _
    rw [e]; rfl
  · show ((qsJ A hA l gs' t').filterMap dec5).toFinset = _
    rw [e]; rfl
  · show ((qsJ A hA l gs' t').filterMap decC).toFinset = _
    rw [e]; rfl

/-- The value the runs' reader reads: the operation and the query list. -/
noncomputable def runsVal (v : SecN U × Log × (Fin (U + M) → Tab3) × TabU L) : UOp × List DomIC :=
  (runT (ansPN v.2.2.1 v.2.2.2) (oaN A hA v.2.1), qsJ A hA v.2.1 v.2.2.1 v.2.2.2)

lemma runsGRd_val (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L)
    (gs' : Fin (U + M) → Tab3) (t' : TabU L) (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    runsVal A hA (ω, l, gs', t') = runsVal A hA (ω, l, gs, t) := by
  obtain ⟨e1, e2⟩ := runsGRd_agree A hA h
  simp only [runsVal, e1, e2]

/-! ## The verifier and the extractor at an operation and a query list -/

/-- The verifier's `H₅` keys on an operation. -/
noncomputable def verQ5 (op : UOp) (t : TabU L) : Finset (ZK.Sim.Bytes 37) :=
  match op with
  | .issue req ci => verKeys5 (p := pI) (Hb := hbX t.2.2)
      (Privacy.MoussakaUnbound.stI (stOfI req ci)) (toBA (req.drop uovM)) (shOf t)
  | .redeem S' req ci cr cd => verKeys5 (p := pR) (Hb := hbX t.2.2)
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) (shOf t)

/-- The verifier's cipher points on an operation. -/
noncomputable def verQE (op : UOp) (t : TabU L) : Finset (Blk × Blk) :=
  match op with
  | .issue req ci => verPtsE pI (hbX t.2.2) (Privacy.MoussakaUnbound.stI (stOfI req ci))
      (toBA (req.drop uovM)) (shOf t)
  | .redeem S' req ci cr cd => verPtsE pR (hbX t.2.2)
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) (shOf t)

/-- (Stated for a variable row type: at `R = Blk → Blk` the kernel would check the unfolding of
`verILUH` by evaluating the verifier.) -/
lemma verILUH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : IssueInstance) (pf : Bytes)
    (s s' : ShM R)
    (h : verRO pI Hb (Privacy.MoussakaUnbound.stI x) (toBA pf) s' =
      verRO pI Hb (Privacy.MoussakaUnbound.stI x) (toBA pf) s) :
    verILUH Hb x pf s' = verILUH Hb x pf s :=
  congrArg Transcript.accept h

lemma verRLUH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : RedeemInstance) (pf : Bytes)
    (s s' : ShM R)
    (h : verRO pR Hb (Privacy.MoussakaUnbound.stR x) (toBA pf) s' =
      verRO pR Hb (Privacy.MoussakaUnbound.stR x) (toBA pf) s) :
    verRLUH Hb x pf s' = verRLUH Hb x pf s :=
  congrArg Transcript.accept h

/-- **The verifier on an operation reads at its points, consistently.** -/
lemma ver_cons (op : UOp) (t t' : TabU L) (h2 : t'.1 = t.1) (hx : t'.2.2 = t.2.2)
    (h5 : ∀ k ∈ verQ5 op t, t.2.1.1 k = t'.2.1.1 k)
    (hE : ∀ kz ∈ verQE op t, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2) :
    (AccOp (verILUX hbX) (verRLUX hbX) op t' ↔ AccOp (verILUX hbX) (verRLUX hbX) op t) ∧
      verQ5 op t' = verQ5 op t ∧ verQE op t' = verQE op t := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pI) (Hb := hbX t.2.2)
      (Privacy.MoussakaUnbound.stI (stOfI req ci)) (toBA (req.drop uovM)) (shOf t) (shOf t') h2
      h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : verILUX hbX (stOfI req ci) (req.drop uovM) t' =
          verILUX hbX (stOfI req ci) (req.drop uovM) t := by
        unfold verILUX
        rw [hx]
        exact verILUH_congr _ _ _ _ _ a
      show _ ∧ _ ∧ verILUX hbX _ _ t' = true ↔ _ ∧ _ ∧ verILUX hbX _ _ t = true
      rw [a3]
    · show verKeys5 (p := pI) (Hb := hbX t'.2.2) _ _ (shOf t') =
        verKeys5 (p := pI) (Hb := hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact b
    · show verPtsE pI (hbX t'.2.2) _ _ (shOf t') = verPtsE pI (hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact e
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pR) (Hb := hbX t.2.2)
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) (shOf t)
      (shOf t') h2 h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : verRLUX hbX (stOfR S' req ci cr cd) (req.drop nfBytes) t' =
          verRLUX hbX (stOfR S' req ci cr cd) (req.drop nfBytes) t := by
        unfold verRLUX
        rw [hx]
        exact verRLUH_congr _ _ _ _ _ a
      show _ ∧ _ ∧ _ ∧ verRLUX hbX _ _ t' = true ↔ _ ∧ _ ∧ _ ∧ verRLUX hbX _ _ t = true
      rw [a3]
    · show verKeys5 (p := pR) (Hb := hbX t'.2.2) _ _ (shOf t') =
        verKeys5 (p := pR) (Hb := hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact b
    · show verPtsE pR (hbX t'.2.2) _ _ (shOf t') = verPtsE pR (hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact e

/-- **The reader of the verifier and the extractor** at an operation and a query list. -/
noncomputable def chkGRd (y : UOp × List DomIC) :
    GRd (SecN U) (Option (UI × Bytes)) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) (U + M) where
  Q3 _ _ _ _ _ := ∅
  Q5 _ _ _ t := verQ5 y.1 t
  QE _ _ _ t := verQE y.1 t ∪ romPtsU y.1 y.2 t.2.1.2 t.2.2

lemma chkGRd_agree {y : UOp × List DomIC} {ω : SecN U} {l : Log} {gs gs' : Fin (U + M) → Tab3}
    {t t' : TabU L} (h : (chkGRd (U := U) (M := M) y).Agree ω l gs t gs' t') :
    ((AccOp (verILUX hbX) (verRLUX hbX) y.1 t' ↔ AccOp (verILUX hbX) (verRLUX hbX) y.1 t) ∧
      verQ5 y.1 t' = verQ5 y.1 t ∧ verQE y.1 t' = verQE y.1 t) ∧
      romPtsU y.1 y.2 t'.2.1.2 t'.2.2 = romPtsU y.1 y.2 t.2.1.2 t.2.2 ∧
      eRomU none none y.1 y.2 zT zT t'.2 = eRomU none none y.1 y.2 zT zT t.2 := by
  have hv := ver_cons y.1 t t' h.1 h.2.1 h.2.2.2.1
    fun kz hkz => h.2.2.2.2 kz (mem_union_left _ hkz)
  have hr : ∀ kz ∈ romPtsU y.1 y.2 t.2.1.2 t.2.2, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2 :=
    fun kz hkz => h.2.2.2.2 kz (mem_union_right _ hkz)
  refine ⟨hv, ?_, ?_⟩
  · rw [h.2.1]; exact romPtsU_congr y.1 y.2 t.2.2 hr
  · obtain ⟨G2, ⟨G5, E⟩, x⟩ := t
    obtain ⟨G2', ⟨G5', E'⟩, x'⟩ := t'
    simp only at h hr ⊢
    obtain rfl : x' = x := h.2.1
    exact eRomU_congrP none none y.1 y.2 zT zT zT zT G5 G5' x' hr

/-- **The verifier's and the extractor's reader is consistent.** -/
theorem chkGRd_cons (y : UOp × List DomIC) : (chkGRd (U := U) (M := M) (L := L) y).Cons := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨-, e5, eE⟩, er, -⟩ := chkGRd_agree h
  refine ⟨rfl, e5, ?_⟩
  show verQE y.1 t' ∪ romPtsU y.1 y.2 t'.2.1.2 t'.2.2 = _
  rw [eE, er]; rfl

/-! ## The event as the composed reader's event -/

/-- **The event at an operation and a query list**: `BadN` with the operation and the extractor's
query list given (`runsVal` supplies them). -/
def chkEv (y : UOp × List DomIC) (v : SecN U × Log × (Fin (U + M) → Tab3) × TabU L) : Prop :=
  AccOp (verILUX hbX) (verRLUX hbX) y.1 v.2.2.2 ∧ FreshOpN v.2.1 y.1 ∧
    (¬ RelOp y.1 (eRomU none none y.1 y.2 zT zT v.2.2.2.2) ∨
      ∃ h, HitOp (tOfN A v.1 h) (List.ofFn (v.1 h).1) y.1
        (eRomU none none y.1 y.2 zT zT v.2.2.2.2))

/-- **The verifier's and the extractor's reader reads the event at its value.** -/
theorem chkGRd_reads (y : UOp × List DomIC) : (chkGRd (U := U) (M := M) y).Reads (chkEv A y) := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨ea, -, -⟩, -, ee⟩ := chkGRd_agree h
  simp only [chkEv, ee, ea]

/-- **The composed reader of the event**: the runs (the last stage and the patches' prefixes),
then the verifier and the extractor at the operation and the query list. -/
noncomputable def badGRd :
    GRd (SecN U) (Option (UI × Bytes)) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M) (U + M) :=
  GRd.seq (runsGRd A hA) (runsVal A hA) chkGRd

/-- **The composed reader is consistent.** -/
theorem badGRd_cons : (badGRd A hA).Cons :=
  GRd.seq_cons (runsGRd_cons A hA) (runsGRd_val A hA) chkGRd_cons

/-- **`BadN` with `ROM/`'s extractor is the event at the runs' value.** -/
theorem badN_iff (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG) ω l gs t ↔
      chkEv A (runsVal A hA (ω, l, gs, t)) (ω, l, gs, t) := by
  unfold BadN accN freshN relN hitN hitH
  rw [extRomUN_eq A hA, opN_eq A hA]
  rfl

/-- **The composed reader reads the event.** -/
theorem badGRd_reads :
    (badGRd A hA).Reads (fun v => BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG)
      v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  have h := GRd.seq_reads (R₁ := runsGRd A hA) (runsGRd_val A hA) (chkEv A) (chkGRd_reads A)
  intro ω l gs t gs' t' hag
  show BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG) ω l gs' t' ↔
    BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG) ω l gs t
  rw [badN_iff A hA, badN_iff A hA]
  exact h ω l gs t gs' t' hag

/-! ## The budgets -/

lemma length_takeRev_le (l : Log) : ((l.take (U + M)).reverse).length ≤ U + M := by
  simp only [List.length_reverse, List.length_take]; omega

/-- The extractor's query list has at most `N·cells(pR) + q_E` cipher queries' keys. -/
lemma card_qsJ_decE_le (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    ((qsJ A hA l gs t).filterMap decE).toFinset.card ≤ (U + M) * verifyCellBound pR + qE := by
  have := card_runsN_le decE (fun d => d.isRight) (fun _ _ h => decE_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQUm e).2) (oaN_bud A hA l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pR) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

lemma card_qsJ_decC_le (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    ((qsJ A hA l gs t).filterMap decC).toFinset.card ≤ (U + M) * verifyCellBound pR + qE := by
  have := card_runsN_le decC (fun d => d.isRight) (fun _ _ h => decC_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQUm e).2) (oaN_bud A hA l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pR) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

lemma card_verQ5_le (op : UOp) (t : TabU L) : (verQ5 op t).card ≤ 312 := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · exact (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).h5 zT (shOf t)
  · exact (verPtRd_bnd (p := pR) (Hb := hbX t.2.2) _ _).h5 zT (shOf t)

lemma card_verQE_keys_le (op : UOp) (t : TabU L) :
    (ptCls (verQE op t)).card ≤ 4607 ∧ ((verQE op t).image Prod.fst).card ≤ 4607 := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).hE zT (shOf t)⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pR) (Hb := hbX t.2.2) _ _).hE zT (shOf t)⟩

/-- The composed reader's cipher points: the query list's cells, the verifier's, and the
extractor's at the forged `iv`. -/
lemma badGRd_QE_subset (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    (badGRd A hA).QE ω l gs t ⊆ ((qsJ A hA l gs t).filterMap decC).toFinset ∪
      verQE (runsVal A hA (ω, l, gs, t)).1 t ∪
      ptsOf (fdKeysP (fdU (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t) t.2.1.2 t.2.2)
        (fdIv (fdU (runsVal A hA (ω, l, gs, t)).1) t.2.2) := by
  intro kz hkz
  simp only [badGRd, GRd.seq, runsGRd, chkGRd, romPtsU, fdPts, mem_union] at hkz ⊢
  tauto

/-- **The composed reader's budgets**: each slice at `q h3` keys, `H₅` at
`N·312 + q h5 + 312`, the cipher at `2·(N·cells(pR) + q_E) + 9215` keys. -/
theorem badGRd_bnd :
    (badGRd A hA).Bnd (q .h3) ((U + M) * 312 + q .h5 + 312)
      (2 * ((U + M) * verifyCellBound pR + qE) + 9215) := by
  classical
  refine ⟨fun ω l gs t j => ?_, fun ω l gs t => ?_, fun ω l gs t => ?_⟩
  · show (((qsJ A hA l gs t).filterMap (dec3N j)).toFinset ∪ ∅).card ≤ q .h3
    rw [union_empty]
    have := card_runsN_le (dec3N j) (kindB .h3) (fun _ _ h => dec3N_kind h) (ansPN gs t)
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQUm e).1 .h3)
      (isQueryBoundP_kind (oaN_bud A hA l).1.1 .h3) ((l.take (U + M)).reverse)
    rw [qPre_h3, mul_zero, zero_add] at this
    exact this
  · show (((qsJ A hA l gs t).filterMap dec5).toFinset ∪
      verQ5 (runsVal A hA (ω, l, gs, t)).1 t).card ≤ _
    have h1 := card_runsN_le dec5 (kindB .h5) (fun _ _ h => dec5_kind h) (ansPN gs t)
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQUm e).1 .h5)
      (isQueryBoundP_kind (oaN_bud A hA l).1.1 .h5) ((l.take (U + M)).reverse)
    rw [qPre_h5] at h1
    have hl := Nat.mul_le_mul_right 312 (length_takeRev_le (U := U) (M := M) l)
    have h2 := card_verQ5_le (runsVal A hA (ω, l, gs, t)).1 t
    refine (card_union_le _ _).trans ?_
    unfold qsJ at *
    omega
  · refine (card_le_card (image_subset_image (badGRd_QE_subset A hA ω l gs t))).trans ?_
    rw [image_union, image_union]
    have a1 := (card_le_card (image_decC_subset (qsJ A hA l gs t))).trans
      (card_qsJ_decE_le A hA l gs t)
    have a2 := (card_verQE_keys_le (runsVal A hA (ω, l, gs, t)).1 t).2
    have a3 := (card_fst_ptsOf_le (K := fdKeysP (fdU (runsVal A hA (ω, l, gs, t)).1)
      (qsJ A hA l gs t) t.2.1.2 t.2.2) (iv := fdIv (fdU (runsVal A hA (ω, l, gs, t)).1) t.2.2)).trans
      ((card_fdKeysP_le _ _ _ _).trans (Nat.add_le_add_right (card_qsJ_decE_le A hA l gs t) _))
    have u1 := card_union_le (((qsJ A hA l gs t).filterMap decC).toFinset.image Prod.fst ∪
      (verQE (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
      ((ptsOf (fdKeysP (fdU (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t) t.2.1.2 t.2.2)
        (fdIv (fdU (runsVal A hA (ω, l, gs, t)).1) t.2.2)).image Prod.fst)
    have u2 := card_union_le (((qsJ A hA l gs t).filterMap decC).toFinset.image Prod.fst)
      ((verQE (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
    omega

/-- **`T₃`: all slices together are read at most at the last stage's `q h3` slice queries.** -/
theorem badGRd_T3 (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    ∑ j, ((badGRd A hA).Q3 ω l gs t j).card ≤ q .h3 := by
  classical
  have e : ∀ j, ((badGRd A hA).Q3 ω l gs t j) =
      ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset := fun j => by
    show ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset ∪ ∅ = _
    rw [union_empty]
  simp only [e]
  refine (sum_card_dec3N_le _).trans ?_
  unfold qsJ
  rw [List.countP_append]
  have h1 := countP_flatMap_qlog_le vQUm (ansPN gs t) (kindB .h3)
    (fun e => isQueryBoundP_kind (qBud_vQUm e).1 .h3) ((l.take (U + M)).reverse)
  have h2 := countP_qlog_le (oaN A hA l) (ansPN gs t) (kindB .h3)
    (isQueryBoundP_kind (oaN_bud A hA l).1.1 .h3)
  rw [qPre_h3, mul_zero] at h1
  omega

/-- **`c_E`: the classes `(key, middle bytes)` of the composed reader's cipher points**: the
query list's cells, the verifier's `4607` keys at one `iv`, and the extractor's keys (the cells'
keys and `4608` more) at the forged proof's `iv`. -/
theorem badGRd_cls (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabU L) :
    (ptCls ((badGRd A hA).QE ω l gs t)).card ≤ 2 * ((U + M) * verifyCellBound pR + qE) + 9215 := by
  classical
  refine (card_le_card (ptCls_mono (badGRd_QE_subset A hA ω l gs t))).trans ?_
  rw [ptCls_union, ptCls_union]
  have a1 := (card_ptCls_le (((qsJ A hA l gs t).filterMap decC).toFinset)).trans
    (card_qsJ_decC_le A hA l gs t)
  have a2 := (card_verQE_keys_le (runsVal A hA (ω, l, gs, t)).1 t).1
  have a3 := (card_ptCls_ptsOf_le (fdKeysP (fdU (runsVal A hA (ω, l, gs, t)).1)
    (qsJ A hA l gs t) t.2.1.2 t.2.2) (fdIv (fdU (runsVal A hA (ω, l, gs, t)).1) t.2.2)).trans
    ((card_fdKeysP_le _ _ _ _).trans (Nat.add_le_add_right (card_qsJ_decE_le A hA l gs t) _))
  have u1 := card_union_le (ptCls ((qsJ A hA l gs t).filterMap decC).toFinset ∪
    ptCls (verQE (runsVal A hA (ω, l, gs, t)).1 t))
    (ptCls (ptsOf (fdKeysP (fdU (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t) t.2.1.2 t.2.2)
      (fdIv (fdU (runsVal A hA (ω, l, gs, t)).1) t.2.2)))
  have u2 := card_union_le (ptCls ((qsJ A hA l gs t).filterMap decC).toFinset)
    (ptCls (verQE (runsVal A hA (ω, l, gs, t)).1 t))
  omega

end Bad

end MoussakaUnbound

end VoleMole.Theft
