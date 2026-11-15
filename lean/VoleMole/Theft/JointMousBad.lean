import VoleMole.Theft.JointBad
import VoleMole.Theft.PlainMousManyRom

/-!
# The redirect event as one game reader's event (Moussaka)

The Moussaka counterpart of `Theft/JointBad.lean`. `real_sim_leN_leanA`
(`Theft/JointLeanSum.lean`) bounds `|Pr_real[Ev] − Pr_sim[Ev]|` for the events `Ev` that one
consistent game reader (`GRd`) reads. The redirect event `BadN` (`Theft/MoussakaMany.lean`) is read
by the adversary's last stage, the verifiers on its operation and `ROM/`'s extractor (`extRomMN`).

* **The extraction at points, for any forgery** (`romIvF`, `romKeysF`, `romPtsF`,
  `rOut_congrP`, `romPtsF_congr`): `eRom_congrP` (`Theft/JointExt.lean`) with the forgery
  `f : Hit.FD` as a parameter, so it serves every protocol whose extractor is `ROM/`'s
  (`rOut`, `candOf` of `fd op`). **`eRomM_congrP`**: Moussaka's `eRomM` reads neither the slices
  nor `H₅`, and the cipher only at `romPtsF (fd op)`.
* **`oaN`, `qsJ`**: the last stage's computation (`extLN`'s choice) and the extractor's query list
  as runs on the game's answers (`extRomMN_eq`).
* **`runsGRd`**, **`chkGRd`**, **`badGRd`** = `GRd.seq runsGRd … chkGRd`: consistent
  (`badGRd_cons`); **`badGRd_reads`**: it reads `BadN` with `extRomMN`.
* the budgets (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`): each slice at `q h3` keys and all slices
  together at `q h3` (`T₃`); `H₅` at `q h5 + N·312 + 312`; the cipher at
  `2·(N·cells(pR) + q_E) + 9215` keys and classes (`c_E`), `cells(pR) = 69116`.
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## `ROM/`'s extraction at points, for any forgery -/

section ERomF

open VoleMole.Theft.Ratatouille (rOut ctOf cLog_congr logKeys_cLog_subset)

variable {L M : ℕ}

/-- The forgery's `iv` (with the extra table's `H₄`, `mu₁`). -/
noncomputable def romIvF (f : Hit.FD) (x : XTab L M) : ByteArray :=
  ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))

/-- **The keys the extraction reads at the forgery's `iv`**: the zero key, the query list's
cells' keys, the reconstruction's nodes. -/
noncomputable def romKeysF (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    rdKeys E (romIvF f x) (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩))

/-- **The points the extraction reads**: the query list's cells, and `romKeysF` at the CTR blocks
of the forgery's `iv`. -/
noncomputable def romPtsF (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    Finset (Blk × Blk) :=
  (qs.filterMap decC).toFinset ∪ ptsOf (romKeysF f qs E x) (romIvF f x)

lemma card_romKeysF_le (f : Hit.FD) (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) :
    (romKeysF f qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (rdKeys_card E (romIvF f x)
      (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

set_option maxHeartbeats 1000000 in
/-- **The extraction reads the cipher only at `romPtsF`**: `rOut` and the candidates of the
forgery `f` agree on tables that agree there. -/
theorem rOut_congrP (f : Hit.FD) (qs : List DomIC) {E E' : Blk → Blk → Blk} (x : XTab L M)
    (h : ∀ kz ∈ romPtsF f qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    rOut f.1 f.2 (hbX x) (ctOf E') (cLog (ctOf E') qs) =
        rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs) ∧
      candOf (ctOf E') f.1 (rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs)) =
        candOf (ctOf E) f.1 (rOut f.1 f.2 (hbX x) (ctOf E) (cLog (ctOf E) qs)) := by
  have hc : cLog (ctOf E') qs = cLog (ctOf E) qs :=
    (cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      exact h c (mem_union_left _ (mem_dec hc rfl))).symm
  rw [hc]
  have hP : ∀ k ∈ romKeysF f qs E x, PtsAgree E E' k (romIvF f x) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨hk, c, t, rfl⟩))
  unfold romKeysF romIvF at hP
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

/-- **Tables that agree at the extraction's points have the same points.** -/
theorem romPtsF_congr (f : Hit.FD) (qs : List DomIC) {E E' : Blk → Blk → Blk} (x : XTab L M)
    (h : ∀ kz ∈ romPtsF f qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    romPtsF f qs E' x = romPtsF f qs E x := by
  have hA : RecAgreeP E E' (romIvF f x) (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨mem_insert_of_mem (mem_union_right _ hk), c, t, rfl⟩))
  unfold romPtsF romKeysF
  rw [rdKeys_ic_congrP hA]

end ERomF

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre qPre_h3 qPre_h5 card_runsN_le countP_flatMap_qlog_le
  decE_of_decC image_decC_subset)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## `eRomM` at points -/

section ERomM

variable {L : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`eRomM` reads neither the slices nor `H₅`, and the cipher only at `romPtsF (fd op)`.** -/
theorem eRomM_congrP (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : MOp) (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {E E' : Blk → Blk → Blk}
    (x : XTab L Arith.Moussaka.M)
    (h : ∀ kz ∈ romPtsF (Hit.Mous.fd op) qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    eRomM p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRomM p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  obtain ⟨h1, h2⟩ := rOut_congrP (Hit.Mous.fd op) qs x h
  show pickM _ _ _ = pickM _ _ _
  dsimp only
  rw [h1, h2]

end ERomM

/-! ## The extractor's query list as runs on `ansPN` -/

section Bad

variable {U M L : ℕ}

/-- The redirect games' shared tables (function rows). -/
abbrev TabM (L : ℕ) := ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)

/-- **The patches' prefix computations do not read `H₂³`.** -/
lemma qlog_vQMm_G2 (e : Option (MI × Bytes)) (t : TabM L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabM L)) (vQMm e) = qlog (ansP zT zT t) (vQMm e) := by
  have h0 : ∀ f : (d : DomIC) → AnsIC d,
      qlog f (pure ByteArray.empty : OracleComp specIC ByteArray) = [] := fun _ => rfl
  rcases e with _ | ⟨x | x, π⟩
  · exact (h0 _).trans (h0 _).symm
  · exact qlog_vPreIC_G2 zT zT t (fun _ => 0) _ _ _
  · exact qlog_vPreIC_G2 zT zT t (fun _ => 0) _ _ _

/-- **The patches' prefix computations are runs on the game's answers.** -/
lemma qlog_vQMm_N {N : ℕ} (e : Option (MI × Bytes)) (gs : Fin N → Tab3) (t : TabM L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabM L)) (vQMm e) = qlog (ansPN gs t) (vQMm e) := by
  rw [qlog_vQMm_G2, (noH3_ansPN (vQMm e) gs zT zT t (noH3_of_kind (qBud_vQMm e).1 qPre_h3 _)).1]

variable (A : ThiefN U M Tab3 (TabM L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds))

include hA in
lemma admLN_opN (l : Log) : AdmLN (QBudT q qE nG) ansPN (opN A l) := hA _ _

/-- **The last stage's computation**, as `extLN` chooses it. -/
noncomputable def oaN (l : Log) : OracleComp specIC MOp := (admLN_opN A hA l).choose

lemma oaN_bud (l : Log) : QBudT q qE nG (oaN A hA l) := (admLN_opN A hA l).choose_spec.1

/-- **The operation is the run of `oaN`.** -/
lemma opN_eq (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    opN A l gs t = runT (ansPN gs t) (oaN A hA l) :=
  congrFun (congrFun (admLN_opN A hA l).choose_spec.2 gs) t

/-- **The extractor's query list**, as runs on `ansPN`: the patches' prefixes of the first `N` log
entries (most recent first), then the last stage's queries. -/
noncomputable def qsJ (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) : List DomIC :=
  ((l.take (U + M)).reverse.flatMap fun e => qlog (ansPN gs t) (vQMm e)) ++
    qlog (ansPN gs t) (oaN A hA l)

/-- **`extRomMN` is `eRomM` on the run and `qsJ`.** -/
lemma extRomMN_eq (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    extRomMN q qE nG l (opN A l) gs t =
      eRomM none none (runT (ansPN gs t) (oaN A hA l)) (qsJ A hA l gs t) zT zT t.2 := by
  classical
  unfold extRomMN extLN
  simp only [dite_eq_left (admLN_opN A hA l)]
  unfold eRomMN
  rw [opN_eq A hA l gs t]
  congr 1
  unfold qsJ logsL
  congr 1
  exact List.flatMap_congr fun e _ => (logQMm_eq e gs t.2).trans (qlog_vQMm_N e gs t)

/-! ## The runs' reader -/

/-- **The reader of the extractor's query list**: the slice keys, `H₅` keys and cells of `qsJ`. -/
noncomputable def runsGRd : GRd (SecN U) (Option (MI × Bytes)) pI (XTab L Arith.Moussaka.M) (U + M) where
  Q3 _ l gs t j := ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset
  Q5 _ l gs t := ((qsJ A hA l gs t).filterMap dec5).toFinset
  QE _ l gs t := ((qsJ A hA l gs t).filterMap decC).toFinset

/-- **Agreement at the runs' reads gives the same query list and operation.** -/
lemma runsGRd_agree {ω : SecN U} {l : Log} {gs gs' : Fin (U + M) → Tab3} {t t' : TabM L}
    (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    qsJ A hA l gs' t' = qsJ A hA l gs t ∧
      runT (ansPN gs' t') (oaN A hA l) = runT (ansPN gs t) (oaN A hA l) := by
  have hd : ∀ d ∈ qsJ A hA l gs t, ansPN gs t d = ansPN gs' t' d := fun d hd =>
    ansPN_agree gs gs' t t' h.1 h.2.1 d (fun j k hk => h.2.2.1 j k (mem_dec hd hk))
      (fun k hk => h.2.2.2.1 k (mem_dec hd hk)) (fun kz hkz => h.2.2.2.2 kz (mem_dec hd hkz))
  have e1 := flatMap_qlog_congr' vQMm (ansPN gs t) (ansPN gs' t') ((l.take (U + M)).reverse)
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
noncomputable def runsVal (v : SecN U × Log × (Fin (U + M) → Tab3) × TabM L) : MOp × List DomIC :=
  (runT (ansPN v.2.2.1 v.2.2.2) (oaN A hA v.2.1), qsJ A hA v.2.1 v.2.2.1 v.2.2.2)

lemma runsGRd_val (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L)
    (gs' : Fin (U + M) → Tab3) (t' : TabM L) (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    runsVal A hA (ω, l, gs', t') = runsVal A hA (ω, l, gs, t) := by
  obtain ⟨e1, e2⟩ := runsGRd_agree A hA h
  simp only [runsVal, e1, e2]

/-! ## The verifiers and the extractor at an operation and a query list -/

/-- The verifiers' `H₅` keys on an operation. -/
noncomputable def verQ5 (op : MOp) (t : TabM L) : Finset (ZK.Sim.Bytes 37) :=
  match op with
  | .issue req ci => verKeys5 (p := pI) (Hb := hbX t.2.2) (Privacy.Moussaka.stI (stOfI req ci))
      (toBA (req.drop uovM)) (shOf t)
  | .redeem S' req ci cr cd => verKeys5 (p := pR) (Hb := hbX t.2.2)
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) (shOf (p := pI) t)

/-- The verifiers' cipher points on an operation. -/
noncomputable def verQE (op : MOp) (t : TabM L) : Finset (Blk × Blk) :=
  match op with
  | .issue req ci => verPtsE pI (hbX t.2.2) (Privacy.Moussaka.stI (stOfI req ci))
      (toBA (req.drop uovM)) (shOf t)
  | .redeem S' req ci cr cd => verPtsE pR (hbX t.2.2)
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) (shOf (p := pI) t)

/-- (Stated for a variable row type: at `R = Blk → Blk` the kernel would check the unfolding of
`verILH` by evaluating the verifier.) -/
lemma verILH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : IssueInstance) (pf : Bytes)
    (s s' : ShM R)
    (h : verRO pI Hb (Privacy.Moussaka.stI x) (toBA pf) s' =
      verRO pI Hb (Privacy.Moussaka.stI x) (toBA pf) s) :
    verILH Hb x pf s' = verILH Hb x pf s :=
  congrArg Transcript.accept h

lemma verRLH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : RedeemInstance) (pf : Bytes)
    (s s' : ShM R)
    (h : verRO pR Hb (Privacy.Moussaka.stR x) (toBA pf) s' =
      verRO pR Hb (Privacy.Moussaka.stR x) (toBA pf) s) :
    verRLH Hb x pf s' = verRLH Hb x pf s :=
  congrArg Transcript.accept h

/-- **The verifiers on an operation read at their points, consistently.** -/
lemma ver_cons (op : MOp) (t t' : TabM L) (h2 : t'.1 = t.1) (hx : t'.2.2 = t.2.2)
    (h5 : ∀ k ∈ verQ5 op t, t.2.1.1 k = t'.2.1.1 k)
    (hE : ∀ kz ∈ verQE op t, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2) :
    (AccOp (verILX hbX) (verRLX hbX) op t' ↔ AccOp (verILX hbX) (verRLX hbX) op t) ∧
      verQ5 op t' = verQ5 op t ∧ verQE op t' = verQE op t := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pI) (Hb := hbX t.2.2)
      (Privacy.Moussaka.stI (stOfI req ci)) (toBA (req.drop uovM)) (shOf t) (shOf t') h2 h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : verILX hbX (stOfI req ci) (req.drop uovM) t' =
          verILX hbX (stOfI req ci) (req.drop uovM) t := by
        unfold verILX
        rw [hx]
        exact verILH_congr _ _ _ _ _ a
      show (_ ∧ _ ∧ verILX hbX _ _ t' = true) ↔ (_ ∧ _ ∧ verILX hbX _ _ t = true)
      rw [a3]
    · show verKeys5 (p := pI) (Hb := hbX t'.2.2) _ _ (shOf t') =
        verKeys5 (p := pI) (Hb := hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact b
    · show verPtsE pI (hbX t'.2.2) _ _ (shOf t') = verPtsE pI (hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact e
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pR) (Hb := hbX t.2.2)
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes))
      (shOf (p := pI) t) (shOf (p := pI) t') h2 h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : verRLX hbX (stOfR S' req ci cr cd) (req.drop nfBytes) t' =
          verRLX hbX (stOfR S' req ci cr cd) (req.drop nfBytes) t := by
        unfold verRLX
        rw [hx]
        exact verRLH_congr _ _ _ _ _ a
      show (_ ∧ verRLX hbX _ _ t' = true) ↔ (_ ∧ verRLX hbX _ _ t = true)
      rw [a3]
    · show verKeys5 (p := pR) (Hb := hbX t'.2.2) _ _ (shOf (p := pI) t') =
        verKeys5 (p := pR) (Hb := hbX t.2.2) _ _ (shOf (p := pI) t)
      rw [hx]; exact b
    · show verPtsE pR (hbX t'.2.2) _ _ (shOf (p := pI) t') =
        verPtsE pR (hbX t.2.2) _ _ (shOf (p := pI) t)
      rw [hx]; exact e

/-- **The reader of the verifiers and the extractor** at an operation and a query list. -/
noncomputable def chkGRd (y : MOp × List DomIC) :
    GRd (SecN U) (Option (MI × Bytes)) pI (XTab L Arith.Moussaka.M) (U + M) where
  Q3 _ _ _ _ _ := ∅
  Q5 _ _ _ t := verQ5 y.1 t
  QE _ _ _ t := verQE y.1 t ∪ romPtsF (Hit.Mous.fd y.1) y.2 t.2.1.2 t.2.2

lemma chkGRd_agree {y : MOp × List DomIC} {ω : SecN U} {l : Log} {gs gs' : Fin (U + M) → Tab3}
    {t t' : TabM L} (h : (chkGRd (U := U) (M := M) y).Agree ω l gs t gs' t') :
    ((AccOp (verILX hbX) (verRLX hbX) y.1 t' ↔ AccOp (verILX hbX) (verRLX hbX) y.1 t) ∧
      verQ5 y.1 t' = verQ5 y.1 t ∧ verQE y.1 t' = verQE y.1 t) ∧
      romPtsF (Hit.Mous.fd y.1) y.2 t'.2.1.2 t'.2.2 = romPtsF (Hit.Mous.fd y.1) y.2 t.2.1.2 t.2.2 ∧
      eRomM none none y.1 y.2 zT zT t'.2 = eRomM none none y.1 y.2 zT zT t.2 := by
  have hv := ver_cons y.1 t t' h.1 h.2.1 h.2.2.2.1
    fun kz hkz => h.2.2.2.2 kz (mem_union_left _ hkz)
  have hr : ∀ kz ∈ romPtsF (Hit.Mous.fd y.1) y.2 t.2.1.2 t.2.2,
      t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2 :=
    fun kz hkz => h.2.2.2.2 kz (mem_union_right _ hkz)
  refine ⟨hv, ?_, ?_⟩
  · rw [h.2.1]; exact romPtsF_congr (Hit.Mous.fd y.1) y.2 t.2.2 hr
  · obtain ⟨G2, ⟨G5, E⟩, x⟩ := t
    obtain ⟨G2', ⟨G5', E'⟩, x'⟩ := t'
    simp only at h hr ⊢
    obtain rfl : x' = x := h.2.1
    exact eRomM_congrP none none y.1 y.2 zT zT zT zT G5 G5' x' hr

/-- **The verifiers' and the extractor's reader is consistent.** -/
theorem chkGRd_cons (y : MOp × List DomIC) : (chkGRd (U := U) (M := M) (L := L) y).Cons := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨-, e5, eE⟩, er, -⟩ := chkGRd_agree h
  refine ⟨rfl, e5, ?_⟩
  show verQE y.1 t' ∪ romPtsF (Hit.Mous.fd y.1) y.2 t'.2.1.2 t'.2.2 = _
  rw [eE, er]; rfl

/-! ## The redirect event as the composed reader's event -/

/-- **The event at an operation and a query list**: `BadN` with the operation and the extractor's
query list given (`runsVal` supplies them). -/
def chkEv (y : MOp × List DomIC) (v : SecN U × Log × (Fin (U + M) → Tab3) × TabM L) : Prop :=
  AccOp (verILX hbX) (verRLX hbX) y.1 v.2.2.2 ∧ FreshOpN v.2.1 y.1 ∧
    (¬ RelOp y.1 (eRomM none none y.1 y.2 zT zT v.2.2.2.2) ∨
      ∃ h, OpensOp (tOfN A v.1 h) y.1 (eRomM none none y.1 y.2 zT zT v.2.2.2.2))

/-- **The verifiers' and the extractor's reader reads the event at its value.** -/
theorem chkGRd_reads (y : MOp × List DomIC) : (chkGRd y).Reads (chkEv A y) := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨ea, -, -⟩, -, ee⟩ := chkGRd_agree h
  simp only [chkEv, ee, ea]

/-- **The composed reader of the redirect event**: the runs (the last stage and the patches'
prefixes), then the verifiers and the extractor at the operation and the query list. -/
noncomputable def badGRd : GRd (SecN U) (Option (MI × Bytes)) pI (XTab L Arith.Moussaka.M) (U + M) :=
  GRd.seq (runsGRd A hA) (runsVal A hA) chkGRd

/-- **The composed reader is consistent.** -/
theorem badGRd_cons : (badGRd A hA).Cons :=
  GRd.seq_cons (runsGRd_cons A hA) (runsGRd_val A hA) chkGRd_cons

/-- **`BadN` with `ROM/`'s extractor is the event at the runs' value.** -/
theorem badN_iff (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG) ω l gs t ↔
      chkEv A (runsVal A hA (ω, l, gs, t)) (ω, l, gs, t) := by
  unfold BadN accN freshN relN opensN opensH
  rw [extRomMN_eq A hA, opN_eq A hA]
  rfl

/-- **The composed reader reads the redirect event.** -/
theorem badGRd_reads :
    (badGRd A hA).Reads (fun v => BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG)
      v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  have h := GRd.seq_reads (R₁ := runsGRd A hA) (runsGRd_val A hA) (chkEv A) (chkGRd_reads A)
  intro ω l gs t gs' t' hag
  show BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG) ω l gs' t' ↔
    BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG) ω l gs t
  rw [badN_iff A hA, badN_iff A hA]
  exact h ω l gs t gs' t' hag

/-! ## The budgets -/

lemma length_takeRev_le (l : Log) : ((l.take (U + M)).reverse).length ≤ U + M := by
  simp only [List.length_reverse, List.length_take]; omega

/-- The extractor's query list has at most `N·cells(pR) + q_E` cipher queries' keys. -/
lemma card_qsJ_decE_le (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    ((qsJ A hA l gs t).filterMap decE).toFinset.card ≤ (U + M) * verifyCellBound pR + qE := by
  have := card_runsN_le decE (fun d => d.isRight) (fun _ _ h => decE_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQMm e).2) (oaN_bud A hA l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pR) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

lemma card_qsJ_decC_le (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    ((qsJ A hA l gs t).filterMap decC).toFinset.card ≤ (U + M) * verifyCellBound pR + qE := by
  have := card_runsN_le decC (fun d => d.isRight) (fun _ _ h => decC_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQMm e).2) (oaN_bud A hA l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pR) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

lemma card_verQ5_le (op : MOp) (t : TabM L) : (verQ5 op t).card ≤ 312 := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · exact (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).h5 zT (shOf t)
  · exact (verPtRd_bnd (p := pR) (Hb := hbX t.2.2) _ _).h5 zT (shOf (p := pI) t)

lemma card_verQE_keys_le (op : MOp) (t : TabM L) :
    (ptCls (verQE op t)).card ≤ 4607 ∧ ((verQE op t).image Prod.fst).card ≤ 4607 := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).hE zT (shOf t)⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pR) (Hb := hbX t.2.2) _ _).hE zT (shOf (p := pI) t)⟩

/-- The composed reader's cipher points: the query list's cells, the verifiers', and the
extractor's at the forged `iv`. -/
lemma badGRd_QE_subset (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    (badGRd A hA).QE ω l gs t ⊆ ((qsJ A hA l gs t).filterMap decC).toFinset ∪
      verQE (runsVal A hA (ω, l, gs, t)).1 t ∪
      ptsOf (romKeysF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t) t.2.1.2 t.2.2)
        (romIvF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) t.2.2) := by
  intro kz hkz
  simp only [badGRd, GRd.seq, runsGRd, chkGRd, romPtsF, mem_union] at hkz ⊢
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
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQMm e).1 .h3)
      (isQueryBoundP_kind (oaN_bud A hA l).1.1 .h3) ((l.take (U + M)).reverse)
    rw [qPre_h3, mul_zero, zero_add] at this
    exact this
  · show (((qsJ A hA l gs t).filterMap dec5).toFinset ∪
      verQ5 (runsVal A hA (ω, l, gs, t)).1 t).card ≤ _
    have h1 := card_runsN_le dec5 (kindB .h5) (fun _ _ h => dec5_kind h) (ansPN gs t)
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQMm e).1 .h5)
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
    have a3 := (card_fst_ptsOf_le (K := romKeysF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1)
      (qsJ A hA l gs t) t.2.1.2 t.2.2)
      (iv := romIvF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) t.2.2)).trans
      ((card_romKeysF_le _ _ _ _).trans (Nat.add_le_add_right (card_qsJ_decE_le A hA l gs t) _))
    have u1 := card_union_le (((qsJ A hA l gs t).filterMap decC).toFinset.image Prod.fst ∪
      (verQE (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
      ((ptsOf (romKeysF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t) t.2.1.2
        t.2.2) (romIvF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) t.2.2)).image Prod.fst)
    have u2 := card_union_le (((qsJ A hA l gs t).filterMap decC).toFinset.image Prod.fst)
      ((verQE (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
    omega

/-- **`T₃`: all slices together are read at most at the last stage's `q h3` slice queries.** -/
theorem badGRd_T3 (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    ∑ j, ((badGRd A hA).Q3 ω l gs t j).card ≤ q .h3 := by
  classical
  have e : ∀ j, ((badGRd A hA).Q3 ω l gs t j) = ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset :=
    fun j => by
      show ((qsJ A hA l gs t).filterMap (dec3N j)).toFinset ∪ ∅ = _
      rw [union_empty]
  simp only [e]
  refine (sum_card_dec3N_le _).trans ?_
  unfold qsJ
  rw [List.countP_append]
  have h1 := countP_flatMap_qlog_le vQMm (ansPN gs t) (kindB .h3)
    (fun e => isQueryBoundP_kind (qBud_vQMm e).1 .h3) ((l.take (U + M)).reverse)
  have h2 := countP_qlog_le (oaN A hA l) (ansPN gs t) (kindB .h3)
    (isQueryBoundP_kind (oaN_bud A hA l).1.1 .h3)
  rw [qPre_h3, mul_zero] at h1
  omega

/-- **`c_E`: the classes `(key, middle bytes)` of the composed reader's cipher points**: the
query list's cells, the verifiers' `4607` keys at one `iv`, and the extractor's keys (the cells'
keys and `4608` more) at the forged proof's `iv`. -/
theorem badGRd_cls (ω : SecN U) (l : Log) (gs : Fin (U + M) → Tab3) (t : TabM L) :
    (ptCls ((badGRd A hA).QE ω l gs t)).card ≤ 2 * ((U + M) * verifyCellBound pR + qE) + 9215 := by
  classical
  refine (card_le_card (ptCls_mono (badGRd_QE_subset A hA ω l gs t))).trans ?_
  rw [ptCls_union, ptCls_union]
  have a1 := (card_ptCls_le (((qsJ A hA l gs t).filterMap decC).toFinset)).trans
    (card_qsJ_decC_le A hA l gs t)
  have a2 := (card_verQE_keys_le (runsVal A hA (ω, l, gs, t)).1 t).1
  have a3 := (card_ptCls_ptsOf_le (romKeysF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1)
    (qsJ A hA l gs t) t.2.1.2 t.2.2) (romIvF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) t.2.2)).trans
    ((card_romKeysF_le _ _ _ _).trans (Nat.add_le_add_right (card_qsJ_decE_le A hA l gs t) _))
  have u1 := card_union_le (ptCls ((qsJ A hA l gs t).filterMap decC).toFinset ∪
    ptCls (verQE (runsVal A hA (ω, l, gs, t)).1 t))
    (ptCls (ptsOf (romKeysF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) (qsJ A hA l gs t)
      t.2.1.2 t.2.2) (romIvF (Hit.Mous.fd (runsVal A hA (ω, l, gs, t)).1) t.2.2)))
  have u2 := card_union_le (ptCls ((qsJ A hA l gs t).filterMap decC).toFinset)
    (ptCls (verQE (runsVal A hA (ω, l, gs, t)).1 t))
  omega

end Bad

end Moussaka

end VoleMole.Theft
