import VoleMole.Theft.JointExt
import VoleMole.Theft.JointLeanSum

/-!
# The theft event as one game reader's event (Ratatouille)

`real_sim_leN_leanG` and `real_sim_leN_leanA` (`Theft/JointLeanSum.lean`) bound
`|Pr_real[Ev] − Pr_sim[Ev]|` for the events `Ev` that one **consistent game reader** (`GRd`)
reads. The theft event `BadN` (`Theft/RatatouilleMany.lean`) is read by the adversary's last stage,
the verifier on its operation and `ROM/`'s extractor (`extRomN`). Here they are composed into one
reader, for an adversary whose last stage is the run of an oracle computation (`AdmLN`):

* **`oaN`**: the computation `extLN` takes with `Classical.choose` (the same term, by proof
  irrelevance), so the extractor's query list is the run's;
* **`qsJ`**: the extractor's query list as runs on the game's answers `ansPN`: the patches'
  prefix computations `vQM` of the first `N` log entries (`qsJ_eq`: they make no `H₃` query and do
  not read `H₂³`), then the last stage;
* **`runsGRd`**: the reader of those runs (their slice keys, `H₅` keys and cells), consistent
  (`runsGRd_cons`), which reads the operation and the query list (`runsGRd_val`);
* **`chkGRd`**: at an operation and a query list, the verifier's points (`verPtsE` of the
  operation's statement and proof, issuance at `pI`, spend at `pS`) and the extractor's points
  (`romPts`); consistent (`chkGRd_cons`, by `verPt_cons`, `romPts_congr`);
* **`badGRd`** = `GRd.seq runsGRd … chkGRd`: consistent (`badGRd_cons`), and **`badGRd_reads`**:
  it reads `BadN` with `extRomN`;
* the budgets (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`): each slice at `q h3` keys and all slices
  together at `q h3` (`T₃`); `H₅` at `q h5 + N·312 + 312`; the cipher at
  `q_E + N·cells(pS) + 4607 + 4608` keys and `2·(q_E + N·cells(pS)) + 4607 + 4608` classes
  (`c_E`: the extractor reads every logged key again at the CTR blocks of the forged proof's
  `iv`, a different class).
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Classes of the CTR blocks of one `iv` -/

section Cls

/-- **A CTR block of `iv` has `iv`'s lanes 1 and 2** (any `iv`). -/
lemma lanes12_of_inY {iv : ByteArray} {z : Blk} (h : InY iv z) :
    AES.getLE32 (ba z) 4 = AES.getLE32 iv 4 ∧ AES.getLE32 (ba z) 8 = AES.getLE32 iv 8 := by
  obtain ⟨c, t, rfl⟩ := h
  have hs : (AES.ctrBlock iv c t).size = 16 := ctrBlock_size _ _ _
  have hz : ba (blk 16 (AES.ctrBlock iv c t)) = AES.ctrBlock iv c t := ba_blk_of_size hs
  have hl := lanes_ctrBlock iv c t
  refine ⟨?_, ?_⟩
  · rw [hz]
    have := congrFun hl 1
    simp only [lanes, Seed.Commitments.ctrInput] at this
    exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _)
      (UInt32.toNat_lt _) (by simpa using this))
  · rw [hz]
    have := congrFun hl 2
    simp only [lanes, Seed.Commitments.ctrInput] at this
    exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _)
      (UInt32.toNat_lt _) (by simpa using this))

/-- **Two CTR blocks of one `iv` have the same middle bytes** (any `iv`). -/
lemma midB_eq_of_inY {iv : ByteArray} {z z' : Blk} (h : InY iv z) (h' : InY iv z') :
    midB z = midB z' := by
  obtain ⟨a1, a2⟩ := lanes12_of_inY h
  obtain ⟨b1, b2⟩ := lanes12_of_inY h'
  have h1 := bytes_of_getLE32_eq (o := 4) (by norm_num) (a1.trans b1.symm)
  have h2 := bytes_of_getLE32_eq (o := 8) (by norm_num) (a2.trans b2.symm)
  funext i
  obtain ⟨i, hi⟩ := i
  simp only [midB]
  by_cases hi4 : i < 4
  · exact h1 (i + 4) (by omega)
  · exact h2 (i + 4) (by omega)

/-- **Keys read at the CTR blocks of one `iv`**: at most as many classes as keys. -/
lemma card_ptCls_ptsOf_le (K : Finset Blk) (iv : ByteArray) : (ptCls (ptsOf K iv)).card ≤ K.card := by
  classical
  by_cases hne : ∃ z, InY iv z
  · obtain ⟨z0, hz0⟩ := hne
    have : ptCls (ptsOf K iv) ⊆ K.image fun k => (k, midB z0) := by
      intro c hc
      obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hc
      obtain ⟨hk, hz⟩ := mem_ptsOf.1 hkz
      exact mem_image.2 ⟨kz.1, hk, by rw [midB_eq_of_inY hz hz0]⟩
    exact (card_le_card this).trans card_image_le
  · have : ptsOf K iv = ∅ :=
      eq_empty_of_forall_notMem fun kz hkz => hne ⟨_, (mem_ptsOf.1 hkz).2⟩
    rw [this]
    simp [ptCls]

end Cls

/-! ## Slice reads summed over the slices -/

section Slices

variable {N : ℕ}

/-- A query is a key of at most one slice. -/
lemma dec3N_unique {d : DomIC} {j j' : Fin N} {k k' : Bytes 16} (h : dec3N j d = some k)
    (h' : dec3N j' d = some k') : j = j' := by
  classical
  rcases d with ⟨k0, b⟩ | c
  · simp only [dec3N] at h h'
    split_ifs at h h' with h1 h2 h3 h4
    exact h3.symm.trans h4
  · simp [dec3N] at h

/-- **All slices together are read at most at the `H₃` queries**:
`Σ_j #(slice-j keys of a query list) ≤ #(H₃ queries)`. -/
lemma sum_card_dec3N_le (L : List DomIC) :
    ∑ j : Fin N, ((L.filterMap (dec3N j)).toFinset.card) ≤ L.countP (kindB .h3) := by
  classical
  induction L with
  | nil => simp
  | cons d L ih =>
    have hstep : ∀ j : Fin N, (((d :: L).filterMap (dec3N j)).toFinset.card) ≤
        ((L.filterMap (dec3N j)).toFinset.card) + (if (dec3N j d).isSome then 1 else 0) := by
      intro j
      cases hd : dec3N j d with
      | none => simp [hd]
      | some k =>
        simp only [List.filterMap_cons, hd, List.toFinset_cons, Option.isSome_some, ↓reduceIte]
        exact card_insert_le _ _
    refine (Finset.sum_le_sum fun j _ => hstep j).trans ?_
    rw [Finset.sum_add_distrib]
    have hone : ∑ j : Fin N, (if (dec3N j d).isSome then 1 else 0) ≤
        if kindB .h3 d then 1 else 0 := by
      rw [Finset.sum_boole]
      by_cases hk : ∃ j : Fin N, (dec3N j d).isSome
      · obtain ⟨j, hj⟩ := hk
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hj
        have hfil : (univ.filter fun j' : Fin N => (dec3N j' d).isSome = true) ⊆ {j} := by
          intro j' hj'
          obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (mem_filter.1 hj').2
          exact mem_singleton.2 (dec3N_unique hk' hk)
        have := card_le_card hfil
        rw [card_singleton] at this
        simp only [dec3N_kind hk, ↓reduceIte, Nat.cast_id]
        exact this
      · push Not at hk
        have : (univ.filter fun j' : Fin N => (dec3N j' d).isSome = true) = ∅ :=
          filter_eq_empty_iff.2 fun j _ => by simpa using hk j
        rw [this, card_empty]
        exact Nat.zero_le _
    rw [List.countP_cons]
    omega

end Slices

/-! ## Runs on the game's answers -/

section Runs

variable {β E : Type}

/-- **A list of runs agrees** when the answers agree at every query of the runs. -/
lemma flatMap_qlog_congr' (v : E → OracleComp specIC β) (f f' : (d : DomIC) → AnsIC d) :
    ∀ l : List E, (∀ d ∈ l.flatMap (fun e => qlog f (v e)), f d = f' d) →
      l.flatMap (fun e => qlog f' (v e)) = l.flatMap (fun e => qlog f (v e))
  | [], _ => rfl
  | e :: l, h => by
    simp only [List.flatMap_cons] at h ⊢
    rw [(runT_congr (v e) f f' fun d hd => h d (List.mem_append_left _ hd)).1,
      flatMap_qlog_congr' v f f' l fun d hd => h d (List.mem_append_right _ hd)]

end Runs

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-! ## The extractor's query list as runs on `ansPN` -/

section Bad

variable {U M L : ℕ}

/-- The theft games' shared tables (function rows). -/
abbrev TabR (L : ℕ) := ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)

/-- **The patches' prefix computations do not read `H₂³`.** -/
lemma qlog_vQM_G2 (e : Ent Sizes.labelRows) (t : TabR L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabR L)) (vQM e) = qlog (ansP zT zT t) (vQM e) := by
  have h0 : ∀ f : (d : DomIC) → AnsIC d,
      qlog f (pure ByteArray.empty : OracleComp specIC ByteArray) = [] := fun _ => rfl
  rcases e with _ | ⟨x | x, π | π⟩
  · exact (h0 _).trans (h0 _).symm
  · exact qlog_vPreIC_G2 zT zT t (fun _ => 0) _ _ _
  · exact (h0 _).trans (h0 _).symm
  · exact (h0 _).trans (h0 _).symm
  · exact qlog_vPreIC_G2 zT zT t (fun _ => 0) _ _ _

/-- **The patches' prefix computations are runs on the game's answers.** -/
lemma qlog_vQM_N {N : ℕ} (e : Ent Sizes.labelRows) (gs : Fin N → Tab3) (t : TabR L) :
    qlog (ansP zT zT ((fun _ => 0, t.2) : TabR L)) (vQM e) = qlog (ansPN gs t) (vQM e) := by
  rw [qlog_vQM_G2, (noH3_ansPN (vQM e) gs zT zT t (noH3_of_kind (qBud_vQM e).1 qPre_h3 _)).1]

variable (A : ThiefN Sizes.labelRows U M Tab3 (TabR L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ iss sp, AdmLN (QBudT q qE nG) ansPN (A.out iss sp))

include hA in
lemma admLN_opN (ω : SecN U M) (l : LogR Sizes.labelRows) :
    AdmLN (QBudT q qE nG) ansPN (opN A (pubOf ω) l) :=
  hA _ _

/-- **The last stage's computation**, as `extLN` chooses it. -/
noncomputable def oaN (ω : SecN U M) (l : LogR Sizes.labelRows) :
    OracleComp specIC (Op Sizes.labelRows) :=
  (admLN_opN A hA ω l).choose

lemma oaN_bud (ω : SecN U M) (l : LogR Sizes.labelRows) : QBudT q qE nG (oaN A hA ω l) :=
  (admLN_opN A hA ω l).choose_spec.1

/-- **The operation is the run of `oaN`.** -/
lemma opN_eq (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3) (t : TabR L) :
    opN A (pubOf ω) l gs t = runT (ansPN gs t) (oaN A hA ω l) :=
  congrFun (congrFun (admLN_opN A hA ω l).choose_spec.2 gs) t

/-- **The extractor's query list**, as runs on `ansPN`: the patches' prefixes of the first `N` log
entries (most recent first), then the last stage's queries. -/
noncomputable def qsJ (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) : List DomIC :=
  ((l.take (U + M)).reverse.flatMap fun e => qlog (ansPN gs t) (vQM e)) ++
    qlog (ansPN gs t) (oaN A hA ω l)

/-- **`extRomN` is `eRom` on the run and `qsJ`.** -/
lemma extRomN_eq (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) :
    extRomN A q qE nG l (opN A (pubOf ω) l) gs t =
      eRom A.base none none (runT (ansPN gs t) (oaN A hA ω l)) (qsJ A hA ω l gs t) zT zT t.2 := by
  classical
  unfold extRomN extLN
  simp only [dite_eq_left (admLN_opN A hA ω l)]
  unfold eRomN
  rw [opN_eq A hA ω l gs t]
  congr 1
  unfold qsJ logsL
  congr 1
  exact List.flatMap_congr fun e _ => (logQM_eq e gs t.2).trans (qlog_vQM_N e gs t)

/-! ## The runs' reader -/

/-- **The reader of the extractor's query list**: the slice keys, `H₅` keys and cells of `qsJ`
(the patches' prefixes and the last stage). -/
noncomputable def runsGRd :
    GRd (SecN U M) (Ent Sizes.labelRows) pI (XTab L Arith.Ratatouille.uovM) (U + M) where
  Q3 ω l gs t j := ((qsJ A hA ω l gs t).filterMap (dec3N j)).toFinset
  Q5 ω l gs t := ((qsJ A hA ω l gs t).filterMap dec5).toFinset
  QE ω l gs t := ((qsJ A hA ω l gs t).filterMap decC).toFinset

/-- **Agreement at the runs' reads gives the same query list and operation.** -/
lemma runsGRd_agree {ω : SecN U M} {l : LogR Sizes.labelRows} {gs gs' : Fin (U + M) → Tab3}
    {t t' : TabR L} (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    qsJ A hA ω l gs' t' = qsJ A hA ω l gs t ∧
      runT (ansPN gs' t') (oaN A hA ω l) = runT (ansPN gs t) (oaN A hA ω l) := by
  have hd : ∀ d ∈ qsJ A hA ω l gs t, ansPN gs t d = ansPN gs' t' d := fun d hd =>
    ansPN_agree gs gs' t t' h.1 h.2.1 d (fun j k hk => h.2.2.1 j k (mem_dec hd hk))
      (fun k hk => h.2.2.2.1 k (mem_dec hd hk)) (fun kz hkz => h.2.2.2.2 kz (mem_dec hd hkz))
  have e1 := flatMap_qlog_congr' vQM (ansPN gs t) (ansPN gs' t') ((l.take (U + M)).reverse)
    fun d hd' => hd d (List.mem_append_left _ hd')
  have e2 := runT_congr (oaN A hA ω l) (ansPN gs t) (ansPN gs' t')
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
    show ((qsJ A hA ω l gs' t').filterMap (dec3N j)).toFinset = _
    rw [e]; rfl
  · show ((qsJ A hA ω l gs' t').filterMap dec5).toFinset = _
    rw [e]; rfl
  · show ((qsJ A hA ω l gs' t').filterMap decC).toFinset = _
    rw [e]; rfl

/-- The value the runs' reader reads: the operation and the query list. -/
noncomputable def runsVal (v : SecN U M × LogR Sizes.labelRows × (Fin (U + M) → Tab3) × TabR L) :
    Op Sizes.labelRows × List DomIC :=
  (runT (ansPN v.2.2.1 v.2.2.2) (oaN A hA v.1 v.2.1), qsJ A hA v.1 v.2.1 v.2.2.1 v.2.2.2)

lemma runsGRd_val (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3) (t : TabR L)
    (gs' : Fin (U + M) → Tab3) (t' : TabR L) (h : (runsGRd A hA).Agree ω l gs t gs' t') :
    runsVal A hA (ω, l, gs', t') = runsVal A hA (ω, l, gs, t) := by
  obtain ⟨e1, e2⟩ := runsGRd_agree A hA h
  simp only [runsVal, e1, e2]

/-! ## The verifier and the extractor at an operation and a query list -/

/-- The verifier's `H₅` keys on an operation. -/
noncomputable def verQ5 (op : Op Sizes.labelRows) (t : TabR L) : Finset (ZK.Sim.Bytes 37) :=
  match op with
  | .issue q' tt c => verKeys5 (p := pI) (Hb := hbX t.2.2) (Privacy.Ratatouille.stI (opXI q' tt c))
      (bOf (issueReqProof q')) (shOf t)
  | .spend q' c _ => verKeys5 (p := pS) (Hb := hbX t.2.2) (Privacy.Ratatouille.stS (opXS A.base q' c))
      (bOf (SpendReq.parse q').proof) (shOf (p := pI) t)

/-- The verifier's cipher points on an operation. -/
noncomputable def verQE (op : Op Sizes.labelRows) (t : TabR L) : Finset (Blk × Blk) :=
  match op with
  | .issue q' tt c => verPtsE pI (hbX t.2.2) (Privacy.Ratatouille.stI (opXI q' tt c)) (bOf (issueReqProof q')) (shOf t)
  | .spend q' c _ => verPtsE pS (hbX t.2.2) (Privacy.Ratatouille.stS (opXS A.base q' c))
      (bOf (SpendReq.parse q').proof) (shOf (p := pI) t)

/-- (Stated for a variable row type: at `R = Blk → Blk` the kernel would check the unfolding of
`leanVIRH` by evaluating the verifier.) -/
lemma leanVIRH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : IssueInstance)
    (π : IssueProof Sizes.labelRows) (s s' : ShR R)
    (h : verRO pI Hb (Privacy.Ratatouille.stI x) (bOf π) s' =
      verRO pI Hb (Privacy.Ratatouille.stI x) (bOf π) s) :
    leanVIRH Hb x π s' = leanVIRH Hb x π s :=
  congrArg Transcript.accept h

lemma leanVSRH_congr {R : Type} [CipherRow R] (Hb : Hashes) (x : SpendInstance)
    (π : SpendProof Sizes.labelRows) (s s' : ShR R)
    (h : verRO pS Hb (Privacy.Ratatouille.stS x) (bOf π) s' =
      verRO pS Hb (Privacy.Ratatouille.stS x) (bOf π) s) :
    leanVSRH Hb x π s' = leanVSRH Hb x π s :=
  congrArg Transcript.accept h

/-- **The verifier on an operation reads at its points, consistently.** -/
lemma ver_cons (op : Op Sizes.labelRows) (t t' : TabR L) (h2 : t'.1 = t.1) (hx : t'.2.2 = t.2.2)
    (h5 : ∀ k ∈ verQ5 A op t, t.2.1.1 k = t'.2.1.1 k)
    (hE : ∀ kz ∈ verQE A op t, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2) :
    (AccOp A.base (leanVIRX hbX) (leanVSRX hbX) op t' ↔
        AccOp A.base (leanVIRX hbX) (leanVSRX hbX) op t) ∧
      verQ5 A op t' = verQ5 A op t ∧ verQE A op t' = verQE A op t := by
  rcases op with ⟨q', tt, c⟩ | ⟨q', c, r⟩
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pI) (Hb := hbX t.2.2)
      (Privacy.Ratatouille.stI (opXI q' tt c)) (bOf (issueReqProof q')) (shOf t) (shOf t') h2 h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : leanVIRX hbX (opXI q' tt c) (issueReqProof q') t' =
          leanVIRX hbX (opXI q' tt c) (issueReqProof q') t := by
        unfold leanVIRX
        rw [hx]
        exact leanVIRH_congr _ _ _ _ _ a
      show leanVIRX hbX _ _ t' = true ↔ leanVIRX hbX _ _ t = true
      rw [a3]
    · show verKeys5 (p := pI) (Hb := hbX t'.2.2) _ _ (shOf t') =
        verKeys5 (p := pI) (Hb := hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact b
    · show verPtsE pI (hbX t'.2.2) _ _ (shOf t') = verPtsE pI (hbX t.2.2) _ _ (shOf t)
      rw [hx]; exact e
  · obtain ⟨a, b, e⟩ := verPt_cons (p := pS) (Hb := hbX t.2.2)
      (Privacy.Ratatouille.stS (opXS A.base q' c)) (bOf (SpendReq.parse q').proof)
      (shOf (p := pI) t) (shOf (p := pI) t') h2 h5 hE
    refine ⟨?_, ?_, ?_⟩
    · have a3 : leanVSRX hbX (opXS A.base q' c) (SpendReq.parse q').proof t' =
          leanVSRX hbX (opXS A.base q' c) (SpendReq.parse q').proof t := by
        unfold leanVSRX
        rw [hx]
        exact leanVSRH_congr _ _ _ _ _ a
      show leanVSRX hbX _ _ t' = true ↔ leanVSRX hbX _ _ t = true
      rw [a3]
    · show verKeys5 (p := pS) (Hb := hbX t'.2.2) _ _ (shOf (p := pI) t') =
        verKeys5 (p := pS) (Hb := hbX t.2.2) _ _ (shOf (p := pI) t)
      rw [hx]; exact b
    · show verPtsE pS (hbX t'.2.2) _ _ (shOf (p := pI) t') =
        verPtsE pS (hbX t.2.2) _ _ (shOf (p := pI) t)
      rw [hx]; exact e

/-- **The reader of the verifier and the extractor** at an operation and a query list. -/
noncomputable def chkGRd (y : Op Sizes.labelRows × List DomIC) :
    GRd (SecN U M) (Ent Sizes.labelRows) pI (XTab L Arith.Ratatouille.uovM) (U + M) where
  Q3 _ _ _ _ _ := ∅
  Q5 _ _ _ t := verQ5 A y.1 t
  QE _ _ _ t := verQE A y.1 t ∪ romPts A.base y.1 y.2 t.2.1.2 t.2.2

lemma chkGRd_agree {y : Op Sizes.labelRows × List DomIC} {ω : SecN U M}
    {l : LogR Sizes.labelRows} {gs gs' : Fin (U + M) → Tab3} {t t' : TabR L}
    (h : (chkGRd A y).Agree ω l gs t gs' t') :
    ((AccOp A.base (leanVIRX hbX) (leanVSRX hbX) y.1 t' ↔
        AccOp A.base (leanVIRX hbX) (leanVSRX hbX) y.1 t) ∧
      verQ5 A y.1 t' = verQ5 A y.1 t ∧ verQE A y.1 t' = verQE A y.1 t) ∧
      romPts A.base y.1 y.2 t'.2.1.2 t'.2.2 = romPts A.base y.1 y.2 t.2.1.2 t.2.2 ∧
      eRom A.base none none y.1 y.2 zT zT t'.2 = eRom A.base none none y.1 y.2 zT zT t.2 := by
  have hv := ver_cons A y.1 t t' h.1 h.2.1 h.2.2.2.1
    fun kz hkz => h.2.2.2.2 kz (mem_union_left _ hkz)
  have hr : ∀ kz ∈ romPts A.base y.1 y.2 t.2.1.2 t.2.2, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2 :=
    fun kz hkz => h.2.2.2.2 kz (mem_union_right _ hkz)
  refine ⟨hv, ?_, ?_⟩
  · rw [h.2.1]; exact romPts_congr A.base y.1 y.2 t.2.2 hr
  · obtain ⟨G2, ⟨G5, E⟩, x⟩ := t
    obtain ⟨G2', ⟨G5', E'⟩, x'⟩ := t'
    simp only at h hr ⊢
    obtain rfl : x' = x := h.2.1
    exact eRom_congrP A.base none none y.1 y.2 zT zT zT zT G5 G5' x' hr

/-- **The verifier's and the extractor's reader is consistent.** -/
theorem chkGRd_cons (y : Op Sizes.labelRows × List DomIC) : (chkGRd A y).Cons := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨-, e5, eE⟩, er, -⟩ := chkGRd_agree A h
  refine ⟨rfl, e5, ?_⟩
  show verQE A y.1 t' ∪ romPts A.base y.1 y.2 t'.2.1.2 t'.2.2 = _
  rw [eE, er]; rfl

/-! ## The theft event as the composed reader's event -/

/-- **The event at an operation and a query list**: `BadN` with the operation and the extractor's
query list given (`runsVal` supplies them). -/
def chkEv (y : Op Sizes.labelRows × List DomIC)
    (v : SecN U M × LogR Sizes.labelRows × (Fin (U + M) → Tab3) × TabR L) : Prop :=
  AccOp A.base (leanVIRX hbX) (leanVSRX hbX) y.1 v.2.2.2 ∧ FreshOpN A v.2.1 y.1 ∧
    (¬ RelOp A.base y.1 (eRom A.base none none y.1 y.2 zT zT v.2.2.2.2) ∨
      ∃ j : Fin (U + M), ∃ c, comAt A (pubOf v.1) v.2.1 j = some c ∧
        ∃ o ∈ opensOf y.1 (eRom A.base none none y.1 y.2 zT zT v.2.2.2.2), comOf o = c)

/-- **The verifier's and the extractor's reader reads the event at its value.** -/
theorem chkGRd_reads (y : Op Sizes.labelRows × List DomIC) : (chkGRd A y).Reads (chkEv A y) := by
  intro ω l gs t gs' t' h
  obtain ⟨⟨ea, -, -⟩, -, ee⟩ := chkGRd_agree A h
  simp only [chkEv, ee, ea]

/-- **The composed reader of the theft event**: the runs (the last stage and the patches'
prefixes), then the verifier and the extractor at the operation and the query list. -/
noncomputable def badGRd :
    GRd (SecN U M) (Ent Sizes.labelRows) pI (XTab L Arith.Ratatouille.uovM) (U + M) :=
  GRd.seq (runsGRd A hA) (runsVal A hA) (chkGRd A)

/-- **The composed reader is consistent.** -/
theorem badGRd_cons : (badGRd A hA).Cons :=
  GRd.seq_cons (runsGRd_cons A hA) (runsGRd_val A hA) (chkGRd_cons A)

/-- **`BadN` with `ROM/`'s extractor is the event at the runs' value.** -/
theorem badN_iff (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3) (t : TabR L) :
    BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG) ω l gs t ↔
      chkEv A (runsVal A hA (ω, l, gs, t)) (ω, l, gs, t) := by
  unfold BadN accN freshN relN opensN opensJ
  rw [extRomN_eq A hA, opN_eq A hA]
  rfl

/-- **The composed reader reads the theft event.** -/
theorem badGRd_reads :
    (badGRd A hA).Reads (fun v => BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)
      v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  have h := GRd.seq_reads (R₁ := runsGRd A hA) (runsGRd_val A hA) (chkEv A) (chkGRd_reads A)
  intro ω l gs t gs' t' hag
  show BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG) ω l gs' t' ↔
    BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG) ω l gs t
  rw [badN_iff A hA, badN_iff A hA]
  exact h ω l gs t gs' t' hag

/-! ## The budgets -/

lemma length_takeRev_le (l : LogR Sizes.labelRows) : ((l.take (U + M)).reverse).length ≤ U + M := by
  simp only [List.length_reverse, List.length_take]; omega

/-- The extractor's query list has at most `N·cells(pS) + q_E` cipher queries' keys. -/
lemma card_qsJ_decE_le (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) :
    ((qsJ A hA ω l gs t).filterMap decE).toFinset.card ≤ (U + M) * verifyCellBound pS + qE := by
  have := card_runsN_le decE (fun d => d.isRight) (fun _ _ h => decE_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQM e).2) (oaN_bud A hA ω l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pS) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

lemma card_qsJ_decC_le (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) :
    ((qsJ A hA ω l gs t).filterMap decC).toFinset.card ≤ (U + M) * verifyCellBound pS + qE := by
  have := card_runsN_le decC (fun d => d.isRight) (fun _ _ h => decC_right h) (ansPN gs t)
    (ansPN gs t) (fun e => (qBud_vQM e).2) (oaN_bud A hA ω l).1.2 ((l.take (U + M)).reverse)
  have hl := Nat.mul_le_mul_right (verifyCellBound pS) (length_takeRev_le (U := U) (M := M) l)
  exact this.trans (by omega)

/-- The cells' keys are the cipher queries' keys. -/
lemma image_decC_subset (qs : List DomIC) :
    (qs.filterMap decC).toFinset.image Prod.fst ⊆ (qs.filterMap decE).toFinset := by
  intro k hk
  obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hk
  obtain ⟨d, hd, hdk⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 hkz)
  exact mem_dec hd (decE_of_decC hdk)

lemma card_verQ5_le (op : Op Sizes.labelRows) (t : TabR L) : (verQ5 A op t).card ≤ 312 := by
  rcases op with ⟨q', tt, c⟩ | ⟨q', c, r⟩
  · exact (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).h5 zT (shOf t)
  · exact (verPtRd_bnd (p := pS) (Hb := hbX t.2.2) _ _).h5 zT (shOf (p := pI) t)

lemma card_verQE_keys_le (op : Op Sizes.labelRows) (t : TabR L) :
    (ptCls (verQE A op t)).card ≤ 4607 ∧ ((verQE A op t).image Prod.fst).card ≤ 4607 := by
  rcases op with ⟨q', tt, c⟩ | ⟨q', c, r⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pI) (Hb := hbX t.2.2) _ _).hE zT (shOf t)⟩
  · exact ⟨(card_ptCls_ptsOf_le _ _).trans (rdKeys_card _ _ _ _),
      (verPtRd_bnd (p := pS) (Hb := hbX t.2.2) _ _).hE zT (shOf (p := pI) t)⟩

/-- The composed reader's cipher points: the query list's cells, the verifier's, and the
extractor's at the forged `iv`. -/
lemma badGRd_QE_subset (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) :
    (badGRd A hA).QE ω l gs t ⊆ ((qsJ A hA ω l gs t).filterMap decC).toFinset ∪
      verQE A (runsVal A hA (ω, l, gs, t)).1 t ∪
      ptsOf (romKeysP A.base (runsVal A hA (ω, l, gs, t)).1 (qsJ A hA ω l gs t) t.2.1.2 t.2.2)
        (romIv A.base (runsVal A hA (ω, l, gs, t)).1 t.2.2) := by
  intro kz hkz
  simp only [badGRd, GRd.seq, runsGRd, chkGRd, romPts, mem_union] at hkz ⊢
  tauto

/-- **The composed reader's budgets**: each slice at `q h3` keys, `H₅` at
`N·312 + q h5 + 312`, the cipher at `2·(N·cells(pS) + q_E) + 9215` keys. -/
theorem badGRd_bnd :
    (badGRd A hA).Bnd (q .h3) ((U + M) * 312 + q .h5 + 312)
      (2 * ((U + M) * verifyCellBound pS + qE) + 9215) := by
  classical
  refine ⟨fun ω l gs t j => ?_, fun ω l gs t => ?_, fun ω l gs t => ?_⟩
  · show (((qsJ A hA ω l gs t).filterMap (dec3N j)).toFinset ∪ ∅).card ≤ q .h3
    rw [union_empty]
    have := card_runsN_le (dec3N j) (kindB .h3) (fun _ _ h => dec3N_kind h) (ansPN gs t)
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQM e).1 .h3)
      (isQueryBoundP_kind (oaN_bud A hA ω l).1.1 .h3) ((l.take (U + M)).reverse)
    rw [qPre_h3, mul_zero, zero_add] at this
    exact this
  · show (((qsJ A hA ω l gs t).filterMap dec5).toFinset ∪
      verQ5 A (runsVal A hA (ω, l, gs, t)).1 t).card ≤ _
    have h1 := card_runsN_le dec5 (kindB .h5) (fun _ _ h => dec5_kind h) (ansPN gs t)
      (ansPN gs t) (fun e => isQueryBoundP_kind (qBud_vQM e).1 .h5)
      (isQueryBoundP_kind (oaN_bud A hA ω l).1.1 .h5) ((l.take (U + M)).reverse)
    rw [qPre_h5] at h1
    have hl := Nat.mul_le_mul_right 312 (length_takeRev_le (U := U) (M := M) l)
    have h2 := card_verQ5_le A (runsVal A hA (ω, l, gs, t)).1 t
    refine (card_union_le _ _).trans ?_
    unfold qsJ at *
    omega
  · refine (card_le_card (image_subset_image (badGRd_QE_subset A hA ω l gs t))).trans ?_
    rw [image_union, image_union]
    have a1 := (card_le_card (image_decC_subset (qsJ A hA ω l gs t))).trans
      (card_qsJ_decE_le A hA ω l gs t)
    have a2 := (card_verQE_keys_le A (runsVal A hA (ω, l, gs, t)).1 t).2
    have a3 := (card_fst_ptsOf_le (K := romKeysP A.base (runsVal A hA (ω, l, gs, t)).1
      (qsJ A hA ω l gs t) t.2.1.2 t.2.2) (iv := romIv A.base (runsVal A hA (ω, l, gs, t)).1 t.2.2)).trans
      ((card_romKeysP_le _ _ _ _ _).trans
        (Nat.add_le_add_right (card_qsJ_decE_le A hA ω l gs t) _))
    have u1 := card_union_le (((qsJ A hA ω l gs t).filterMap decC).toFinset.image Prod.fst ∪
      (verQE A (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
      ((ptsOf (romKeysP A.base (runsVal A hA (ω, l, gs, t)).1 (qsJ A hA ω l gs t) t.2.1.2 t.2.2)
        (romIv A.base (runsVal A hA (ω, l, gs, t)).1 t.2.2)).image Prod.fst)
    have u2 := card_union_le (((qsJ A hA ω l gs t).filterMap decC).toFinset.image Prod.fst)
      ((verQE A (runsVal A hA (ω, l, gs, t)).1 t).image Prod.fst)
    omega

/-- **`T₃`: all slices together are read at most at the last stage's `q h3` slice queries.** -/
theorem badGRd_T3 (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) : ∑ j, ((badGRd A hA).Q3 ω l gs t j).card ≤ q .h3 := by
  classical
  have e : ∀ j, ((badGRd A hA).Q3 ω l gs t j) =
      ((qsJ A hA ω l gs t).filterMap (dec3N j)).toFinset := fun j => by
    show ((qsJ A hA ω l gs t).filterMap (dec3N j)).toFinset ∪ ∅ = _
    rw [union_empty]
  simp only [e]
  refine (sum_card_dec3N_le _).trans ?_
  unfold qsJ
  rw [List.countP_append]
  have h1 := countP_flatMap_qlog_le vQM (ansPN gs t) (kindB .h3)
    (fun e => isQueryBoundP_kind (qBud_vQM e).1 .h3) ((l.take (U + M)).reverse)
  have h2 := countP_qlog_le (oaN A hA ω l) (ansPN gs t) (kindB .h3)
    (isQueryBoundP_kind (oaN_bud A hA ω l).1.1 .h3)
  rw [qPre_h3, mul_zero] at h1
  omega

/-- **`c_E`: the classes `(key, middle bytes)` of the composed reader's cipher points**: the
query list's cells, the verifier's `4607` keys at one `iv`, and the extractor's keys (the cells'
keys and `4608` more) at the forged proof's `iv`. -/
theorem badGRd_cls (ω : SecN U M) (l : LogR Sizes.labelRows) (gs : Fin (U + M) → Tab3)
    (t : TabR L) :
    (ptCls ((badGRd A hA).QE ω l gs t)).card ≤ 2 * ((U + M) * verifyCellBound pS + qE) + 9215 := by
  classical
  refine (card_le_card (ptCls_mono (badGRd_QE_subset A hA ω l gs t))).trans ?_
  rw [ptCls_union, ptCls_union]
  have a1 := (card_ptCls_le (((qsJ A hA ω l gs t).filterMap decC).toFinset)).trans
    (card_qsJ_decC_le A hA ω l gs t)
  have a2 := (card_verQE_keys_le A (runsVal A hA (ω, l, gs, t)).1 t).1
  have a3 := (card_ptCls_ptsOf_le (romKeysP A.base (runsVal A hA (ω, l, gs, t)).1
    (qsJ A hA ω l gs t) t.2.1.2 t.2.2) (romIv A.base (runsVal A hA (ω, l, gs, t)).1 t.2.2)).trans
    ((card_romKeysP_le _ _ _ _ _).trans (Nat.add_le_add_right (card_qsJ_decE_le A hA ω l gs t) _))
  have u1 := card_union_le (ptCls ((qsJ A hA ω l gs t).filterMap decC).toFinset ∪
    ptCls (verQE A (runsVal A hA (ω, l, gs, t)).1 t))
    (ptCls (ptsOf (romKeysP A.base (runsVal A hA (ω, l, gs, t)).1 (qsJ A hA ω l gs t) t.2.1.2 t.2.2)
      (romIv A.base (runsVal A hA (ω, l, gs, t)).1 t.2.2)))
  have u2 := card_union_le (ptCls ((qsJ A hA ω l gs t).filterMap decC).toFinset)
    (ptCls (verQE A (runsVal A hA (ω, l, gs, t)).1 t))
  omega

end Bad

end Ratatouille

end VoleMole.Theft
