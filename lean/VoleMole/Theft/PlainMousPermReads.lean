import VoleMole.Theft.PlainMousPerm
import VoleMole.Theft.PlainMousReads
import VoleMole.Theft.PlainRataPermReads

/-!
# The read budget of `ROM/`'s extractor with inverse queries (Moussaka)

The Moussaka counterpart of `Theft/PlainRataPermReads.lean`:

* `romRowsMP`, **`eRomMP_congr`**: `eRomMP` reads neither the slices nor `H₅`, and the
  permutations only at the keys of its cipher queries, the reconstruction's rows and the zero
  key's row.
* **`stageBudgetX_extRomMP`**: `extRomMP` reads each `H₃` slice at `q h3` keys, `H₅` at
  `q h5 + 624` and the permutation table at `qE + cells(pR) + cells(pI) + 4608` rows.
* **`noRedirect_lean_romP'`**: `noRedirect_lean_romP` without `hX`:

      Pr[Bad] ≤ εROPm(pI; q') + εROPm(pR; q') + δ_R + ε_rom
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 138230)`, for `q_E + 129015 < 2¹²⁸`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

variable {L : ℕ}

/-- **The rows `eRomMP` reads**: the keys of the cipher queries, the reconstruction's rows and the
zero key's row. -/
noncomputable def romRowsMP (op : MOp) (qs : List DomP) (π : PTable)
    (x : XTab L Arith.Moussaka.M) : Finset Blk :=
  romRowsM op (qs.map (toIC π)) (Ratatouille.fnRows π) x

lemma romRowsMP_eq (op : MOp) (qs : List DomP) (π : PTable) (x : XTab L Arith.Moussaka.M) :
    romRowsMP op qs π x = insert zeroRow ((qs.filterMap decEP).toFinset ∪
      treeRows (Ratatouille.fnRows π) (ivOf (hbX x) ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩
          ((Hit.Mous.fd op).1.mu1 (hbX x)))
        (Proof.opening ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩)
        (Proof.delta ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩)) := by
  unfold romRowsMP romRowsM
  rw [Ratatouille.filterMap_decE_toIC]

lemma card_romRowsMP_le (op : MOp) (qs : List DomP) (π : PTable) (x : XTab L Arith.Moussaka.M) :
    (romRowsMP op qs π x).card ≤ (qs.filterMap decEP).toFinset.card + 4608 := by
  have h := card_romRowsM_le op (qs.map (toIC π)) (Ratatouille.fnRows π) x
  rw [Ratatouille.filterMap_decE_toIC] at h
  exact h

/-- **`eRomMP` reads neither the slices nor `H₅`, and the permutations only in `romRowsMP`.** -/
theorem eRomMP_congr (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : MOp) (qs : List DomP) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {π π' : PTable}
    (x : XTab L Arith.Moussaka.M) (h : ∀ k ∈ romRowsMP op qs π x, π k = π' k) :
    eRomMP p₁ p₂ op qs g₁' g₂' ((G5', π'), x) = eRomMP p₁ p₂ op qs g₁ g₂ ((G5, π), x) := by
  have hq : qs.map (toIC π') = qs.map (toIC π) := Ratatouille.map_toIC_congr fun k hk =>
    h k (by rw [romRowsMP_eq]; exact mem_insert_of_mem (mem_union_left _ hk))
  show eRomM p₁ p₂ op (qs.map (toIC π')) g₁' g₂' ((G5', Ratatouille.fnRows π'), x) =
    eRomM p₁ p₂ op (qs.map (toIC π)) g₁ g₂ ((G5, Ratatouille.fnRows π), x)
  rw [hq]
  exact eRomM_congr p₁ p₂ op _ g₁ g₂ g₁' g₂' G5 G5' x fun k hk =>
    congrArg (fun σ : Equiv.Perm Blk => (σ : Blk → Blk)) (h k hk)

/-- The extractor's query list on the tables `t`: the two prefixes' (forward) queries, then the
last stage's. -/
noncomputable def qsRMP {α : Type} {L M : ℕ} (p₁ : Option (IssueInstance × Bytes))
    (p₂ : Option (RedeemInstance × Bytes)) (oa : OracleComp specP α)
    (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) pI (XTab L M)) : List DomP :=
  qlog (ansQ g₁ g₂ ((fun _ => 0, t.2) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQR p₂)) ++
    (qlog (ansQ g₁ g₂ ((fun _ => 0, t.2) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQIm p₁)) ++
      qlog (ansQ g₁ g₂ t) oa)

lemma logQIPm_eq (p₁ : Option (IssueInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) :
    logQIPm p₁ g₁ g₂ b = qlog (ansQ g₁ g₂ ((fun _ => 0, b) :
      ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M))) (liftP (vQIm p₁)) := by
  rw [qlog_liftP, ← logQIm_eq]
  rfl

lemma logQRPm_eq (p₂ : Option (RedeemInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) :
    logQRPm p₂ g₁ g₂ b = qlog (ansQ g₁ g₂ ((fun _ => 0, b) :
      ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M))) (liftP (vQR p₂)) := by
  rw [qlog_liftP, ← logQRm_eq]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The read budget of `ROM/`'s extractor with inverse queries in the redirect game**: for an
adversary whose last stage is the run of an oracle computation within `QBudP q qE`, `extRomMP`
reads each `H₃` slice at `q h3` keys, `H₅` at `q h5 + 624` and the permutation table at
`qE + cells(pR) + cells(pI) + 4608` rows. -/
theorem stageBudgetX_extRomMP
    (A : Thief Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    {q : Kind → ℕ} {qE : ℕ} (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂))
    (o₁ : Bytes) (o₂ : Except Error Bytes) :
    StageBudgetX (extRomMP q qE (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) (q .h3) (q .h5 + 624)
      (qE + verifyCellBound pR + verifyCellBound pI + 4608) := by
  obtain ⟨oa, hb, he⟩ := extL_of_admL (logQ₁ := logQIPm) (logQ₂ := logQRPm) (e := eRomMP)
    (hA o₁ o₂)
  set p₁ := stI A o₁
  set p₂ := stR A o₁ o₂
  have hfun : extRomMP q qE p₁ p₂ (A.out o₁ o₂) = fun g₁ g₂ t =>
      eRomMP p₁ p₂ (runT (ansQ g₁ g₂ t) oa) (qsRMP p₁ p₂ oa g₁ g₂ t) g₁ g₂ t.2 := by
    unfold extRomMP
    rw [he]
    funext g₁ g₂ t
    rw [logQIPm_eq, logQRPm_eq]
    rfl
  rw [hfun]
  intro x
  have hS := qBudP_liftP (qBud_vQR p₂)
  have hI := qBudP_liftP (qBud_vQIm p₁)
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · -- the first slice
    refine ⟨fun g₁ => ((qsRMP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3P false)).toFinset,
      fun g₁ => (card_runs_leG (dec3P false) (kindBP .h3) (fun _ _ => dec3P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h3) (isQueryBoundP_kindP hI.1 .h3)
        (isQueryBoundP_kindP hb.1 .h3)).trans
          (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]),
      fun g₁ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG (dec3P false) _ (f₀' := ansQ g' g₂ _)
      (f' := ansQ g' g₂ (atX s x)) (liftP (vQR p₂)) (liftP (vQIm p₁)) oa subset_rfl
      (fun d hd => ansQ_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansQ_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g' g₂ (atX s x)) _ _ _ =
      eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRMP
    rw [e1, e2]
    rfl
  · -- the second slice
    refine ⟨fun g₂ => ((qsRMP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3P true)).toFinset,
      fun g₂ => (card_runs_leG (dec3P true) (kindBP .h3) (fun _ _ => dec3P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h3) (isQueryBoundP_kindP hI.1 .h3)
        (isQueryBoundP_kindP hb.1 .h3)).trans
          (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]),
      fun g₂ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG (dec3P true) _ (f₀' := ansQ g₁ g' _)
      (f' := ansQ g₁ g' (atX s x)) (liftP (vQR p₂)) (liftP (vQIm p₁)) oa subset_rfl
      (fun d hd => ansQ_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansQ_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g₁ g' (atX s x)) _ _ _ =
      eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRMP
    rw [e1, e2]
    rfl
  · -- `H₅`
    refine ⟨fun s => ((qsRMP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap dec5P).toFinset,
      fun s => (card_runs_leG dec5P (kindBP .h5) (fun _ _ => dec5P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h5) (isQueryBoundP_kindP hI.1 .h5)
        (isQueryBoundP_kindP hb.1 .h5)).trans
          (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]; omega),
      fun s G5 hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG dec5P _
      (f₀' := ansQ g₁ g₂ ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansQ g₁ g₂ (atX (s.1, G5, s.2.2) x)) (liftP (vQR p₂)) (liftP (vQIm p₁)) oa subset_rfl
      (fun d hd => ansQ_h5 g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansQ_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g₁ g₂ (atX (s.1, G5, s.2.2) x)) _ _ _ =
      eRomMP p₁ p₂ _ (qsRMP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRMP
    rw [e1, e2]
    exact eRomMP_congr p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 G5 x fun _ _ => rfl
  · -- the permutations
    refine ⟨fun s => romRowsMP (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRMP p₁ p₂ oa g₁ g₂ (atX s x))
        s.2.2 x,
      fun s => (card_romRowsMP_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runs_leG decEP (fun d => d.isRight) (fun _ _ => decEP_right)
        (ansQ g₁ g₂ ((fun _ => 0, (atX s x).2) :
          ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (ansQ g₁ g₂ (atX s x)) hS.2 hI.2 hb.2
      unfold qsRMP
      omega
    have hsub : ((qsRMP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap decEP).toFinset ⊆
        romRowsMP (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRMP p₁ p₂ oa g₁ g₂ (atX s x)) s.2.2 x := by
      rw [romRowsMP_eq]
      exact fun k hk => mem_insert_of_mem (mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := runs_congrG decEP _
      (f₀' := ansQ g₁ g₂ ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansQ g₁ g₂ (atX (s.1, s.2.1, E) x)) (liftP (vQR p₂)) (liftP (vQIm p₁)) oa hsub
      (fun d hd => ansQ_E g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansQ_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomMP p₁ p₂ (runT (ansQ g₁ g₂ (atX (s.1, s.2.1, E) x)) oa)
        (qsRMP p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x)) _ _ _ =
      eRomMP p₁ p₂ (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRMP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    have e1' : qsRMP p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x) = qsRMP p₁ p₂ oa g₁ g₂ (atX s x) := e1
    rw [e1', e2]
    exact eRomMP_congr p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 s.2.1 x hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Redemption non-malleability with permutation rows, inverse cipher queries and `ROM/`'s plain
extraction, without a read-budget hypothesis** (Moussaka, one token): `noRedirect_lean_romP` with
the extractor's read budget proved (`stageBudgetX_extRomMP`), for `q_E + 129015 < 2¹²⁸`:

    Pr[Bad] ≤ εROPm(pI; q') + εROPm(pR; q') + δ_R + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 138230)`, `ε_rom = epsRomMP q₀ (q_E + cells(pR) +
cells(pI)) (totK Moussaka.M q₀)`, `q₀ = q + 2·qPre`. -/
theorem noRedirect_lean_romP'
    (A : Thief Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hqE : qE + 129015 < 2 ^ 128)
    (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMP q qE)) ≤
      ZKRow.εz (Equiv.Perm Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        ZKRow.εz (Equiv.Perm Blk) pR (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        ((epsRomMP (q + Ratatouille.qPre + Ratatouille.qPre)
          (qE + verifyCellBound pR + verifyCellBound pI)
          (totK Arith.Moussaka.M (q + Ratatouille.qPre + Ratatouille.qPre))).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extRomMP q qE) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have hq : qE + verifyCellBound pR + verifyCellBound pI + 4607 < 2 ^ 128 := by
    have e : qE + verifyCellBound pR + verifyCellBound pI + 4607 = qE + 129015 := by
      rw [verifyCellBound_pIm, verifyCellBound_pR]
    rw [e]; exact hqE
  have h := noRedirect_lean_romP A hw hk hL hq hA fun o₁ o₂ => stageBudgetX_extRomMP A hA o₁ o₂
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + 624) + 936 = 2 * q .h5 + 1560 := by ring
  have eE : qE + (qE + verifyCellBound pR + verifyCellBound pI + 4608) + 9214 = 2 * qE + 138230 := by
    rw [verifyCellBound_pIm, verifyCellBound_pR]; ring
  rw [e3, e5, eE] at h
  exact h

end VoleMole.Theft.Moussaka
