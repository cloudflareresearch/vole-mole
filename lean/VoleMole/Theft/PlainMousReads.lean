import VoleMole.Theft.PlainMousRedirect
import VoleMole.Theft.PlainRataReads

/-!
# The read budget of `ROM/`'s extractor in the redirect game (Moussaka)

The Moussaka counterpart of `Theft/PlainRataReads.lean`: `noRedirect_lean_rom`
(`Theft/PlainMousRedirect.lean`) has the read budget `hX` of its extractor `extRomM` as a
hypothesis; here it is proved, with the row sets of `ROM/ExtractCells.lean`.

* `vQIm`, `vQR`: the patches' prefix computations as one oracle computation each (`logQIm_eq`,
  `logQRm_eq`), with `QBud qPre (cells p)`.
* `romRowsM`, **`eRomM_congr`**: `eRomM` reads neither the slices nor `H₅`, and the cipher only in
  the cells' rows of its query list, the reconstruction's rows and the zero key's row.
* **`stageBudgetX_extRomM`**: `extRomM` reads each `H₃` slice at `q h3` keys, `H₅` at `q h5 + 624`
  and the cipher at `qE + cells(pR) + cells(pI) + 4608` rows, `cells(pI) = 55292`,
  `cells(pR) = 69116` (`verifyCellBound_pIm`, `verifyCellBound_pR`).
* **`noRedirect_lean_rom'`**: `noRedirect_lean_rom` without `hX`:

      Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_rom
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 138230)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

/-! ## The patches' queries as runs -/

/-- The issuance patch's prefix computation (none for no proof). -/
noncomputable def vQIm : Option (IssueInstance × Bytes) → OracleComp specIC ByteArray
  | none => pure ByteArray.empty
  | some (x, π) => vPreIC CrtGen.tables (Privacy.Moussaka.stI x) (toBA π)

/-- The redemption patch's prefix computation (none for no proof). -/
noncomputable def vQR : Option (RedeemInstance × Bytes) → OracleComp specIC ByteArray
  | none => pure ByteArray.empty
  | some (x, π) => vPreIC CrtGen.tables (Privacy.Moussaka.stR x) (toBA π)

section Patches

variable {R : Type} [CipherRow R] {L M : ℕ}

lemma logQIm_eq (p₁ : Option (IssueInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → R)) × XTab L M) :
    logQIm p₁ g₁ g₂ b = qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M))) (vQIm p₁) := by
  rcases p₁ with _ | ⟨x, π⟩ <;> rfl

lemma logQRm_eq (p₂ : Option (RedeemInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → R)) × XTab L M) :
    logQRm p₂ g₁ g₂ b = qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M))) (vQR p₂) := by
  rcases p₂ with _ | ⟨x, π⟩ <;> rfl

end Patches

lemma qBud_vQIm (p₁ : Option (IssueInstance × Bytes)) :
    QBud Ratatouille.qPre (verifyCellBound pI) (vQIm p₁) := by
  rcases p₁ with _ | ⟨x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩

lemma qBud_vQR (p₂ : Option (RedeemInstance × Bytes)) :
    QBud Ratatouille.qPre (verifyCellBound pR) (vQR p₂) := by
  rcases p₂ with _ | ⟨x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩

set_option maxRecDepth 100000 in
lemma verifyCellBound_pIm : verifyCellBound pI = 55292 := by
  rw [verifyCellBound_eq]; decide

set_option maxRecDepth 100000 in
lemma verifyCellBound_pR : verifyCellBound pR = 69116 := by
  rw [verifyCellBound_eq]; decide

/-! ## The rows `eRomM` reads -/

variable {L : ℕ}

/-- **The rows `eRomM` reads**: the cells' rows of the query list, the reconstruction's rows of the
operation's proof, and the zero key's row. -/
noncomputable def romRowsM (op : MOp) (qs : List DomIC) (E : Blk → Blk → Blk)
    (x : XTab L Arith.Moussaka.M) : Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    treeRows E (ivOf (hbX x) ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩
        ((Hit.Mous.fd op).1.mu1 (hbX x)))
      (Proof.opening ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩)
      (Proof.delta ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩))

lemma card_romRowsM_le (op : MOp) (qs : List DomIC) (E : Blk → Blk → Blk)
    (x : XTab L Arith.Moussaka.M) :
    (romRowsM op qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (card_treeRows_le E
      (ivOf (hbX x) ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩
        ((Hit.Mous.fd op).1.mu1 (hbX x)))
      (Proof.opening ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩)
      (Proof.delta ⟨(Hit.Mous.fd op).1.params, (Hit.Mous.fd op).2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

/-- **`eRomM` reads neither the slices nor `H₅`, and the cipher only in `romRowsM`.** -/
theorem eRomM_congr
    (p₁ : Option (IssueInstance × Bytes))
    (p₂ : Option (RedeemInstance × Bytes)) (op : MOp)
    (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {E E' : Blk → Blk → Blk}
    (x : XTab L Arith.Moussaka.M) (h : ∀ k ∈ romRowsM op qs E x, E k = E' k) :
    eRomM p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRomM p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  show pickM _ _ _ = pickM _ _ _
  dsimp only
  have hc : cLog (Ratatouille.ctOf E') qs = cLog (Ratatouille.ctOf E) qs :=
    (Ratatouille.cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      rw [h c.1 (mem_insert_of_mem (mem_union_left _ (mem_dec hc rfl)))]).symm
  rw [hc]
  unfold romRowsM at h
  generalize Hit.Mous.fd op = f at h ⊢
  generalize cLog (Ratatouille.ctOf E) qs = log at hc ⊢
  have hsub : logKeys log ⊆ (qs.filterMap decE).toFinset := hc ▸ Ratatouille.logKeys_cLog_subset _ _
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
  have hr : Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E') log = Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E) log := by
    unfold Ratatouille.rOut
    rw [← hk, ← hkn]
  rw [hr]
  generalize hR : Ratatouille.rOut f.1 f.2 (hbX x) (Ratatouille.ctOf E) log = r
  have hu' : ∀ (i : Fin BAVC.tau) (j : ℕ), @uBit (icPrg (Ratatouille.ctOf E').cipher) f.1.params (outChain r).iv
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

/-- The extractor's query list on the tables `t`: the two prefixes' queries (on the tables with
`H₂³` zero, as `logQI`, `logQS`), then the last stage's. -/
noncomputable def qsRM {α : Type} {L M : ℕ} (p₁ : Option (IssueInstance × Bytes))
    (p₂ : Option (RedeemInstance × Bytes)) (oa : OracleComp specIC α)
    (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) pI (XTab L M)) : List DomIC :=
  qlog (ansP g₁ g₂ ((fun _ => 0, t.2) : ShX (Blk → Blk) pI (XTab L M))) (vQR p₂) ++
    (qlog (ansP g₁ g₂ ((fun _ => 0, t.2) : ShX (Blk → Blk) pI (XTab L M))) (vQIm p₁) ++
      qlog (ansP g₁ g₂ t) oa)

variable {L : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The read budget of `ROM/`'s extractor in the redirect game**: for an adversary whose last stage
is the run of an oracle computation within `QBudT q qE nG`, `extRomM` reads each `H₃` slice at
`q h3` keys, `H₅` at `q h5 + 624` (the last stage's and the two prefixes' `312` gate inputs) and
the cipher at `qE + cells(pR) + cells(pI) + 4608` rows (the last stage's and the prefixes' cells,
the reconstruction's `4607` rows and the zero key's). -/
theorem stageBudgetX_extRomM
    (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    {q : Kind → ℕ} {qE nG : ℕ} (hA : ∀ o₁ o₂, AdmL (QBudT q qE nG) ansP (A.out o₁ o₂))
    (o₁ : Bytes) (o₂ : Except Error Bytes) :
    StageBudgetX (extRomM q qE nG (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) (q .h3) (q .h5 + 624)
      (qE + verifyCellBound pR + verifyCellBound pI + 4608) := by
  obtain ⟨oa, hb, he⟩ := extL_of_admL (logQ₁ := logQIm) (logQ₂ := logQRm) (e := eRomM) (hA o₁ o₂)
  set p₁ := stI A o₁
  set p₂ := stR A o₁ o₂
  have hfun : extRomM q qE nG p₁ p₂ (A.out o₁ o₂) = fun g₁ g₂ t =>
      eRomM p₁ p₂ (runT (ansP g₁ g₂ t) oa) (qsRM p₁ p₂ oa g₁ g₂ t) g₁ g₂ t.2 := by
    unfold extRomM
    rw [he]
    funext g₁ g₂ t
    rw [logQIm_eq, logQRm_eq]
    rfl
  rw [hfun]
  intro x
  have hS := qBud_vQR p₂
  have hI := qBud_vQIm p₁
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · -- the first slice
    refine ⟨fun g₁ => ((qsRM p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3 false)).toFinset,
      fun g₁ => (card_runs_le (dec3 false) (kindB .h3) (fun _ _ => dec3_kind) _ _
        (isQueryBoundP_kind hS.1 .h3) (isQueryBoundP_kind hI.1 .h3)
        (isQueryBoundP_kind hb.1.1 .h3)).trans (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]),
      fun g₁ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr (dec3 false) _ (f₀' := ansP g' g₂ _) (f' := ansP g' g₂ (atX s x))
      (vQR p₂) (vQIm p₁) oa subset_rfl
      (fun d hd => ansP_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansP_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g' g₂ (atX s x)) _ _ _ = eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRM
    rw [e1, e2]
    rfl
  · -- the second slice
    refine ⟨fun g₂ => ((qsRM p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3 true)).toFinset,
      fun g₂ => (card_runs_le (dec3 true) (kindB .h3) (fun _ _ => dec3_kind) _ _
        (isQueryBoundP_kind hS.1 .h3) (isQueryBoundP_kind hI.1 .h3)
        (isQueryBoundP_kind hb.1.1 .h3)).trans (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]),
      fun g₂ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr (dec3 true) _ (f₀' := ansP g₁ g' _) (f' := ansP g₁ g' (atX s x))
      (vQR p₂) (vQIm p₁) oa subset_rfl
      (fun d hd => ansP_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansP_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g₁ g' (atX s x)) _ _ _ = eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRM
    rw [e1, e2]
    rfl
  · -- `H₅`
    refine ⟨fun s => ((qsRM p₁ p₂ oa g₁ g₂ (atX s x)).filterMap dec5).toFinset,
      fun s => (card_runs_le dec5 (kindB .h5) (fun _ _ => dec5_kind) _ _
        (isQueryBoundP_kind hS.1 .h5) (isQueryBoundP_kind hI.1 .h5)
        (isQueryBoundP_kind hb.1.1 .h5)).trans (by simp [Ratatouille.qPre, extractorQueries, vPreQueries]; omega),
      fun s G5 hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr dec5 _
      (f₀' := ansP g₁ g₂ ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansP g₁ g₂ (atX (s.1, G5, s.2.2) x)) (vQR p₂) (vQIm p₁) oa subset_rfl
      (fun d hd => ansP_h5 g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansP_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g₁ g₂ (atX (s.1, G5, s.2.2) x)) _ _ _ =
      eRomM p₁ p₂ _ (qsRM p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRM
    rw [e1, e2]
    exact eRomM_congr p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 G5 x fun _ _ => rfl
  · -- the cipher
    refine ⟨fun s => romRowsM (runT (ansP g₁ g₂ (atX s x)) oa) (qsRM p₁ p₂ oa g₁ g₂ (atX s x)) s.2.2 x,
      fun s => (card_romRowsM_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runs_le decE (fun d => d.isRight) (fun _ _ => decE_right)
        (ansP g₁ g₂ ((fun _ => 0, (atX s x).2) : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (ansP g₁ g₂ (atX s x)) hS.2 hI.2 hb.1.2
      unfold qsRM
      omega
    obtain ⟨e1, e2⟩ := runs_congr decE _
      (f₀' := ansP g₁ g₂ ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansP g₁ g₂ (atX (s.1, s.2.1, E) x)) (vQR p₂) (vQIm p₁) oa
      (fun k hk => mem_insert_of_mem (mem_union_left _ hk))
      (fun d hd => ansP_E g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansP_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomM p₁ p₂ (runT (ansP g₁ g₂ (atX (s.1, s.2.1, E) x)) oa)
        (qsRM p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x)) _ _ _ =
      eRomM p₁ p₂ (runT (ansP g₁ g₂ (atX s x)) oa) (qsRM p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    have e1' : qsRM p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x) = qsRM p₁ p₂ oa g₁ g₂ (atX s x) := e1
    rw [e1', e2]
    exact eRomM_congr p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 s.2.1 x hg

/-- **Redemption non-malleability with `ROM/`'s plain extraction, without a read-budget
hypothesis** (Moussaka, one token): `noRedirect_lean_rom` with the extractor's read budget proved
(`stageBudgetX_extRomM`):

    Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 138230)` and `ε_rom = epsRomM (q + 2·qPre)
(q_E + cells(pR) + cells(pI)) (nG + 2·338)`. -/
theorem noRedirect_lean_rom' (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE nG : ℕ} (hA : ∀ o₁ o₂, AdmL (QBudT q qE nG) ansP (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomM q qE nG)) ≤
      ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        ZKRow.εz (Blk → Blk) pR (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        ((epsRomM (q + Ratatouille.qPre + Ratatouille.qPre)
          (qE + verifyCellBound pR + verifyCellBound pI) (nG + 338 + 338)).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extRomM q qE nG) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have h := noRedirect_lean_rom A hw hk hL hA fun o₁ o₂ => stageBudgetX_extRomM A hA o₁ o₂
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + 624) + 936 = 2 * q .h5 + 1560 := by ring
  have eE : qE + (qE + verifyCellBound pR + verifyCellBound pI + 4608) + 9214 = 2 * qE + 138230 := by
    rw [verifyCellBound_pIm, verifyCellBound_pR]; ring
  rw [e3, e5, eE] at h
  exact h

end VoleMole.Theft.Moussaka
