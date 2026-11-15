import VoleMole.Theft.PlainRataManyPerm
import VoleMole.Theft.PlainMousPermReads
import VoleMole.Theft.PlainMousManyRom

/-!
# Redemption non-malleability for `U` tokens, permutation rows and inverse queries (Moussaka)

`noRedirectN_lean_rom'` (`Theft/PlainMousManyRom.lean`, function rows, forward queries) restated
with **permutation rows** (`ZKRow.perm`) and an adversary over `specP` with **forward and
inverse** cipher queries, on the `N = U + M` slices (`ansPNQ`), as `noTheftN_lean_romP'`
(`Theft/PlainRataManyPerm.lean`) for Ratatouille:

* **`plainSENL_romMP`**: `plainSEL_romMP` with the slices as advice, for `FreshKN kt`.
* `progQMmP`, `hpatchMmP`, `hlogMmP`, `qBudP_redQNm`: the forward-only patches.
* **`stageBudgetNX_extRomMNP`**: the extractor's read budget.
* **`noRedirectN_lean_romP`**, **`noRedirectN_lean_romP'`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre qPre_h3 qPre_h5 advEquiv fnRows romRowsP_eq)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {U M L : ℕ}

/-! ## Plain extraction from `ROM/`'s permutation-model bound -/

section Plain

/-- **`ROM/`'s straight-line extractor with `N` slices and inverse queries**: `eRomMP`. -/
noncomputable def eRomMNP (N : ℕ) : Log → MOp → List DomP → (Fin N → Tab3) →
    (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ op qs _ b => eRomMP none none op qs zT zT b

/-- `eRomMP` reads the query list only through the cells it determines, and not the slices. -/
lemma eRomMP_cLog (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : MOp) {qs qs' : List DomP} (g₁ g₂ g₁' g₂' : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M)
    (h : cLog (PTable.fwd b.1.2) (qs.map (toIC b.1.2)) =
      cLog (PTable.fwd b.1.2) (qs'.map (toIC b.1.2))) :
    eRomMP p₁ p₂ op qs g₁ g₂ b = eRomMP p₁ p₂ op qs' g₁' g₂' b :=
  eRomM_cLog p₁ p₂ op g₁ g₂ g₁' g₂' ((b.1.1, fnRows b.1.2), b.2) h

set_option maxHeartbeats 1000000 in
/-- **Plain extraction for `U` tokens and `M` redemptions from `ROM/`'s permutation-model bound**
(permutation rows, inverse queries, `M = Moussaka.M`, `L ≥ 8193`): `PlainSENL` for `eRomMNP`
against `QBudP q qE`, for `FreshKN kt`, with the one-token error
`epsRomMP q qE (totK Moussaka.M q)`. -/
theorem plainSENL_romMP (kt : Bytes → UOVKey) (hL : Lrom ≤ L) (N : ℕ) (q : Kind → ℕ) {qE : ℕ}
    (hqE : qE + 4607 < 2 ^ 128) :
    PlainSENL N (ansPNQ (p := pI) (L := L) (M := Arith.Moussaka.M))
      (AccOp (verILX hbX) (verRLX hbX)) (FreshKN kt) RelOp (eRomMNP (L := L) N) (QBudP q qE)
      (epsRomMP q qE (totK Arith.Moussaka.M q)).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_romMP (L := L) kt hL q hqE (α × (Fin N → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locNQ b.2 (oa b.1)) fun b => qBudP_locHQ _ _ (hoa b.1)
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α N
    (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, hfr, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) z.2.2.2.1.2
  refine ⟨?_, ?_, ?_⟩
  · show AccOp _ _ (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show FreshK kt none none (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
    rw [hr]
    exact ⟨hfr.1.freshOk, hfr.2⟩
  · show ¬ RelOp (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
      (eRomMP none none (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
        (qlog (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRomMP_cLog none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches, and the reduction's budget -/

section Patch

/-- **The patch of a simulated proof of either relation, by forward queries.** -/
noncomputable abbrev progQMmP : MI → SimCoins pI × SimCoins pR →
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => liftP (progQMm xi c)

/-- **The patch's queries, from a log entry** (none for no proof). -/
noncomputable def logQMmP {N : ℕ} : Option (MI × Bytes) → (Fin N → Tab3) →
    (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M → List DomP
  | some (.inl x, π), _, b => logQIPm (some (x, π)) zT zT b
  | some (.inr x, π), _, b => logQRPm (some (x, π)) zT zT b
  | none, _, _ => []

lemma qBudP_progQMmP (xi : MI) (c : SimCoins pI × SimCoins pR) :
    QBudP qPre (verifyCellBound pR) (progQMmP xi c) :=
  qBudP_liftP (qBudT_progQMm xi c).1

lemma progQMmP_ansPNQ {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPNQ g t) (progQMmP xi c) = qlog (ansQ zT zT t) (progQMmP xi c) ∧
      runT (ansPNQ g t) (progQMmP xi c) = runT (ansQ zT zT t) (progQMmP xi c) :=
  noH3_ansPNQ _ g zT zT t (noH3_of_kindP (qBudP_progQMmP xi c).1 qPre_h3 _)

lemma hlogMmP {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPNQ g t) (progQMmP xi c) =
      logQMmP (pairO (some xi) (simM (leanSim pI) (leanSim pR) xi c)) g t.2 := by
  rw [(progQMmP_ansPNQ xi c g t).1]
  rcases xi with x | x
  · exact hlogIPm x c.1 zT zT t
  · exact hlogRPm x c.2 zT zT t

lemma hpatchMmP {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) (d : DomP) :
    ansPNQ g (progM (leanProgIX hbX) (leanProgRX hbX) xi c t) d =
      patch2P pI (runT (ansPNQ g t) (progQMmP xi c)) d (ansPNQ g t d) := by
  rw [(progQMmP_ansPNQ xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPNQ_slPt _ _ hs, ansPNQ_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne (p := pI) (runT (ansQ zT zT t) (progQMmP xi c)) (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPNQ_eq g _ zT zT hd, ansPNQ_eq g t zT zT hd]
    rcases xi with x | x
    · exact hpatchIPm x c.1 zT zT t d
    · exact hpatchRPm x c.2 zT zT t d

lemma logQMmP_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) :
    logQMmP none g b = [] := rfl

lemma progM_sndMP (x : MI) (c : SimCoins pI × SimCoins pR)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :
    (progM (leanProgIX hbX) (leanProgRX hbX) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches** (permutation model). -/
theorem qBudP_redQNm {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specP α}
    (h : QBudP q qE oa) :
    ∀ ys : List (Option MI × (SimCoins pI × SimCoins pR)),
      QBudP (q + ys.length • qPre) (qE + ys.length * verifyCellBound pR)
        (redQN progQMmP (patch2P pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudP_redQNm h ys
    have h₁ := Ratatouille.qBudP_progQO (fun x c => qBudP_progQMmP x c) y.1 y.2
    refine ⟨?_, ?_⟩
    · refine IsKindQueryBoundP.mono (isKindQueryBoundP_bind h₁.1 fun m =>
        isQueryBound_simP _ ih.1) fun k => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, List.length_cons]
      exact le_of_eq (by ring)
    · refine (isQueryBoundP_bind h₁.2 fun m _ => isQueryBoundP_simP _ ih.2).mono ?_
      simp only [List.length_cons]
      exact le_of_eq (by ring)

end Patch

/-! ## The extractor's read budget -/

section Reads

lemma logQMmP_eq {N : ℕ} (e : Option (MI × Bytes)) (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) :
    logQMmP e g b = qlog (ansQ zT zT ((fun _ => 0, b) :
      ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M))) (liftP (vQMm e)) := by
  rcases e with _ | ⟨x | x, π⟩
  · rfl
  · exact logQIPm_eq (some (x, π)) zT zT b
  · exact logQRPm_eq (some (x, π)) zT zT b

/-- The extractor's query list on the tables `t`: the patches' prefixes, then the last stage's. -/
noncomputable def qsNMP {α : Type} {N : ℕ} (ls : List (Option (MI × Bytes)))
    (oa : OracleComp specP α) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) : List DomP :=
  (ls.flatMap fun e => qlog (ansQ zT zT ((fun _ => 0, t.2) :
    ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M))) (liftP (vQMm e))) ++
    qlog (ansPNQ g t) oa

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices and inverse queries** (Moussaka):
each slice at `q h3` keys, `H₅` at `q h5 + N·312`, the permutation table at
`qE + N·cells(pR) + 4608` rows. -/
theorem stageBudgetNX_extRomMNP {N : ℕ} {q : Kind → ℕ} {qE : ℕ}
    {F : (Fin N → Tab3) → ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M) → MOp}
    (hF : AdmLN (QBudP q qE) ansPNQ F) (l : Log) :
    StageBudgetNX (extLN ansPNQ (QBudP q qE) logQMmP (eRomMNP N) l F) (q .h3)
      (q .h5 + N * 312) (qE + N * verifyCellBound pR + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQMmP) (e := eRomMNP N) hF
  set ls := (l.take N).reverse
  have hlen : ls.length ≤ N := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPNQ (QBudP q qE) logQMmP (eRomMNP N) l F = fun g t =>
      eRomMP none none (runT (ansPNQ g t) oa) (qsNMP ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomMNP qsNMP logsL
    congr 2
    exact List.flatMap_congr fun e _ => logQMmP_eq e g t.2
  rw [hfun]
  intro x
  have hS : ∀ e, QBudP qPre (verifyCellBound pR) (liftP (vQMm e)) :=
    fun e => qBudP_liftP (qBud_vQMm e)
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPNQ (Function.update g j u) (atX s x)) oa).filterMap
        (dec3NQ j)).toFinset,
      fun u => card_dec_leG _ _ _ _ (isQueryBoundP_kindP hb.1 .h3) fun _ _ => dec3NQ_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPNQ (Function.update g j u) (atX s x))
      (ansPNQ (Function.update g j u') (atX s x)) fun d hd =>
        ansPNQ_h3 g j u u' _ d fun k hk => hg k (mem_decG hd hk)
    show eRomMP none none _ (qsNMP ls oa _ _) zT zT _ =
      eRomMP none none _ (qsNMP ls oa _ _) zT zT _
    unfold qsNMP
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsNMP ls oa g (atX s x)).filterMap dec5P).toFinset,
      fun s => (card_runsN_leG dec5P (kindBP .h5) (fun _ _ => dec5P_kind) _ _
        (fun e => isQueryBoundP_kindP (hS e).1 .h5) (isQueryBoundP_kindP hb.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congrG dec5P _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansPNQ g (atX (s.1, G5, s.2.2) x)) (fun e => liftP (vQMm e)) ls oa subset_rfl
      (fun d hd => ansQ_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_h5 g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomMP none none _ (qsNMP ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRomMP none none _ (qsNMP ls oa g (atX s x)) zT zT _
    unfold qsNMP
    rw [e1, e2]
    exact eRomMP_congr none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the permutations
    refine ⟨fun s => romRowsMP (runT (ansPNQ g (atX s x)) oa) (qsNMP ls oa g (atX s x)) s.2.2 x,
      fun s => (card_romRowsMP_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_leG decEP (fun d => d.isRight) (fun _ _ => decEP_right)
        (ansQ zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (ansPNQ g (atX s x)) (fun e => (hS e).2) hb.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pR) hlen
      unfold qsNMP
      generalize verifyCellBound pR = c at this h2 ⊢
      omega
    have hsub : ((qsNMP ls oa g (atX s x)).filterMap decEP).toFinset ⊆
        romRowsMP (runT (ansPNQ g (atX s x)) oa) (qsNMP ls oa g (atX s x)) s.2.2 x := by
      rw [romRowsMP_eq]
      exact fun k hk => mem_insert_of_mem (mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := runsN_congrG decEP _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansPNQ g (atX (s.1, s.2.1, E) x)) (fun e => liftP (vQMm e)) ls oa hsub
      (fun d hd => ansQ_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_E g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomMP none none (runT (ansPNQ g (atX (s.1, s.2.1, E) x)) oa)
        (qsNMP ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRomMP none none (runT (ansPNQ g (atX s x)) oa) (qsNMP ls oa g (atX s x)) zT zT _
    have e1' : qsNMP ls oa g (atX (s.1, s.2.1, E) x) = qsNMP ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRomMP_congr none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## Redemption non-malleability for `U` tokens with permutation rows -/

section Theorem

/-- **The extractor**: `eRomMNP` on the reduction's queries. -/
noncomputable def extRomMNP (q : Kind → ℕ) (qE : ℕ) :
    ExtN U M Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :=
  extLN ansPNQ (QBudP q qE) logQMmP (eRomMNP (U + M))

variable (A : ThiefN U M Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions with permutation rows,
inverse cipher queries and `ROM/`'s plain extraction** (Moussaka, `M = Moussaka.M`, `L ≥ 8193`):
as `noRedirectN_lean_rom`, with `ZKRow.perm`, an adversary over `specP` within `QBudP q q_E` (no
total hash budget) and the extractor `extRomMNP`;
`ε_rom = epsRomMP (q + N·qPre) (q_E + N·cells(pR)) (totK Moussaka.M (q + N·qPre))`. -/
theorem noRedirectN_lean_romP (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hL : Lrom ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hqE : qE + (U + M) * verifyCellBound pR + 4607 < 2 ^ 128)
    (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMNP q qE)) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Equiv.Perm Blk) pR (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((epsRomMP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMNP q qE) h) := by
  have hSB : ∀ reqs reds, StageBudgetNX (A.out reqs reds) (q .h3) (q .h5) qE := fun reqs reds => by
    obtain ⟨oa, hb, hF⟩ := hA reqs reds
    rw [hF]
    exact stageBudgetNX_runTNQ hb
  have hX : ∀ l, StageBudgetNX (extRomMNP q qE l (opN A l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pR + 4608) :=
    fun l => stageBudgetNX_extRomMNP (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) → ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M) →
      MOp, AdmLN (QBudP q qE) ansPNQ F →
      Hit.AdmHitN (R := Equiv.Perm Blk) (p := pI) (L := L) (M := Arith.Moussaka.M)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTNQ hb
  have hL' : Hit.Mous.Lmin ≤ L := lmin_le_lrom.trans hL
  have hmv := ((progMovesN_hit (U := U) (M := M) (R := Equiv.Perm Blk) hL' (q .mu) (q .h21)
    (q .h22)).mono hAH).fresh_mono (Fresh' := FreshKN kt) fun _ _ h => h.1
  exact noRedirectN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIX hbX) (leanPRX hbX)
    (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (verILX hbX) (verRLX hbX)
    (extRomMNP q qE) (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPN_budgetXI' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPN_budgetXR' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_okK A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (verILX hbX)
      (verRLX hbX) (extRomMNP q qE) hw hk
      (weakSEN_of_plainL progQMmP (patch2P pI) logQMmP (plainSENL_romMP kt hL _ _ hqE) hmv
        progM_sndMP hpatchMmP hlogMmP logQMmP_none fun oa ys hl h => hl ▸ qBudP_redQNm h ys)
      fun _ => hA _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens with permutation rows**, the hops' budgets
simplified (`cells(pR) = 69116`), for `q_E + N·69116 + 4607 < 2¹²⁸`:

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·73723 + 4608),   N = U + M. -/
theorem noRedirectN_lean_romP' (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hL : Lrom ≤ L) {q : Kind → ℕ} {qE : ℕ} (hqE : qE + (U + M) * 69116 + 4607 < 2 ^ 128)
    (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMNP q qE)) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 73723 + 4608) +
        M * ZKRow.εz (Equiv.Perm Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 73723 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((epsRomMP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMNP q qE) h) := by
  have hq : qE + (U + M) * verifyCellBound pR + 4607 < 2 ^ 128 := by
    rw [verifyCellBound_pR]; exact hqE
  have h := noRedirectN_lean_romP A hw hk hL hq hA
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 73723 + 4608 := by
    rw [verifyCellBound_pR]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

end VoleMole.Theft.Moussaka
