import VoleMole.Theft.PlainSlicesNP
import VoleMole.Theft.PlainRataPermReads
import VoleMole.Theft.PlainRataManyRom

/-!
# No theft for `U` Clients and `M` spends, permutation rows and inverse queries (Ratatouille)

`noTheftN_lean_rom'` (`Theft/PlainRataManyRom.lean`, function rows, forward queries) restated
with **permutation rows** (`ZKRow.perm`) and an adversary over `specP` with **forward and
inverse** cipher queries, on the `N = U + M` slices (`ansPNQ`, `Theft/PlainSlicesNP.lean`):

* **`plainSENL_romP`**: `PlainSENL` for `eRomNP A` (the one-Client `eRomP`) against
  `QBudP q q_E`, error `epsRomP q q_E (totK uovM q)`: `plainSEL_romP` with the slices as advice
  (`locNQ`, `runT_locNQ`).
* `progQMP`, `hpatchMP`, `hlogMP`, `qBudP_redQN`: the forward-only patches and the reduction's
  budget `QBudP (q + N·qPre) (q_E + N·cells(pS))`.
* **`stageBudgetNX_extRomNP`**: the extractor's read budget (each slice at `q h3`, `H₅` at
  `q h5 + N·312`, the permutation table at `q_E + N·cells(pS) + 4608` rows).
* **`noTheftN_lean_romP`**, **`noTheftN_lean_romP'`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Runs of a list of computations, any oracle -/

section Runs

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β E K : Type}

lemma flatMap_qlog_congrG (dec : ι → Option K) (Q : Finset K) (v : E → OracleComp spec β)
    {f f' : (d : ι) → spec d} (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    ∀ l : List E, (∀ d ∈ l.flatMap (fun e => qlog f (v e)), ∀ k, dec d = some k → k ∈ Q) →
      l.flatMap (fun e => qlog f' (v e)) = l.flatMap (fun e => qlog f (v e))
  | [], _ => rfl
  | e :: l, hQ => by
    simp only [List.flatMap_cons] at hQ ⊢
    rw [(runT_congr (v e) f f' fun d hd => h d (hQ d (List.mem_append_left _ hd))).1,
      flatMap_qlog_congrG dec Q v h l fun d hd => hQ d (List.mem_append_right _ hd)]

lemma countP_flatMap_qlog_leG (v : E → OracleComp spec β) (f : (d : ι) → spec d)
    (P : ι → Bool) {n : ℕ} (hb : ∀ e, IsQueryBoundP (v e) (fun d => P d = true) n) :
    ∀ l : List E, (l.flatMap fun e => qlog f (v e)).countP P ≤ l.length * n
  | [] => by simp
  | e :: l => by
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    calc _ ≤ n + l.length * n :=
          Nat.add_le_add (countP_qlog_le (v e) f P (hb e)) (countP_flatMap_qlog_leG v f P hb l)
      _ = (l.length + 1) * n := by ring

lemma runsN_congrG [DecidableEq K] (dec : ι → Option K) (Q : Finset K)
    {f₀ f f₀' f' : (d : ι) → spec d}
    (v : E → OracleComp spec β) (l : List E) (oa : OracleComp spec α)
    (hQ : (((l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa).filterMap dec).toFinset ⊆ Q)
    (h₀ : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f₀ d = f₀' d)
    (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    (l.flatMap fun e => qlog f₀' (v e)) ++ qlog f' oa =
        (l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa ∧ runT f' oa = runT f oa := by
  have hm : ∀ d ∈ (l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa, ∀ k, dec d = some k → k ∈ Q :=
    fun d hd k hk => hQ (mem_decG hd hk)
  have e₀ := flatMap_qlog_congrG dec Q v h₀ l fun d hd => hm d (List.mem_append_left _ hd)
  have e := runT_congr oa f f' fun d hd => h d (hm d (List.mem_append_right _ hd))
  exact ⟨by rw [e₀, e.1], e.2⟩

lemma card_runsN_leG [DecidableEq K] (dec : ι → Option K) (P : ι → Bool)
    (hdec : ∀ d k, dec d = some k → P d = true) (f₀ f : (d : ι) → spec d)
    {v : E → OracleComp spec β} {oa : OracleComp spec α} {n₁ n : ℕ}
    (h₁ : ∀ e, IsQueryBoundP (v e) (fun d => P d = true) n₁)
    (h : IsQueryBoundP oa (fun d => P d = true) n) (l : List E) :
    (((l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa).filterMap dec).toFinset.card ≤
      l.length * n₁ + n := by
  have hc : ∀ l : List ι, l.countP (fun d => (dec d).isSome) ≤ l.countP P :=
    fun l => List.countP_mono_left fun d _ hd => by
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (by simpa using hd)
      exact hdec d k hk
  refine (card_toFinset_filterMap_le _ _).trans ?_
  rw [List.countP_append]
  have a₁ := (hc _).trans (countP_flatMap_qlog_leG v f₀ P h₁ l)
  have a := (hc _).trans (countP_qlog_le oa f P h)
  omega

end Runs

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {U M L : ℕ}

/-! ## Plain extraction from `ROM/`'s permutation-model bound -/

section Plain

variable {G S : Type}

/-- **`ROM/`'s straight-line extractor with `N` slices and inverse queries**: the one-Client
`eRomP`. -/
noncomputable def eRomNP (A : ThiefN Sizes.labelRows U M G S) :
    LogR Sizes.labelRows → Op Sizes.labelRows → List DomP → (Fin (U + M) → Tab3) →
      (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Ratatouille.uovM → Wit :=
  fun _ op qs _ b => eRomP A.base none none op qs zT zT b

/-- `eRomP` reads the query list only through the cells it determines, and not the slices. -/
lemma eRomP_cLog {L' M' : ℕ} (A : Thief Sizes.labelRows G S)
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    {qs qs' : List DomP} (g₁ g₂ g₁' g₂' : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L' M')
    (h : cLog (PTable.fwd b.1.2) (qs.map (toIC b.1.2)) =
      cLog (PTable.fwd b.1.2) (qs'.map (toIC b.1.2))) :
    eRomP A p₁ p₂ op qs g₁ g₂ b = eRomP A p₁ p₂ op qs' g₁' g₂' b :=
  eRom_cLog A p₁ p₂ op g₁ g₂ g₁' g₂' ((b.1.1, fnRows b.1.2), b.2) h

/-- **Plain extraction for `U` Clients and `M` spends from `ROM/`'s permutation-model bound**
(permutation rows, inverse queries, `M = uovM`, `L ≥ Lmin`): `PlainSENL` holds for `eRomNP A`
against the last stages within `QBudP q qE`, with the one-Client error
`epsRomP q qE (totK uovM q)`, for any freshness. -/
theorem plainSENL_romP
    (A : ThiefN Sizes.labelRows U M Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) (q : Kind → ℕ) {qE : ℕ} (hqE : qE + 4607 < 2 ^ 128)
    (Fresh : LogR Sizes.labelRows → Op Sizes.labelRows → Prop) :
    PlainSENL (U + M) ansPNQ (AccOp A.base (leanVIRX hbX) (leanVSRX hbX)) Fresh (RelOp A.base)
      (eRomNP A) (QBudP q qE) (epsRomP q qE (totK Arith.Ratatouille.uovM q)).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_romP A.base hL q hqE (α × (Fin (U + M) → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locNQ b.2 (oa b.1)) fun b => qBudP_locHQ _ _ (hoa b.1)
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α (U + M)
    (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, -, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locNQ z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) z.2.2.2.1.2
  refine ⟨?_, freshOp_none _ _, ?_⟩
  · show AccOp A.base _ _ (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show ¬ RelOp A.base (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
      (eRomP A.base none none (runT (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1)))
        (qlog (ansQ z.2.1.1 z.2.1.2 z.2.2) (locNQ z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRomP_cLog A.base none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches, and the reduction's budget -/

section Patch

/-- **The patch of a simulated proof of either relation, by forward queries.** -/
noncomputable abbrev progQMP : RI → SimCoins pI × SimCoins pS →
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => liftP (progQM xi c)

/-- **The patch's queries, from a log entry** (none for no proof). -/
noncomputable def logQMP {N : ℕ} : Ent Sizes.labelRows → (Fin N → Tab3) →
    (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Ratatouille.uovM → List DomP
  | some (.inl x, .inl π), _, b => logQIP (some (x, π)) zT zT b
  | some (.inr x, .inr π), _, b => logQSP (some (x, π)) zT zT b
  | _, _, _ => []

lemma qBudP_progQMP (xi : RI) (c : SimCoins pI × SimCoins pS) :
    QBudP qPre (verifyCellBound pS) (progQMP xi c) :=
  qBudP_liftP (qBudT_progQM xi c).1

/-- **The patch's queries on the `N` slices are its queries on two.** -/
lemma progQMP_ansPNQ {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    qlog (ansPNQ g t) (progQMP xi c) = qlog (ansQ zT zT t) (progQMP xi c) ∧
      runT (ansPNQ g t) (progQMP xi c) = runT (ansQ zT zT t) (progQMP xi c) :=
  noH3_ansPNQ _ g zT zT t (noH3_of_kindP (qBudP_progQMP xi c).1 qPre_h3 _)

lemma hlogMP {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    qlog (ansPNQ g t) (progQMP xi c) =
      logQMP (pairO (some xi) (simM leanSimIR leanSimSR xi c)) g t.2 := by
  rw [(progQMP_ansPNQ xi c g t).1]
  rcases xi with x | x
  · show qlog (ansQ zT zT t) (progQIP x c.1) = _
    rw [hlogIP x c.1 zT zT t]
    show _ = logQMP (pairO (some (Sum.inl x)) ((leanSimIR x c.1).map Sum.inl)) g t.2
    rcases leanSimIR x c.1 with _ | π <;> rfl
  · show qlog (ansQ zT zT t) (progQSP x c.2) = _
    rw [hlogSP x c.2 zT zT t]
    show _ = logQMP (pairO (some (Sum.inr x)) ((leanSimSR x c.2).map Sum.inr)) g t.2
    rcases leanSimSR x c.2 with _ | π <;> rfl

lemma hpatchMP {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) (d : DomP) :
    ansPNQ g (progM (leanProgIRX hbX) (leanProgSRX hbX) xi c t) d =
      patch2P pI (runT (ansPNQ g t) (progQMP xi c)) d (ansPNQ g t d) := by
  rw [(progQMP_ansPNQ xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPNQ_slPt _ _ hs, ansPNQ_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne (p := pI) (runT (ansQ zT zT t) (progQMP xi c)) (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPNQ_eq g _ zT zT hd, ansPNQ_eq g t zT zT hd]
    rcases xi with x | x
    · exact hpatchIP x c.1 zT zT t d
    · exact hpatchSP x c.2 zT zT t d

lemma logQMP_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Ratatouille.uovM) :
    logQMP none g b = [] := rfl

lemma progM_sndRP (x : RI) (c : SimCoins pI × SimCoins pS)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    (progM (leanProgIRX hbX) (leanProgSRX hbX) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches** (permutation model): the patches' forward queries
(each `qPre` hash queries and `cells(pS)` cells), then the adversary's. -/
theorem qBudP_redQN {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specP α}
    (h : QBudP q qE oa) :
    ∀ ys : List (Option RI × (SimCoins pI × SimCoins pS)),
      QBudP (q + ys.length • qPre) (qE + ys.length * verifyCellBound pS)
        (redQN progQMP (patch2P pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudP_redQN h ys
    have h₁ := qBudP_progQO (fun x c => qBudP_progQMP x c) y.1 y.2
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

lemma logQMP_eq {N : ℕ} (e : Ent Sizes.labelRows) (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Ratatouille.uovM) :
    logQMP e g b = qlog (ansQ zT zT ((fun _ => 0, b) :
      ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM))) (liftP (vQM e)) := by
  rcases e with _ | ⟨x | x, π | π⟩
  · rfl
  · exact logQIP_eq (some (x, π)) zT zT b
  · rfl
  · rfl
  · exact logQSP_eq (some (x, π)) zT zT b

/-- The extractor's query list on the tables `t`: the patches' prefixes, then the last stage's. -/
noncomputable def qsNP {α : Type} {N : ℕ} (ls : List (Ent Sizes.labelRows))
    (oa : OracleComp specP α) (g : Fin N → Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) : List DomP :=
  (ls.flatMap fun e => qlog (ansQ zT zT ((fun _ => 0, t.2) :
    ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM))) (liftP (vQM e))) ++
    qlog (ansPNQ g t) oa

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices and inverse queries**: each slice at
`q h3` keys, `H₅` at `q h5 + N·312` and the permutation table at `qE + N·cells(pS) + 4608`
rows. -/
theorem stageBudgetNX_extRomNP
    (A : ThiefN Sizes.labelRows U M Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    {q : Kind → ℕ} {qE : ℕ}
    {F : (Fin (U + M) → Tab3) → ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM) →
      Op Sizes.labelRows}
    (hF : AdmLN (QBudP q qE) ansPNQ F) (l : LogR Sizes.labelRows) :
    StageBudgetNX (extLN ansPNQ (QBudP q qE) logQMP (eRomNP A) l F) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pS + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQMP) (e := eRomNP A) hF
  set ls := (l.take (U + M)).reverse
  have hlen : ls.length ≤ U + M := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPNQ (QBudP q qE) logQMP (eRomNP A) l F = fun g t =>
      eRomP A.base none none (runT (ansPNQ g t) oa) (qsNP ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomNP qsNP logsL
    congr 2
    exact List.flatMap_congr fun e _ => logQMP_eq e g t.2
  rw [hfun]
  intro x
  have hS : ∀ e, QBudP qPre (verifyCellBound pS) (liftP (vQM e)) := fun e => qBudP_liftP (qBud_vQM e)
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPNQ (Function.update g j u) (atX s x)) oa).filterMap
        (dec3NQ j)).toFinset,
      fun u => card_dec_leG _ _ _ _ (isQueryBoundP_kindP hb.1 .h3) fun _ _ => dec3NQ_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPNQ (Function.update g j u) (atX s x))
      (ansPNQ (Function.update g j u') (atX s x)) fun d hd =>
        ansPNQ_h3 g j u u' _ d fun k hk => hg k (mem_decG hd hk)
    show eRomP A.base none none _ (qsNP ls oa _ _) zT zT _ =
      eRomP A.base none none _ (qsNP ls oa _ _) zT zT _
    unfold qsNP
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsNP ls oa g (atX s x)).filterMap dec5P).toFinset,
      fun s => (card_runsN_leG dec5P (kindBP .h5) (fun _ _ => dec5P_kind) _ _
        (fun e => isQueryBoundP_kindP (hS e).1 .h5) (isQueryBoundP_kindP hb.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congrG dec5P _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansPNQ g (atX (s.1, G5, s.2.2) x)) (fun e => liftP (vQM e)) ls oa subset_rfl
      (fun d hd => ansQ_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_h5 g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomP A.base none none _ (qsNP ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRomP A.base none none _ (qsNP ls oa g (atX s x)) zT zT _
    unfold qsNP
    rw [e1, e2]
    exact eRomP_congr A.base none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the permutations
    refine ⟨fun s => romRowsP A.base (runT (ansPNQ g (atX s x)) oa) (qsNP ls oa g (atX s x))
        s.2.2 x,
      fun s => (card_romRowsP_le _ _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_leG decEP (fun d => d.isRight) (fun _ _ => decEP_right)
        (ansQ zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (ansPNQ g (atX s x)) (fun e => (hS e).2) hb.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pS) hlen
      unfold qsNP
      generalize verifyCellBound pS = c at this h2 ⊢
      omega
    have hsub : ((qsNP ls oa g (atX s x)).filterMap decEP).toFinset ⊆
        romRowsP A.base (runT (ansPNQ g (atX s x)) oa) (qsNP ls oa g (atX s x)) s.2.2 x := by
      rw [romRowsP_eq]
      exact fun k hk => mem_insert_of_mem (mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := runsN_congrG decEP _
      (f₀' := ansQ zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansPNQ g (atX (s.1, s.2.1, E) x)) (fun e => liftP (vQM e)) ls oa hsub
      (fun d hd => ansQ_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansPNQ_E g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomP A.base none none (runT (ansPNQ g (atX (s.1, s.2.1, E) x)) oa)
        (qsNP ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRomP A.base none none (runT (ansPNQ g (atX s x)) oa) (qsNP ls oa g (atX s x)) zT zT _
    have e1' : qsNP ls oa g (atX (s.1, s.2.1, E) x) = qsNP ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRomP_congr A.base none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## No theft for `U` Clients and `M` spends with permutation rows -/

section Theorem

/-- **The extractor**: `eRomNP A` on the reduction's queries. -/
noncomputable def extRomNP
    (A : ThiefN Sizes.labelRows U M Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (q : Kind → ℕ) (qE : ℕ) :
    ExtN Sizes.labelRows U M Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :=
  extLN ansPNQ (QBudP q qE) logQMP (eRomNP A)

variable (A : ThiefN Sizes.labelRows U M Tab3
  (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends with permutation rows, inverse cipher queries and
`ROM/`'s plain extraction** (Ratatouille, `M = uovM`, `L ≥ Lmin`): as `noTheftN_lean_rom`, with
AES as uniformly random permutations (`ZKRow.perm`), an adversary over `specP` within
`QBudP q q_E` on the `N = U + M` slices (no total hash budget), and the extractor `extRomNP`;
`ε_rom = epsRomP (q + N·qPre) (q_E + N·cells(pS)) (totK uovM (q + N·qPre))`. -/
theorem noTheftN_lean_romP (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hqE : qE + (U + M) * verifyCellBound pS + 4607 < 2 ^ 128)
    (hA : ∀ iss sp, AdmLN (QBudP q qE) ansPNQ (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomNP A q qE)) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Equiv.Perm Blk) pS (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
            (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        ((epsRomP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
            (totK Arith.Ratatouille.uovM (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomNP A q qE) j) := by
  have hSB : ∀ iss sp, StageBudgetNX (A.out iss sp) (q .h3) (q .h5) qE := fun iss sp => by
    obtain ⟨oa, hb, hF⟩ := hA iss sp
    rw [hF]
    exact stageBudgetNX_runTNQ hb
  have hX : ∀ pb l, StageBudgetNX (extRomNP A q qE l (opN A pb l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pS + 4608) :=
    fun pb l => stageBudgetNX_extRomNP A (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) →
      ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM) →
      Op Sizes.labelRows, AdmLN (QBudP q qE) ansPNQ F →
      Hit.AdmHitN (R := Equiv.Perm Blk) (p := pI) (L := L) (M := Arith.Ratatouille.uovM)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTNQ hb
  exact noTheftN_of_se (CI := SimCoins pI) (CS := SimCoins pS) A (leanPIRX hbX) (leanPSRX hbX)
    leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
    (extRomNP A q qE) (leanPIRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPSRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPI_budgetX' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPS_budgetX' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_ok A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanVIRX hbX)
      (leanVSRX hbX) (extRomNP A q qE)
      (weakSEN_of_plainL progQMP (patch2P pI) logQMP
        (plainSENL_romP A hL _ hqE (FreshOkN A))
        ((progMovesN_hit A hL (q .mu) (q .h21) (q .h22)).mono hAH) progM_sndRP hpatchMP hlogMP
        logQMP_none fun oa ys hl h => hl ▸ qBudP_redQN h ys)
      hA)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends with permutation rows**, the hops' budgets
simplified (`cells(pS) = 142844`), for `q_E + N·142844 + 4607 < 2¹²⁸`:

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·147451 + 4608),   N = U + M. -/
theorem noTheftN_lean_romP' (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hqE : qE + (U + M) * 142844 + 4607 < 2 ^ 128)
    (hA : ∀ iss sp, AdmLN (QBudP q qE) ansPNQ (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomNP A q qE)) ≤
      U * ZKRow.εz (Equiv.Perm Blk) pI (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 147451 + 4608) +
        M * ZKRow.εz (Equiv.Perm Blk) pS (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 147451 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
            (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        ((epsRomP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
            (totK Arith.Ratatouille.uovM (q + (U + M) • qPre))).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomNP A q qE) j) := by
  have hq : qE + (U + M) * verifyCellBound pS + 4607 < 2 ^ 128 := by
    rw [verifyCellBound_pS]; exact hqE
  have h := noTheftN_lean_romP A hL hq hA
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 147451 + 4608 := by
    rw [verifyCellBound_pS]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

end Ratatouille

end VoleMole.Theft
