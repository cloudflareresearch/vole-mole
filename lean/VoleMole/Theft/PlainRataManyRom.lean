import VoleMole.Theft.PlainSlicesN
import VoleMole.Theft.ManyPlainLog
import VoleMole.Theft.PlainRataReads
import VoleMole.Theft.RatatouilleManyHit

/-!
# Plain extraction for `U` Clients and `M` spends from `ROM/`'s bound (Ratatouille)

`noTheftN_leanX_hit` (`Theft/RatatouilleManyHit.lean`) keeps plain extraction `PlainSEN` as a
hypothesis. Here it is replaced by `PlainSENL` (`Theft/ManyPlainLog.lean`) and proved from
`ROM/`'s simultaneous extraction, as `noTheft_lean_rom'` does for one Client
(`docs/security/ratatouille.md` §5, item 5):

* **`plainSENL_rom`**: `PlainSENL` for `ROM/`'s straight-line extractor (`eRomN A`: `eRom` of the
  one-Client file, which reads only the cipher entries of the query list) against `QBudT q qE nG`,
  with the one-Client error `ε_rom q qE nG`. The adversary on the `N` slices is the adversary on
  two slices with the slice queries answered locally (`locN`, `runT_locN`): `plainSEL_rom`
  applies with the slices as advice.
* `progQM`, `logQM`: the patches of the sum of the two simulators, by queries (the one-Client
  `progQI`, `progQS`, which make no `H₃` query, so they run on `ansPN` as on `ansP`:
  `hlogM`, `hpatchM`). **`qBudT_redQN`**: the reduction for `N` patches is within
  `QBudT (q + N·qPre) (qE + N·cells(pS)) (nG + N·338)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.ZK.Sim
  VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

variable {U M L : ℕ}

/-! ## Plain extraction from `ROM/`'s bound -/

section Plain

variable {G S : Type}

/-- **`ROM/`'s straight-line extractor with `N` slices**: the one-Client extractor `eRom`, which
reads the operation, the cipher entries of the query list, the cipher rows and the extra table. -/
noncomputable def eRomN (A : ThiefN Sizes.labelRows U M G S) :
    LogR Sizes.labelRows → Op Sizes.labelRows → List DomIC → (Fin (U + M) → Tab3) →
      (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Ratatouille.uovM → Wit :=
  fun _ op qs _ b => eRom A.base none none op qs zT zT b

/-- `eRom` reads the query list only through its cipher entries, and not the slices. -/
lemma eRom_cLog {L' M' : ℕ} (A : Thief Sizes.labelRows G S)
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    {qs qs' : List DomIC} (g₁ g₂ g₁' g₂' : Tab3) (b : (Tab5F × (Blk → Blk → Blk)) × XTab L' M')
    (h : cLog (ctOf b.1.2) qs = cLog (ctOf b.1.2) qs') :
    eRom A p₁ p₂ op qs g₁ g₂ b = eRom A p₁ p₂ op qs' g₁' g₂' b := by
  obtain ⟨⟨G5, E⟩, x⟩ := b
  rw [eRom_eq, eRom_eq]
  simp only at h
  rw [h]

lemma freshOp_none (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) :
    FreshOp A none none op := by
  cases op <;> exact fun y hy => by cases hy

/-- The slices as advice: `(α × slices) × ((two slices) × tables)` is
`(two slices) × (α × (slices × tables))`. -/
def advEquiv (α : Type) (N : ℕ) (S : Type) : (α × (Fin N → Tab3)) × ((Tab3 × Tab3) × S) ≃
    (Tab3 × Tab3) × (α × ((Fin N → Tab3) × S)) where
  toFun z := (z.2.1, (z.1.1, (z.1.2, z.2.2)))
  invFun y := ((y.2.1, y.2.2.1), (y.1, y.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Plain extraction for `U` Clients and `M` spends from `ROM/`'s bound** (function rows,
`M = uovM`, `L ≥ Lmin`): `PlainSENL` holds for `ROM/`'s straight-line extractor `eRomN A` against
the last stages within `QBudT q qE nG`, with the one-Client error `epsRom q qE nG`, for any
freshness. -/
theorem plainSENL_rom
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) (q : Kind → ℕ) (qE nG : ℕ)
    (Fresh : LogR Sizes.labelRows → Op Sizes.labelRows → Prop) :
    PlainSENL (U + M) ansPN (AccOp A.base (leanVIRX hbX) (leanVSRX hbX)) Fresh (RelOp A.base)
      (eRomN A) (QBudT q qE nG) (epsRom q qE nG).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_rom A.base hL q qE nG (α × (Fin (U + M) → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locN b.2 (oa b.1)) fun b => qBudT_locN (hoa b.1) b.2
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α (U + M)
    (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, -, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) (ctOf z.2.2.2.1.2)
  refine ⟨?_, freshOp_none _ _, ?_⟩
  · show AccOp A.base _ _ (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show ¬ RelOp A.base (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
      (eRom A.base none none (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
        (qlog (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRom_cLog A.base none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches of the two simulators, and the reduction's budget -/

section Patch

/-- **The patch of a simulated proof of either relation, by queries.** -/
noncomputable abbrev progQM : RI → SimCoins pI × SimCoins pS →
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => match xi with
    | .inl x => progQI x c.1
    | .inr x => progQS x c.2

/-- **The patch's queries, from a log entry** (none for no proof). -/
noncomputable def logQM {N : ℕ} : Ent Sizes.labelRows → (Fin N → Tab3) →
    (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Ratatouille.uovM → List DomIC
  | some (.inl x, .inl π), _, b => logQI (some (x, π)) zT zT b
  | some (.inr x, .inr π), _, b => logQS (some (x, π)) zT zT b
  | _, _, _ => []

lemma cells_pI_le : verifyCellBound pI ≤ verifyCellBound pS := by
  rw [verifyCellBound_pI, verifyCellBound_pS]; norm_num

/-- A budget with a larger cell count. (Stated for variables: elaborating `mono` on the cell
counts of `pI`, `pS` evaluates them.) -/
lemma qBud_mono_cells {α : Type} {oa : OracleComp specIC α} {q : Kind → ℕ} {n m : ℕ}
    (h : QBud q n oa) (hnm : n ≤ m) : QBud q m oa := ⟨h.1, h.2.mono hnm⟩

set_option maxHeartbeats 4000000 in
/-- **The patch's budget**: `qPre` hash queries, at most `338` in all, and `cells(pS)` cells.
(Stated as a conjunction: a statement headed by `IsQueryBoundP` on the patch is reduced, by
`whnf`, into the simulator's evaluation.) -/
lemma qBudT_progQM : ∀ (xi : RI) (c : SimCoins pI × SimCoins pS),
    QBudT qPre (verifyCellBound pS) 338 (progQM xi c)
  | .inl x, c => ⟨qBud_mono_cells (qBud_progQI x c.1) cells_pI_le, left_progQI x c.1⟩
  | .inr x, c => ⟨qBud_progQS x c.2, left_progQS x c.2⟩

lemma qPre_h3 : qPre .h3 = 0 := by decide

/-- **The patch's queries on the `N` slices are its queries on two.** -/
lemma progQM_ansPN {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    qlog (ansPN g t) (progQM xi c) = qlog (ansP zT zT t) (progQM xi c) ∧
      runT (ansPN g t) (progQM xi c) = runT (ansP zT zT t) (progQM xi c) :=
  noH3_ansPN _ g zT zT t (noH3_of_kind (qBudT_progQM xi c).1.1 qPre_h3 _)

lemma hlogM {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    qlog (ansPN g t) (progQM xi c) =
      logQM (pairO (some xi) (simM leanSimIR leanSimSR xi c)) g t.2 := by
  rw [(progQM_ansPN xi c g t).1]
  rcases xi with x | x
  · show qlog (ansP zT zT t) (progQI x c.1) = _
    rw [hlogI x c.1 zT zT t]
    show _ = logQM (pairO (some (Sum.inl x)) ((leanSimIR x c.1).map Sum.inl)) g t.2
    rcases leanSimIR x c.1 with _ | π <;> rfl
  · show qlog (ansP zT zT t) (progQS x c.2) = _
    rw [hlogS x c.2 zT zT t]
    show _ = logQM (pairO (some (Sum.inr x)) ((leanSimSR x c.2).map Sum.inr)) g t.2
    rcases leanSimSR x c.2 with _ | π <;> rfl

lemma hpatchM {N : ℕ} (xi : RI) (c : SimCoins pI × SimCoins pS) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) (d : DomIC) :
    ansPN g (progM (leanProgIRX hbX) (leanProgSRX hbX) xi c t) d =
      patch2 pI (runT (ansPN g t) (progQM xi c)) d (ansPN g t d) := by
  rw [(progQM_ansPN xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne _ (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd, ansPN_eq g t zT zT hd]
    rcases xi with x | x
    · exact hpatchI x c.1 zT zT t d
    · exact hpatchS x c.2 zT zT t d

lemma logQM_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Ratatouille.uovM) : logQM none g b = [] := rfl

lemma progM_sndR (x : RI) (c : SimCoins pI × SimCoins pS)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    (progM (leanProgIRX hbX) (leanProgSRX hbX) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches**: the patches' queries (each `qPre` hash queries, at
most `338` in all, and `cells(pS)` cells), then the adversary's. -/
theorem qBudT_redQN {α : Type} {q : Kind → ℕ} {qE nG : ℕ} {oa : OracleComp specIC α}
    (h : QBudT q qE nG oa) :
    ∀ ys : List (Option RI × (SimCoins pI × SimCoins pS)),
      QBudT (q + ys.length • qPre) (qE + ys.length * verifyCellBound pS) (nG + ys.length * 338)
        (redQN progQM (patch2 pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudT_redQN h ys
    have h₁ := qBud_progQO (fun x c => (qBudT_progQM x c).1) y.1 y.2
    have h₁' := left_progQO (fun x c => (qBudT_progQM x c).2) y.1 y.2
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

/-! ## Runs of a list of computations -/

section Runs

variable {α β E K : Type}

/-- **The runs of a list of computations agree** when the answers agree at every query whose key is
in `Q`, and `Q` holds the keys of their queries. -/
lemma flatMap_qlog_congr (dec : DomIC → Option K) (Q : Finset K) (v : E → OracleComp specIC β)
    {f f' : (d : DomIC) → AnsIC d} (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    ∀ l : List E, (∀ d ∈ l.flatMap (fun e => qlog f (v e)), ∀ k, dec d = some k → k ∈ Q) →
      l.flatMap (fun e => qlog f' (v e)) = l.flatMap (fun e => qlog f (v e))
  | [], _ => rfl
  | e :: l, hQ => by
    simp only [List.flatMap_cons] at hQ ⊢
    rw [(runT_congr (v e) f f' fun d hd => h d (hQ d (List.mem_append_left _ hd))).1,
      flatMap_qlog_congr dec Q v h l fun d hd => hQ d (List.mem_append_right _ hd)]

lemma countP_flatMap_qlog_le (v : E → OracleComp specIC β) (f : (d : DomIC) → AnsIC d)
    (P : DomIC → Bool) {n : ℕ} (hb : ∀ e, IsQueryBoundP (v e) (fun d => P d = true) n) :
    ∀ l : List E, (l.flatMap fun e => qlog f (v e)).countP P ≤ l.length * n
  | [] => by simp
  | e :: l => by
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    calc _ ≤ n + l.length * n :=
          Nat.add_le_add (countP_qlog_le (v e) f P (hb e)) (countP_flatMap_qlog_le v f P hb l)
      _ = (l.length + 1) * n := by ring

/-- **A list of runs, then a run, agree** when their answers agree at every query whose key is in
`Q`, and `Q` holds the keys of their queries. -/
lemma runsN_congr [DecidableEq K] (dec : DomIC → Option K) (Q : Finset K) {f₀ f f₀' f' : (d : DomIC) → AnsIC d}
    (v : E → OracleComp specIC β) (l : List E) (oa : OracleComp specIC α)
    (hQ : (((l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa).filterMap dec).toFinset ⊆ Q)
    (h₀ : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f₀ d = f₀' d)
    (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    (l.flatMap fun e => qlog f₀' (v e)) ++ qlog f' oa =
        (l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa ∧ runT f' oa = runT f oa := by
  have hm : ∀ d ∈ (l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa, ∀ k, dec d = some k → k ∈ Q :=
    fun d hd k hk => hQ (mem_dec hd hk)
  have e₀ := flatMap_qlog_congr dec Q v h₀ l fun d hd => hm d (List.mem_append_left _ hd)
  have e := runT_congr oa f f' fun d hd => h d (hm d (List.mem_append_right _ hd))
  exact ⟨by rw [e₀, e.1], e.2⟩

/-- **The keys of a list of runs and a run**, from their query bounds. -/
lemma card_runsN_le [DecidableEq K] (dec : DomIC → Option K) (P : DomIC → Bool)
    (hdec : ∀ d k, dec d = some k → P d = true) (f₀ f : (d : DomIC) → AnsIC d)
    {v : E → OracleComp specIC β} {oa : OracleComp specIC α} {n₁ n : ℕ}
    (h₁ : ∀ e, IsQueryBoundP (v e) (fun d => P d = true) n₁)
    (h : IsQueryBoundP oa (fun d => P d = true) n) (l : List E) :
    (((l.flatMap fun e => qlog f₀ (v e)) ++ qlog f oa).filterMap dec).toFinset.card ≤
      l.length * n₁ + n := by
  have hc : ∀ l : List DomIC, l.countP (fun d => (dec d).isSome) ≤ l.countP P :=
    fun l => List.countP_mono_left fun d _ hd => by
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (by simpa using hd)
      exact hdec d k hk
  refine (card_toFinset_filterMap_le _ _).trans ?_
  rw [List.countP_append]
  have a₁ := (hc _).trans (countP_flatMap_qlog_le v f₀ P h₁ l)
  have a := (hc _).trans (countP_qlog_le oa f P h)
  omega

end Runs

/-! ## The extractor's read budget -/

section Reads

/-- The prefix computation of a log entry (none for no proof). -/
noncomputable def vQM : Ent Sizes.labelRows → OracleComp specIC ByteArray
  | some (.inl x, .inl π) => vQI (some (x, π))
  | some (.inr x, .inr π) => vQS (some (x, π))
  | _ => pure ByteArray.empty

lemma logQM_eq {N : ℕ} (e : Ent Sizes.labelRows) (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Ratatouille.uovM) :
    logQM e g b = qlog (ansP zT zT ((fun _ => 0, b) :
      ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM))) (vQM e) := by
  rcases e with _ | ⟨x | x, π | π⟩
  · rfl
  · exact logQI_eq (R := Blk → Blk) (some (x, π)) zT zT b
  · rfl
  · rfl
  · exact logQS_eq (R := Blk → Blk) (some (x, π)) zT zT b

lemma qBud_vQM (e : Ent Sizes.labelRows) : QBud qPre (verifyCellBound pS) (vQM e) := by
  rcases e with _ | ⟨x | x, π | π⟩
  · exact ⟨trivial, trivial⟩
  · exact qBud_mono_cells (qBud_vQI (some (x, π))) cells_pI_le
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact qBud_vQS (some (x, π))

/-- The answers with another `H₅` table agree at every query whose `H₅` key they agree at. -/
lemma ansPN_h5 {N : ℕ} (g : Fin N → Tab3) (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM))
    (G5 : Tab5F) (d : DomIC) (hd : ∀ k, dec5 d = some k → t.2.1.1 k = G5 k) :
    ansPN g t d = ansPN g (t.1, ((G5, t.2.1.2), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd', ansPN_eq g _ zT zT hd']
    exact ansP_h5 zT zT t G5 d hd

/-- The answers with other cipher rows agree at every query whose row they agree at. -/
lemma ansPN_E {N : ℕ} (g : Fin N → Tab3) (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM))
    (E : Blk → Blk → Blk) (d : DomIC) (hd : ∀ k, decE d = some k → t.2.1.2 k = E k) :
    ansPN g t d = ansPN g (t.1, ((t.2.1.1, E), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd', ansPN_eq g _ zT zT hd']
    exact ansP_E zT zT t E d hd

/-- The extractor's query list on the tables `t`: the patches' prefixes (the first `N` log entries,
most recent first, on the tables with `H₂³` zero), then the last stage's. -/
noncomputable def qsN {α : Type} {N : ℕ} (ls : List (Ent Sizes.labelRows))
    (oa : OracleComp specIC α) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) : List DomIC :=
  (ls.flatMap fun e => qlog (ansP zT zT ((fun _ => 0, t.2) :
    ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM))) (vQM e)) ++ qlog (ansPN g t) oa

lemma qPre_h5 : qPre .h5 = 312 := by decide

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices**: for a last stage that is the run of
an oracle computation within `QBudT q qE nG`, `extLN … (eRomN A)` reads each slice at `q h3` keys,
`H₅` at `q h5 + N·312` (the last stage's and the `N` prefixes' gate inputs) and the cipher at
`qE + N·cells(pS) + 4608` rows (the last stage's and the prefixes' cells, the reconstruction's
and the zero key's rows). -/
theorem stageBudgetNX_extRomN
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    {q : Kind → ℕ} {qE nG : ℕ}
    {F : (Fin (U + M) → Tab3) → ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM) →
      Op Sizes.labelRows}
    (hF : AdmLN (QBudT q qE nG) ansPN F) (l : LogR Sizes.labelRows) :
    StageBudgetNX (extLN ansPN (QBudT q qE nG) logQM (eRomN A) l F) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pS + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQM) (e := eRomN A) hF
  set ls := (l.take (U + M)).reverse
  have hlen : ls.length ≤ U + M := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPN (QBudT q qE nG) logQM (eRomN A) l F = fun g t =>
      eRom A.base none none (runT (ansPN g t) oa) (qsN ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomN qsN logsL
    congr 2
    exact List.flatMap_congr fun e _ => logQM_eq e g t.2
  rw [hfun]
  intro x
  have hS := qBud_vQM
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPN (Function.update g j u) (atX s x)) oa).filterMap
        (dec3N j)).toFinset,
      fun u => card_dec_le _ _ _ _ (isQueryBoundP_kind hb.1.1 .h3) fun _ _ => dec3N_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPN (Function.update g j u) (atX s x))
      (ansPN (Function.update g j u') (atX s x)) fun d hd =>
        ansPN_h3 g j u u' _ d fun k hk => hg k (mem_dec hd hk)
    show eRom A.base none none _ (qsN ls oa _ _) zT zT _ =
      eRom A.base none none _ (qsN ls oa _ _) zT zT _
    unfold qsN
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsN ls oa g (atX s x)).filterMap dec5).toFinset,
      fun s => (card_runsN_le dec5 (kindB .h5) (fun _ _ => dec5_kind) _ _
        (fun e => isQueryBoundP_kind (hS e).1 .h5) (isQueryBoundP_kind hb.1.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congr dec5 _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansPN g (atX (s.1, G5, s.2.2) x)) vQM ls oa subset_rfl
      (fun d hd => ansP_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_h5 g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRom A.base none none _ (qsN ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRom A.base none none _ (qsN ls oa g (atX s x)) zT zT _
    unfold qsN
    rw [e1, e2]
    exact eRom_congr A.base none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the cipher
    refine ⟨fun s => romRows A.base (runT (ansPN g (atX s x)) oa) (qsN ls oa g (atX s x)) s.2.2 x,
      fun s => (card_romRows_le _ _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_le decE (fun d => d.isRight) (fun _ _ => decE_right)
        (ansP zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (ansPN g (atX s x)) (fun e => (hS e).2) hb.1.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pS) hlen
      unfold qsN
      generalize verifyCellBound pS = c at this h2 ⊢
      omega
    obtain ⟨e1, e2⟩ := runsN_congr decE _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansPN g (atX (s.1, s.2.1, E) x)) vQM ls oa
      (fun k hk => mem_insert_of_mem (mem_union_left _ hk))
      (fun d hd => ansP_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_E g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRom A.base none none (runT (ansPN g (atX (s.1, s.2.1, E) x)) oa)
        (qsN ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRom A.base none none (runT (ansPN g (atX s x)) oa) (qsN ls oa g (atX s x)) zT zT _
    have e1' : qsN ls oa g (atX (s.1, s.2.1, E) x) = qsN ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRom_congr A.base none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## The hop budgets for any extractor on the tables with the extra table -/

section Hops

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)
  (A : ThiefN Sizes.labelRows U M Tab3 (ShX R pI X))
  (ext : ExtN Sizes.labelRows U M Tab3 (ShX R pI X)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The bad event at a value of the extra table reads what the last stage, the extractor and
the verifiers read** (`bad_budgetN` for an extractor on the tables with the extra table). -/
theorem bad_budgetNX (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (ext l (opN A pb l)) x3 x5 xE) (x : X) (ω : SecN U M)
    (l : LogR Sizes.labelRows) :
    StageBudgetN (fun g s => BadN A (leanVIRX Hb) (leanVSRX Hb) ext ω l g (atX s x))
      (a3 + x3) (a5 + (x5 + 312)) (aE + (xE + 4607)) := by
  have h := (show StageBudgetN (fun g s => opN A (pubOf ω) l g (atX s x)) a3 a5 aE from
    hA _ _ x).event (V := AccOp (atTN A x).base (leanVIRH (Hb x)) (leanVSRH (Hb x)))
    (fun op w acc => acc ∧ FreshOpN A l op ∧ (¬ RelOp A.base op w ∨
      ∃ j : Fin (U + M), ∃ c, comAt A (pubOf ω) l j = some c ∧ ∃ o ∈ opensOf op w, comOf o = c))
    (hX (pubOf ω) l x) (accOp_rd5 (atTN A x).base _ _ (leanVIRH_rd5 (Hb x)) (leanVSRH_rd5 (Hb x)))
    (accOp_rdE (atTN A x).base _ _ (leanVIRH_rdE (Hb x)) (leanVSRH_rdE (Hb x)))
  have e : (fun g s => BadN A (leanVIRX Hb) (leanVSRX Hb) ext ω l g (atX s x)) =
      fun g s => (AccOp (atTN A x).base (leanVIRH (Hb x)) (leanVSRH (Hb x))
          (opN A (pubOf ω) l g (atX s x)) s ∧ FreshOpN A l (opN A (pubOf ω) l g (atX s x)) ∧
        (¬ RelOp A.base (opN A (pubOf ω) l g (atX s x)) (ext l (opN A (pubOf ω) l) g (atX s x)) ∨
          ∃ j : Fin (U + M), ∃ c, comAt A (pubOf ω) l j = some c ∧
            ∃ o ∈ opensOf (opN A (pubOf ω) l g (atX s x)) (ext l (opN A (pubOf ω) l) g (atX s x)),
              comOf o = c)) := by
    funext g s
    simp only [BadN, accN, freshN, relN, opensN, opensJ, accOp_atXN]
  rw [e]
  exact h

/-- **The budget of every hop's distinguisher, for any extractor on the tables with the extra
table** (`distN_budgetRX` for `ext`). -/
theorem distN_budgetRX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (ext l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIRX Hb) (leanPSRX Hb)) (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω))
        (BadN A (leanVIRX Hb) (leanVSRX Hb) ext) i ω τ) :=
  (distN_budgetX (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
    (fun x => PN (atTN A x) (leanPIRH (Hb x)) (leanPSRH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIRH (Hb x)) (leanProgSRH (Hb x)) (pubOf ω))
    (fun x ω l g s => BadN A (leanVIRX Hb) (leanVSRX Hb) ext ω l g (atX s x))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf ω) l c s)
    (fun _ _ _ _ _ => rfl)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIRH_rd5 (Hb x)) (leanPSRH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIRH_rdE (hHb x)) (leanPSRH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIRH_isProg (Hb x))
      (leanProgSRH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetNX Hb A ext hA hX x ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, for any extractor on the tables with the extra table. -/
theorem distPI_budgetX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (ext l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPI A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
        (leanVIRX Hb) (leanVSRX Hb) ext i ω τ) :=
  (distN_budgetRX' Hb A ext hHb hA hX i ω τ).comp
    (fun o : Option (IssueProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω)) ω (tapeC τ) i).1)
      (o.map Sum.inl))

/-- **The budget of a spend hop**, for any extractor on the tables with the extra table. -/
theorem distPS_budgetX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (ext l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPS A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
        (leanVIRX Hb) (leanVSRX Hb) ext i ω τ) := by
  have h := (distN_budgetRX' Hb A ext hHb hA hX i ω τ).comp
    (fun o : Option (SpendProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω)) ω (tapeC τ) i).1)
      (o.map Sum.inr))
  -- (`pI` and `pS` have the same `H₂³` table type)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

end Hops

/-! ## No theft for `U` Clients and `M` spends with `ROM/`'s plain extraction -/

section Theorem

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomN A` on the reduction's queries. -/
noncomputable def extRomN
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (q : Kind → ℕ) (qE nG : ℕ) :
    ExtN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) :=
  extLN ansPN (QBudT q qE nG) logQM (eRomN A)

variable (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends with `ROM/`'s plain extraction** (Ratatouille,
function rows, `M = uovM`, `L ≥ Lmin`): as `noTheftN_leanX_hit`, for an adversary whose last
stage is the run on the `N = U + M` slices and the tables of an oracle computation with at most
`q k` hash queries of kind `k`, `nG` in all and `q_E` cipher cells (`hA`), and `ROM/`'s
straight-line extractor on the reduction's queries (`extRomN`); plain extraction is no longer a
hypothesis, and the extractor's read budget is proved (`stageBudgetNX_extRomN`):

    Pr[BadN] ≤ U·εz(pI; q') + M·εz(pS; q') + Σ_i δ_i + ε_rom
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_j Adv^ow(inverter j),

`ε_rom = epsRom (q + N·qPre) (q_E + N·cells(pS)) (nG + N·338)` (`ROM/`'s simultaneous extraction
for the reduction's budget, one output) and `q' = (q h3 + q h3, q h5 + (q h5 + N·312) + 312 +
(N − 1)·624, q_E + (q_E + N·cells(pS) + 4608) + N·4607)`. -/
theorem noTheftN_lean_rom (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ iss sp, AdmLN (QBudT q qE nG) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE nG)) ≤
      U * ZKRow.εz (Blk → Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Blk → Blk) pS (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        ((epsRom (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomN A q qE nG) j) := by
  have hSB : ∀ iss sp, StageBudgetNX (A.out iss sp) (q .h3) (q .h5) qE := fun iss sp => by
    obtain ⟨oa, hb, hF⟩ := hA iss sp
    rw [hF]
    exact stageBudgetNX_runTN hb.1
  have hX : ∀ pb l, StageBudgetNX (extRomN A q qE nG l (opN A pb l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pS + 4608) :=
    fun pb l => stageBudgetNX_extRomN A (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) → ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM) →
      Op Sizes.labelRows, AdmLN (QBudT q qE nG) ansPN F →
      Hit.AdmHitN (R := Blk → Blk) (p := pI) (L := L) (M := Arith.Ratatouille.uovM)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTN hb.1
  exact noTheftN_of_se (CI := SimCoins pI) (CS := SimCoins pS) A (leanPIRX hbX) (leanPSRX hbX)
    leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
    (extRomN A q qE nG) (leanPIRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPSRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPI_budgetX' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPS_budgetX' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_ok A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanVIRX hbX)
      (leanVSRX hbX) (extRomN A q qE nG)
      (weakSEN_of_plainL progQM (patch2 pI) logQM (plainSENL_rom A hL _ _ _ (FreshOkN A))
        ((progMovesN_hit A hL (q .mu) (q .h21) (q .h22)).mono hAH) progM_sndR hpatchM hlogM
        logQM_none fun oa ys hl h => hl ▸ qBudT_redQN h ys)
      hA)

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends with `ROM/`'s plain extraction**, the hops' budgets
simplified (`cells(pS) = 142844`): `noTheftN_lean_rom` with

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·147451 + 4608),   N = U + M. -/
theorem noTheftN_lean_rom' (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ iss sp, AdmLN (QBudT q qE nG) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE nG)) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 147451 + 4608) +
        M * ZKRow.εz (Blk → Blk) pS (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624) (2 * qE + (U + M) * 147451 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        ((epsRom (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomN A q qE nG) j) := by
  have h := noTheftN_lean_rom A hL hA
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pS + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 147451 + 4608 := by
    rw [verifyCellBound_pS]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

end VoleMole.Theft.Ratatouille
