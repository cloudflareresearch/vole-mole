import VoleMole.Theft.PlainRataManyRom
import VoleMole.Theft.PlainMousReads
import VoleMole.Theft.MoussakaManyHit

/-!
# Plain extraction for `U` tokens and `M` redemptions from `ROM/`'s bound (Moussaka)

`noRedirectN_leanX_hit` (`Theft/MoussakaManyHit.lean`) keeps plain extraction `PlainSEN` as a
hypothesis. Here it is replaced by `PlainSENL` (`Theft/ManyPlainLog.lean`) and proved from
`ROM/`'s simultaneous extraction, as `noRedirect_lean_rom'` does for one token and
`noTheftN_lean_rom'` (`Theft/PlainRataManyRom.lean`) for Ratatouille (`docs/security/moussaka.md`
§5.3):

* **`FreshKN kt`**: the freshness of the bound: `FreshOkN` and, for a redemption, Anchor keys that
  are the keys `kt d` of their digests (`KeysOp`). In the game, for adversaries whose output
  redemptions have the keys of `kt` (`KeysOutN`), the game's freshness is `FreshKN kt`
  (`sim_se_leN_okK`).
* **`plainSENL_romM`**: `PlainSENL` for `eRomMN` (the one-token `eRomM`) against `QBudT q qE nG`,
  for `FreshKN kt`, with the one-token error `ε_rom q qE nG` (`plainSEL_romM`, the slices as
  advice).
* `progQMm`, `logQMm`: the patches of the two simulators, by queries (`hlogMm`, `hpatchMm`).
  `qBudT_redQNm`: the reduction for `N` patches is within
  `QBudT (q + N·qPre) (qE + N·cells(pR)) (nG + N·338)`.
* **`stageBudgetNX_extRomMN`**: the extractor's read budget: each slice at `q h3` keys, `H₅` at
  `q h5 + N·312`, the cipher at `qE + N·cells(pR) + 4608` rows.
* **`noRedirectN_lean_rom'`**: the theorem, with `cells(pR) = 69116`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

/-! ## The programming term is monotone in the freshness -/

section Moves

variable {N : ℕ} {I P C G A B Out : Type} [Fintype C] [Nonempty C] [Fintype G] [Fintype A]
  [Fintype B]

lemma ProgMovesN.fresh_mono {sim : I → C → Option P} {prog : I → C → A × B → A × B}
    {Acc : Out → A × B → Prop} {Fresh Fresh' : List (Option (I × P)) → Out → Prop}
    {Adm : ((Fin N → G) → A × B → Out) → Prop} {ε : ℝ}
    (h : ProgMovesN N sim prog Acc Fresh Adm ε) (hF : ∀ l o, Fresh' l o → Fresh l o) :
    ProgMovesN N sim prog Acc Fresh' Adm ε :=
  fun α _ _ x out hout =>
    (Privacy.pr_mono fun _ hz => ⟨hF _ _ hz.1, hz.2⟩).trans (h α x out hout)

end Moves

namespace Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre qBud_mono_cells flatMap_qlog_congr runsN_congr
  card_runsN_le advEquiv qPre_h3 qPre_h5)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {U M L : ℕ}

/-! ## The freshness of the bound, in the game -/

/-- **The freshness of `ROM/`'s bound** for `U + M` simulated proofs: `FreshOkN` and the Anchor
keys of `kt`. -/
def FreshKN (kt : Bytes → UOVKey) (l : Log) (op : MOp) : Prop := FreshOkN l op ∧ KeysOp kt op

section Game

variable {G S : Type} (A : ThiefN U M G S)

/-- **The adversary's output redemptions have the Anchor keys of `kt`.** -/
def KeysOutN (kt : Bytes → UOVKey) : Prop := ∀ reqs reds g s, KeysOp kt (A.out reqs reds g s)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : ExtN U M G S) [Nonempty CI] [Nonempty CR] [Fintype CI] [Fintype CR] [Fintype G]
  [Fintype S] [Nonempty G]

/-- **`sim_se_leN_ok` for `FreshKN kt`**, for `HitWfN` adversaries with the keys of `kt`. -/
theorem sim_se_leN_okK (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    {AdmE : ((Fin (U + M) → G) → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simR) (progM progI progR) (AccOp verI verR) (FreshKN kt)
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

/-- **`ROM/`'s straight-line extractor with `N` slices**: the one-token extractor `eRomM`. -/
noncomputable def eRomMN (N : ℕ) : Log → MOp → List DomIC → (Fin N → Tab3) →
    (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ op qs _ b => eRomM none none op qs zT zT b

/-- `eRomM` reads the query list only through its cipher entries, and not the slices. -/
lemma eRomM_cLog (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (op : MOp) {qs qs' : List DomIC} (g₁ g₂ g₁' g₂' : Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M)
    (h : cLog (Ratatouille.ctOf b.1.2) qs = cLog (Ratatouille.ctOf b.1.2) qs') :
    eRomM p₁ p₂ op qs g₁ g₂ b = eRomM p₁ p₂ op qs' g₁' g₂' b := by
  simp only [eRomM, h]

set_option maxHeartbeats 1000000 in
/-- **Plain extraction for `U` tokens and `M` redemptions from `ROM/`'s bound** (function rows,
`M = Moussaka.M`, `L ≥ 8193`): `PlainSENL` holds for `eRomMN` against the last stages within
`QBudT q qE nG`, for the freshness `FreshKN kt`, with the one-token error `epsRomM q qE nG`. -/
theorem plainSENL_romM (kt : Bytes → UOVKey) (hL : Lrom ≤ L) (N : ℕ) (q : Kind → ℕ)
    (qE nG : ℕ) :
    PlainSENL N (ansPN (R := Blk → Blk) (p := pI) (L := L) (M := Arith.Moussaka.M))
      (AccOp (verILX hbX) (verRLX hbX)) (FreshKN kt) RelOp (eRomMN (L := L) N) (QBudT q qE nG)
      (epsRomM q qE nG).toReal := by
  classical
  intro α _ _ lg oa hoa
  have hP := plainSEL_romM (L := L) kt hL q qE nG (α × (Fin N → Tab3)) (fun _ => none)
    (fun _ => none) (fun b => locN b.2 (oa b.1)) fun b => qBudT_locN (hoa b.1) b.2
  rw [← pr_prod_snd (α := Tab3 × Tab3), ← pr_equiv (advEquiv α N
    (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))]
  refine (Privacy.pr_mono fun z hz => ?_).trans hP
  obtain ⟨hacc, hfr, hrel⟩ := hz
  obtain ⟨hr, -⟩ := runT_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1)
  have hc := cLog_locN z.1.2 z.2.1.1 z.2.1.2 z.2.2 (oa z.1.1) (Ratatouille.ctOf z.2.2.2.1.2)
  refine ⟨?_, ?_, ?_⟩
  · show AccOp _ _ (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.2
    rw [hr]
    exact hacc
  · show FreshK kt none none (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
    rw [hr]
    exact ⟨hfr.1.freshOk, hfr.2⟩
  · show ¬ RelOp (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
      (eRomM none none (runT (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1)))
        (qlog (ansP z.2.1.1 z.2.1.2 z.2.2) (locN z.1.2 (oa z.1.1))) z.2.1.1 z.2.1.2 z.2.2.2)
    rw [hr, eRomM_cLog none none _ _ _ zT zT _ hc]
    exact hrel

end Plain

/-! ## The patches of the two simulators, and the reduction's budget -/

section Patch

/-- **The patch of a simulated proof of either relation, by queries.** -/
noncomputable abbrev progQMm : MI → SimCoins pI × SimCoins pR →
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  fun xi c => match xi with
    | .inl x => progQIm x c.1
    | .inr x => progQRm x c.2

/-- **The patch's queries, from a log entry** (none for no proof). -/
noncomputable def logQMm {N : ℕ} : Option (MI × Bytes) → (Fin N → Tab3) →
    (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M → List DomIC
  | some (.inl x, π), _, b => logQIm (some (x, π)) zT zT b
  | some (.inr x, π), _, b => logQRm (some (x, π)) zT zT b
  | none, _, _ => []

lemma cells_pI_le_pR : verifyCellBound pI ≤ verifyCellBound pR := by
  rw [verifyCellBound_pIm, verifyCellBound_pR]; norm_num

set_option maxHeartbeats 4000000 in
/-- **The patch's budget**: `qPre` hash queries, at most `338` in all, and `cells(pR)` cells. -/
lemma qBudT_progQMm : ∀ (xi : MI) (c : SimCoins pI × SimCoins pR),
    QBudT qPre (verifyCellBound pR) 338 (progQMm xi c)
  | .inl x, c => ⟨qBud_mono_cells (qBud_progQIm x c.1) cells_pI_le_pR, left_progQIm x c.1⟩
  | .inr x, c => ⟨qBud_progQRm x c.2, left_progQRm x c.2⟩

/-- **The patch's queries on the `N` slices are its queries on two.** -/
lemma progQMm_ansPN {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPN g t) (progQMm xi c) = qlog (ansP zT zT t) (progQMm xi c) ∧
      runT (ansPN g t) (progQMm xi c) = runT (ansP zT zT t) (progQMm xi c) :=
  noH3_ansPN _ g zT zT t (noH3_of_kind (qBudT_progQMm xi c).1.1 qPre_h3 _)

lemma hlogMm {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansPN g t) (progQMm xi c) =
      logQMm (pairO (some xi) (simM (leanSim pI) (leanSim pR) xi c)) g t.2 := by
  rw [(progQMm_ansPN xi c g t).1]
  rcases xi with x | x
  · exact hlogIm x c.1 zT zT t
  · exact hlogRm x c.2 zT zT t

lemma hpatchMm {N : ℕ} (xi : MI) (c : SimCoins pI × SimCoins pR) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) (d : DomIC) :
    ansPN g (progM (leanProgIX hbX) (leanProgRX hbX) xi c t) d =
      patch2 pI (runT (ansPN g t) (progQMm xi c)) d (ansPN g t d) := by
  rw [(progQMm_ansPN xi c g t).2]
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨⟨k, b⟩, rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
    have hk : k = .h3 := hs.1
    subst hk
    exact (patch2_ne _ (by decide) b _).symm
  · have hd : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd, ansPN_eq g t zT zT hd]
    rcases xi with x | x
    · exact hpatchIm x c.1 zT zT t d
    · exact hpatchRm x c.2 zT zT t d

lemma logQMm_none {N : ℕ} (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M) : logQMm none g b = [] := rfl

lemma progM_sndM (x : MI) (c : SimCoins pI × SimCoins pR)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) :
    (progM (leanProgIX hbX) (leanProgRX hbX) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget for `n` patches.** -/
theorem qBudT_redQNm {α : Type} {q : Kind → ℕ} {qE nG : ℕ} {oa : OracleComp specIC α}
    (h : QBudT q qE nG oa) :
    ∀ ys : List (Option MI × (SimCoins pI × SimCoins pR)),
      QBudT (q + ys.length • qPre) (qE + ys.length * verifyCellBound pR) (nG + ys.length * 338)
        (redQN progQMm (patch2 pI) ys oa)
  | [] => by simpa [redQN] using h
  | y :: ys => by
    have ih := qBudT_redQNm h ys
    have h₁ := Ratatouille.qBud_progQO (fun x c => (qBudT_progQMm x c).1) y.1 y.2
    have h₁' := Ratatouille.left_progQO (fun x c => (qBudT_progQMm x c).2) y.1 y.2
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

/-! ## The extractor's read budget -/

section Reads

/-- The prefix computation of a log entry (none for no proof). -/
noncomputable def vQMm : Option (MI × Bytes) → OracleComp specIC ByteArray
  | some (.inl x, π) => vQIm (some (x, π))
  | some (.inr x, π) => vQR (some (x, π))
  | none => pure ByteArray.empty

lemma logQMm_eq {N : ℕ} (e : Option (MI × Bytes)) (g : Fin N → Tab3)
    (b : (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M) :
    logQMm e g b = qlog (ansP zT zT ((fun _ => 0, b) :
      ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M))) (vQMm e) := by
  rcases e with _ | ⟨x | x, π⟩
  · rfl
  · exact logQIm_eq (R := Blk → Blk) (some (x, π)) zT zT b
  · exact logQRm_eq (R := Blk → Blk) (some (x, π)) zT zT b

lemma qBud_vQMm (e : Option (MI × Bytes)) : QBud qPre (verifyCellBound pR) (vQMm e) := by
  rcases e with _ | ⟨x | x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact qBud_mono_cells (qBud_vQIm (some (x, π))) cells_pI_le_pR
  · exact qBud_vQR (some (x, π))

lemma ansPN_h5M {N : ℕ} (g : Fin N → Tab3) (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M))
    (G5 : Tab5F) (d : DomIC) (hd : ∀ k, dec5 d = some k → t.2.1.1 k = G5 k) :
    ansPN g t d = ansPN g (t.1, ((G5, t.2.1.2), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd', ansPN_eq g _ zT zT hd']
    exact ansP_h5 zT zT t G5 d hd

lemma ansPN_EM {N : ℕ} (g : Fin N → Tab3) (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M))
    (E : Blk → Blk → Blk) (d : DomIC) (hd : ∀ k, decE d = some k → t.2.1.2 k = E k) :
    ansPN g t d = ansPN g (t.1, ((t.2.1.1, E), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPN_eq g _ zT zT hd', ansPN_eq g _ zT zT hd']
    exact ansP_E zT zT t E d hd

/-- The extractor's query list on the tables `t`: the patches' prefixes, then the last stage's. -/
noncomputable def qsNM {α : Type} {N : ℕ} (ls : List (Option (MI × Bytes)))
    (oa : OracleComp specIC α) (g : Fin N → Tab3)
    (t : ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) : List DomIC :=
  (ls.flatMap fun e => qlog (ansP zT zT ((fun _ => 0, t.2) :
    ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M))) (vQMm e)) ++ qlog (ansPN g t) oa

set_option maxHeartbeats 4000000 in
/-- **The read budget of `ROM/`'s extractor with `N` slices** (Moussaka): each slice at `q h3`
keys, `H₅` at `q h5 + N·312`, the cipher at `qE + N·cells(pR) + 4608` rows. -/
theorem stageBudgetNX_extRomMN {N : ℕ} {q : Kind → ℕ} {qE nG : ℕ}
    {F : (Fin N → Tab3) → ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M) → MOp}
    (hF : AdmLN (QBudT q qE nG) ansPN F) (l : Log) :
    StageBudgetNX (extLN ansPN (QBudT q qE nG) logQMm (eRomMN N) l F) (q .h3)
      (q .h5 + N * 312) (qE + N * verifyCellBound pR + 4608) := by
  obtain ⟨oa, hb, -, he⟩ := extLN_of_admLN (logQ := logQMm) (e := eRomMN N) hF
  set ls := (l.take N).reverse
  have hlen : ls.length ≤ N := by
    simp only [ls, List.length_reverse, List.length_take]; omega
  have hfun : extLN ansPN (QBudT q qE nG) logQMm (eRomMN N) l F = fun g t =>
      eRomM none none (runT (ansPN g t) oa) (qsNM ls oa g t) zT zT t.2 := by
    rw [he l]
    funext g t
    unfold eRomMN qsNM logsL
    congr 2
    exact List.flatMap_congr fun e _ => logQMm_eq e g t.2
  rw [hfun]
  intro x
  have hS := qBud_vQMm
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · -- slice `j`
    refine ⟨fun u => ((qlog (ansPN (Function.update g j u) (atX s x)) oa).filterMap
        (dec3N j)).toFinset,
      fun u => card_dec_le _ _ _ _ (isQueryBoundP_kind hb.1.1 .h3) fun _ _ => dec3N_kind,
      fun u u' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runT_congr oa (ansPN (Function.update g j u) (atX s x))
      (ansPN (Function.update g j u') (atX s x)) fun d hd =>
        ansPN_h3 g j u u' _ d fun k hk => hg k (mem_dec hd hk)
    show eRomM none none _ (qsNM ls oa _ _) zT zT _ = eRomM none none _ (qsNM ls oa _ _) zT zT _
    unfold qsNM
    rw [e1, e2]
  · -- `H₅`
    refine ⟨fun s => ((qsNM ls oa g (atX s x)).filterMap dec5).toFinset,
      fun s => (card_runsN_le dec5 (kindB .h5) (fun _ _ => dec5_kind) _ _
        (fun e => isQueryBoundP_kind (hS e).1 .h5) (isQueryBoundP_kind hb.1.1 .h5) ls).trans ?_,
      fun s G5 hg => ?_⟩
    · rw [qPre_h5, Nat.add_comm]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 312 hlen) _
    obtain ⟨e1, e2⟩ := runsN_congr dec5 _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansPN g (atX (s.1, G5, s.2.2) x)) vQMm ls oa subset_rfl
      (fun d hd => ansP_h5 zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_h5M g (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomM none none _ (qsNM ls oa g (atX (s.1, G5, s.2.2) x)) zT zT _ =
      eRomM none none _ (qsNM ls oa g (atX s x)) zT zT _
    unfold qsNM
    rw [e1, e2]
    exact eRomM_congr none none _ _ zT zT zT zT s.2.1 G5 x fun _ _ => rfl
  · -- the cipher
    refine ⟨fun s => romRowsM (runT (ansPN g (atX s x)) oa) (qsNM ls oa g (atX s x)) s.2.2 x,
      fun s => (card_romRowsM_le _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runsN_le decE (fun d => d.isRight) (fun _ _ => decE_right)
        (ansP zT zT ((fun _ => 0, (atX s x).2) :
          ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (ansPN g (atX s x)) (fun e => (hS e).2) hb.1.2 ls
      have h2 := Nat.mul_le_mul_right (verifyCellBound pR) hlen
      unfold qsNM
      generalize verifyCellBound pR = c at this h2 ⊢
      omega
    obtain ⟨e1, e2⟩ := runsN_congr decE _
      (f₀' := ansP zT zT ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
      (f' := ansPN g (atX (s.1, s.2.1, E) x)) vQMm ls oa
      (fun k hk => mem_insert_of_mem (mem_union_left _ hk))
      (fun d hd => ansP_E zT zT ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansPN_EM g (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomM none none (runT (ansPN g (atX (s.1, s.2.1, E) x)) oa)
        (qsNM ls oa g (atX (s.1, s.2.1, E) x)) zT zT _ =
      eRomM none none (runT (ansPN g (atX s x)) oa) (qsNM ls oa g (atX s x)) zT zT _
    have e1' : qsNM ls oa g (atX (s.1, s.2.1, E) x) = qsNM ls oa g (atX s x) := e1
    rw [e1', e2]
    exact eRomM_congr none none _ _ zT zT zT zT s.2.1 s.2.1 x hg

end Reads

/-! ## The hop budgets for any extractor on the tables with the extra table -/

section Hops

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes) (A : ThiefN U M Tab3 (ShX R pI X))
  (ext : ExtN U M Tab3 (ShX R pI X)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The bad event at a value of the extra table reads what the last stage, the extractor and
the verifiers read** (`bad_budgetN` for an extractor on the tables with the extra table). -/
theorem bad_budgetNXm (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (x : X) (ω : SecN U) (l : Log) :
    StageBudgetN (fun g s => BadN A (verILX Hb) (verRLX Hb) ext ω l g (atX s x))
      (a3 + x3) (a5 + (x5 + 312)) (aE + (xE + 4607)) := by
  have h := (show StageBudgetN (fun g s => opN A l g (atX s x)) a3 a5 aE from hA _ _ x).event
    (V := AccOp (verILH (Hb x)) (verRLH (Hb x)))
    (fun op w acc => acc ∧ FreshOpN l op ∧ (¬ RelOp op w ∨ ∃ h, OpensOp (tOfN A ω h) op w))
    (hX l x) (accOp_rd5 _ _ (verILH_rd5 (Hb x)) (verRLH_rd5 (Hb x)))
    (accOp_rdE _ _ (verILH_rdE (Hb x)) (verRLH_rdE (Hb x)))
  have e : (fun g s => BadN A (verILX Hb) (verRLX Hb) ext ω l g (atX s x)) =
      fun g s => (AccOp (verILH (Hb x)) (verRLH (Hb x)) (opN A l g (atX s x)) s ∧
        FreshOpN l (opN A l g (atX s x)) ∧
        (¬ RelOp (opN A l g (atX s x)) (ext l (opN A l) g (atX s x)) ∨
          ∃ h, OpensOp (tOfN A ω h) (opN A l g (atX s x)) (ext l (opN A l) g (atX s x)))) := by
    funext g s
    simp only [BadN, accN, freshN, relN, opensN, opensH, accOp_atX]
  rw [e]
  exact h

/-- **The budget of every hop's distinguisher, for any extractor on the tables with the extra
table** (`distN_budgetMX` for `ext`). -/
theorem distN_budgetMX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIX Hb) (leanPRX Hb))
        (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω))
        (BadN A (verILX Hb) (verRLX Hb) ext) i ω τ) :=
  (distN_budgetX (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun x => PN (atTN A x) (leanPIH (Hb x)) (leanPRH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIH (Hb x)) (leanProgRH (Hb x)) (pubOf A ω))
    (fun x ω l g s => BadN A (verILX Hb) (verRLX Hb) ext ω l g (atX s x))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf A ω) l c s)
    (fun _ _ _ _ _ => rfl)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIH_rd5 (Hb x)) (leanPRH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIH_rdE (hHb x)) (leanPRH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIH_isProg (Hb x))
      (leanProgRH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetNXm Hb A ext hA hX x ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, for any extractor on the tables with the extra table. -/
theorem distPN_budgetXI' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
        (leanProgRX Hb) (verILX Hb) (verRLX Hb) ext i ω τ) :=
  (distN_budgetMX' Hb A ext hHb hA hX i ω τ).comp
    (fun o : Bytes => pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω)) ω (tapeC τ) i).1)
      (some o))

/-- **The budget of a redemption hop**, for any extractor on the tables with the extra table. -/
theorem distPN_budgetXR' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
        (leanProgRX Hb) (verILX Hb) (verRLX Hb) ext i ω τ) := by
  have h := distPN_budgetXI' Hb A ext hHb hA hX i ω τ
  -- (`pI` and `pR` have the same `H₂³` table type)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

end Hops

/-! ## Redemption non-malleability for `U` tokens and `M` redemptions with `ROM/`'s plain
extraction -/

section Theorem

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomMN` on the reduction's queries. -/
noncomputable def extRomMN (q : Kind → ℕ) (qE nG : ℕ) :
    ExtN U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) :=
  extLN ansPN (QBudT q qE nG) logQMm (eRomMN (U + M))

variable (A : ThiefN U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions with `ROM/`'s plain
extraction** (Moussaka, function rows, `M = Moussaka.M`, `L ≥ 8193`): as `noRedirectN_leanX_hit`,
for a `HitWfN` adversary whose output redemptions have the Anchor keys of `kt` (`hk`) and whose
last stage is the run on the `N = U + M` slices and the tables of an oracle computation with at
most `q k` hash queries of kind `k`, `nG` in all and `q_E` cipher cells (`hA`), and `ROM/`'s
straight-line extractor on the reduction's queries (`extRomMN`); plain extraction is no longer a
hypothesis, and the extractor's read budget is proved (`stageBudgetNX_extRomMN`):

    Pr[BadN] ≤ U·εz(pI; q') + M·εz(pR; q') + Σ_i δ_i + ε_rom
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_h Adv^ow(inverter h),

`ε_rom = epsRomM (q + N·qPre) (q_E + N·cells(pR)) (nG + N·338)` and `q' = (q h3 + q h3,
q h5 + (q h5 + N·312) + 312 + (N − 1)·624, q_E + (q_E + N·cells(pR) + 4608) + N·4607)`. -/
theorem noRedirectN_lean_rom (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hL : Lrom ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) ≤
      U * ZKRow.εz (Blk → Blk) pI (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        M * ZKRow.εz (Blk → Blk) pR (q .h3 + q .h3)
          (q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624)
          (qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((epsRomM (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMN q qE nG) h) := by
  have hSB : ∀ reqs reds, StageBudgetNX (A.out reqs reds) (q .h3) (q .h5) qE := fun reqs reds => by
    obtain ⟨oa, hb, hF⟩ := hA reqs reds
    rw [hF]
    exact stageBudgetNX_runTN hb.1
  have hX : ∀ l, StageBudgetNX (extRomMN q qE nG l (opN A l)) (q .h3)
      (q .h5 + (U + M) * 312) (qE + (U + M) * verifyCellBound pR + 4608) :=
    fun l => stageBudgetNX_extRomMN (hA _ _) l
  have hAH : ∀ F : (Fin (U + M) → Tab3) → ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M) → MOp,
      AdmLN (QBudT q qE nG) ansPN F →
      Hit.AdmHitN (R := Blk → Blk) (p := pI) (L := L) (M := Arith.Moussaka.M)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTN hb.1
  have hL' : Hit.Mous.Lmin ≤ L := lmin_le_lrom.trans hL
  have hmv := ((progMovesN_hit (U := U) (M := M) hL' (q .mu) (q .h21) (q .h22)).mono hAH).fresh_mono
    (Fresh' := FreshKN kt) fun _ _ h => h.1
  exact noRedirectN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIX hbX) (leanPRX hbX)
    (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (verILX hbX) (verRLX hbX)
    (extRomMN q qE nG) (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (fun i _ ω τ => distPN_budgetXI' hbX A _ hbX_wf hSB hX i ω τ)
    (fun i _ ω τ => distPN_budgetXR' hbX A _ hbX_wf hSB hX i ω τ)
    (sim_se_leN_okK A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (verILX hbX)
      (verRLX hbX) (extRomMN q qE nG) hw hk
      (weakSEN_of_plainL progQMm (patch2 pI) logQMm (plainSENL_romM kt hL _ _ _ _) hmv
        progM_sndM hpatchMm hlogMm logQMm_none fun oa ys hl h => hl ▸ qBudT_redQNm h ys)
      fun _ => hA _ _)

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions with `ROM/`'s plain
extraction**, the hops' budgets simplified (`cells(pR) = 69116`): `noRedirectN_lean_rom` with

    q' = (2·q h3, 2·q h5 + N·312 + 312 + (N − 1)·624, 2·q_E + N·73723 + 4608),   N = U + M. -/
theorem noRedirectN_lean_rom' (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hL : Lrom ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 73723 + 4608) +
        M * ZKRow.εz (Blk → Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624) (2 * qE + (U + M) * 73723 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((epsRomM (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (nG + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMN q qE nG) h) := by
  have h := noRedirectN_lean_rom A hw hk hL hA
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + (U + M) * 312) + 312 + (U + M - 1) * 624 =
      2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624 := by ring
  have eE : qE + (qE + (U + M) * verifyCellBound pR + 4608) + (U + M) * 4607 =
      2 * qE + (U + M) * 73723 + 4608 := by
    rw [verifyCellBound_pR]; ring
  rw [e3, e5, eE] at h
  exact h

end Theorem

end Moussaka

end VoleMole.Theft
