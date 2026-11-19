import VoleMole.Theft.PlainMousRom

/-!
# Redemption non-malleability with `ROM/`'s plain extraction (Moussaka)

`noRedirect_leanX_hitL` (`Theft/PlainMous.lean`) keeps plain extraction `PlainSEL` as a
hypothesis. Here it is discharged by `plainSEL_romM` (`Theft/PlainMousRom.lean`;
`docs/security/moussaka.md` §5.3), for function rows, `M = Moussaka.M` and `L ≥ 8193`:

* `plainSEL_romM` is for the freshness `FreshK kt` (`FreshOk` and Anchor keys of `kt`), so the
  game step needs, besides `HitWf`, that the adversary's output redemptions have the keys of `kt`
  (`KeysOut kt A`; in C++ two keys with one digest are a SHAKE256 collision).
  `sim_se_le_okK`, `noRedirect_okK`: `Hit.Mous.sim_se_le_ok`, `Hit.Mous.noRedirect_ok` for
  `FreshK kt`. `ProgMoves.fresh_mono`: the programming term for `FreshOk` bounds it for `FreshK`.
* `qBudT_redQm`: the reduction's budget with a total (`338` hash queries per patch).
* **`noRedirect_lean_rom`**: for a `HitWf` adversary with the keys of `kt`, whose last stage is the
  run of an oracle computation within `QBudT q qE nG`, and the extractor `extRomM` (`extL` of
  `eRomM`) with read budget `hX`,

      Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_rom
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `ε_rom = epsRomM (q + 2·qPre) (qE + cells(pR) + cells(pI)) (nG + 2·338)`,
  `q' = (q h3 + x₃, q h5 + x₅ + 936, qE + x_E + 9214)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

/-! ## The programming term is monotone in the freshness -/

section Moves

variable {I₁ I₂ P₁ P₂ G A B Out C₁ C₂ : Type} [Fintype G] [Fintype A] [Fintype B]
  [Fintype C₁] [Fintype C₂]

lemma ProgMoves.fresh_mono {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → A × B → A × B}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → A × B → A × B} {Acc : Out → A × B → Prop}
    {Fresh Fresh' : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop}
    {Adm : (G → G → A × B → Out) → Prop} {ε : ℝ}
    (h : ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh Adm ε)
    (hF : ∀ p₁ p₂ o, Fresh' p₁ p₂ o → Fresh p₁ p₂ o) :
    ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh' Adm ε :=
  fun α _ _ x₁ x₂ out hout =>
    (Privacy.pr_mono fun _ hz => ⟨hF _ _ _ hz.1, hz.2⟩).trans (h α x₁ x₂ out hout)

end Moves

namespace Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka

/-! ## The game step for `FreshK` -/

section Game

variable {G S : Type} (A : Thief G S)

/-- **The adversary's output redemptions have the Anchor keys of `kt`.** -/
def KeysOut (kt : Bytes → UOVKey) : Prop := ∀ o₁ o₂ g₁ g₂ s, KeysOp kt (A.out o₁ o₂ g₁ g₂ s)

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : Ext G S) {CI CR : Type} (simI : IssueInstance → CI → Bytes)
  (progI : IssueInstance → CI → S → S) (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → S → S) [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **`Hit.Mous.sim_se_le_ok` for `FreshK kt`**, for `HitWf` adversaries with the keys of `kt`. -/
theorem sim_se_le_okK (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt)
    {AdmE : (G → G → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) (FreshK kt) RelOp ext
      AdmE εSE) (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
          (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (seEv A verI verR ext)) ≤ εSE := by
  have h := hse Sec (fun ω => some ⟨tOf A ω, A.ci⟩)
    (fun ω π₁ => xR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI (tOf A ω) π₁)
      (reqR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  have h1 := stI_simIss A simI (tOf A z.1.1) (length_com _ _ _ _) z.1.2.1
  have h2 := stR_simRed A simR (List.ofFn z.1.1.1) (tOf A z.1.1)
    (simIssP A simI (tOf A z.1.1) z.1.2.1) List.length_ofFn z.2.1.1
  simp only [simG, seEv, accE, freshE, relE, h1, h2] at hz
  exact ⟨hz.1, ⟨Hit.Mous.freshOk_of_game A hw (length_com _ _ _ _) List.length_ofFn _ _ _ _ _ _ _
    hz.1 hz.2.1, hk _ _ _ _ _⟩, hz.2.2⟩

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- **Redemption non-malleability with weak simulation-extractability for `FreshK kt`**, for
`HitWf` adversaries with the keys of `kt` (as `Hit.Mous.noRedirect_ok`). -/
theorem noRedirect_okK [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt)
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → MOp) → Prop} {εI εR εSE : ℝ}
    (hzkI : ZeroKnowledgeRO Privacy.Moussaka.IssueRelW (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s)
      simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO Privacy.Moussaka.RedeemRelW (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s)
      simR progR AdmR εR) (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) (FreshK kt) RelOp ext
      AdmE εSE) (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A PI PR verI verR ext) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE +
        owAdv A.ci A.cr (inverter A ext simI progI simR progR) :=
  noRedirect_of_se A PI PR verI verR ext simI progI simR progR hzkI hεI hzkR hεR hAI hAR
    (sim_se_le_okK A verI verR ext simI progI simR progR hw hk hse hAE)

end Game

/-! ## The reduction's budget with a total -/

open VoleMole.Privacy.Moussaka

lemma left_progQIm (x : IssueInstance) (c : SimCoins pI) :
    IsQueryBoundP (progQIm x c) (fun t => t.isLeft = true) 338 :=
  (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_vPreIC _ _ _)

lemma left_progQRm (x : RedeemInstance) (c : SimCoins pR) :
    IsQueryBoundP (progQRm x c) (fun t => t.isLeft = true) 338 :=
  (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_vPreIC _ _ _)

set_option maxHeartbeats 1000000 in
/-- **The reduction's budget with a total**: the two patches' queries (338 hash queries each),
then the adversary's. -/
theorem qBudT_redQm {α : Type} {q : Kind → ℕ} {qE nG : ℕ} {oa : OracleComp specIC α}
    (h : QBudT q qE nG oa) (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (x₂ : Option RedeemInstance) (c₂ : SimCoins pR) :
    QBudT (q + Ratatouille.qPre + Ratatouille.qPre) (qE + verifyCellBound pR + verifyCellBound pI)
      (nG + 338 + 338) (redQ progQIm (patch2 pI) progQRm (patch2 pI) x₁ c₁ x₂ c₂ oa) := by
  refine ⟨qBud_redQm h.1 x₁ c₁ x₂ c₂, ?_⟩
  unfold redQ
  have h2 : IsQueryBoundP (progQO progQRm x₂ c₂) (fun t => t.isLeft = true) 338 :=
    Ratatouille.left_progQO (fun x c => left_progQRm x c) x₂ c₂
  have h1 : IsQueryBoundP (progQO progQIm x₁ c₁) (fun t => t.isLeft = true) 338 :=
    Ratatouille.left_progQO (fun x c => left_progQIm x c) x₁ c₁
  refine (isQueryBoundP_bind (n := 338) (m := 338 + nG) h2 fun m₂ _ =>
    isQueryBoundP_bind (n := 338) (m := nG) h1 fun m₁ _ => ?_).mono (by omega)
  exact isQueryBoundP_simP _ h.2

/-! ## Redemption non-malleability -/

variable {L : ℕ}

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomM` on the reduction's queries. -/
noncomputable def extRomM (q : Kind → ℕ) (qE nG : ℕ) :
    Moussaka.Ext Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)) :=
  extL ansP (QBudT q qE nG) logQIm logQRm eRomM

set_option maxHeartbeats 1000000 in
/-- **Redemption non-malleability with `ROM/`'s plain extraction** (Moussaka, one token): as
`noRedirect_leanX_hitL`, with function rows, `M = Moussaka.M`, `L ≥ 8193`, a `HitWf` adversary
whose output redemptions have the Anchor keys of `kt` (`hk`) and whose last stage is the run on the
tables of an oracle computation with at most `q k` hash queries of kind `k`, `nG` in all and `q_E`
cipher cells (`hA`), and `ROM/`'s straight-line extractor (`extRomM`); plain extraction is no longer
a hypothesis:

    Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`ε_rom = epsRomM (q + 2·qPre) (q_E + cells(pR) + cells(pI)) (nG + 2·338)`,
`q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)` with the extractor's read budget `hX`. -/
theorem noRedirect_lean_rom (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE nG x3 x5 xE : ℕ}
    (hA : ∀ o₁ o₂, AdmL (QBudT q qE nG) ansP (A.out o₁ o₂))
    (hX : ∀ o₁ o₂, StageBudgetX (extRomM q qE nG (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomM q qE nG)) ≤
      ZKRow.εz (Blk → Blk) pI (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        ZKRow.εz (Blk → Blk) pR (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        ((epsRomM (q + Ratatouille.qPre + Ratatouille.qPre)
          (qE + verifyCellBound pR + verifyCellBound pI) (nG + 338 + 338)).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extRomM q qE nG) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have hSB : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) (q .h3) (q .h5) qE := fun o₁ o₂ => by
    obtain ⟨oa, hb, hF⟩ := hA o₁ o₂
    rw [hF]
    exact stageBudgetX_runT hb.1
  have hAH : ∀ F : Tab3 → Tab3 → ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M) → MOp,
      AdmL (QBudT q qE nG) ansP F →
      Hit.AdmHit (R := Blk → Blk) (p := pI) (L := L) (M := Arith.Moussaka.M) (G := Tab3)
        (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHit_runT hb.1
  have hL' : Hit.Mous.Lmin ≤ L := lmin_le_lrom.trans hL
  have hplain := plainSEL_romM (L := L) kt hL (q + Ratatouille.qPre + Ratatouille.qPre)
    (qE + verifyCellBound pR + verifyCellBound pI) (nG + 338 + 338)
  have hmv0 : ProgMoves (simI' (leanSim pI)) (leanProgIX hbX) (simR' (leanSim pR))
      (leanProgRX hbX) (AccOp (verILX hbX) (verRLX hbX)) Hit.Mous.FreshOk
      (AdmL (QBudT q qE nG) ansP) (Hit.epsHit (q .mu) (q .h21) (q .h22)) :=
    progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (accOp_movesX (R := Blk → Blk) (X := XTab L Arith.Moussaka.M) hbX)
      ((Hit.Mous.progEv_hit hL' (q .mu) (q .h21) (q .h22)).mono hAH)
  have hmv : ProgMoves (simI' (leanSim pI)) (leanProgIX hbX) (simR' (leanSim pR)) (leanProgRX hbX)
      (AccOp (verILX hbX) (verRLX hbX)) (FreshK kt) (AdmL (QBudT q qE nG) ansP)
      (Hit.epsHit (q .mu) (q .h21) (q .h22)) :=
    ProgMoves.fresh_mono hmv0 fun _ _ _ h => h.1
  have hse := weakSE2_of_plainL progQIm (patch2 pI) progQRm (patch2 pI) logQIm logQRm hplain hmv
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpatchIm hpatchRm
    (fun x c g₁ g₂ s s' h => hpreIm x c g₁ g₂ s s' h) hlogIm hlogRm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) fun oa x₁ c₁ x₂ c₂ h => qBudT_redQm h x₁ c₁ x₂ c₂
  exact noRedirect_okK (CI := SimCoins pI) (CR := SimCoins pR) A (verILX hbX) (verRLX hbX)
    (extRomM q qE nG) (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (leanPIX hbX)
    (leanPRX hbX) hw hk (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX' hbX A _ hbX_wf hSB hX) (distR_budgetX' hbX A _ hSB hX) hse hA

end Moussaka

end VoleMole.Theft
