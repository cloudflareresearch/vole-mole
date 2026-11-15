import VoleMole.Theft.DeltaX
import VoleMole.Theft.MoussakaUnboundTables
import VoleMole.Theft.RatatouilleMany
import VoleMole.Theft.MoussakaMany
import VoleMole.Theft.MoussakaUnboundMany

/-!
# The collision terms of the theft games, bounded

The theft and non-malleability theorems with the Lean prover (`noTheft_lean_romK`, …,
`Theft/PlainTotalRom.lean`, and the `_romP'` versions) carry the collision terms of their
zero-knowledge hops: `δ_S` (`deltaS`), `δ_R` (`deltaR`), and `δ_i` for each hop of the games with
`U` tokens and `M` proofs (`deltaNR`, `deltaNM`, `deltaNU`). Each is the probability that a real
proof, run on the tables the earlier simulations programmed, differs from the proof on the original
tables. Here they are bounded with `pr_collide_zkX` (`Theft/DeltaX.lean`), for every type of cipher
rows with `ZKRow R` and every base record read off an extra table:

* **`deltaS_le`** (Ratatouille, one Client), **`deltaR_le`** (Moussaka, one token):

      δ ≤ 2⁻¹¹³ + εz(p; 0, 312, 4607) + noHitProb + 2⁻¹⁰²⁴,

  `p` the parameters of the real proof (`pS`, `pR`). The earlier simulation is the issuance; its
  programmed block has the tail `simTail c₁` (its uniform `ã`).
* **`deltaNR_le`**, **`deltaNM_le`**, **`deltaNU_le`** (`U` tokens, `M` proofs): for hop `i`,

      δ_i ≤ 2⁻¹¹³ + εz(pI; 0, 312, 4607) + εz(pS or pR; 0, 312, 4607) + noHitProb
        + 2·(U + M)·2⁻¹⁰²⁴.

  The `i` earlier slots each program at most one block, with the tail of one of their two coins
  (issuance or spend/redemption coins), so at most `2·i ≤ 2·(U + M)` tails.

If the Client makes no proof at the slot (its checks fail), the term is `0`. Nothing here depends
on SHAKE: the base record is any `Hb x` with `HashesWF`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-- The bound is nonnegative. -/
lemma deltaBound_nonneg (a k : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    0 ≤ 1 / 2 ^ 113 + a + (noHitProb + k / 2 ^ 1024 : ℝ) := by
  have := pr_nonneg (α := Grind) (fun g => firstHit g = none)
  unfold noHitProb; positivity

/-- Widening the bound. -/
lemma deltaBound_mono {a b c c' : ℝ} (hb : 0 ≤ b) (hc : c ≤ c') :
    1 / 2 ^ 113 + a + (noHitProb + c / 2 ^ 1024 : ℝ) ≤
      1 / 2 ^ 113 + (a + b) + (noHitProb + c' / 2 ^ 1024) := by
  exact add_le_add (add_le_add le_rfl (le_add_of_nonneg_right hb))
    (add_le_add le_rfl (div_le_div_of_nonneg_right hc (by positivity)))

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] {X : Type} [Fintype X] [Nonempty X]
  {Hb : X → Hashes}

lemma leanPSRX_vec (x : SpendInstance) (w : SpendWitness) (ρ : Coins 16) (g : Tab3)
    (t : ShX R pI X) :
    leanPSRX Hb x w (vec ρ) g t =
      vecOf _ (realRO pS (Hb t.2.2) (Privacy.Ratatouille.stS x) (encS x w) ρ g (shOf t)) := by
  simp only [leanPSRX, leanPSRH, realRO, bOf_vec]
  rfl

lemma leanPIRX_vec (x : IssueInstance) (w : IssueWitness) (ρ : Coins 16) (g : Tab3)
    (t : ShX R pI X) :
    leanPIRX Hb x w (vec ρ) g t =
      vecOf _ (realRO pI (Hb t.2.2) (Privacy.Ratatouille.stI x) (encI x w) ρ g (shOf t)) := by
  simp only [leanPIRX, leanPIRH, realRO, bOf_vec]

lemma progTails_leanProgIRX (hHb : ∀ x, HashesWF (Hb x)) (x : IssueInstance) (c : SimCoins pI) :
    ProgTails (leanProgIRX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) hHb Privacy.Ratatouille.stI (fun _ => rfl) x c

lemma progTails_leanProgSRX (hHb : ∀ x, HashesWF (Hb x)) (x : SpendInstance) (c : SimCoins pS) :
    ProgTails (leanProgSRX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) (p := pS) hHb Privacy.Ratatouille.stS (fun _ => rfl) x c

lemma smallParams_pI' : SmallParams pI := smallParams_of_le (by decide) (by decide)
lemma smallParams_pS' : SmallParams pS := smallParams_of_le (by decide) (by decide)

/-- **The spend proof's collision bound**, for a fixed statement and witness in the relation. -/
lemma pr_collide_spend [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : SpendInstance}
    {w : SpendWitness} (hxw : SpendRel x w) {L : ShX R pI X → ShX R pI X} {T : Finset ByteArray}
    (hL : ProgTails L T) :
    pr ((Coins 16 × Tab3) × ShX R pI X) (fun a =>
        leanPSRX Hb x w (vec a.1.1) a.1.2 (L a.2) ≠ leanPSRX Hb x w (vec a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pS 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.Ratatouille.stS x) (w := encS x w) hHb rfl
      (zkHypS x w hxw) smallParams_pS' hL)
  rw [leanPSRX_vec, leanPSRX_vec, hL.snd_snd] at ha
  exact fun e => ha (congrArg _ e)

/-- **The issuance proof's collision bound**, for a fixed statement and witness in the
relation. -/
lemma pr_collide_issue [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : IssueInstance}
    {w : IssueWitness} (hxw : IssueRel x w) {L : ShX R pI X → ShX R pI X} {T : Finset ByteArray}
    (hL : ProgTails L T) :
    pr ((Coins 16 × Tab3) × ShX R pI X) (fun a =>
        leanPIRX Hb x w (vec a.1.1) a.1.2 (L a.2) ≠ leanPIRX Hb x w (vec a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pI 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.Ratatouille.stI x) (w := encI x w) hHb rfl
      (zkHypI x w hxw) smallParams_pI' hL)
  rw [leanPIRX_vec, leanPIRX_vec, hL.snd_snd] at ha
  exact fun e => ha (congrArg _ e)

/-- **The collision term of no theft, one Client**: `δ_S ≤ 2⁻¹¹³ + εz(pS; 0, 312, 4607) +
noHitProb + 2⁻¹⁰²⁴`. -/
theorem deltaS_le [ZKRow R] (hHb : ∀ x, HashesWF (Hb x))
    (A : Thief Sizes.labelRows Tab3 (ShX R pI X)) :
    pr _ (deltaS A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb)) ≤
      1 / 2 ^ 113 + ZKRow.εz R pS 0 312 4607 + (noHitProb + 1 / 2 ^ 1024) := by
  unfold deltaS deltaG
  refine pr_le_of_fst fun γ => ?_
  have hL : ProgTails (pgI A (leanProgIRX Hb) γ.1 γ.2.1) {simTail γ.2.1} :=
    ProgTails.progO fun i _ => progTails_leanProgIRX hHb i γ.2.1
  rcases hx : xwS A γ.1 (simIss A leanSimIR γ.1 γ.2.1) with _ | ⟨x, w⟩
  · refine le_trans (le_of_eq ?_) (deltaBound_nonneg _ _ (ZKRow.εz_nonneg _ _ _ _) zero_le_one)
    rw [← pr_false (α := (Coins 16 × Tab3) × ShX R pI X)]
    refine pr_congr fun b => ⟨fun h => h ?_, False.elim⟩
    rw [specS_eq, specS_eq, hx]
    rfl
  · refine (Privacy.pr_mono fun b hb => ?_).trans
      ((pr_collide_spend hHb (xwS_rel A γ.1 _ x w hx) hL).trans (le_of_eq (by simp)))
    rw [specS_eq, specS_eq, hx] at hb
    exact fun e => hb (by simp only [proveO, PS'] at e ⊢; rw [e])

variable {U M : ℕ}

/-- A slot's programming programs at the tail of one of its two coins. -/
lemma progTails_pgPR (hHb : ∀ x, HashesWF (Hb x)) (A : ThiefN Sizes.labelRows U M Tab3 (ShX R pI X))
    (p : Pub) (l : LogR Sizes.labelRows) (c : SimCoins pI × SimCoins pS) :
    ProgTails (pgP A (leanProgIRX Hb) (leanProgSRX Hb) p l c) {simTail c.1, simTail c.2} := by
  refine (ProgTails.progO (prog := progM (leanProgIRX Hb) (leanProgSRX Hb)) fun x _ => ?_).congr
    fun t => rfl
  rcases x with xi | xs
  · exact (progTails_leanProgIRX hHb xi c.1).mono (by simp)
  · exact (progTails_leanProgSRX hHb xs c.2).mono (by simp)

/-- **The collision term of hop `i` of no theft for `U` Clients and `M` spends**:
`δ_i ≤ 2⁻¹¹³ + εz(pI; 0, 312, 4607) + εz(pS; 0, 312, 4607) + noHitProb + 2·(U + M)·2⁻¹⁰²⁴`. -/
theorem deltaNR_le [ZKRow R] (hHb : ∀ x, HashesWF (Hb x))
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX R pI X)) (i : Fin (U + M)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShX R pI X))
        (deltaNR A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR
          (leanProgSRX Hb) i) ≤
      1 / 2 ^ 113 + (ZKRow.εz R pI 0 312 4607 + ZKRow.εz R pS 0 312 4607) +
        (noHitProb + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024) := by
  unfold deltaNR
  refine pr_deltaN_le _ _ _ i fun ω τ => ?_
  have hL := simPre_progTails (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
    (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω))
    (fun c => {simTail c.1, simTail c.2}) (fun ω l c => progTails_pgPR hHb A (pubOf ω) l c) ω
    (tapeC τ) i
  have hcard : (((Finset.range i).biUnion fun k =>
      ({simTail (tapeC τ k).1, simTail (tapeC τ k).2} : Finset ByteArray)).card : ℝ) ≤
      ((2 * (U + M) : ℕ) : ℝ) := by
    have h1 := card_biUnion_le_two (fun c : SimCoins pI × SimCoins pS =>
      ({simTail c.1, simTail c.2} : Finset ByteArray)) (fun _ => Finset.card_le_two) (tapeC τ) i
    have h2 : 2 * (i : ℕ) ≤ 2 * (U + M) := by have := i.isLt; omega
    exact_mod_cast h1.trans h2
  generalize (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
    (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω)) ω (tapeC τ) i) = sp at hL ⊢
  rcases hx : xwN A ω sp.1 with _ | ⟨x, w⟩
  · refine le_trans (le_of_eq ?_) (deltaBound_nonneg _ _ (add_nonneg (ZKRow.εz_nonneg _ _ _ _)
      (ZKRow.εz_nonneg _ _ _ _)) (by positivity))
    rw [← pr_false (α := (Coins 16 × Tab3) × ShX R pI X)]
    refine pr_congr fun b => ⟨fun h => h ?_, False.elim⟩
    simp only [PN, hx, proveO]
  · have hR : RelRI x w ∨ RelRS x w := by
      by_cases hl : sp.1.length < U
      · exact Or.inl (xwN_relI A ω sp.1 hl x w hx)
      · exact Or.inr (xwN_relS A ω sp.1 hl x w hx)
    rcases x with xi | xs
    · have hxw : IssueRel xi w.1 := by
        rcases hR with h | h
        · exact h
        · exact h.elim
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_issue hHb hxw hL).trans
        (deltaBound_mono (ZKRow.εz_nonneg _ _ _ _) hcard))
      simp only [PN, hx, proveO, PM, sumProveO, PI'] at ha
      exact fun e => ha (by rw [e])
    · have hxw : SpendRel xs w.2 := by
        rcases hR with h | h
        · exact h.elim
        · exact h
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_spend hHb hxw hL).trans
        (le_trans (deltaBound_mono (b := ZKRow.εz R pI 0 312 4607) (ZKRow.εz_nonneg _ _ _ _) hcard)
          (le_of_eq (by rw [add_comm (ZKRow.εz R pS 0 312 4607)]))))
      simp only [PN, hx, proveO, PM, sumProveO, PS'] at ha
      exact fun e => ha (by rw [e])

end Ratatouille

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] {X : Type} [Fintype X] [Nonempty X]
  {Hb : X → Hashes}

lemma leanPRX_ofFn (w : Bytes) (x : RedeemInstance) (ρ : Coins proveSeedBytes) (g : Tab3)
    (t : ShX R pI X) :
    leanPRX Hb w x (List.ofFn ρ) g t = toL ((realRO pR (Hb t.2.2) (Privacy.Moussaka.stR x)
      (toBA w) ρ g (shOf t)).toOption.getD .empty) := by
  simp only [leanPRX, leanPRH, realRO, toBA_ofFn]
  rfl

lemma leanPIX_ofFn (w : Bytes) (x : IssueInstance) (ρ : Coins proveSeedBytes) (g : Tab3)
    (t : ShX R pI X) :
    leanPIX Hb w x (List.ofFn ρ) g t = toL ((realRO pI (Hb t.2.2) (Privacy.Moussaka.stI x)
      (toBA w) ρ g (shOf t)).toOption.getD .empty) := by
  simp only [leanPIX, leanPIH, realRO, toBA_ofFn]

lemma progTails_leanProgIX (hHb : ∀ x, HashesWF (Hb x)) (x : IssueInstance) (c : SimCoins pI) :
    ProgTails (leanProgIX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) hHb Privacy.Moussaka.stI (fun _ => rfl) x c

lemma progTails_leanProgRX (hHb : ∀ x, HashesWF (Hb x)) (x : RedeemInstance) (c : SimCoins pR) :
    ProgTails (leanProgRX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) (p := pR) hHb Privacy.Moussaka.stR (fun _ => rfl) x c

lemma smallParams_pIm : SmallParams pI := smallParams_of_le (by decide) (by decide)
lemma smallParams_pRm : SmallParams pR := smallParams_of_le (by decide) (by decide)

lemma toL_ne {o o' : Except String ByteArray}
    (h : toL (o.toOption.getD .empty) ≠ toL (o'.toOption.getD .empty)) : o ≠ o' :=
  fun e => h (by rw [e])

/-- **The redemption proof's collision bound**, for a fixed statement and witness. -/
lemma pr_collide_redeem [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : RedeemInstance}
    {w : Bytes} (hxw : RedeemRelW x w) {L : ShX R pI X → ShX R pI X} {T : Finset ByteArray}
    (hL : ProgTails L T) :
    pr ((Coins proveSeedBytes × Tab3) × ShX R pI X) (fun a =>
        leanPRX Hb w x (List.ofFn a.1.1) a.1.2 (L a.2) ≠
          leanPRX Hb w x (List.ofFn a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pR 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.Moussaka.stR x) (w := toBA w) hHb rfl
      (zkHypR x w hxw) smallParams_pRm hL)
  rw [leanPRX_ofFn, leanPRX_ofFn, hL.snd_snd] at ha
  exact toL_ne ha

/-- **The issuance proof's collision bound**, for a fixed statement and witness. -/
lemma pr_collide_issue [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : IssueInstance}
    {w : Bytes} (hxw : IssueRelW x w) {L : ShX R pI X → ShX R pI X} {T : Finset ByteArray}
    (hL : ProgTails L T) :
    pr ((Coins proveSeedBytes × Tab3) × ShX R pI X) (fun a =>
        leanPIX Hb w x (List.ofFn a.1.1) a.1.2 (L a.2) ≠
          leanPIX Hb w x (List.ofFn a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pI 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.Moussaka.stI x) (w := toBA w) hHb rfl
      (zkHypI x w hxw) smallParams_pIm hL)
  rw [leanPIX_ofFn, leanPIX_ofFn, hL.snd_snd] at ha
  exact toL_ne ha

/-- **The collision term of redemption non-malleability, one token**: `δ_R ≤ 2⁻¹¹³ +
εz(pR; 0, 312, 4607) + noHitProb + 2⁻¹⁰²⁴`. -/
theorem deltaR_le [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) (A : Thief Tab3 (ShX R pI X)) :
    pr _ (deltaR A (leanPRX Hb) (leanSim pI) (leanProgIX Hb)) ≤
      1 / 2 ^ 113 + ZKRow.εz R pR 0 312 4607 + (noHitProb + 1 / 2 ^ 1024) := by
  unfold deltaR deltaG
  refine pr_le_of_fst fun γ => ?_
  have hL : ProgTails (pgIP A (leanProgIX Hb) (tOf A γ.1) γ.2.1) {simTail γ.2.1} :=
    ProgTails.progO fun i _ => progTails_leanProgIX hHb i γ.2.1
  rcases hx : xwR A γ.1 (simIssP A (leanSim pI) (tOf A γ.1) γ.2.1) with _ | ⟨x, w⟩
  · refine le_trans (le_of_eq ?_) (deltaBound_nonneg _ _ (ZKRow.εz_nonneg _ _ _ _) zero_le_one)
    rw [← pr_false (α := (Coins proveSeedBytes × Tab3) × ShX R pI X)]
    refine pr_congr fun b => ⟨fun h => h ?_, False.elim⟩
    rw [specR_eq, specR_eq, hx]
    rfl
  · refine (Privacy.pr_mono fun b hb => ?_).trans
      ((pr_collide_redeem hHb (xwR_rel A γ.1 _ x w hx) hL).trans (le_of_eq (by simp)))
    rw [specR_eq, specR_eq, hx] at hb
    exact fun e => hb (by simp only [proveO, PR'] at e ⊢; rw [e])

variable {U M : ℕ}

/-- A slot's programming programs at the tail of one of its two coins. -/
lemma progTails_pgPM (hHb : ∀ x, HashesWF (Hb x)) (A : ThiefN U M Tab3 (ShX R pI X))
    (p : Pub U) (l : Log) (c : SimCoins pI × SimCoins pR) :
    ProgTails (pgP A (leanProgIX Hb) (leanProgRX Hb) p l c) {simTail c.1, simTail c.2} := by
  refine (ProgTails.progO (prog := progM (leanProgIX Hb) (leanProgRX Hb)) fun x _ => ?_).congr
    fun t => rfl
  rcases x with xi | xr
  · exact (progTails_leanProgIX hHb xi c.1).mono (by simp)
  · exact (progTails_leanProgRX hHb xr c.2).mono (by simp)

/-- **The collision term of hop `i` of redemption non-malleability for `U` tokens and `M`
redemptions**: `δ_i ≤ 2⁻¹¹³ + εz(pI; 0, 312, 4607) + εz(pR; 0, 312, 4607) + noHitProb +
2·(U + M)·2⁻¹⁰²⁴`. -/
theorem deltaNM_le [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) (A : ThiefN U M Tab3 (ShX R pI X))
    (i : Fin (U + M)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
        (deltaNM A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
          (leanProgRX Hb) i) ≤
      1 / 2 ^ 113 + (ZKRow.εz R pI 0 312 4607 + ZKRow.εz R pR 0 312 4607) +
        (noHitProb + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024) := by
  unfold deltaNM
  refine pr_deltaN_le _ _ _ i fun ω τ => ?_
  have hL := simPre_progTails (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω))
    (fun c => {simTail c.1, simTail c.2}) (fun ω l c => progTails_pgPM hHb A (pubOf A ω) l c) ω
    (tapeC τ) i
  have hcard : (((Finset.range i).biUnion fun k =>
      ({simTail (tapeC τ k).1, simTail (tapeC τ k).2} : Finset ByteArray)).card : ℝ) ≤
      ((2 * (U + M) : ℕ) : ℝ) := by
    have h1 := card_biUnion_le_two (fun c : SimCoins pI × SimCoins pR =>
      ({simTail c.1, simTail c.2} : Finset ByteArray)) (fun _ => Finset.card_le_two) (tapeC τ) i
    have h2 : 2 * (i : ℕ) ≤ 2 * (U + M) := by have := i.isLt; omega
    exact_mod_cast h1.trans h2
  generalize (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω)) ω (tapeC τ) i) = sp at hL ⊢
  rcases hx : xwN A ω sp.1 with _ | ⟨x, w⟩
  · refine le_trans (le_of_eq ?_) (deltaBound_nonneg _ _ (add_nonneg (ZKRow.εz_nonneg _ _ _ _)
      (ZKRow.εz_nonneg _ _ _ _)) (by positivity))
    rw [← pr_false (α := (Coins proveSeedBytes × Tab3) × ShX R pI X)]
    refine pr_congr fun b => ⟨fun h => h ?_, False.elim⟩
    simp only [PN, hx, proveO]
  · have hR : RelMI x w ∨ RelMR x w := by
      by_cases hl : sp.1.length < U
      · exact Or.inl (xwN_relI A ω sp.1 hl x w hx)
      · exact Or.inr (xwN_relR A ω sp.1 hl x w hx)
    rcases x with xi | xr
    · have hxw : IssueRelW xi w := by
        rcases hR with h | h
        · exact h
        · exact h.elim
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_issue hHb hxw hL).trans
        (deltaBound_mono (ZKRow.εz_nonneg _ _ _ _) hcard))
      simp only [PN, hx, proveO, PM, sumProve] at ha
      exact fun e => ha (by rw [e])
    · have hxw : RedeemRelW xr w := by
        rcases hR with h | h
        · exact h.elim
        · exact h
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_redeem hHb hxw hL).trans
        (le_trans (deltaBound_mono (b := ZKRow.εz R pI 0 312 4607) (ZKRow.εz_nonneg _ _ _ _) hcard)
          (le_of_eq (by rw [add_comm (ZKRow.εz R pR 0 312 4607)]))))
      simp only [PN, hx, proveO, PM, sumProve] at ha
      exact fun e => ha (by rw [e])

end Moussaka

/-! ## Unbound Moussaka -/

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (proveSeedBytes)
open VoleMole.Privacy.Moussaka (leanSim)
open VoleMole.Theft.Moussaka (toL_ne)

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] {X : Type} [Fintype X] [Nonempty X]
  {Hb : X → Hashes} {U M : ℕ}

lemma leanPRUX_ofFn (w : Bytes) (x : RedeemInstance) (ρ : Coins proveSeedBytes) (g : Tab3)
    (t : ShX R Privacy.Moussaka.pI X) :
    leanPRUX Hb w x (List.ofFn ρ) g t = toL ((realRO pR (Hb t.2.2) (Privacy.MoussakaUnbound.stR x)
      (toBA w) ρ g (shOf t)).toOption.getD .empty) := by
  simp only [leanPRUX, leanPRUH, realRO, toBA_ofFn]
  rfl

lemma leanPIUX_ofFn (w : Bytes) (x : IssueInstance) (ρ : Coins proveSeedBytes) (g : Tab3)
    (t : ShX R Privacy.Moussaka.pI X) :
    leanPIUX Hb w x (List.ofFn ρ) g t = toL ((realRO pI (Hb t.2.2) (Privacy.MoussakaUnbound.stI x)
      (toBA w) ρ g (shOf t)).toOption.getD .empty) := by
  simp only [leanPIUX, leanPIUH, realRO, toBA_ofFn]
  rfl

lemma progTails_leanProgIUX (hHb : ∀ x, HashesWF (Hb x)) (x : IssueInstance) (c : SimCoins pI) :
    ProgTails (leanProgIUX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) hHb Privacy.MoussakaUnbound.stI (fun _ => rfl) x c

lemma progTails_leanProgRUX (hHb : ∀ x, HashesWF (Hb x)) (x : RedeemInstance) (c : SimCoins pR) :
    ProgTails (leanProgRUX (R := R) Hb x c) {simTail c} :=
  progTails_progRO (R := R) (p := pR) hHb Privacy.MoussakaUnbound.stR (fun _ => rfl) x c

lemma smallParams_pIu : SmallParams pI := smallParams_of_le (by decide) (by decide)
lemma smallParams_pRu : SmallParams pR := smallParams_of_le (by decide) (by decide)

/-- **The unbound redemption proof's collision bound**, for a fixed statement and witness. -/
lemma pr_collide_redeem [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : RedeemInstance}
    {w : Bytes} (hxw : RedeemRelW x w) {L : ShX R Privacy.Moussaka.pI X → ShX R Privacy.Moussaka.pI X}
    {T : Finset ByteArray} (hL : ProgTails L T) :
    pr ((Coins proveSeedBytes × Tab3) × ShX R Privacy.Moussaka.pI X) (fun a =>
        leanPRUX Hb w x (List.ofFn a.1.1) a.1.2 (L a.2) ≠
          leanPRUX Hb w x (List.ofFn a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pR 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.MoussakaUnbound.stR x) (w := toBA w) hHb rfl
      (zkHypR x w hxw) smallParams_pRu hL)
  rw [leanPRUX_ofFn, leanPRUX_ofFn, hL.snd_snd] at ha
  exact toL_ne ha

/-- **The unbound issuance proof's collision bound**, for a fixed statement and witness. -/
lemma pr_collide_issue [ZKRow R] (hHb : ∀ x, HashesWF (Hb x)) {x : IssueInstance}
    {w : Bytes} (hxw : IssueRelW x w) {L : ShX R Privacy.Moussaka.pI X → ShX R Privacy.Moussaka.pI X}
    {T : Finset ByteArray} (hL : ProgTails L T) :
    pr ((Coins proveSeedBytes × Tab3) × ShX R Privacy.Moussaka.pI X) (fun a =>
        leanPIUX Hb w x (List.ofFn a.1.1) a.1.2 (L a.2) ≠
          leanPIUX Hb w x (List.ofFn a.1.1) a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R pI 0 312 4607 + (noHitProb + T.card / 2 ^ 1024) := by
  refine (Privacy.pr_mono fun a ha => ?_).trans
    (pr_collide_zkX (R := R) (st := Privacy.MoussakaUnbound.stI x) (w := toBA w) hHb rfl
      (zkHypI x w hxw) smallParams_pIu hL)
  rw [leanPIUX_ofFn, leanPIUX_ofFn, hL.snd_snd] at ha
  exact toL_ne ha

/-- A slot's programming programs at the tail of one of its two coins. -/
lemma progTails_pgPU (hHb : ∀ x, HashesWF (Hb x))
    (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI X)) (p : Pub U) (l : Log)
    (c : SimCoins pI × SimCoins pR) :
    ProgTails (pgP A (leanProgIUX Hb) (leanProgRUX Hb) p l c) {simTail c.1, simTail c.2} := by
  refine (ProgTails.progO (prog := progU (leanProgIUX Hb) (leanProgRUX Hb)) fun x _ => ?_).congr
    fun t => rfl
  rcases x with xi | xr
  · exact (progTails_leanProgIUX hHb xi c.1).mono (by simp)
  · exact (progTails_leanProgRUX hHb xr c.2).mono (by simp)

/-- **The collision term of hop `i` of unbound non-malleability for `U` tokens and `M`
redemptions**: `δ_i ≤ 2⁻¹¹³ + εz(pI; 0, 312, 4607) + εz(pR; 0, 312, 4607) + noHitProb +
2·(U + M)·2⁻¹⁰²⁴`. -/
theorem deltaNU_le [ZKRow R] (hHb : ∀ x, HashesWF (Hb x))
    (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI X)) (i : Fin (U + M)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
        (deltaNU A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
          (leanProgRUX Hb) i) ≤
      1 / 2 ^ 113 + (ZKRow.εz R pI 0 312 4607 + ZKRow.εz R pR 0 312 4607) +
        (noHitProb + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024) := by
  unfold deltaNU
  refine pr_deltaN_le _ _ _ i fun ω τ => ?_
  have hL := simPre_progTails (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω))
    (fun c => {simTail c.1, simTail c.2}) (fun ω l c => progTails_pgPU hHb A (pubOf A ω) l c) ω
    (tapeC τ) i
  have hcard : (((Finset.range i).biUnion fun k =>
      ({simTail (tapeC τ k).1, simTail (tapeC τ k).2} : Finset ByteArray)).card : ℝ) ≤
      ((2 * (U + M) : ℕ) : ℝ) := by
    have h1 := card_biUnion_le_two (fun c : SimCoins pI × SimCoins pR =>
      ({simTail c.1, simTail c.2} : Finset ByteArray)) (fun _ => Finset.card_le_two) (tapeC τ) i
    have h2 : 2 * (i : ℕ) ≤ 2 * (U + M) := by have := i.isLt; omega
    exact_mod_cast h1.trans h2
  generalize (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω)) ω (tapeC τ) i) = sp at hL ⊢
  rcases hx : xwN A ω sp.1 with _ | ⟨x, w⟩
  · refine le_trans (le_of_eq ?_) (deltaBound_nonneg _ _ (add_nonneg (ZKRow.εz_nonneg _ _ _ _)
      (ZKRow.εz_nonneg _ _ _ _)) (by positivity))
    rw [← pr_false (α := (Coins proveSeedBytes × Tab3) × ShX R Privacy.Moussaka.pI X)]
    refine pr_congr fun b => ⟨fun h => h ?_, False.elim⟩
    simp only [PN, hx, proveO]
  · have hR : RelUI x w ∨ RelUR x w := by
      by_cases hl : sp.1.length < U
      · exact Or.inl (xwN_relI A ω sp.1 hl x w hx)
      · exact Or.inr (xwN_relR A ω sp.1 hl x w hx)
    rcases x with xi | xr
    · have hxw : IssueRelW xi w := by
        rcases hR with h | h
        · exact h
        · exact h.elim
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_issue hHb hxw hL).trans
        (deltaBound_mono (ZKRow.εz_nonneg _ _ _ _) hcard))
      simp only [PN, hx, proveO, PU, sumProve] at ha
      exact fun e => ha (by rw [e])
    · have hxw : RedeemRelW xr w := by
        rcases hR with h | h
        · exact h.elim
        · exact h
      refine (Privacy.pr_mono fun a ha => ?_).trans ((pr_collide_redeem hHb hxw hL).trans
        (le_trans (deltaBound_mono (b := ZKRow.εz R pI 0 312 4607) (ZKRow.εz_nonneg _ _ _ _) hcard)
          (le_of_eq (by rw [add_comm (ZKRow.εz R pR 0 312 4607)]))))
      simp only [PN, hx, proveO, PU, sumProve] at ha
      exact fun e => ha (by rw [e])

end MoussakaUnbound

end VoleMole.Theft
