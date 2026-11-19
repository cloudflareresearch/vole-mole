import VoleMole.ZK.MainSharedLin4
import VoleMole.Privacy.RatatouilleMainSharedAll

/-!
# Ratatouille unlinkability on `main`, all tables shared, on the linear joint hop

`unlinkability_main_sharedAll` (`Privacy/RatatouilleMainSharedAll.lean`) is Theorem 2 on `main`
with all tables shared, through the four-proof joint hop `main_sharedAll_le`:
`15·(εS(q₃, q_E + 8·4607) + Δ23)` per world, `15` on `bstar`, and `2·2⁻¹²⁸` per world for two
proofs with one prefix. Here the same game goes through `main_sharedAll_le4Lin`
(`main_sharedAll_le4LinJ`, `ZK/MainSharedLin4.lean`): per world
`8·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))`, `1` on `bstar`, no prefix-collision term, for an
Issuer whose guess and `H₅` read set read `H₃` and the cipher jointly (`ConsJ`; `ConsH.consJ`: at
twice the budgets for separate read sets). Hiding, the coincidence of the worlds and the predictors
(`predHR₀`, `predHR₁`, `predHRC`) are those of `unlinkability_main_sharedAll`.

## The bound (`unlinkability_main_sharedLin`)

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]| ≤ 16·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))
        + PUH(b₁, b₂) + PUH(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸ + 2·εhide
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

attribute [local irreducible] simulate realRO progRO

variable [HasPrg] (A : AdversaryRH)

/-- **Separate read sets are joint read sets at the sum of the budgets.** -/
theorem rdTHR_pair {X Y : Type*} {f : VisSR → H3T → X} {g : VisSR → H3T → Y}
    {R : VisSR → H3T → Finset (ZK.Sim.Bytes 37)} {q3 qE q3' qE' : ℕ} (hf : RdTHR f R q3 qE)
    (hg : RdTHR g R q3' qE') : RdTHR (fun t T => (f t T, g t T)) R (q3 + q3') (qE + qE') := by
  classical
  obtain ⟨QE, hQEc, hQE⟩ := hf.hE
  obtain ⟨QT, hQTc, hQT⟩ := hf.hT
  obtain ⟨PE, hPEc, hPE⟩ := hg.hE
  obtain ⟨PT, hPTc, hPT⟩ := hg.hT
  refine ⟨fun t T G5 h => ?_, ⟨fun t T => QE t T ∪ PE t T, fun t T => (card_union_le _ _).trans
      (add_le_add (hQEc t T) (hPEc t T)), fun t T E h => ?_⟩,
    ⟨fun t T => QT t T ∪ PT t T, fun t T => (card_union_le _ _).trans
      (add_le_add (hQTc t T) (hPTc t T)), fun t T T' h => ?_⟩⟩
  · show (f _ T, g _ T) = (f t T, g t T)
    rw [hf.h5 t T G5 h, hg.h5 t T G5 h]
  · show (f _ T, g _ T) = (f t T, g t T)
    rw [hQE t T E fun k hk => h k (mem_union_left _ hk),
      hPE t T E fun k hk => h k (mem_union_right _ hk)]
  · show (f t T', g t T') = (f t T, g t T)
    rw [hQT t T T' fun k hk => h k (mem_union_left _ hk),
      hPT t T T' fun k hk => h k (mem_union_right _ hk)]

/-- **Joint consistent reads**: with its input fixed, the guess and its `H₅` read set read `H₃` at
one set of `q3` points and the cipher at one set of `qE` keys, and `H₅` at `R5`. -/
structure AdversaryRH.ConsJ (q3 qE : ℕ) : Prop where
  j : ∀ y, RdTHR (fun t T => (A.guess y t T, A.R5 y t T)) (A.R5 y) q3 qE

omit [HasPrg] in
/-- Consistent reads are joint consistent reads at twice the budgets. -/
theorem AdversaryRH.ConsH.consJ {A : AdversaryRH} {q3 qE : ℕ} (h : A.ConsH q3 qE) :
    A.ConsJ (q3 + q3) (qE + qE) :=
  ⟨fun y => rdTHR_pair (h.g y) (h.r y)⟩

/-- **The joint hop in each world, linear**: all four proofs at once, all tables shared, no
prefix-collision term. -/
theorem real_sim_sharedLinR {q3 qE : ℕ} (hC : A.ConsJ q3 qE) (b₁ b₂ : Bool) :
    |realRH A b₁ b₂ - simRH A b₁ b₂| ≤
      8 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
          (gameSR A.base b₁ b₂) (fun v T => bstar Hashes.shake (gameSR A.base b₁ b₂)
            (fun v => r5RH A b₁ b₂ v T) v) :=
  main_sharedAll_le4LinJ (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
    (gameSR A.base b₁ b₂) mainP_pIr mainP_pIr mainP_pSr mainP_pSr small_pIr small_pIr small_pSr
    small_pSr hashesWF_shake (gvalidSR A.base b₁ b₂) (evRH A b₁ b₂) (r5RH A b₁ b₂)
    (rdHR_of A (f := fun y t T => (A.guess y t T, A.R5 y t T)) (R := fun y t T => A.R5 y t T)
      hC.j b₁ b₂)

/-- **Theorem 2 on `main` (no label rows), all tables shared, on the linear joint hop.** For the
malicious Issuer of `unlinkability_main_sharedAll` with joint reads (`AdversaryRH.ConsJ`), any two
worlds differ by at most

    16·(εS(q3 + 4, qE + 8·4607) + Δ23N(9, 4)) + PUH(b₁, b₂) + PUH(b₁', b₂')
      + 8·noHitProb + 3750·2⁻¹²⁸ + 2·εhide,

`PUH(b₁, b₂)` the (PU) advantages of `predHR₀`, `predHR₁` (`comI`) and `predHRC` (`comCh`).
Compared with `unlinkability_main_sharedAll`: `30` becomes `16`, the factor `15` on the (PU) terms
becomes `1`, and the prefix-collision term `4·2⁻¹²⁸` is gone. -/
theorem unlinkability_main_sharedLin {q3 qE : ℕ} (hC : A.ConsJ q3 qE) {εhide : ℝ}
    (hhide : ∀ T b₁ b₂ a, hidingAdv A.ctx (redSR23 (A.withH T) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |realRH A b₁ b₂ - realRH A b₁' b₂'| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (puAdv (comI A.base.toM) (predHR₀ A b₁ b₂) +
          puAdv (comI A.base.toM) (predHR₁ A b₁ b₂) +
          puAdv (comCh A.base.toM b₁) (predHRC A b₁ b₂) +
          (puAdv (comI A.base.toM) (predHR₀ A b₁' b₂') +
            puAdv (comI A.base.toM) (predHR₁ A b₁' b₂') +
            puAdv (comCh A.base.toM b₁') (predHRC A b₁' b₂')) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have r0 := real_sim_sharedLinR A hC b₁ b₂
  have r1 := real_sim_sharedLinR A hC b₁' b₂'
  have p0 := simAll_bstar_leR A b₁ b₂
  have p1 := simAll_bstar_leR A b₁' b₂'
  have h0 := hiding_hopRH A b₁ b₂ (fun T => hhide T b₁ b₂)
  have h1 := hiding_hopRH A b₁' b₂' (fun T => hhide T b₁' b₂')
  have e0 := idealRH_eq A b₁ b₂
  have e1 := idealRH_eq A b₁' b₂'
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Ratatouille
