import VoleMole.ROM.OneMoreLemmaPSimPerm

/-!
# PomFRIT's Theorem U2 with simultaneous extraction, AES as random permutations

`lean/docs/security/pomfrit.md` §6.2, §6.4, `lean/docs/probabilistic-plan.md` §2o. `pomfrit_U2_sim`
(`ROM/OneMoreShiftSim.lean`) in the permutation model of `ROM/OneMoreLemmaPSimPerm.lean`: the
forger makes forward and inverse cipher queries against a uniform permutation table (`gameP`).
The derived provers are those of U1 (`proverP` reads neither hints nor targets), so the
permutation-model pieces (`RecFamily`, N1, `keysPre_proverP`) carry over unchanged:

* per table, `prEvent_shiftFailZ_sim_le_Ec` with `cf = PostPOut`;
* averaged (`prEvent_shiftFailZ_sim_leP`) with `sum_fail_le_fam`;
* **Theorem U2** (`prEvent_shiftFail_sim_leP`, `pomfrit_U2_simP`):

      Pr[PomWin] ≤ Adv^{ompr⊕17}(red …; Q_T + ℓ + 1, ℓ) + sfailSimEpsP(q', q_E', n', ℓ),

  `sfailSimEpsP` = `sfailSimEps` with `failEpsP` for `failEps`, at the budgets of
  `pomfrit_U1_simP`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-- **`sfailSimEps` in the permutation model**: the failure terms `failEpsP`. -/
noncomputable def sfailSimEpsP (q : Kind → ℕ) (qE n ℓ : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
      simEpsS (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
    (ℓ + 1) * (failEpsP q qE + (2 ^ 128 : ℝ≥0∞)⁻¹)

section Joint

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : ForgerP) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U2's term with simultaneous extraction, permutation model, for a fixed key and target
stream**: over the permutation table and the hash table, some forgery fails with probability at
most `sfailSimEpsP`. -/
theorem prEvent_shiftFailZ_sim_leP (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let π ← $ᵗ PTable; let z ← (simulateQ randomOracle
        ((simulateQ (htW (AR := Ans) noHint pre) (Acomp CrtGen.tables lr π.fwd (hintS lr π.fwd)
          tgts2 pk ℓ (A.toIC lr π))).run (hs0G Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z] ≤
      sfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ := by
  classical
  set q := qP (addH4 qA) QT ℓ
  set e := eP lr qE ℓ
  set ε := simEpsS (nP (nA + qA .h21) QT ℓ + (2 + verifierTotal))
    (q + extractorQueries + verifierQueries)
  set c := ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k
  set pL := pomfritParams lr
  have hb : ∀ (π : PTable) (j : Fin (ℓ + 1)),
      IsKindQueryBoundIC (proverP lr pk pre (A.toIC lr π) Lst j.val) q ∧
      IsQueryBoundP (proverP lr pk pre (A.toIC lr π) Lst j.val) (fun t => t.isLeft = true)
        (nP (nA + qA .h21) QT ℓ) ∧
      IsQueryBoundP (proverP lr pk pre (A.toIC lr π) Lst j.val) (fun t => t.isRight = true) e :=
    fun π j => proverP_bounds lr pre pk (hA.toIC lr π) Lst (Nat.lt_succ_iff.1 j.isLt)
  have havg := prEvent_avgP_le_sum4 _ (fun _ z => ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z) c
    (Finset.univ : Finset (Fin (ℓ + 1)))
    (fun j π => (simulateQ randomOracle (gameDP lr π.fwd pk pre (A.toIC lr π) Lst j.val)).run' ∅)
    (fun π r => bindFailA (stG lr pk) π.fwd r) (fun π r => deadOpenA (stG lr pk) π.fwd r)
    (fun π r => PostPOut pL π.fwd r)
    (fun _ r => r.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)
    (fun π => prEvent_shiftFailZ_sim_le_Ec lr pk pre (A.toIC lr π) Lst ℓ hd (hA.toIC lr π) π.fwd
      (PostPOut pL π.fwd) fun j s g h => keysPre_proverP lr pk pre A Lst π j.val s g h)
  refine havg.trans ?_
  have h3 := sum_fail_le_fam CrtGen.tables (stG lr pk) pL (fun _ => rfl)
    (fun (j : Fin (ℓ + 1)) π => proverP lr pk pre (A.toIC lr π) Lst j.val) Finset.univ
    (fun j _ => recFamily_proverP lr pk pre A Lst j.val) e (fun j _ π => (hb π j).2.2) q
    (fun j _ π => (hb π j).1)
  rw [Finset.sum_add_distrib]
  refine (add_le_add le_rfl (add_le_add h3
    (Finset.sum_le_card_nsmul _ _ (2 ^ 128 : ℝ≥0∞)⁻¹ fun j _ => ?_))).trans_eq ?_
  · exact prEvent_avgP_le _ _ _ fun π =>
      prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) (proverP lr pk pre (A.toIC lr π) Lst j.val)
        π.fwd
  simp only [c, sfailSimEpsP, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp only [add_mul, mul_assoc, mul_add]
  ring

end Joint

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : ForgerP)

/-- **U2's term with simultaneous extraction, permutation model** (`prEvent_shiftFail_sim_le`
with AES as random permutations and inverse queries). -/
theorem prEvent_shiftFail_sim_leP (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre n ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r] ≤
      sfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ := by
  unfold gameP omuf advCP
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _
    (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ PTable) (unifList TG n) (fun π L => (do
    let r ← (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (hintS lr π.fwd) tgts2 kp.1 ℓ (A.toIC lr π))).run
        (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro L
  refine le_trans (le_of_eq ?_)
    (prEvent_shiftFailZ_sim_leP lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ π : PTable, (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (hintS lr π.fwd) tgts2 kp.1 ℓ (A.toIC lr π))).run
        (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint (pre kp.2))
          (Acomp CrtGen.tables lr π.fwd (hintS lr π.fwd) tgts2 kp.1 ℓ (A.toIC lr π))).run
            (hs0G L))).run ∅ := fun π =>
    realImpl_run_eq noHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTSG (List TG)) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), ShiftFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U2 with simultaneous extraction, AES as random permutations with inverse queries**
(`pomfrit.md` §6.2, §6.4; G8): as `pomfrit_U2_sim`, for a forger of the permutation model,

    Pr[PomWin] ≤ Adv^{ompr⊕17}(red …; Q_T + ℓ + 1, ℓ) + sfailSimEpsP(q', q_E', n', ℓ),

`q' = qP (addH4 qA) Q_T ℓ`, `q_E' = eP lr q_E ℓ`, `n' = nP (nA + qA₂₁) Q_T ℓ`. -/
theorem pomfrit_U2_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1))
          (red noHint (advCP ℓ CrtGen.tables lr A (hintS lr) tgts2))}[
        Wins ℓ (goodShift BAVC.tau relP) r.1 r.2.1 r.2.2] +
      sfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ :=
  (pomfrit_U2_boundP KG pre ℓ CrtGen.tables lr A QT BAVC.tau (shP lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_shiftFail_sim_leP KG pre lr A _ ℓ hdig hA))

end Game

end VoleMole.ROM.OneMore.Pomfrit
