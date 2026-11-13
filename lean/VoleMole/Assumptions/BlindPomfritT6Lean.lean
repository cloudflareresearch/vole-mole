import VoleMole.Assumptions.BlindPomfritComplete

/-!
# Theorem 6 at PomFRIT for the Lean client, without a completeness hypothesis

`lean/docs/security/pomfrit.md` §6.4, G9; `uov-assumptions.md` §5.6. The assembly of
`Assumptions/BlindPomfritComplete.lean`: for fixed key, coins and target stream the game is the lazy
random oracle's run of one computation (`OneMore.realImpl_run_eq`); at every table a completeness
failure is `GrindBad` of one of the `ℓ + 1` claimed sessions (`fail_table`); the union over them
(`ROM/ExtractReduce.lean`, `prEvent_le_sum_of_table`) and the fresh-grinding bound
(`prEvent_grindBad_le`) give

* **`compFail_le`**: `compFail ≤ (ℓ + 1)·2⁻¹¹³` for the Lean client;
* **`pomfrit_T6_lean`**: `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger (leanClient …) n B)] +
  (ℓ + 1)·2⁻¹¹³`; **`pomfrit_T6_lean_bound`**: with `B`'s target budget `Q` and `Q + ℓ + 1`
  targets.

Assumed of `B` besides `pomfrit_T6`'s: its random oracle has finite nonempty answer types (needed
to pass from the lazy oracle to tables; true of any coin oracle).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
  VoleMole.Assumptions.Blind VoleMole.Assumptions.UOV
open scoped ENNReal

namespace VoleMole.Assumptions.BlindPomfrit

/-! ## The bound on `compFail`, and Theorem 6 for the Lean client -/

section Bound

lemma pr_bind_le {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (P : β → Prop) (ε : ℝ≥0∞)
    (h : ∀ x, Pr{let y ← f x}[P y] ≤ ε) : Pr{let y ← mx >>= f}[P y] ≤ ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← f x}[P y] ∂𝒟[mx] ≤ ∫⁻ _, ε ∂𝒟[mx] := MeasureTheory.lintegral_mono h
    _ = ε * 𝒟[mx] Set.univ := MeasureTheory.lintegral_const ε
    _ ≤ ε * 1 := by gcongr; exact MeasureTheory.prob_le_one
    _ = ε := mul_one ε

lemma pr_map_bind_pure {α β γ : Type} (X : ProbComp α) (f : α → β) (g : β → γ) (P : γ → Prop) :
    Pr{let y ← (do let r ← f <$> X; pure (g r))}[P y] = Pr{let a ← X}[P (g (f a))] := by
  have : (do let r ← f <$> X; pure (g r)) = (fun a => g (f a)) <$> X := by
    rw [bind_map_left, map_eq_bind_pure_comp]
    rfl
  rw [this, prEvent_map]

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, Fintype (AR d)]
  [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] (lr : Bool) (ℓ n : ℕ) {X' Hn' : Type}
  [DecidableEq X'] {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss)
  (B : UovPk → ProbComp (OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))))

/-- **The completeness term of Theorem 6 for the Lean client** (faest-arch-opt's CRT tables, any
layout): `compFail ≤ (ℓ + 1)·2⁻¹¹³`, for every OMPR adversary (with a finite random oracle), key
generation and Issuer. -/
theorem compFail_le :
    compFail CrtGen.tables lr ℓ (leanClient CrtGen.tables lr) n KG pre B ≤
      (ℓ + 1 : ℝ≥0∞) * (2 ^ 113 : ℝ≥0∞)⁻¹ := by
  classical
  unfold compFail omuf
  simp only [blindAdv, bind_assoc, pure_bind]
  refine pr_bind_le _ _ _ _ fun kp => ?_
  refine pr_bind_le _ _ _ _ fun b => ?_
  have hc : (toClient CrtGen.tables lr ℓ (leanClient CrtGen.tables lr)).coins = (do
      let E ← $ᵗ CTable
      let κ ← (leanClient CrtGen.tables lr).coins
      pure (E, κ)) := rfl
  rw [hc]
  simp only [bind_assoc, pure_bind]
  refine pr_bind_le _ _ _ _ fun E => ?_
  refine pr_bind_le _ _ _ _ fun κc => ?_
  refine pr_bind_le _ _ _ _ fun L => ?_
  show Pr{let y ← (do
      let r ← (simulateQ (realImpl addHint (pre kp.2)) (gameA lr ℓ n kp.1 (E, κc) b)).run
        ((fun _ => none), ch0 L)
      pure (kp.1, r.1, r.2))}[Wins ℓ (goodPre relP) y.1 y.2.1.1 y.2.2.2 ∧ y.2.1.2 = false] ≤ _
  rewrite [realImpl_run_eq, pr_map_bind_pure]
  let Q : (List (ByteArray × SIss) × Bool) × HTS → Prop := fun o =>
    Wins ℓ (goodPre relP) kp.1 o.1.1 (chOf (AR := WB AR) o.2.2 ∅) ∧ o.1.2 = false
  refine (prEvent_mono _ _
    (fun z : ((List (ByteArray × SIss) × Bool) × HTS) × (ofFn (WB AR)).QueryCache => Q z.1)
    fun z hz => hz).trans ?_
  rewrite [← prEvent_map _ Prod.fst Q, ← StateT.run'_eq]
  refine (prEvent_le_sum_of_table _ (Finset.range (ℓ + 1))
    (fun p => pfxB lr ℓ n kp.1 (pre kp.2) (E, κc) b L p >>= blockW) Q
    (fun _ r => GrindBad CrtGen.tables r)
    (fun G hG => fail_table lr ℓ n kp.1 (pre kp.2) (E, κc) b L G hG)).trans ?_
  refine (Finset.sum_le_sum fun p _ =>
    prEvent_grindBad_le _ (allQ_pfxB (pre kp.2) lr ℓ n kp.1 (E, κc) b L p)).trans ?_
  rewrite [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_rfl

/-- **Theorem 6 at PomFRIT for the Lean client** (`uov-assumptions.md` §5.6, `pomfrit.md` G9): for
every OMPR adversary `B` (with a finite random oracle), the blinding forger running the Lean
client (`leanClient`, faest-arch-opt's tables) wins PomFRIT's one-more forgery game with

    Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin] + (ℓ + 1)·2⁻¹¹³. -/
theorem pomfrit_T6_lean (tgts : TG × TG → List TG) :
    advOMPR (Links.pomTrap KG pre) n ℓ B ≤
      Pr{let r ← gameB CrtGen.tables lr tgts ℓ KG pre n
          (blindForger lr (leanClient CrtGen.tables lr) n B) addHint (fun _ => hint0)}[
        PomWinB ℓ r] + (ℓ + 1 : ℝ≥0∞) * (2 ^ 113 : ℝ≥0∞)⁻¹ :=
  (pomfrit_T6 CrtGen.tables lr ℓ (leanClient CrtGen.tables lr) n KG pre tgts B).trans
    (add_le_add le_rfl (compFail_le lr ℓ n KG pre B))

/-- **Theorem 6 at PomFRIT for the Lean client, with `B`'s target budget**: for `B` with at most
`Q` target requests, the game with `Q + ℓ + 1` targets (U1's convention). -/
theorem pomfrit_T6_lean_bound (Q : ℕ) (tgts : TG × TG → List TG)
    (hB : ∀ pk, ∀ b ∈ support (B pk), IsQueryBoundP b (fun q => isTgt q = true) Q) :
    advOMPR (Links.pomTrap KG pre) Q ℓ B ≤
      Pr{let r ← gameB CrtGen.tables lr tgts ℓ KG pre (Q + (ℓ + 1))
          (blindForger lr (leanClient CrtGen.tables lr) (Q + (ℓ + 1)) B) addHint
          (fun _ => hint0)}[PomWinB ℓ r] + (ℓ + 1 : ℝ≥0∞) * (2 ^ 113 : ℝ≥0∞)⁻¹ :=
  (pomfrit_T6_bound CrtGen.tables lr ℓ Q (leanClient CrtGen.tables lr) KG pre tgts B hB).trans
    (add_le_add le_rfl (compFail_le lr ℓ (Q + (ℓ + 1)) KG pre B))

end Bound

end VoleMole.Assumptions.BlindPomfrit
