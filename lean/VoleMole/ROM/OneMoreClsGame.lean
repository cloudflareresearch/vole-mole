import VoleMole.ROM.OneMoreClsBound

/-!
# Theorem U1^cls in the one-more game

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). The reduction of U1^cls runs the forger wrapped
(`wrapE`, reading the cipher table that the reduction samples) with the hint `E₁^cls` (`e1C`).

* **The game with a forger that depends on the cipher table** (`advCE`, `gameE`) and U1's reduction
  for it (`pomfrit_U1_boundE`, `pomWin_forgesE`): `pomfrit_U1_bound` with `A` replaced by `AE E`.
* **The wrapper does not change the win** (`pomWin_le_wrapE`): table by table the wrapped forger
  outputs the same forgeries, the target oracle gives the same answers and the Issuer is asked as
  often (`eval_wrapE`), so the verifications accept the same forgeries (`verAll_flags_sameG`).
* `prEvent_clsFail_le`: U1^cls's term in the game.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The verifications accept the same forgeries for states with the same answers -/

section Flags

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable) (φ : TG → TG ≃ TG)
  (hint : QueryLog specIC → ByteArray → TG) (tgts : TG × TG → List TG) (pk : UovPk)
  (pre : TG → SIss)

/-- **The verifications' decisions and the Issuer count read the target oracle's answers only.** -/
theorem verAll_flags_sameG (L₁ L₂ : QueryLog specIC) :
    ∀ (outs : List (ByteArray × ByteArray)) (s₁ s₂ : HTSG TG) (t : HTS), SameG s₁ t → SameG s₂ t →
      let a := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L₁ outs)).run s₁)
      let b := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L₂ outs)).run s₂)
      a.1.map Prod.snd = b.1.map Prod.snd ∧ a.2.2.2.2 = b.2.2.2.2
  | [], s₁, s₂, t, h₁, h₂ => by
    simp only [verAll, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, List.map_nil,
      true_and]
    exact h₁.2.2.trans h₂.2.2.symm
  | (m, sg) :: rest, s₁, s₂, t, h₁, h₂ => by
    simp only [verAll, eval_htW_bindG, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure,
      List.map_cons]
    rw [eval_verOneG, eval_verOneG]
    split_ifs with hr
    · simp only
      obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest s₁ s₂ t h₁ h₂
      exact ⟨by rw [f1], f2⟩
    · cases c1T g lr E pk sg with
      | none =>
        simp only
        obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest s₁ s₂ t h₁ h₂
        exact ⟨by rw [f1], f2⟩
      | some c1 =>
        simp only
        set x := tgtIn pk lr sg m c1
        obtain ⟨a1, a2⟩ := tStep_sameG φ h₁ x (hint (L₁ ++ axT g lr L₁ x) x) 0
        obtain ⟨b1, b2⟩ := tStep_sameG φ h₂ x (hint (L₂ ++ axT g lr L₂ x) x) 0
        obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest _ _ _ a2 b2
        refine ⟨?_, f2⟩
        rw [f1, a1, b1]

/-- **The wrapped forger wins exactly when the forger does, table by table**: the same flag and
Issuer count in the game with any hint rule. -/
theorem flag_wrapE (A : Forger) (ℓ : ℕ) (Lst : List TG) :
    let zA := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (Acomp T lr E hint tgts pk ℓ A)).run (hs0G Lst))
    let zW := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (Acomp T lr E hint tgts pk ℓ (wrapE lr E A))).run (hs0G Lst))
    zA.1.2 = zW.1.2 ∧ zA.2.2.2.2 = zW.2.2.2.2 := by
  obtain ⟨a1, a2, a3⟩ := eval_forgerG g E lr φ hint pre (A pk) [] (hs0G Lst) (hs0 Lst)
    (fun _ => none) (InvG.init hint Lst)
  obtain ⟨c1, c2, c3⟩ := eval_forgerG g E lr φ hint pre (wrapE lr E A pk) [] (hs0G Lst) (hs0 Lst)
    (fun _ => none) (InvG.init hint Lst)
  obtain ⟨w1, w2, -, -⟩ := eval_wrapE g E lr pre A pk (hs0 Lst)
  simp only [Acomp]
  rw [eval_htW_bindG, eval_htW_bindG]
  set fA := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    ((simulateQ (wrapImpl lr E hint) (A pk)).run [])).run (hs0G Lst))
  set fW := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    ((simulateQ (wrapImpl lr E hint) (wrapE lr E A pk)).run [])).run (hs0G Lst))
  have ho : fA.1.1 = fW.1.1 := by rw [a1, c1, w1]
  have hsA : SameG fA.2 _ := a3.1
  have hsW : SameG fW.2 _ := c3.1
  rw [w2] at hsW
  rw [← ho]
  split_ifs with hlen
  · rw [eval_htW_bindG, eval_htW_bindG]
    simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
    obtain ⟨f1, f2⟩ := verAll_flags_sameG g T lr E φ hint tgts pk pre fA.1.2 fW.1.2 fA.1.1 _ _ _
      hsA hsW
    refine ⟨?_, f2⟩
    have hall : ∀ (l : List ((ByteArray × SIss) × Bool)), (∀ v ∈ l, v.2 = true) ↔
        ∀ b ∈ l.map Prod.snd, b = true := fun l => by simp
    simp only [hall, f1]
  · simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, true_and]
    exact hsA.2.2.trans hsW.2.2.symm

end Flags

end VoleMole.ROM.OneMore.Pomfrit
