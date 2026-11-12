import VoleMole.Assumptions.Blind
import VoleMole.Assumptions.UOVLinks

/-!
# Non-vacuity of the OMPR / OMPR⊕τ / PomFRIT relations

`Assumptions/Shift.lean` (A1, P8(a)) and `Assumptions/Blind.lean` (Theorem 6, generic core),
instantiated at PomFRIT's trapdoor (`Links.pomTrap`: Def. 3.1's relation `relP`, the honest Issuer
`honestPre`, any fixed key) with `τ = 17`. The only hypotheses are `τ ≥ 1` and, for Theorem 6,
distinct session labels; a client with labels `0, 1, 2, …` satisfies it (`idClient_distinct`), and
since its finishing phase always accepts, its completeness term is `0` (`idClient_compFail`), so
Theorem 6 gives `Adv^{ompr}(B) ≤ Pr[Forges]` for it.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit
open VoleMole.Assumptions.UOV VoleMole.Assumptions.UOV.Links VoleMole.Assumptions.Shift
open VoleMole.Assumptions.Blind
open scoped ENNReal

namespace VoleMole.Audit.OMPRShift

variable (pk : VoleMole.Verifier.UovPk) (sk : VoleMole.Spec.Signer) (n ℓ : ℕ)

/-- `B`'s world in these examples: a random oracle `Unit → Bool` (its coins). -/
abbrev AB : Unit → Type := fun _ => Bool

/-- **A1** at PomFRIT's trapdoor, `τ = 17`. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :=
  advOMPR_le_shift (pomTrap (pure (pk, sk)) honestPre) (τ := 17) (by norm_num) n ℓ B

/-- **P8(a)** at PomFRIT's trapdoor, `τ = 17`. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray (List TG) TG SIss) (List (ByteArray × SIss)))) :=
  advOMPRShift_le_guess (pomTrap (pure (pk, sk)) honestPre) 17 n ℓ B

/-- A client whose session `k` has label `k`, blinding `0`, and whose finishing phase accepts. -/
def idClient : Client (fun _ : Empty => Unit) ℕ TG SIss Unit Unit VoleMole.Verifier.UovPk where
  coins := pure ()
  start _ _ k := pure (k, 0, ())
  post _ _ _ := pure true

theorem idClient_distinct (pk : VoleMole.Verifier.UovPk) (κ : Unit) :
    Distinct idClient pk κ := by
  intro i j hij a ha b hb
  simp only [idClient, support_pure, Set.mem_singleton_iff] at ha hb
  subst ha; subst hb
  exact hij

/-- **Theorem 6** at PomFRIT's trapdoor, with `idClient`: its hypothesis holds. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :=
  ompr_le_blind (pomTrap (pure (pk, sk)) honestPre) idClient n ℓ B
    fun pk κ _ => idClient_distinct pk κ

/-- `idClient` never fails completeness: its flag is always `true`. -/
theorem idClient_compFail (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :
    Pr{let r ← omuf (pomTrap (pure (pk, sk)) honestPre).keyGen
        (pomTrap (pure (pk, sk)) honestPre).D n addHint (blindAdv idClient n B)}[
      Wins ℓ (goodPre (pomTrap (pure (pk, sk)) honestPre).IsPre) r.1 r.2.1.1 r.2.2.2 ∧
        r.2.1.2 = false] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr h => ?_
  simp only [omuf, blindAdv, idClient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ⟨b, -, κ, -, rfl⟩, L, -, r', hr', rfl⟩ := hr
  have := support_simulateQ_run'_subset
    (realImpl addHint ((pomTrap (pure (pk, sk)) honestPre).D kp.2)) _ (fun _ => none, ch0 L) (by
      rw [StateT.run'_eq, support_map]; exact ⟨r', hr', rfl⟩)
  simp only [mem_support_bind_iff, simulateQ_pure, support_pure, Set.mem_singleton_iff] at this
  obtain ⟨z, -, f, hf, he⟩ := this
  rw [he] at h
  rw [hf] at h
  exact Bool.true_eq_false_eq_False h.2

end VoleMole.Audit.OMPRShift
