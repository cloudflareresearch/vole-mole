import VoleMole.Assumptions.BlindPomfrit
import VoleMole.Assumptions.BlindPomfritT6Lean

/-!
# Non-vacuity of Theorem 6 at PomFRIT

`Assumptions/BlindPomfrit.lean` instantiated at PomFRIT's trapdoor with the honest Issuer
(`Links.pomTrap`, `honestPre`, any fixed key). `pomfrit_T6` has no hypothesis (the labels'
distinctness is a theorem, `distinct_toClient`). `pomfrit_T6_bound`'s only hypothesis, `B`'s
target budget, holds for an adversary that makes one target request (`oneReq_bound`). For a
forger without coins `gameB` is `Pomfrit.game` (`gameB_liftF`), so the game is not a new one.

**The Lean client** (G9, `Assumptions/PomClientLean.lean`, `Assumptions/BlindPomfritT6Lean.lean`):
`compFail ≤ (ℓ + 1)·2⁻¹¹³` (`compFail_le`) and Theorem 6 without a completeness term
(`pomfrit_T6_lean`, `pomfrit_T6_lean_bound`), instantiated below with the honest Issuer and the
adversaries above; their extra assumption, a finite nonempty answer type for `B`'s oracle, holds for
`AB` (`Bool`). The client's two steps agree per table with the executable prover
(`eval_start`, `eval_finish`), so the client is the Lean prover, not a stand-in.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV VoleMole.Assumptions.UOV.Links
  VoleMole.Assumptions.Blind VoleMole.Assumptions.BlindPomfrit
open scoped ENNReal

namespace VoleMole.Audit.T6Pomfrit

variable (pk : VoleMole.Verifier.UovPk) (sk : VoleMole.Spec.Signer) (n ℓ : ℕ)
  (T : VoleMole.Verifier.CrtTables) (lr : Bool) {Cn St : Type} (cl : PomClient Cn St)

/-- `B`'s world in these examples: a random oracle `Unit → Bool` (its coins). -/
abbrev AB : Unit → Type := fun _ => Bool

/-- **Theorem 6 at PomFRIT**, honest Issuer, a fixed key, any client: no hypothesis. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :=
  pomfrit_T6 T lr ℓ cl n (pure (pk, sk)) honestPre tgts1 B

/-- An OMPR adversary with one target request and no claim. -/
def oneReq : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss))) :=
  fun _ => pure do
    let _ ← (liftM ((specB AB ByteArray Unit TG SIss).query (.inr (.inl (ByteArray.empty, ())))) :
      OracleComp (specB AB ByteArray Unit TG SIss) (Option TG))
    pure []

theorem oneReq_bound : ∀ pk, ∀ b ∈ support (oneReq pk),
    IsQueryBoundP b (fun q => isTgt q = true) 1 := by
  intro pk b hb
  simp only [oneReq, support_pure, Set.mem_singleton_iff] at hb
  subst hb
  erw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-- **Theorem 6 at PomFRIT with `B`'s budget**: its hypothesis holds for `oneReq`. -/
example := pomfrit_T6_bound T lr ℓ 1 cl (pure (pk, sk)) honestPre tgts1 oneReq oneReq_bound

/-- **`gameB` is `Pomfrit.game`** for a forger without coins (here U1's game shape). -/
example (A : Forger) (e1 : CTable → QueryLog specIC → ByteArray → TG) :=
  gameB_liftF (AR := AB) T lr tgts1 ℓ (pure (pk, sk)) honestPre n A addHint e1

/-- **The completeness term for the Lean client**, honest Issuer, fixed key. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :
    compFail VoleMole.Verifier.CrtGen.tables lr ℓ (leanClient VoleMole.Verifier.CrtGen.tables lr) n
      (pure (pk, sk)) honestPre B ≤ (ℓ + 1 : ℝ≥0∞) * (2 ^ 113 : ℝ≥0∞)⁻¹ :=
  compFail_le lr ℓ n (pure (pk, sk)) honestPre B

/-- **Theorem 6 at PomFRIT for the Lean client**: no hypothesis. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :=
  pomfrit_T6_lean lr ℓ n (pure (pk, sk)) honestPre B tgts1

/-- **With `B`'s budget**: the hypothesis holds for `oneReq`. -/
example := pomfrit_T6_lean_bound lr ℓ (pure (pk, sk)) honestPre oneReq 1 tgts1 oneReq_bound

/-- **The Lean client's step 1 is the executable prover's** at every table. -/
example (g : Table) (E : CTable) (κ : VoleMole.Prob.Bytes 32) (k : ℕ) :=
  eval_start g E VoleMole.Verifier.CrtGen.tables lr pk κ k

end VoleMole.Audit.T6Pomfrit
