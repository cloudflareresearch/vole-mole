import VoleMole.Assumptions.PomfritLemmaP
import VoleMole.Assumptions.PomfritLemmaPSim

/-!
# Non-vacuity of Theorem U1 with Lemma P's term explicit

`ROM/OneMoreLemmaPBound.lean` (`pomfrit_U1_explicit`, `prEvent_pfail_le`) and
`Assumptions/PomfritLemmaP.lean` (`pomfrit_U1_ompr_explicit`), and their simultaneous versions
(`ROM/OneMoreLemmaPSim.lean`: `pomfrit_U1_sim`, `prEvent_pfail_sim_le`;
`Assumptions/PomfritLemmaPSim.lean`: `pomfrit_U1_ompr_sim`) instantiated with the honest Issuer
(`honestPre`), a key with a 32-byte digest (the size of pqov's `SHAKE256(cpk)`), and two forgers
within their budgets: the forger that outputs nothing (all budgets `0`) and a forger that makes one
hash query, one cipher query and one `hash_to_target` query (`oneQ`, budgets `1`). The hypotheses
of the theorems are the key digest's size and the forger's budget; both hold here.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV.Links
open scoped ENNReal

namespace VoleMole.Audit.PomfritLemmaP

/-- A public key with a 32-byte digest. -/
def pk32 : VoleMole.Verifier.UovPk := ⟨⟨Array.replicate 32 0⟩, ByteArray.empty⟩

theorem pk32_digest (sk : VoleMole.Spec.Signer) :
    ∀ kp ∈ support (pure (pk32, sk) : ProbComp (VoleMole.Verifier.UovPk × VoleMole.Spec.Signer)),
      kp.1.digest.size = 32 := by
  intro kp hkp
  simp only [support_pure, Set.mem_singleton_iff] at hkp
  subst hkp
  simp [pk32, ByteArray.size]

/-- The forger that outputs nothing is within the zero budget. -/
theorem nil_bound : ForgerBound (fun _ => pure []) 0 0 0 0 :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- A forger that makes one `H₁` query, one cipher query and one `hash_to_target` query, and outputs
nothing. -/
def oneQ : Forger := fun _ => do
  let _ ← (liftM (specU.query (.inl (.inl (.h1, ByteArray.empty)))) :
    OracleComp specU (Ans (.h1, ByteArray.empty)))
  let _ ← (liftM (specU.query (.inl (.inr (0, 0)))) : OracleComp specU (AnsIC (.inr (0, 0))))
  let _ ← (liftM (specU.query (.inr (.inl ByteArray.empty))) : OracleComp specU TG)
  pure []

theorem oneQ_bound : ForgerBound oneQ (Function.update 0 .h1 1) 1 1 1 := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by decide, fun _ => ?_⟩
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => ?_⟩
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

variable (sk : VoleMole.Spec.Signer) (ℓ : ℕ) (lr : Bool)

/-- **U1 with Lemma P's term explicit**, honest Issuer, the empty forger. -/
example := pomfrit_U1_explicit (pure (pk32, sk)) honestPre lr (fun _ => pure []) ℓ (pk32_digest sk)
  nil_bound

/-- **U1 with Lemma P's term explicit**, honest Issuer, a forger with one query of each kind. -/
example := pomfrit_U1_explicit (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk) oneQ_bound

/-- **U1 against the standalone OMPR game, every term explicit**. -/
example := pomfrit_U1_ompr_explicit (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk)
  oneQ_bound

/-- **Lemma P's term**, for any number of targets. -/
example (n : ℕ) := prEvent_pfail_le (pure (pk32, sk)) honestPre lr oneQ n ℓ (pk32_digest sk)
  oneQ_bound

/-- **U1 with simultaneous extraction**, honest Issuer, the empty forger. -/
example := pomfrit_U1_sim (pure (pk32, sk)) honestPre lr (fun _ => pure []) ℓ (pk32_digest sk)
  nil_bound

/-- **U1 with simultaneous extraction**, honest Issuer, a forger with one query of each kind. -/
example := pomfrit_U1_sim (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk) oneQ_bound

/-- **U1 with simultaneous extraction against the standalone OMPR game**. -/
example := pomfrit_U1_ompr_sim (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk) oneQ_bound

/-- **Lemma P's term with simultaneous extraction**, for any number of targets. -/
example (n : ℕ) := prEvent_pfail_sim_le (pure (pk32, sk)) honestPre lr oneQ n ℓ (pk32_digest sk)
  oneQ_bound

end VoleMole.Audit.PomfritLemmaP
