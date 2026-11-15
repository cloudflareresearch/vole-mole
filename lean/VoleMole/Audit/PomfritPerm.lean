import VoleMole.Assumptions.PomfritPermSim
import VoleMole.Audit.PomfritLemmaP

/-!
# Non-vacuity of PomFRIT's Theorems U1 and U2 with AES as random permutations

`ROM/OneMoreLemmaPSimPerm.lean` (`pomfrit_U1_simP`, `prEvent_pfail_sim_leP`),
`ROM/OneMoreShiftSimPerm.lean` (`pomfrit_U2_simP`, `prEvent_shiftFail_sim_leP`) and
`Assumptions/PomfritPermSim.lean` (`pomfrit_U1_ompr_simP`, `pomfrit_U2_omprShift_simP`),
instantiated with the honest Issuer, a key with a 32-byte digest and two forgers of the
permutation model within their budgets: the forger that outputs nothing and `invQ1`, which makes an
`H₂¹` query (the reduction adds the `H₄` query of its `iv`), a forward and an **inverse** cipher
query and a `hash_to_target` query (budgets: one `H₂¹` query, one hash query, two cipher queries,
one target query). The hypotheses are the key digest's size and the forger's budget.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV.Links VoleMole.Audit.PomfritLemmaP
open VoleMole.ZK.Sim
open scoped ENNReal

namespace VoleMole.Audit.PomfritPerm

/-- The forger of the permutation model that outputs nothing is within the zero budget. -/
theorem nilP_bound : ForgerBoundP (fun _ => pure []) 0 0 0 0 :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- A forger that makes an `H₂¹` query, a forward and an inverse cipher query and a
`hash_to_target` query, and outputs nothing. -/
def invQ1 : ForgerP := fun _ => do
  let _ ← (liftM (specUP.query (.inl (.inl (.h21, ByteArray.empty)))) :
    OracleComp specUP (Ans (.h21, ByteArray.empty)))
  let _ ← (liftM (specUP.query (.inl (.inr (true, (0, 0))))) : OracleComp specUP Blk)
  let _ ← (liftM (specUP.query (.inl (.inr (false, (0, 0))))) : OracleComp specUP Blk)
  let _ ← (liftM (specUP.query (.inr (.inl ByteArray.empty))) : OracleComp specUP TG)
  pure []

theorem invQ1_bound : ForgerBoundP invQ1 (Function.update 0 .h21 1) 1 2 1 := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by decide, fun _ => ?_⟩
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => ?_⟩
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => ?_⟩
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => trivial⟩
  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by decide), fun _ => ?_⟩
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

variable (sk : VoleMole.Spec.Signer) (ℓ : ℕ) (lr : Bool)

/-- **U1 with simultaneous extraction, permutation model**, honest Issuer, the empty forger. -/
example := pomfrit_U1_simP (pure (pk32, sk)) honestPre lr (fun _ => pure []) ℓ (pk32_digest sk)
  nilP_bound

/-- **U1 with simultaneous extraction, permutation model**, a forger with an inverse query. -/
example := pomfrit_U1_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk) invQ1_bound

/-- **U1 against the standalone OMPR game, permutation model**. -/
example := pomfrit_U1_ompr_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk)
  invQ1_bound

/-- **Lemma P's term, permutation model**, for any number of targets. -/
example (n : ℕ) := prEvent_pfail_sim_leP (pure (pk32, sk)) honestPre lr invQ1 n ℓ
  (pk32_digest sk) invQ1_bound

/-- **U2 with simultaneous extraction, permutation model**, honest Issuer, the empty forger. -/
example := pomfrit_U2_simP (pure (pk32, sk)) honestPre lr (fun _ => pure []) ℓ (pk32_digest sk)
  nilP_bound

/-- **U2 with simultaneous extraction, permutation model**, a forger with an inverse query. -/
example := pomfrit_U2_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk) invQ1_bound

/-- **U2 against the standalone OMPR⊕17 game, permutation model**. -/
example := pomfrit_U2_omprShift_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk)
  invQ1_bound

/-- **U2's term, permutation model**, for any number of targets. -/
example (n : ℕ) := prEvent_shiftFail_sim_leP (pure (pk32, sk)) honestPre lr invQ1 n ℓ
  (pk32_digest sk) invQ1_bound

/-- The normalized forger's budget: one more `H₄` query (the reduction's `iv` query), the inverse
query counted as one forward query. -/
example (π : PTable) : ForgerBound (invQ1.toIC lr π)
    (addH4 (Function.update 0 .h21 1)) 2 2 1 := invQ1_bound.toIC lr π

end VoleMole.Audit.PomfritPerm
