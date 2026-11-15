import VoleMole.Audit.PomfritPerm
import VoleMole.Assumptions.PomfritClsPerm

/-!
# Non-vacuity of Theorem U1^cls with AES as random permutations

`ROM/OneMoreClsPerm.lean` (`pomfrit_U1_cls_simP`, `prEvent_clsFail_sim_leP`, `pomWin_le_wrapP`)
and `Assumptions/PomfritClsPerm.lean` (`pomfrit_U1_ompr_cls_simP`), instantiated with the honest
Issuer, a key with a 32-byte digest and the two forgers of `Audit/PomfritPerm.lean` within their
budgets (the empty forger, and `invQ1` with an `H₂¹` query, a forward and an inverse cipher query
and a target query). The hypotheses are the key digest's size and the forger's budget; the wrapped
normalized forger's budget is a theorem (`forgerBound_wrapE`, `ForgerBoundP.toIC`).
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV.Links VoleMole.Audit.PomfritLemmaP
  VoleMole.Audit.PomfritPerm
open scoped ENNReal

namespace VoleMole.Audit.PomfritClsPerm

variable (sk : VoleMole.Spec.Signer) (ℓ : ℕ) (lr : Bool)

/-- **U1^cls with simultaneous extraction, permutation model**, honest Issuer, the empty forger. -/
example := pomfrit_U1_cls_simP (pure (pk32, sk)) honestPre lr (fun _ => pure []) ℓ
  (pk32_digest sk) nilP_bound

/-- **U1^cls with simultaneous extraction, permutation model**, a forger with an inverse query. -/
example := pomfrit_U1_cls_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk) invQ1_bound

/-- **U1^cls against the standalone OMPR game, permutation model**. -/
example := pomfrit_U1_ompr_cls_simP (pure (pk32, sk)) honestPre lr invQ1 ℓ (pk32_digest sk)
  invQ1_bound

/-- **U1^cls's term, permutation model**, for any number of targets. -/
example (n : ℕ) := prEvent_clsFail_sim_leP (pure (pk32, sk)) honestPre lr invQ1 n ℓ
  (pk32_digest sk) invQ1_bound

/-- The wrapper does not change the win in the permutation model (any number of targets). -/
example (n : ℕ) := pomWin_le_wrapP (pure (pk32, sk)) honestPre n ℓ lr invQ1

/-- The wrapped normalized forger's budget, for every permutation table. -/
example (π : PTable) := forgerBound_wrapE lr π.fwd (invQ1_bound.toIC lr π)

end VoleMole.Audit.PomfritClsPerm
