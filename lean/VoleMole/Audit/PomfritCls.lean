import VoleMole.Audit.PomfritLemmaP
import VoleMole.Assumptions.PomfritCls

/-!
# Non-vacuity of Theorem U1^cls

`ROM/OneMoreClsQueries.lean` (`pomfrit_U1_cls_sim'`, `pomfrit_U1_cls'`, `forgerBound_wrapE`),
`ROM/OneMoreClsSim.lean` (`pomfrit_U1_cls_sim`), `ROM/OneMoreClsGame.lean` (`pomfrit_U1_cls`,
`pomWin_le_wrapE`) and `Assumptions/PomfritCls.lean` (`pomfrit_U1_ompr_cls_sim`,
`pomfrit_U1_ompr_cls`), instantiated with the honest Issuer, a key with a 32-byte digest and the two
forgers of `Audit/PomfritLemmaP.lean` within their budgets. The hypotheses are the key digest's
size and the forger's budget; the wrapped forger's budget is a theorem (`forgerBound_wrapE`).
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV.Links VoleMole.Audit.PomfritLemmaP
open scoped ENNReal

namespace VoleMole.Audit.PomfritCls

variable (sk : VoleMole.Spec.Signer) (ℓ : ℕ) (lr : Bool)

/-- **U1^cls with simultaneous extraction**, honest Issuer, the empty forger. -/
example := pomfrit_U1_cls_sim' (pure (pk32, sk)) honestPre ℓ lr (fun _ => pure []) (pk32_digest sk)
  nil_bound

/-- **U1^cls with simultaneous extraction**, honest Issuer, a forger with one query of each kind. -/
example := pomfrit_U1_cls_sim' (pure (pk32, sk)) honestPre ℓ lr oneQ (pk32_digest sk) oneQ_bound

/-- **U1^cls, union over the forgeries**, honest Issuer, a forger with one query of each kind. -/
example := pomfrit_U1_cls' (pure (pk32, sk)) honestPre ℓ lr oneQ (pk32_digest sk) oneQ_bound

/-- **U1^cls against the standalone OMPR game**. -/
example := pomfrit_U1_ompr_cls_sim (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk) oneQ_bound

/-- **U1^cls union bound against the standalone OMPR game**. -/
example := pomfrit_U1_ompr_cls (pure (pk32, sk)) honestPre lr oneQ ℓ (pk32_digest sk) oneQ_bound

/-- The wrapped forger's budget, for every cipher table. -/
example (E : CTable) := forgerBound_wrapE lr E oneQ_bound

/-- The wrapper does not change the win (any number of targets). -/
example (n : ℕ) := pomWin_le_wrapE (pure (pk32, sk)) honestPre n ℓ lr oneQ

/-- The decoder's `H₅` inputs at an `H₂¹` query are at most `NdC`. -/
example (E : CTable) (L : QueryLog specIC) (x1 iv : ByteArray) :
    (decIns lr E L x1 iv).length ≤ NdC := decIns_length_le lr E L x1 iv

end VoleMole.Audit.PomfritCls
