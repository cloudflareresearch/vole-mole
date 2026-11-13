import VoleMole.Assumptions.PermSimLinks
import VoleMole.Audit.PermOMPR
import VoleMole.Audit.SimExtract

/-!
# Non-vacuity of Moussaka with AES and `Com` both random permutations
(`Assumptions/PermSimLinks.lean`)

`omuf_le_num_ompr_simP` (AES as random permutations with inverse queries, `Com` a random
permutation with inverse queries in the standalone CT-UF^open game) for the permutation-model
adversary `aUP` of `Audit/SimExtract.lean` (an inverse cipher query first), the toy trapdoor and
the toy permutation-model forger of `Audit/PermOMPR.lean`: every hypothesis, the modelling
hypothesis `hmodelP` for the forger `ctufForgerP` included, holds (`toy_hmodelP`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.PermSim

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Audit VoleMole.Assumptions.UOV
open VoleMole.Assumptions.UOV.Links VoleMole.Audit.PermOMPR VoleMole.Audit.SimExtract

/-- **Moussaka down to OMPR, AES and `Com` random permutations** (`omuf_le_num_ompr_simP`): every
hypothesis holds for `aUP` and the toy forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_ompr_simP lr pkU 1 aUP sk toyTrap (fun _ => ((), ())) aUP_budget pkU_digest pkU_inj
    embU_inj (toyFP 2) (toyFP_budget 2) (toy_hmodelP _ (prEvent_le_one _))

end VoleMole.Audit.PermSim
