import VoleMole.ZK.CrtMask

/-!
# The CRT mask certificate for faest-arch-opt's tables

`maskInvOk_tables`: the left inverse `maskInv` of the 128 assembly columns (`ZK/CrtMask.lean`) is
checked against `CrtGen.tables` in the kernel (`decide +kernel`; separate module because the
computation needs more memory than the rest).
-/

namespace VoleMole.ZK

open VoleMole.Verifier

/-- The certificate holds for faest-arch-opt's tables (kernel computation). -/
theorem maskInvOk_tables : maskInvOk CrtGen.tables = true := by decide +kernel

/-- **A uniform `(u_low, u_hi)` gives a uniform CRT mask** for faest-arch-opt's tables. -/
theorem balanced_crtVal_tables :
    Balanced (fun x : (Fin BAVC.tau → UInt8) × UInt8 => crtVal CrtGen.tables x.1 x.2) :=
  balanced_crtVal maskInvOk_tables

end VoleMole.ZK
