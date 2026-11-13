import VoleMole.Spec.Common

/-!
# The definitions of pqov's signer model, without the field structure

The computable definitions of `Spec/PqovSigner.lean`'s model of pqov's `ov_preimage_core` (the
public map `qmap`, its polar form `polar`, the vectors `vinVec`, `oilVec`, the system `sysMat`, the
target, the byte conversion and pqov's vinegar derivation `vinShake`), kept apart from
`Arith/GF256Field.lean` so that executables can use them: importing `Arith/GFField.lean` into an
executable runs the initializer of its computable `Fintype GF128` instance, which enumerates
`2¹²⁸` elements (an out-of-memory kill at start-up). The model, its theorems and the
noncomputable steps (`OilSpace`, `oilSol`, `attempt`, `signer`) are in `Spec/PqovSigner.lean`; the
executable twin of the signer is `Spec/PqovSignerExec.lean`.
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-- A vinegar vector (`_V = 74` bytes). -/
abbrev Vin := Fin 74 → GF256

/-- An oil matrix `O` (`sk->O`): column `j < 45` is `O_j ∈ GF(256)⁷⁴`. -/
abbrev OilMat := Fin 45 → Fin 74 → GF256

/-- `P(σ)` (`UOVKey.eval` before the byte conversion). -/
def qmap (pk : UOVKey) (σ : ℕ → GF256) : Fin 45 → GF256 := publicMap 119 45 pk.map σ

/-- The polar form `B(a, b) = P(a + b) − P(a) − P(b)`, monomial by monomial. -/
def polar (pk : UOVKey) (a b : ℕ → GF256) (k : Fin 45) : GF256 :=
  ((forEachMonomial 119 45).map fun m => pk.map (m.off + k) * (a m.i * b m.j + b m.i * a m.j)).sum

/-- `x₀ = (v, 0)`. -/
def vinVec (v : Vin) : ℕ → GF256 := fun i => if h : i < 74 then v ⟨i, h⟩ else 0

/-- The oil vector `ō_j = (O_j, e_j)`. -/
def oilVec (O : OilMat) (j : Fin 45) : ℕ → GF256 := fun i =>
  if h : i < 74 then O j ⟨i, h⟩ else if i = 74 + j.val then 1 else 0

/-- **The system matrix** of the attempt with vinegar `v`: `L_v[k][j] = B(x₀, ō_j)_k` (pqov's
`vᵀ S_k`). -/
def sysMat (pk : UOVKey) (O : OilMat) (v : Vin) : Matrix (Fin 45) (Fin 45) GF256 :=
  Matrix.of fun k j => polar pk (vinVec v) (oilVec O j) k

/-- The target as a vector. -/
def target (t : Bytes) : Fin 45 → GF256 := fun k => ⟨t.getD k 0⟩

/-- The first `119` coordinates as bytes. -/
def toBytes (σ : ℕ → GF256) : Bytes := List.ofFn fun i : Fin 119 => (σ i).val

/-- `PREIMAGE_DST` (`ov.c`, patch 0001). -/
def preimageDst : Bytes := "pqov-derive-preimage".toList.map fun c => c.toNat.toUInt8

/-- pqov's vinegar of attempt `ctr` at target `t`: `SHAKE256(t ‖ sk_seed ‖ DST ‖ ctr)`, 74 bytes. -/
def vinShake (skSeed : Bytes) (t : Bytes) (ctr : Fin 256) : Vin := fun i =>
  ⟨(shake256B (t ++ skSeed ++ preimageDst ++ [ctr.val.toUInt8]) 74).getD i.val 0⟩

end VoleMole.Spec.Pqov
