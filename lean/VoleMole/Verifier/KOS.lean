import VoleMole.Verifier.VOLE
import VoleMole.Arith.GF

/-!
# The VOLE check (KOS / VOLEHash) and `chal2` (executable)

The verifier's side of the CRT VOLE check, `kos_vole_check_receiver` → `kos_vole_check_both`
(`fao/kos_vole_check.hpp:82-176, 204-217`; `fao/` is `subprojects/faest-arch-opt/`), and the
derivation of `chal2` (`src/voleith.hpp:435-450`).

* `chal1` (136 bytes) is parsed as `kos_vole_check_challenge::load`: four field elements `r_i`
  (`matrix`), four keys `s_i` (`keys`) and a 64-bit key `t` (`key_4`, a field element of degree
  `< 64`).
* The hashed rows are `x = (q_0, …, q_{ℓ−1}, q_mask[0], …, q_mask[d−2])` (`L = ℓ + d − 1` rows:
  the CRT-lifted witness rows before the correction `d`, then the masks not used by the check).
  `P_s(x) = Σ_k x_k s^{L−1−k}` (Horner; `uhasher_gfsecpar`, `uhasher_gfsecpar_64`,
  `fao/universal_hash.hpp:12-150`).
* `h_i = q_mask[d−1+i] + P_{s_{i+1}}(x) + r_i·P_{s_0}(x)` for `i < 3` and
  `h_3 = q_mask[d+2] + P_t(x) + r_3·P_{s_0}(x)` (`combine_hashes`), then the verifier adds
  `Δ'·ũ_i` with `Δ'` the CRT-lifted `Δ` and `ũ` the prover's VOLEHash from the proof. There is no
  equality test: `ũ ‖ h` goes into `chal2`, so a wrong `h` only changes the challenges.
* `chal2 = H(chal1 ‖ ũ ‖ h ‖ [mu] ‖ binder₂ ‖ d ‖ 10)` (56 bytes), with `mu` only for delayed
  instance binding.

This is `Seed/KOS.lean`'s model (`voleHashP`, `kosValue`) with `L = ℓ + d − 1`.
-/

namespace VoleMole.Verifier

open VoleMole.Arith

/-- A block as a field element (same bit order: bit `i` of byte `j` is the coefficient of
`X^(8j+i)`). -/
@[inline] def W128.toGF (a : W128) : GF128 := ⟨a.lo, a.hi⟩

@[inline] def gfOfBytes (b : ByteArray) (off : Nat := 0) : GF128 := (W128.ofBytes b off).toGF

def gfToBytes (a : GF128) : ByteArray := (W128.mk a.lo a.hi).toBytes

/-- `Σ_k x_k key^{n−1−k}` (Horner). -/
def horner (key : GF128) (xs : Array GF128) : GF128 := xs.foldl (fun s x => s * key + x) 0

/-- The verifier's VOLEHash `h` (4 field elements). -/
def voleHashReceiver (p : Params) (chal1 : ByteArray) (rows qMask : Array W128) (deltaL : GF128)
    (uTilde : ByteArray) : Array GF128 := Id.run do
  let r : Array GF128 := (Array.range 4).map fun i => gfOfBytes chal1 (16 * i)
  let s : Array GF128 := (Array.range 4).map fun i => gfOfBytes chal1 (64 + 16 * i)
  let t : GF128 := ⟨W128.word chal1 128, 0⟩
  let d := p.qsDegree
  let xs : Array GF128 := rows.map (·.toGF) ++ (qMask.extract 0 (d - 1)).map (·.toGF)
  let y0 := horner s[0]! xs
  let ys : Array GF128 := #[horner s[1]! xs, horner s[2]! xs, horner s[3]! xs, horner t xs]
  return (Array.range 4).map fun i =>
    qMask[d - 1 + i]!.toGF + ys[i]! + y0 * r[i]! + deltaL * gfOfBytes uTilde (16 * i)

/-- `chal2`; `muDelayed` is `mu` for delayed instance binding (else empty). -/
def chal2 (pf : Proof) (chal1 : ByteArray) (h : Array GF128) (muDelayed binder2 : ByteArray) :
    ByteArray :=
  let hb := h.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty
  H ((chal1 ++ pf.voleCheck ++ hb ++ muDelayed ++ binder2 ++ pf.correction).push 10) 56

end VoleMole.Verifier
