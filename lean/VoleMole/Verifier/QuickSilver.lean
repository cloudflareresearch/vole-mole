import VoleMole.Verifier.KOS

/-!
# The QuickSilver verifier and `chal3` (executable)

`quicksilver_state<S, true, d>` (`fao/quicksilver.hpp:307-378, 420-432, 521-534, 642-659` and the
verifier arithmetic `:662-905`; `fao/` is `subprojects/faest-arch-opt/`), run by
`voleith_verify_commit` (`src/voleith.hpp:452-480`).

## Constraint values without the degree bookkeeping

The verifier holds a key `q_j = v_j + w_j Δ` per witness bit (`Δ` the CRT-lifted `Δ`, `q_j` after
the correction `d`). The C++ evaluates each constraint on keys, tracking a formal degree `e` per
value: a witness bit has degree 1; a constant `c` at degree `e` is `c·Δ^e`; products add degrees;
sums are taken at equal degree after raising the lower one by a power of `Δ`; `add_constraint`
raises to `d`. By induction on the expression, a value of formal degree `e` that represents the
polynomial `g` of the witness bits equals `Δ^e · g(q/Δ)`. Hence the verifier's value of constraint
`f_k` is `Δ^d · f_k(q_0/Δ, q_1/Δ, …)` whatever degrees the C++ tracks, so it can be computed by
evaluating the `Arith/*` constraint generators (any evaluator of the constraint polynomials over
`GF128`) at `x_j = q_j·Δ⁻¹` and multiplying by `Δ^d`. (`Δ ≠ 0` for every proof that passes the
final check, up to a `2⁻¹²⁸` chance; `verify` rejects `Δ = 0`.)

## ZKHash and the check value

`chal2 = (a₀, a₁, s, t)` (16 + 16 + 16 + 8 bytes; `init_hashers`). With `c_k` the constraint values
in `add_constraint` order, `A = Σ c_k s^{n−1−k}`, `B = Σ c_k t^{n−1−k}` and the mask
`q_mask[0] + Σ_{i=1}^{d−2} (ã_{i−1} + q_mask[i]) Δ^i + ã_{d−2} Δ^{d−1}` (`verify(q_mask, …)`), the
check value is `mask + a₀ A + a₁ B` (`finalize_hashes`). Then
`chal3 = H(chal2 ‖ check ‖ ã ‖ ctr ‖ 11)` (16 bytes), and the proof is accepted iff `chal3 = Δ`
(the raw, unlifted `Δ` from the proof).
-/

namespace VoleMole.Verifier

open VoleMole.Arith

/-- `a^n` by square-and-multiply. -/
def gfPow (a : GF128) (n : Nat) : GF128 :=
  if n = 0 then 1
  else
    let r := gfPow a (n / 2)
    if n % 2 = 1 then r * r * a else r * r
termination_by n
decreasing_by omega

/-- `a⁻¹ = a^(2¹²⁸ − 2)` (and `0 ↦ 0`). -/
def gfInv (a : GF128) : GF128 := gfPow a (2 ^ 128 - 2)

/-- The corrected witness keys `q_j = q_j + d_j Δ`, `j < ℓ` (dedicated label rows get no `d`). -/
def correctedKeys (pf : Proof) (rows : Array W128) (deltaL : GF128) : Array GF128 :=
  (Array.range pf.params.witnessBits).map fun j =>
    let q := rows[j]!.toGF
    if (pf.correction.get! (j / 8) >>> (j % 8).toUInt8) &&& 1 == 1 then q + deltaL else q

/-- The verifier's constraint values: `Δ^d · f_k(q/Δ)`, given an evaluator of the constraints. -/
def constraintKeys (p : Params) (keys : Array GF128) (deltaL : GF128)
    (values : (Nat → GF128) → List GF128) : List GF128 :=
  let inv := gfInv deltaL
  let xs := keys.map (· * inv)
  let dd := gfPow deltaL p.qsDegree
  (values fun j => xs.getD j 0).map (dd * ·)

/-- The QuickSilver check value. -/
def qsCheck (pf : Proof) (chal2 : ByteArray) (cs : List GF128) (qMask : Array W128)
    (deltaL : GF128) : GF128 :=
  let d := pf.params.qsDegree
  let a0 := gfOfBytes chal2 0
  let a1 := gfOfBytes chal2 16
  let s := gfOfBytes chal2 32
  let t : GF128 := ⟨W128.word chal2 48, 0⟩
  let arr := cs.toArray
  let A := horner s arr
  let B := horner t arr
  let aT := fun i => gfOfBytes pf.qsProof (16 * i)
  let mask : GF128 := if d ≥ 2 then
      ((List.range (d - 2)).map fun j => (aT j + qMask[j + 1]!.toGF) * gfPow deltaL (j + 1)).foldl
        (· + ·) qMask[0]!.toGF + aT (d - 2) * gfPow deltaL (d - 1)
    else 0
  mask + a0 * A + a1 * B

/-- `chal3` (16 bytes). -/
def chal3 (pf : Proof) (chal2 : ByteArray) (check : GF128) : ByteArray :=
  H ((chal2 ++ gfToBytes check ++ pf.qsProof ++ pf.ctr).push 11) 16

end VoleMole.Verifier
