import VoleMole.Spec.PqovSignerDefs

/-!
# An executable twin of the signer model, for known-answer checks

`Spec.Pqov.signer` (`Spec/PqovSigner.lean`) is noncomputable only through the matrix inverse of
`oilSol`. `signerExec` runs the same model with that one step replaced by a Gauss–Jordan
elimination (`solveExec`), and keeps every other definition of the model: the vinegars
(`vinShake`, pqov's `SHAKE256(t ‖ sk_seed ‖ DST ‖ ctr)`), the system `sysMat` (the public map's
polar form, not pqov's stored `S`), the constant `t − P(x₀)` (`qmap`), the vectors `vinVec`,
`oilVec`, and `toBytes`. The oil matrix of a compact secret key is `oilOfSeed` (bytes
`16 + 74 j + l` of `SHAKE256(sk_seed)`, `Verifier.Keygen.compressedPk`).

This file imports only `Spec/PqovSignerDefs.lean` (not the field structure of
`Arith/GF256Field.lean`, whose import would make an executable enumerate `GF128` at start-up).
An attempt's solution `x` is accepted only after the check `L_v x = t − P(x₀)` on the model's own
`sysMat` (`checkSol`). Then (`attemptExec_sound`, `Spec/PqovKey.lean`) the attempt's output **is the
model's**
`attempt pk O t v` whenever `det L_v ≠ 0` (which a successful elimination witnesses, but which is
not proved of `solveExec`). An attempt that `solveExec` rejects is taken as singular, as the model
does for `det L_v = 0`; that `solveExec` rejects exactly the singular systems is not proved.

`lake exe spec_kats` (`Spec/Kats.lean`) runs `deriveRefExec` (pqov's 255 attempts) on the KAT
targets of the test key (`filled(0x60)`, the key generated in Lean from its seed) and compares the
output with the C++ `derive_preimage` responses byte for byte: the model of pqov's signer computed
from the public map's polar form reproduces pqov's signer on a real key.
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-- The oil matrix from the bytes `a = SHAKE256(sk_seed)`. (A separate definition: the compiler
eta-expands definitions of function type, so the hash is computed once only if the array is
passed in.) -/
def oilOfArray (a : Array UInt8) : OilMat := fun j l => ⟨a.getD (16 + 74 * j.val + l.val) 0⟩

/-- The oil matrix of a compact secret key: `O j l` is byte `16 + 74 j + l` of
`SHAKE256(sk_seed)` (after `pk_seed`; `Verifier.Keygen.compressedPk`). -/
def oilOfSeed (skSeed : Bytes) : OilMat :=
  oilOfArray (shake256B skSeed (16 + 74 * 45)).toArray

/-- The inverse in GF(256), by search (`0` for `0`). -/
def gfInv (a : GF256) : GF256 := (GF256.all.find? fun b => decide (a * b = 1)).getD 0

/-- `Σ_{j < 45} f j` as a fold (computable). -/
def sum45 (f : Fin 45 → GF256) : GF256 := (List.finRange 45).foldr (fun j acc => f j + acc) 0

/-- Gauss–Jordan elimination: a solution of `A x = b`, or `none` if a pivot is missing. -/
def solveExec (A : Fin 45 → Fin 45 → GF256) (b : Fin 45 → GF256) : Option (Fin 45 → GF256) :=
  Id.run do
    let mut rows : Array (Array GF256) := (List.finRange 45).toArray.map fun r =>
      (Array.ofFn fun j : Fin 45 => A r j).push (b r)
    for col in [0:45] do
      let some piv := (List.range' col (45 - col)).find? (fun r => decide ((rows[r]!)[col]! ≠ 0))
        | return none
      let tmp := rows[col]!
      rows := (rows.set! col rows[piv]!).set! piv tmp
      let inv := gfInv ((rows[col]!)[col]!)
      rows := rows.set! col (rows[col]!.map (inv * ·))
      for r in [0:45] do
        let f := (rows[r]!)[col]!
        if r != col && decide (f ≠ 0) then
          let p := rows[col]!
          let q := rows[r]!
          rows := rows.set! r ((Array.range 46).map fun c => q[c]! + f * p[c]!)
    return some fun k => (rows[k.val]!)[45]!

/-- `L_v x = t − P(x₀)` (`= t + P(x₀)`: characteristic 2), checked on the model's `sysMat`. -/
def checkSol (pk : UOVKey) (O : OilMat) (t : Bytes) (v : Vin) (x : Fin 45 → GF256) : Bool :=
  (List.finRange 45).all fun k =>
    decide (sum45 (fun j => sysMat pk O v k j * x j) = target t k + qmap pk (vinVec v) k)

/-- The model's preimage `w = x₀ + Σ_j x_j ō_j` from a solution `x`, as bytes. -/
def preimageExec (O : OilMat) (v : Vin) (x : Fin 45 → GF256) : Bytes :=
  List.ofFn fun i : Fin 119 => (vinVec v i + sum45 fun j => x j * oilVec O j i).val

/-- **One attempt, executable**: the elimination on `sysMat` (materialized once), then the check. -/
def attemptExec (pk : UOVKey) (O : OilMat) (t : Bytes) (v : Vin) : Option Bytes :=
  let arr := Array.ofFn fun k : Fin 45 => Array.ofFn fun j : Fin 45 => sysMat pk O v k j
  let rhs : Fin 45 → GF256 := fun k => target t k + qmap pk (vinVec v) k
  match solveExec (fun k j => (arr[k.val]!)[j.val]!) rhs with
  | none => none
  | some x => if checkSol pk O t v x then some (preimageExec O v x) else none

/-- `signer` with `attemptExec` (each vinegar evaluated once: `vinShake` hashes at every
coordinate access); also returns the attempt that succeeded. -/
def signerExec (pk : UOVKey) (O : OilMat) (vin : Bytes → Fin 256 → Vin) (tries : ℕ) (t : Bytes) :
    Option (Fin 256 × Bytes) :=
  ((List.finRange 256).filter fun i => decide (i.val < tries)).findSome? fun i =>
    let va := Array.ofFn (vin t i)
    (attemptExec pk O t fun l => va[l.val]!).map (i, ·)

/-- `deriveRef` with `attemptExec`: pqov's vinegars, 255 attempts. -/
def deriveRefExec (pk : UOVKey) (O : OilMat) (skSeed : Bytes) (t : Bytes) :
    Option (Fin 256 × Bytes) :=
  signerExec pk O (vinShake skSeed) 255 t

end VoleMole.Spec.Pqov
