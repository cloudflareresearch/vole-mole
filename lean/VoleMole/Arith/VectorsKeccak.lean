import VoleMole.Arith.Vectors
import VoleMole.Arith.Keccak

/-!
# Differential test of the Keccak-p[800] gadget (`keccak.txt`)

The `keccak` records of `tests/arith/dump_arith_vectors.cpp` (`dump_keccak`): with
`input = qs_input(qs, public_state, input_map)`, the constraints are the 1600 segment constraints
of `qs_keccak(qs, input, wit_off_states, num_out_bits)`, then each output bit `out[i]`,
`i < num_out_bits`, then `qs_byte(out, k)`, `k < num_out_bits / 8`.

Evaluating the `Expr` trees of `qsKeccak` directly is exponential, so this is a values generator:
the segment constraints and the output bits are computed with sharing by `qsKeccakValues`, which
`Keccak.qsKeccak_values` proves equal to `System.values` of `qsKeccak` (and to the evaluation of
its outputs). The input bits and `qsByte` are evaluated as `Expr`s (with the outputs as constants).
-/

namespace VoleMole.Arith.Vectors

open VoleMole.Arith.Keccak

/-- The `input_map` of a record: `-1 ↦ none`, `b ≥ 0 ↦ some b`. -/
def keccakInputMap (r : Record) : Except String (Fin 100 → Option ℕ) := do
  let a ← r.ints "input_map"
  if a.size ≠ 100 then throw s!"input_map: expected 100 entries, got {a.size}"
  pure fun i => let v := a.getD i.val (-1); if v < 0 then none else some v.toNat

/-- The constraint values of a `keccak` record at the committed values `w`. -/
def keccakValues (map : Fin 100 → Option ℕ) (pub : State) (wOff n : ℕ) (hn : n ≤ 800)
    (w : ℕ → GF128) : List GF128 :=
  let input := (qsInput (F := GF128) pub map).map (Expr.eval w)
  let (cs, out) := qsKeccakValues w wOff n hn input
  let outE : Vector (Expr GF128) n := out.map Expr.const
  cs ++ out.toList ++ (List.finRange (n / 8)).map fun k =>
    (qsByte beta outE k.val (by have := k.isLt; omega)).eval w

/-- The standalone Keccak gadget (`keccak.txt`). -/
def keccakGenerator : ValuesGenerator := fun _ r => do
  let map ← keccakInputMap r
  let pubB ← r.bytes "public_state"
  if pubB.size ≠ 100 then throw s!"public_state: expected 100 bytes, got {pubB.size}"
  let pub : State := Vector.ofFn fun i => pubB.get! i.val
  let wOff ← r.nat "wit_off_states"
  let n ← r.nat "num_out_bits"
  if hn : n ≤ 800 then
    pure (keccakValues map pub wOff n hn)
  else
    throw s!"num_out_bits = {n} > 800"

end VoleMole.Arith.Vectors
