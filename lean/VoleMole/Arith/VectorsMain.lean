import VoleMole.Arith.Vectors
import VoleMole.Arith.GFEmbedding
import VoleMole.Arith.UOV
import VoleMole.Arith.PomFRIT
import VoleMole.Arith.VectorsKeccak
import VoleMole.Arith.VectorsMoussaka
import VoleMole.Arith.VectorsRatatouille

/-!
# `lake exe arith_vectors`

Runs the differential tests of `VoleMole/Arith/Vectors.lean` over the vector files written by
`tests/arith/dump_arith_vectors.cpp`:

1. the field arithmetic (`field.txt`) and the exhaustive check that `ι` is an injective ring
   homomorphism, plus the concrete `UOV.IsEmbedding` hypotheses for `β := beta`,
   `toBits := GF256.toBits`, `ofByte := GF256.ofBits` (also kernel-checked:
   `VoleMole.Arith.isEmbedding` in `GFEmbedding.lean`, imported here so that it is built);
2. for every relation record, the leading bit constraints (a framework self-test);
3. every record whose relation has a generator in `registry`.

Usage: `lake exe arith_vectors [VECTOR_DIR]` (default `vectors`, i.e. `lean/vectors` when run from
`lean/`). Exits with status 1 if any check fails. To add a generator, see the module docstring of
`VoleMole/Arith/Vectors.lean` and add an entry to `registry` below.
-/

namespace VoleMole.Arith.Vectors

/-- UOV parameters (`include/vole_mole/uov.hpp`). -/
def uovN : ℕ := 119
def uovM : ℕ := 45

/-- The standalone UOV gadget (`uov.txt`): the single constraint `l(P(s))`, with
`s_i = byteLoad β i`. -/
def uovGenerator : Generator := fun env r => do
  let pk ← env.pk (← r.get "pk")
  let l ← r.coeffs "l" uovM
  pure [UOV.evalCombinedPublicMap beta GF256.toBits uovN uovM pk (fun i => byteLoad beta i) l]

/-- PomFRIT redemption (`pomfrit_redeem.txt`). -/
def pomfritRedeemGenerator : Generator := fun env r => do
  let pk ← env.pk (← r.get "pk")
  let h ← r.byte "h"
  let l ← r.coeffs "l" uovM
  pure (PomFRIT.pomfritRedeemSystem beta GF256.toBits uovN uovM pk (fun k => ⟨h k.val⟩) l)

/-- Relation name (the `RELATION` of `record RELATION NAME`) ↦ Lean generator. -/
def registry : List (String × AnyGenerator) :=
  [("uov", uovGenerator),
   ("keccak", keccakGenerator),
   ("pomfrit_redeem", pomfritRedeemGenerator),
   ("moussaka_issue", moussakaIssueGenerator),
   ("moussaka_redeem", moussakaRedeemGenerator),
   ("ratatouille_issue", ratatouilleIssueGenerator),
   ("ratatouille_spend", ratatouilleSpendGenerator)]

/-- The hypotheses `UOV.IsEmbedding beta GF256.toBits GF256.ofBits`, checked exhaustively, and
agreement of `UOV.embed beta ∘ GF256.toBits` with `iota`. -/
def checkIsEmbedding : List String := Id.run do
  let ι := fun a : GF256 => UOV.embed beta (GF256.toBits a)
  let mut errs : List String := []
  -- toBits ∘ ofBits = id: every v : Fin 8 → Bool is the bits of some byte n.
  for n in List.range 256 do
    let v : Fin 8 → Bool := fun b => n.testBit b.val
    if (List.finRange 8).any fun b => GF256.toBits (GF256.ofBits v) b ≠ v b then
      errs := errs ++ [s!"toBits (ofBits v) ≠ v for v = bits of {n}"]
  if ι 0 ≠ 0 then errs := errs ++ ["embed (toBits 0) ≠ 0"]
  let table := (GF256.all.map ι).toArray
  for a in GF256.all do
    if table[a.val.toNat]! ≠ iota a then errs := errs ++ [s!"embed ∘ toBits ≠ iota at {a.val}"]
  let mut badAdd := 0
  let mut badMul := 0
  for a in GF256.all do
    for b in GF256.all do
      if ι (a + b) ≠ table[a.val.toNat]! + table[b.val.toNat]! then badAdd := badAdd + 1
      if ι (a * b) ≠ table[a.val.toNat]! * table[b.val.toNat]! then badMul := badMul + 1
  if badAdd ≠ 0 then errs := errs ++ [s!"map_add fails for {badAdd} pairs"]
  if badMul ≠ 0 then errs := errs ++ [s!"map_mul fails for {badMul} pairs"]
  let mut seen : Std.HashSet GF128 := {}
  for x in table do seen := seen.insert x
  if seen.size ≠ 256 then errs := errs ++ [s!"injective fails: {seen.size} distinct images"]
  return errs

def vectorFiles : List String :=
  ["field", "uov", "keccak", "pomfrit_redeem", "moussaka_issue", "moussaka_redeem",
   "ratatouille_issue", "ratatouille_spend"]

def report (ok : Bool) (what : String) (errs : List String) : IO Bool := do
  if errs.isEmpty then
    IO.println s!"PASS {what}"
    return ok
  else
    IO.println s!"FAIL {what}"
    for e in errs do IO.println s!"     {e}"
    return false

def run (dir : String) : IO UInt32 := do
  let mut ok := true
  let mut skipped : List String := []
  ok ← report ok "iota is an injective ring homomorphism (65536 sums and products)" checkIotaHom
  ok ← report ok "UOV.IsEmbedding beta GF256.toBits GF256.ofBits (exhaustive)" checkIsEmbedding
  -- UOV keys.
  let (_, keyLines) ← IO.ofExcept (parse "uov_keys.txt" (← IO.FS.readFile s!"{dir}/uov_keys.txt"))
  let mut keys : Std.HashMap String ByteArray := {}
  for (name, hex) in keyLines do
    match Hex.decodeByteArray? hex with
    | some b => keys := keys.insert name b
    | none => throw (IO.userError s!"uov_keys.txt: bad hex for key {name}")
  let env : Env := ⟨keys⟩
  for f in vectorFiles do
    let path := s!"{dir}/{f}.txt"
    let (records, _) ← IO.ofExcept (parse s!"{f}.txt" (← IO.FS.readFile path))
    for r in records do
      if r.relation = "field" then
        ok ← report ok s!"{r.label}: field arithmetic and embedding"
          (match checkField r with | .ok e => e | .error e => [e])
        continue
      if let .ok (some _) := bitPrefix r then
        ok ← report ok s!"{r.label}: bit-constraint prefix (self-test)"
          (match checkBitPrefix r with | .ok none => [] | .ok (some e) => [e] | .error e => [e])
      match registry.lookup r.relation with
      | none => skipped := skipped ++ [r.label]
      | some gen =>
        let t0 ← IO.monoMsNow
        let res ← IO.lazyPure fun _ => checkWith gen env r
        let t1 ← IO.monoMsNow
        let what := s!"{r.label}: Lean generator ({t1 - t0} ms)"
        ok ← report ok what (match res with
          | .ok none => []
          | .ok (some e) => [e]
          | .error e => [e])
  for s in skipped do IO.println s!"SKIP {s}: no Lean generator registered"
  IO.println (if ok then "All checks passed." else "Some checks FAILED.")
  return if ok then 0 else 1

end VoleMole.Arith.Vectors

def main (args : List String) : IO UInt32 :=
  VoleMole.Arith.Vectors.run (args.headD "vectors")
