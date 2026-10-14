import VoleMole.Arith.Basic
import VoleMole.Arith.GF

/-!
# Differential testing against the C++: the vector-file harness

`tests/arith/dump_arith_vectors.cpp` writes text vector files to `lean/vectors/` (its header comment
documents the format): for each relation or gadget, records with the public inputs, a witness as
bits and as a random GF(2¹²⁸)-valued assignment, and the C++ constraint values at both. This file
parses them and compares the C++ values with `System.values` of a Lean generator; `lake exe
arith_vectors` (`VoleMole/Arith/VectorsMain.lean`) runs it over every file.

## Plugging in a generator

A generator is registered as a `Generator`: a function from the record (and the UOV keys) to the
constraint system over `GF128`. The harness evaluates it at the bits of `wit` and at `field_wit` and
compares with `values_bits` and `values_field` (and the count with `num_constraints`). To add one,
append an entry `(relationName, myGenerator)` to `registry` in `VectorsMain.lean`, where the name is
the `RELATION` of the records (`uov`, `keccak`, `pomfrit_redeem`, `moussaka_issue`,
`moussaka_redeem`, `ratatouille_issue`, `ratatouille_spend`). Use the `Record` accessors
(`r.bytes`, `r.byte`, `r.nat`, `r.gfList`, `r.coeffs`, `r.ints`, `env.pk`, `env.pks`) to read the
public inputs, and instantiate the abstract generator with `F := GF128`, `β := beta`, and for GF(256)
`K := GF256`, `toBits := GF256.toBits`. Records of relations without a generator are reported as
skipped. Then `lake build arith_vectors && lake exe arith_vectors`.
-/

namespace VoleMole.Arith.Vectors

/-! ## Records -/

/-- A record `record RELATION NAME … end` of a vector file. -/
structure Record where
  file : String
  relation : String
  name : String
  fields : Std.HashMap String String

/-- Data shared by all records: the UOV keys of `uov_keys.txt`. -/
structure Env where
  keys : Std.HashMap String ByteArray

namespace Record

def label (r : Record) : String := s!"{r.file}: {r.relation} {r.name}"

def get (r : Record) (k : String) : Except String String :=
  match r.fields[k]? with
  | some v => .ok v
  | none => .error s!"missing key `{k}`"

/-- A hex byte string. -/
def bytes (r : Record) (k : String) : Except String ByteArray := do
  match Hex.decodeByteArray? (← r.get k) with
  | some b => pure b
  | none => throw s!"key `{k}`: bad hex"

/-- Byte `i` of a hex byte string, as a function (zero beyond the end). -/
def byte (r : Record) (k : String) : Except String (ℕ → UInt8) := do
  let b ← r.bytes k
  pure fun i => if h : i < b.size then b[i] else 0

/-- A decimal number. -/
def nat (r : Record) (k : String) : Except String ℕ := do
  match (← r.get k).toNat? with
  | some n => pure n
  | none => throw s!"key `{k}`: not a number"

/-- A comma-separated list of integers. -/
def ints (r : Record) (k : String) : Except String (Array Int) := do
  let parts := ((← r.get k).splitOn ",").toArray
  parts.mapM fun s => match s.toInt? with
    | some n => pure n
    | none => throw s!"key `{k}`: bad integer `{s}`"

/-- A list of GF(2¹²⁸) elements. -/
def gfList (r : Record) (k : String) : Except String (Array GF128) := do
  match GF128.listOfHex? (← r.get k) with
  | some a => pure a
  | none => throw s!"key `{k}`: bad list of field elements"

/-- A list of exactly `M` field elements, e.g. the combination coefficients `l`. -/
def coeffs (r : Record) (k : String) (M : ℕ) : Except String (Fin M → GF128) := do
  let a ← r.gfList k
  if a.size ≠ M then throw s!"key `{k}`: expected {M} elements, got {a.size}"
  pure fun i => a.getD i.val 0

end Record

namespace Env

/-- The expanded UOV public key with the given name, as `ℕ → GF256` (zero beyond the end). -/
def pk (env : Env) (name : String) : Except String (ℕ → GF256) :=
  match env.keys[name]? with
  | some b => .ok fun i => if h : i < b.size then ⟨b[i]⟩ else 0
  | none => .error s!"unknown UOV key `{name}`"

/-- A comma-separated list of key names (e.g. an Anchor Set). -/
def pks (env : Env) (names : String) : Except String (List (ℕ → GF256)) :=
  (names.splitOn ",").mapM env.pk

end Env

/-! ## Parsing -/

/-- Parse a vector file into its records and its `key NAME HEX` lines. -/
def parse (file contents : String) :
    Except String (Array Record × Array (String × String)) := do
  let mut records : Array Record := #[]
  let mut keys : Array (String × String) := #[]
  let mut cur : Option Record := none
  let mut lineNo := 0
  for line in contents.splitOn "\n" do
    lineNo := lineNo + 1
    if line.isEmpty || line.startsWith "#" then continue
    let parts := line.splitOn " "
    match cur, parts with
    | none, ["record", rel, name] => cur := some ⟨file, rel, name, {}⟩
    | none, ["key", name, hex] => keys := keys.push (name, hex)
    | some r, ["end"] => records := records.push r; cur := none
    | some r, [k, v] => cur := some { r with fields := r.fields.insert k v }
    | _, _ => throw s!"{file}:{lineNo}: unexpected line"
  if cur.isSome then throw s!"{file}: unterminated record"
  return (records, keys)

/-! ## Checks -/

/-- A generator, instantiated over `GF128`: the constraint system of a record. -/
abbrev Generator := Env → Record → Except String (System GF128)

/-- The committed values of a field assignment (zero beyond the end). -/
def ofArray (a : Array GF128) : ℕ → GF128 := fun i => a.getD i 0

/-- The committed values of witness bytes: bit `i` is bit `i % 8` of byte `i / 8`. -/
def ofWitBytes (b : ByteArray) : ℕ → GF128 :=
  ofBits fun i => if h : i / 8 < b.size then (b[i / 8] >>> (i % 8).toUInt8) &&& 1 = 1 else false

/-- Compare computed and expected values: `none` if equal, else a description. -/
def compareValues (what : String) (got : List GF128) (want : Array GF128) : Option String :=
  if got.length ≠ want.size then
    some s!"{what}: {got.length} constraints, C++ has {want.size}"
  else
    let bad := (got.zipIdx.filter fun (v, i) => v ≠ want.getD i 0).map (·.2)
    match bad with
    | [] => none
    | i :: _ =>
      some s!"{what}: {bad.length} of {want.size} values differ, first at constraint {i} \
        (Lean {got.getD i 0}, C++ {want.getD i 0})"

/-- The outcome of checking one record. -/
inductive Outcome where
  | pass (detail : String)
  | fail (detail : String)
  | skip (detail : String)

/-- Check a record against a generator: the constraint count, the values at the bits of `wit`,
and the values at `field_wit`. -/
def checkWith (gen : Generator) (env : Env) (r : Record) : Except String (Option String) := do
  let cs ← gen env r
  let n ← r.nat "num_constraints"
  if cs.length ≠ n then
    return some s!"{cs.length} constraints, C++ has {n}"
  let wit ← r.bytes "wit"
  let fw ← r.gfList "field_wit"
  if let some e := compareValues "bits" (cs.values (ofWitBytes wit)) (← r.gfList "values_bits") then
    return some e
  return compareValues "field" (cs.values (ofArray fw)) (← r.gfList "values_field")

/-- The number of leading bit constraints `x_i (x_i + 1)`, `i < B`, of each relation (all witness
bits, except for Moussaka redeem, whose selector bits come later). -/
def bitPrefix (r : Record) : Except String (Option ℕ) := do
  match r.relation with
  | "pomfrit_redeem" | "moussaka_issue" | "ratatouille_issue" | "ratatouille_spend" =>
    pure (some (8 * (← r.bytes "wit").size))
  | "moussaka_redeem" => pure (some (8 * 335)) -- 8 * REDEEM_WIT_OFF_B
  | _ => pure none

/-- Framework self-test, independent of any relation generator: the leading bit constraints of a
relation record match `bitConstraint (wit i)` at both assignments. -/
def checkBitPrefix (r : Record) : Except String (Option String) := do
  let some b ← bitPrefix r | return none
  let cs : System GF128 := (List.range b).map fun i => bitConstraint (Expr.wit i)
  let take (a : Array GF128) := a.extract 0 b
  if let some e := compareValues "bit prefix, bits" (cs.values (ofWitBytes (← r.bytes "wit")))
      (take (← r.gfList "values_bits")) then
    return some e
  return compareValues "bit prefix, field" (cs.values (ofArray (← r.gfList "field_wit")))
    (take (← r.gfList "values_field"))

/-! ## Field arithmetic -/

/-- The checks of `field.txt`: `β`, `ι` on all bytes, pqov's GF(256) table, and GF(2¹²⁸) products. -/
def checkField (r : Record) : Except String (List String) := do
  let mut errs : List String := []
  let betaC ← r.gfList "beta"
  for b in List.finRange 8 do
    if beta b ≠ betaC.getD b.val 0 then errs := errs ++ [s!"beta {b} differs"]
  let embedC ← r.gfList "embed"
  if embedC.size ≠ 256 then errs := errs ++ ["embed: expected 256 elements"]
  for a in GF256.all do
    if iota a ≠ embedC.getD a.val.toNat 0 then errs := errs ++ [s!"iota {a.val} differs"]
  let tab ← r.bytes "gf256_mul"
  if tab.size ≠ 65536 then errs := errs ++ ["gf256_mul: expected 65536 bytes"]
  let mut bad256 := 0
  for a in GF256.all do
    for b in GF256.all do
      if (a * b).val ≠ tab.get! (256 * a.val.toNat + b.val.toNat) then bad256 := bad256 + 1
  if bad256 ≠ 0 then errs := errs ++ [s!"gf256_mul: {bad256} products differ"]
  let ma ← r.gfList "mul_a"
  let mb ← r.gfList "mul_b"
  let mab ← r.gfList "mul_ab"
  if ma.size ≠ mb.size ∨ ma.size ≠ mab.size then errs := errs ++ ["mul_*: lengths differ"]
  let mut bad128 := 0
  for i in [0:ma.size] do
    if ma[i]! * mb[i]! ≠ mab[i]! then bad128 := bad128 + 1
  if bad128 ≠ 0 then errs := errs ++ [s!"GF(2^128): {bad128} of {ma.size} products differ"]
  -- The hex encoding round-trips.
  for x in mab do
    if GF128.ofHex? x.toHex ≠ some x then errs := errs ++ [s!"hex round trip fails for {x}"]
  return errs

/-- `ι` is an injective ring homomorphism, checked exhaustively: `ι 0 = 0`, `ι 1 = 1`, all 65536
sums and products, and 256 distinct images. Returns the failures. -/
def checkIotaHom : List String := Id.run do
  let mut errs : List String := []
  if iota 0 ≠ 0 then errs := errs ++ ["iota 0 ≠ 0"]
  if iota 1 ≠ 1 then errs := errs ++ ["iota 1 ≠ 1"]
  let table := (GF256.all.map iota).toArray
  let mut badAdd := 0
  let mut badMul := 0
  for a in GF256.all do
    for b in GF256.all do
      let ia := table[a.val.toNat]!
      let ib := table[b.val.toNat]!
      if iota (a + b) ≠ ia + ib then badAdd := badAdd + 1
      if iota (a * b) ≠ ia * ib then badMul := badMul + 1
  if badAdd ≠ 0 then errs := errs ++ [s!"iota: {badAdd} sums not preserved"]
  if badMul ≠ 0 then errs := errs ++ [s!"iota: {badMul} products not preserved"]
  let mut seen : Std.HashSet GF128 := {}
  for x in table do seen := seen.insert x
  if seen.size ≠ 256 then errs := errs ++ [s!"iota: only {seen.size} distinct images"]
  return errs

end VoleMole.Arith.Vectors
