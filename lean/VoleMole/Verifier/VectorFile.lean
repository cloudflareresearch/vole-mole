/-!
# Vector files of `tests/voleith/dump_verifier_vectors.cpp`

The record format (`record GROUP NAME`, `KEY VALUE` lines, `end`), hex decoding, and a check helper,
for `lake exe verifier_vectors`.
-/

namespace VoleMole.Verifier.Vectors

def nibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Decode lowercase hex (`-` is empty). -/
def unhex (s : String) : Option ByteArray := Id.run do
  if s == "-" then return some ByteArray.empty
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match nibble? cs[2 * i]!, nibble? cs[2 * i + 1]! with
    | some h, some l => out := out.push (h * 16 + l).toUInt8
    | _, _ => return none
  return some out

structure Record where
  group : String
  name : String
  fields : List (String × String)

def Record.get (r : Record) (k : String) : String :=
  (r.fields.lookup k).getD ""

def Record.bytes (r : Record) (k : String) : ByteArray :=
  (unhex (r.get k)).getD ByteArray.empty

def parse (contents : String) : Array Record := Id.run do
  let mut out : Array Record := #[]
  let mut cur : Option Record := none
  for line in contents.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " ", cur with
    | ["record", g, n], none => cur := some ⟨g, n, []⟩
    | ["end"], some r => out := out.push { r with fields := r.fields.reverse }; cur := none
    | [k, v], some r => cur := some { r with fields := (k, v) :: r.fields }
    | _, _ => pure ()
  return out

/-- Run one check, print failures, return success. -/
def check (label : String) (ok : Bool) : IO Bool := do
  unless ok do IO.eprintln s!"FAIL {label}"
  return ok

end VoleMole.Verifier.Vectors
