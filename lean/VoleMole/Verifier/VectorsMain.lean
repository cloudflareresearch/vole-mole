import VoleMole.Verifier.BAVC

/-!
# `lake exe verifier_vectors`

Checks the executable pieces of the Lean VOLEitH verifier (`VoleMole/Verifier/`) against the files
written by `tests/voleith/dump_verifier_vectors.cpp` (format documented there):

* `verifier_prims.txt`: AES-128 (round keys and ciphertexts), `aes_ctr_prg<s128>` (including
  32-bit lane wrap-around of the counter and tweak), and SHAKE128/256 via `Spec.SHAKE` (inputs
  across rate boundaries, multi-block squeezes, a `hash_state_x4` lane).
* `verifier_bavc.txt`: `BAVC.commit` (whole tree, leaves, commitments, check value) and
  `BAVC.reconstruct` (verifier's leaves and commitments, check value) for a fixed seed and `Δ`,
  plus rejection of mutated openings.
* `verifier_kat.txt`: on the first Moussaka issuance KAT proof, `iv = H_4(iv_pre ‖ mu ‖ 4)` and the
  BAVC reconstruction from the proof's opening and `Δ` (leaves, commitments, and the VOLE
  commitment check value `vole_commit_check`).

Usage: `lake exe verifier_vectors [VECTOR_DIR]` (default `vectors`). Exits with status 1 on any
failure.
-/

namespace VoleMole.Verifier.Vectors

open VoleMole.Verifier

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

def checkPrims (rs : Array Record) : IO (Bool × Nat) := do
  let mut ok := true
  let mut n := 0
  for r in rs do
    n := n + 1
    match r.group with
    | "aes" =>
      let rk := AES.expandKey (r.bytes "key")
      ok := (← check s!"aes {r.name} rk" (rk == r.bytes "rk")) && ok
      ok := (← check s!"aes {r.name} ct" (AES.encrypt rk (r.bytes "pt") == r.bytes "ct")) && ok
    | "prg" =>
      let out := AES.prg (r.bytes "key") (r.bytes "iv") (r.get "tweak").toNat!.toUInt32
        (r.get "counter").toNat!.toUInt32 4
      ok := (← check s!"prg {r.name}" (out == r.bytes "out")) && ok
    | "shake" =>
      let expected := r.bytes "out"
      let input := r.bytes "input"
      let out := if r.get "secpar" == "128" then Spec.SHAKE.shake128 input expected.size
        else Spec.SHAKE.shake256 input expected.size
      ok := (← check s!"shake {r.name}" (expected.size > 0 && out == expected)) && ok
    | g => ok := (← check s!"unknown record {g} {r.name}" false) && ok
  return (ok, n)

def checkBavc (rs : Array Record) : IO Bool := do
  let some c := rs.find? (·.name == "commit") | check "bavc commit record" false
  let some o := rs.find? (·.name == "open") | check "bavc open record" false
  let iv := c.bytes "iv"
  let (tree, lv) := BAVC.commit (c.bytes "seed") iv
  let mut ok := true
  ok := (← check "bavc commit tree" (tree.foldl (· ++ ·) ByteArray.empty == c.bytes "tree")) && ok
  ok := (← check "bavc commit leaves" (lv.keys == c.bytes "leaves")) && ok
  ok := (← check "bavc commit hashed_leaves" (lv.coms == c.bytes "hashed_leaves")) && ok
  ok := (← check "bavc commit check" (BAVC.check lv.coms == c.bytes "check")) && ok
  let opening := o.bytes "opening"
  let delta := o.bytes "delta"
  match BAVC.reconstruct iv opening delta with
  | none => ok := (← check "bavc open accepted" false) && ok
  | some v =>
    ok := (← check "bavc open leaves" (v.keys == o.bytes "leaves")) && ok
    ok := (← check "bavc open hashed_leaves" (v.coms == o.bytes "hashed_leaves")) && ok
    ok := (← check "bavc open check" (BAVC.check v.coms == o.bytes "check")) && ok
  -- Mutations: a nonzero trailing byte is rejected; a flipped seed byte changes the check value.
  let last := opening.size - 1
  let bad := opening.set! last (opening.get! last ^^^ 1)
  if opening.get! last == 0 then
    ok := (← check "bavc mutated padding rejected" (BAVC.reconstruct iv bad delta).isNone) && ok
  let seedByte := BAVC.tau * BAVC.hashLen
  let bad2 := opening.set! seedByte (opening.get! seedByte ^^^ 1)
  ok := (← check "bavc mutated seed changes check"
    ((BAVC.reconstruct iv bad2 delta).map (BAVC.check ·.coms) != some (o.bytes "check"))) && ok
  return ok

/-- Offsets in a Moussaka issuance proof (7272 bytes; `faest_sig.hpp:39-66`). -/
def issueOffsets : List (String × Nat × Nat) :=
  let corr := 16 * 256
  let cmult := 12 * 39
  let fields := [("corrections", corr), ("cmult", cmult), ("vole_check", 64), ("correction", 256),
    ("qs_proof", 128), ("open", BAVC.openSize), ("delta", 16), ("iv_pre", 16), ("ctr", 4)]
  let (_, out) := fields.foldl (fun (off, acc) (k, n) => (off + n, acc ++ [(k, off, n)])) (0, [])
  out

def field (proof : ByteArray) (k : String) : ByteArray :=
  match issueOffsets.lookup k with
  | some (off, n) => proof.extract off (off + n)
  | none => ByteArray.empty

def checkKat (rs : Array Record) : IO Bool := do
  let some r := rs[0]? | check "kat record" false
  let proof := r.bytes "proof"
  let mut ok := true
  ok := (← check "kat proof length" (proof.size == 7272)) && ok
  let iv := Spec.SHAKE.shake128 ((field proof "iv_pre" ++ r.bytes "mu").push 4) 16
  ok := (← check "kat iv" (iv == r.bytes "iv")) && ok
  match BAVC.reconstruct iv (field proof "open") (field proof "delta") with
  | none => ok := (← check "kat bavc accepted" false) && ok
  | some v =>
    ok := (← check "kat leaves" (v.keys == r.bytes "leaves")) && ok
    ok := (← check "kat hashed_leaves" (v.coms == r.bytes "hashed_leaves")) && ok
    ok := (← check "kat vole_commit_check" (BAVC.check v.coms == r.bytes "vole_commit_check")) && ok
  return ok

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "vectors"
  let prims := parse (← IO.FS.readFile s!"{dir}/verifier_prims.txt")
  let (ok1, n) ← checkPrims prims
  IO.println s!"verifier_prims: {n} records, {if ok1 then "ok" else "FAILED"}"
  let ok2 ← checkBavc (parse (← IO.FS.readFile s!"{dir}/verifier_bavc.txt"))
  IO.println s!"verifier_bavc: {if ok2 then "ok" else "FAILED"}"
  let ok3 ← checkKat (parse (← IO.FS.readFile s!"{dir}/verifier_kat.txt"))
  IO.println s!"verifier_kat: {if ok3 then "ok" else "FAILED"}"
  return if ok1 && ok2 && ok3 then 0 else 1

end VoleMole.Verifier.Vectors

def main (args : List String) : IO UInt32 := VoleMole.Verifier.Vectors.main args
