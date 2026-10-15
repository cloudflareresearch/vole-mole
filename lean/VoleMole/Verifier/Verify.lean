import VoleMole.Verifier.QuickSilver

/-!
# The VOLEitH verifier (executable, relation-generic)

`voleith_vole_reconstruct` followed by `voleith_verify_commit` (`src/voleith.hpp:354-481`), for a
`Statement`: the relation's parameters and DST, the instance encoding (what `hash_instance`
absorbs), the binders, the UOV combination it reads (if any), and an evaluator of the relation's
constraints. The instance encoding and the constraints may depend on `chal1` (PomFRIT's instance
`h` is derived from it) and the constraints on the combination bytes `H_comb(chal2 ‖ dst)` (the
random linear combinations of the UOV relations), which the verifier computes (`combBytes`).

Every hash goes through the record `Hs : Hashes` (`Hashes.lean`): `verify Hashes.shake` is the
executable verifier of the KAT runners, `verify (Hashes.ofTable g)` the verifier against a random
oracle's answer table (`ROM/Verifier.lean`).

Steps: `check_format` → `mu`/`mu₁`, `iv` → BAVC reconstruction (reject a malformed opening) →
`vole_commit_check`, `chal1` → ConvertToVOLE → CRT VOLE → VOLE check, `chal2` → correction `d` →
QuickSilver check value → `chal3`; accept iff `chal3 = Δ`. See the modules `Proof`, `BAVC`, `VOLE`,
`KOS`, `QuickSilver` for each step and its C++ source.
-/

namespace VoleMole.Verifier

open VoleMole.Arith

/-- What the verifier needs to know about a relation and its instance. -/
structure Statement where
  params : Params
  dst : ByteArray
  /-- Delayed instance binding (PomFRIT): `iv`/`chal1` use `mu₁ = H(DST ‖ 12)`, and `mu` enters
  `chal2`. -/
  delayed : Bool := false
  binder1 : ByteArray := ByteArray.empty
  binder2 : ByteArray := ByteArray.empty
  /-- `chal1 ↦` the bytes `hash_instance` absorbs (only delayed statements may use `chal1`). -/
  instEnc : ByteArray → ByteArray
  /-- The UOV combination `(M, dst)`: the constraints read `l = H_comb(chal2 ‖ dst)`, `16·M`
  bytes (`uov::detail::Combination`). -/
  comb : Option (Nat × ByteArray) := none
  /-- `chal1 ↦ l ↦` the constraint values at a field assignment of the witness bits, with `l` the
  combination bytes (`combBytes`; empty without a combination). -/
  values : ByteArray → ByteArray → (Nat → GF128) → List GF128

/-- `mu₁`: `H₂⁰(inst ‖ DST ‖ 8)`, or `H₂⁴(DST ‖ 12)` for delayed instance binding (no `chal1`). -/
def Statement.mu1 (Hs : Hashes) (st : Statement) : ByteArray :=
  if st.delayed then mu Hs none st.dst else mu Hs (some (st.instEnc ByteArray.empty)) st.dst

/-- The `mu` in `chal2`'s input: `H₂⁰(inst(chal1) ‖ DST ‖ 8)` for delayed instance binding, else
empty. -/
def Statement.muDelayed (Hs : Hashes) (st : Statement) (chal1 : ByteArray) : ByteArray :=
  if st.delayed then mu Hs (some (st.instEnc chal1)) st.dst else ByteArray.empty

/-- The combination bytes `H_comb(chal2 ‖ dst)` the constraints read (empty without one). -/
def Statement.combBytes (Hs : Hashes) (st : Statement) (chal2 : ByteArray) : ByteArray :=
  match st.comb with
  | none => ByteArray.empty
  | some (M, dst) => Hs.hash (.comb M) (chal2 ++ dst)

/-- The verifier's transcript (for tests), and the verdict. -/
structure Transcript where
  iv : ByteArray := ByteArray.empty
  chal1 : ByteArray := ByteArray.empty
  chal2 : ByteArray := ByteArray.empty
  qsCheck : ByteArray := ByteArray.empty
  chal3 : ByteArray := ByteArray.empty
  accept : Bool := false
  /-- Why the proof was rejected before `chal3`, if it was. -/
  error : String := ""

/-- Verify `proof` for `st`, with the hash functions `Hs` and the CRT tables `T`. -/
def verify (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray) : Transcript :=
  Id.run do
  let pf : Proof := { params := st.params, bytes := proof }
  if !pf.checkFormat then return { error := "check_format" }
  let mu1 := st.mu1 Hs
  let iv := ivOf Hs pf mu1
  let some leaves := BAVC.reconstruct iv pf.opening pf.delta | return { error := "opening" }
  let c1 := chal1 Hs pf mu1 (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1
  let cols := convertToVole pf iv leaves
  let crt := crtReconstruct Hs pf T iv cols
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  let c2 := chal2 Hs pf c1 hV (st.muDelayed Hs c1) st.binder2
  if deltaL == 0 then return { iv, chal1 := c1, chal2 := c2, error := "Delta = 0" }
  let keys := correctedKeys pf crt.rows deltaL
  let cs := constraintKeys st.params keys deltaL (st.values c1 (st.combBytes Hs c2))
  let check := qsCheck pf c2 cs crt.qMask deltaL
  let c3 := chal3 Hs pf c2 check
  return { iv, chal1 := c1, chal2 := c2, qsCheck := gfToBytes check, chal3 := c3,
           accept := c3 == pf.delta }

end VoleMole.Verifier
