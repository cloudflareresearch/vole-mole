import VoleMole.Verifier.QuickSilver

/-!
# The VOLEitH verifier (executable, relation-generic)

`voleith_vole_reconstruct` followed by `voleith_verify_commit` (`src/voleith.hpp:354-481`), for a
`Statement`: the relation's parameters and DST, the instance encoding (what `hash_instance`
absorbs), the binders, and an evaluator of the relation's constraints. The instance encoding and the
constraints may depend on `chal1` (PomFRIT's instance `h` is derived from it) and the constraints on
`chal2` (the random linear combinations of the UOV relations).

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
  /-- `chal1 ↦ chal2 ↦` the constraint values at a field assignment of the witness bits. -/
  values : ByteArray → ByteArray → (Nat → GF128) → List GF128

/-- The verifier's transcript (for tests), and the verdict. -/
structure Transcript where
  chal1 : ByteArray := ByteArray.empty
  chal2 : ByteArray := ByteArray.empty
  qsCheck : ByteArray := ByteArray.empty
  chal3 : ByteArray := ByteArray.empty
  accept : Bool := false
  /-- Why the proof was rejected before `chal3`, if it was. -/
  error : String := ""

/-- Verify `proof` for `st`, with the CRT tables `T`. -/
def verify (T : CrtTables) (st : Statement) (proof : ByteArray) : Transcript := Id.run do
  let pf : Proof := { params := st.params, bytes := proof }
  if !pf.checkFormat then return { error := "check_format" }
  let muI : ByteArray → ByteArray := fun c1 => mu (some (st.instEnc c1)) st.dst
  let mu1 := if st.delayed then mu none st.dst else muI ByteArray.empty
  let iv := ivOf pf mu1
  let some leaves := BAVC.reconstruct iv pf.opening pf.delta | return { error := "opening" }
  let c1 := chal1 pf mu1 (BAVC.check leaves.coms) st.binder1
  let cols := convertToVole pf iv leaves
  let crt := crtReconstruct pf T iv cols
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  let c2 := chal2 pf c1 hV (if st.delayed then muI c1 else ByteArray.empty) st.binder2
  if deltaL == 0 then return { chal1 := c1, chal2 := c2, error := "Delta = 0" }
  let keys := correctedKeys pf crt.rows deltaL
  let cs := constraintKeys st.params keys deltaL (st.values c1 c2)
  let check := qsCheck pf c2 cs crt.qMask deltaL
  let c3 := chal3 pf c2 check
  return { chal1 := c1, chal2 := c2, qsCheck := gfToBytes check, chal3 := c3,
           accept := c3 == pf.delta }

end VoleMole.Verifier
