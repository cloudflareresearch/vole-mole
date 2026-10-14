import VoleMole.Verifier.BAVC

/-!
# Proof layout, `check_format`, `mu`, `iv` and `chal1` (executable)

The first steps of `voleith_vole_reconstruct` (`src/voleith.hpp:354-409`) for any of vole-mole's
relations, which differ only in the witness length `ℓ` (bytes `ℓ/8`) and the QuickSilver degree
`d`; everything else is FAEST-EM-128f (`BAVC.lean`).

* `Params`: `ℓ/8` and `d`, and the derived sizes of `fao/constants.hpp:333-470` (`fao/` is
  `subprojects/faest-arch-opt/`): `N_MASK = (d − 1) + 4`, `N_MULT = 312` (generated CRT tables for
  `(s128, τ = 17, 120)`), `VOLE_ROWS = ℓ + 8·N_MASK`, `VOLE_COL_BLOCKS` = `VOLE_ROWS` rounded up to a
  multiple of 256 rows (`TRANSPOSE_BITS_ROWS`), in 128-bit blocks.
* `Proof`: the fields of `fao/faest_sig.hpp:39-66`, in order: corrections `c₁ … c₁₆` (`ℓ/8` bytes
  each), `c_mult` (`N_MASK` rows of 39 bytes), the VOLEHash `ũ` (64), the correction `d` (`ℓ/8`), the
  QuickSilver proof (`(d − 1)·16`), the BAVC opening (2224), `Δ` (16), `iv_pre` (16), the grinding
  counter (4).
* `checkFormat` (`faest_sig.hpp:126-152`): the top 8 bits of `Δ` are zero. (`N_MULT = 312` is a
  multiple of 8, so the `c_mult` padding check is vacuous.)
* `mu = H(inst ‖ DST ‖ 8)` (`hash_mu`, `src/voleith.hpp:107-123`), where `inst` is the byte string
  the relation's `hash_instance` absorbs; with delayed instance binding (PomFRIT), `iv` and `chal1`
  use `mu₁ = H(DST ‖ 12)` instead. `iv = H(iv_pre ‖ mu₁ ‖ 4)` (16 bytes).
* `chal1 = H(mu₁ ‖ vole_commit_check ‖ c₁ ‖ … ‖ c₁₆ ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 9)` (136 bytes,
  `src/voleith.hpp:396-405`).

`H` is SHAKE128 (`hash_state` at `s128`). Checked by `lake exe verifier_vectors` on one KAT proof
per relation (`lean/vectors/verifier_kat.txt`).
-/

namespace VoleMole.Verifier

open Spec.SHAKE

/-- The relation-dependent parameters. -/
structure Params where
  /-- Witness bytes `ℓ/8` (`OWF_CONSTANTS::WITNESS_BITS / 8`). -/
  witnessBytes : Nat
  /-- QuickSilver degree `d` (`OWF_CONSTANTS::QS_DEGREE`). -/
  qsDegree : Nat

namespace Params

variable (p : Params)

def witnessBits : Nat := 8 * p.witnessBytes
def nMask : Nat := p.qsDegree - 1 + 4
def nMult (_ : Params) : Nat := 312
def nMultBytes (_ : Params) : Nat := 39
def voleRows : Nat := p.witnessBits + 8 * p.nMask
def voleColBlocks : Nat := 2 * ((p.voleRows + 255) / 256)
def colBytes : Nat := 16 * p.voleColBlocks

/-- Field sizes, in proof order. -/
def fieldSizes : List (String × Nat) :=
  [("corrections", 16 * p.witnessBytes), ("cmult", p.nMask * p.nMultBytes), ("vole_check", 64),
   ("correction", p.witnessBytes), ("qs_proof", (p.qsDegree - 1) * 16), ("open", BAVC.openSize),
   ("delta", 16), ("iv_pre", 16), ("ctr", 4)]

def proofBytes : Nat := (p.fieldSizes.map (·.2)).sum

/-- Offset and size of a field. -/
def field? (k : String) : Option (Nat × Nat) := Id.run do
  let mut off := 0
  for (k', n) in p.fieldSizes do
    if k' == k then return some (off, n)
    off := off + n
  return none

end Params

/-- A proof, with its parameters. -/
structure Proof where
  params : Params
  bytes : ByteArray

namespace Proof

variable (pf : Proof)

def field (k : String) : ByteArray :=
  match pf.params.field? k with
  | some (off, n) => pf.bytes.extract off (off + n)
  | none => ByteArray.empty

def corrections : ByteArray := pf.field "corrections"
/-- `c_i` for `i = 1 … 16`. -/
def correctionOf (i : Nat) : ByteArray :=
  pf.corrections.extract ((i - 1) * pf.params.witnessBytes) (i * pf.params.witnessBytes)
def cmult : ByteArray := pf.field "cmult"
def voleCheck : ByteArray := pf.field "vole_check"
def correction : ByteArray := pf.field "correction"
def qsProof : ByteArray := pf.field "qs_proof"
def opening : ByteArray := pf.field "open"
def delta : ByteArray := pf.field "delta"
def ivPre : ByteArray := pf.field "iv_pre"
def ctr : ByteArray := pf.field "ctr"

/-- `check_format`: the right length, and the 8 grinding bits of `Δ` are zero. -/
def checkFormat : Bool := pf.bytes.size == pf.params.proofBytes && pf.delta.get! 15 == 0

end Proof

/-- `H(input)` to `n` bytes. -/
def H (input : ByteArray) (n : Nat) : ByteArray := shake128 input n

/-- `hash_mu`: `H(inst ‖ DST ‖ 8)`, or `H(DST ‖ 12)` without an instance. -/
def mu (inst : Option ByteArray) (dst : ByteArray) : ByteArray :=
  match inst with
  | some i => H ((i ++ dst).push 8) 32
  | none => H (dst.push 12) 32

/-- `iv = H(iv_pre ‖ mu₁ ‖ 4)`. -/
def ivOf (pf : Proof) (mu1 : ByteArray) : ByteArray := H ((pf.ivPre ++ mu1).push 4) 16

/-- `chal1`. -/
def chal1 (pf : Proof) (mu1 voleCommitCheck binder1 : ByteArray) : ByteArray :=
  H ((mu1 ++ voleCommitCheck ++ pf.corrections ++ pf.cmult ++ pf.ivPre ++ binder1).push 9) 136

#guard ({ witnessBytes := 256, qsDegree := 9 } : Params).proofBytes == 7272
#guard ({ witnessBytes := 164, qsDegree := 2 } : Params).proofBytes == 5323
#guard ({ witnessBytes := 256, qsDegree := 9 } : Params).voleColBlocks == 18

end VoleMole.Verifier
