import VoleMole.Verifier.BAVC
import VoleMole.Verifier.Hashes

/-!
# Proof layout, `check_format`, `mu`, `iv` and `chal1` (executable)

The first steps of `voleith_vole_reconstruct` (`src/voleith.hpp:354-409`) for any of vole-mole's
relations, which differ only in the witness length `ℓ` (bytes `ℓ/8`) and the QuickSilver degree
`d`; everything else is FAEST-EM-128f (`BAVC.lean`).

* `Params`: `ℓ/8`, `d` and the label-row switch, and the derived sizes of
  `fao/constants.hpp:333-470` (`fao/` is `subprojects/faest-arch-opt/`): `N_MASK = (d − 1) + 4`,
  `N_MULT = 312` (generated CRT tables for `(s128, τ = 17, 120)`), the corrected rows
  `VOLE_CORRECTION_ROWS = ℓ + ℓ_lab`, `VOLE_ROWS = VOLE_CORRECTION_ROWS + 8·N_MASK`,
  `VOLE_COL_BLOCKS` = `VOLE_ROWS` rounded up to a multiple of 256 rows (`TRANSPOSE_BITS_ROWS`), in
  128-bit blocks.
* Label rows. On `main` (as in FAEST), the CRT gate labels are taken from the first 128 witness
  rows and `ℓ_lab = 0`. With `CRT_DEDICATED_LABEL_ROWS` (faest-arch-opt patch 0005, branch
  `voleith-label-rows`), 128 dedicated rows `ℓ … ℓ + 127` follow the witness: they are corrected and
  hashed by the VOLE check like witness rows, but get no `d`; `ℓ_lab = 128` and the label rows start
  at row `ℓ`. `Params.labelRows` selects the layout.
* `Proof`: the fields of `fao/faest_sig.hpp:39-66`, in order: corrections `c₁ … c₁₆`
  (`VOLE_CORRECTION_ROWS/8` bytes each), `c_mult` (`N_MASK` rows of 39 bytes), the VOLEHash `ũ` (64), the correction `d` (`ℓ/8`), the
  QuickSilver proof (`(d − 1)·16`), the BAVC opening (2224), `Δ` (16), `iv_pre` (16), the grinding
  counter (4).
* `checkFormat` (`faest_sig.hpp:126-152`): the top 8 bits of `Δ` are zero. (`N_MULT = 312` is a
  multiple of 8, so the `c_mult` padding check is vacuous.)
* `mu = H(inst ‖ DST ‖ 8)` (`hash_mu`, `src/voleith.hpp:107-123`), where `inst` is the byte string
  the relation's `hash_instance` absorbs; with delayed instance binding (PomFRIT), `iv` and `chal1`
  use `mu₁ = H(DST ‖ 12)` instead. `iv = H(iv_pre ‖ mu₁ ‖ 4)` (16 bytes).
* `chal1 = H(mu₁ ‖ vole_commit_check ‖ c₁ ‖ … ‖ c₁₆ ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 9)` (136 bytes,
  `src/voleith.hpp:396-405`).

`H` is SHAKE128 (`hash_state` at `s128`), in the domain of each call (`Hashes.lean`): `mu` is
`H₂⁰`/`H₂⁴`, `iv` is `H₄`, `chal1` is `H₂¹`. The steps take the hash functions `Hs : Hashes` as an
argument (`Hashes.shake` for SHAKE128). Checked by `lake exe verifier_vectors` on one KAT proof
per relation (`lean/vectors/verifier_kat.txt`).
-/

namespace VoleMole.Verifier


/-- The relation-dependent parameters. -/
structure Params where
  /-- Witness bytes `ℓ/8` (`OWF_CONSTANTS::WITNESS_BITS / 8`). -/
  witnessBytes : Nat
  /-- QuickSilver degree `d` (`OWF_CONSTANTS::QS_DEGREE`). -/
  qsDegree : Nat
  /-- `OWF_CONSTANTS::CRT_DEDICATED_LABEL_ROWS` (branch `voleith-label-rows`). -/
  labelRows : Bool := false

namespace Params

variable (p : Params)

def witnessBits : Nat := 8 * p.witnessBytes
def nMask : Nat := p.qsDegree - 1 + 4
def nMult (_ : Params) : Nat := 312
def nMultBytes (_ : Params) : Nat := 39
/-- Index of the first gate-label row (`CRT_LABEL_ROW_OFFSET`). -/
def labelRowOffset : Nat := if p.labelRows then p.witnessBits else 0
/-- `VOLE_CORRECTION_ROWS`: the rows corrected by `c_i`, CRT-lifted and hashed by the VOLE check. -/
def correctionRows : Nat := p.witnessBits + if p.labelRows then 128 else 0
def correctionBytes : Nat := p.correctionRows / 8
def voleRows : Nat := p.correctionRows + 8 * p.nMask
def voleColBlocks : Nat := 2 * ((p.voleRows + 255) / 256)
def colBytes : Nat := 16 * p.voleColBlocks

/-- Field sizes, in proof order. -/
def fieldSizes : List (String × Nat) :=
  [("corrections", 16 * p.correctionBytes), ("cmult", p.nMask * p.nMultBytes), ("vole_check", 64),
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
  pf.corrections.extract ((i - 1) * pf.params.correctionBytes) (i * pf.params.correctionBytes)
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

/-- `hash_mu`: `H₂⁰(inst ‖ DST ‖ 8)`, or `H₂⁴(DST ‖ 12)` without an instance. -/
def mu (Hs : Hashes) (inst : Option ByteArray) (dst : ByteArray) : ByteArray :=
  match inst with
  | some i => Hs.hash .mu ((i ++ dst).push 8)
  | none => Hs.hash .muDelayed (dst.push 12)

/-- `iv = H₄(iv_pre ‖ mu₁ ‖ 4)`. -/
def ivOf (Hs : Hashes) (pf : Proof) (mu1 : ByteArray) : ByteArray :=
  Hs.hash .h4 ((pf.ivPre ++ mu1).push 4)

/-- The `H₂¹` input `mu₁ ‖ vole_commit_check ‖ c₁ ‖ … ‖ c₁₆ ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 9`. -/
def chal1Input (pf : Proof) (mu1 voleCommitCheck binder1 : ByteArray) : ByteArray :=
  (mu1 ++ voleCommitCheck ++ pf.corrections ++ pf.cmult ++ pf.ivPre ++ binder1).push 9

/-- `chal1 = H₂¹(…)`. -/
def chal1 (Hs : Hashes) (pf : Proof) (mu1 voleCommitCheck binder1 : ByteArray) : ByteArray :=
  Hs.hash .h21 (chal1Input pf mu1 voleCommitCheck binder1)

#guard ({ witnessBytes := 256, qsDegree := 9 } : Params).proofBytes == 7272
#guard ({ witnessBytes := 164, qsDegree := 2 } : Params).proofBytes == 5323
#guard ({ witnessBytes := 256, qsDegree := 9 } : Params).voleColBlocks == 18
#guard ({ witnessBytes := 256, qsDegree := 9, labelRows := true } : Params).proofBytes == 7528
#guard ({ witnessBytes := 164, qsDegree := 2, labelRows := true } : Params).proofBytes == 5579

end VoleMole.Verifier
