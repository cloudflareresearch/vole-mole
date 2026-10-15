import VoleMole.Spec.SHAKE

/-!
# The verifier's hash functions, one per domain

Every hash the VOLEitH verifier computes is a SHAKE128 call in one of the domains of
`docs/extraction/L0-L2-commitments.md` §2.1, with a fixed output length. The executable verifier
(`Verify.lean` and its steps) is parametrised by a record `Hs : Hashes` of these functions, so that
the same code runs with SHAKE128 (`Hashes.shake`, the KAT runners) and with the answers of a random
oracle (`ROM/Verifier.lean`, `Hashes.ofTable`).

* `Kind`: the domains (rows 1–12 of L0 §2.1). `H₁`'s three shapes (rows 1–3, told apart by their
  lengths) are one kind; `comb M` is the UOV combination `l = H(chal₂ ‖ dst)` of a relation combining
  `M` equations (row 12). `h3` (the prover's root seed) is never called by the verifier.
* `Kind.outLen`: the output length of each domain (the "Output" column of L0 §2.1).
* `Hashes`: one function per domain; the argument is the whole SHAKE input, domain byte included.

The verifier calls `h1` (the 17 leaf hashes and `com`), `mu` or `muDelayed` (`mu₁`; PomFRIT also
`mu` with its instance, in `chal₂`'s input), `h4` (`iv`), `h5` (the 312 gate hashes), `h21`,
`h22`, `h23` (`chal₁`, `chal₂`, `chal₃`) and `comb M` (the combined relations). Hashes outside L0
are not in the record: the UOV key digests and expansion (`UovPk`) are computed by the statement's
builder before verification, and PomFRIT's `hash_to_target` (an application-level hash, L0 §2.5) is
part of the statement (`Statement.instEnc`, `values`).
-/

namespace VoleMole.Verifier

/-- The SHAKE128 domains of `L0-L2-commitments.md` §2.1 (rows 1–12). `comb M` is the UOV
combination `l = H(chal₂ ‖ dst)` of a relation combining `M` equations (row 12). -/
inductive Kind
  /-- `H₁`: leaf hashes and `com` (rows 1–3, told apart by their lengths). -/
  | h1
  /-- `H₂⁰`: `mu` with an instance (row 4). -/
  | mu
  /-- `H₂⁴`: `mu` for delayed instance binding (row 5). -/
  | muDelayed
  /-- `H₃`: the prover's root seed (row 6). -/
  | h3
  /-- `H₄`: `iv = H₄(iv_pre ‖ mu ‖ 4)` (row 7). -/
  | h4
  /-- `H₅`: the gate hash (row 8). -/
  | h5
  /-- `H₂¹`: `chal1` (row 9). -/
  | h21
  /-- `H₂²`: `chal2` (row 10). -/
  | h22
  /-- `H₂³`: `chal3` (row 11). -/
  | h23
  /-- The UOV combination `l` of `M` field elements (row 12). -/
  | comb (M : Nat)
  deriving DecidableEq

/-- The number of output bytes of each domain (the "Output" column of L0 §2.1). -/
def Kind.outLen : Kind → Nat
  | .h1 | .mu | .muDelayed | .h3 => 32
  | .h4 => 16
  | .h5 => 4
  | .h21 => 136
  | .h22 => 56
  | .h23 => 16
  | .comb M => 16 * M

/-- **The hash functions the verifier calls**, one per domain: `hash k x` is the `k.outLen`-byte
hash of the whole input `x` (domain byte included). -/
structure Hashes where
  hash : Kind → ByteArray → ByteArray

/-- SHAKE128 in every domain: the hashes of the executable verifier (the KAT runners). -/
def Hashes.shake : Hashes := ⟨fun k x => Spec.SHAKE.shake128 x k.outLen⟩

end VoleMole.Verifier
