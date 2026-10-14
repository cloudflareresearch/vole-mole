import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
import VoleMole.Prob.Bytes

/-!
# The random-oracle model: VCVio's uniform sampling and the hash oracles

Phase B of `docs/probabilistic-plan.md` (M4). Only `VoleMole/ROM/` imports VCVio; everything in
`Prob/` stays Mathlib-only and is transported here.

* **The bridge** (`prEvent_uniformSample_eq_prU`): VCVio's `Pr{let x ← $ᵗ α}[P x]` is phase A's
  `prU α P`, for any uniform sampler of `α` (both are `#{x | P x} / |α|`). So every bound of
  `Prob/` is a bound on a VCVio event.
* **Samplers**: `Bytes n` and `GF128` get (noncomputable) uniform samplers; they are used for
  proofs only, never run.
* **The hash oracles** (`spec`): one VCVio oracle specification `OracleSpec.ofFn` indexed by
  `Dom = Kind × ByteArray`, a domain of `L0-L2-commitments.md` §2.1 and the input string. Each
  domain answers with a fixed number of bytes (`Kind.outLen`). Under `randomOracle` each cell
  `(k, x)` is an independent uniform answer: L0's disjointness of the domains (final byte, and the
  lengths of the three `H₁` shapes; `Protocols/DomainSeparation.lean`) is what justifies splitting
  SHAKE128 into these independent oracles. That step is a modelling assumption here (the plan's
  "domain separation ⇒ independent oracles" lemma is not formalized).
* `Table`: a complete answer table, the object VCVio's eager-sampling bounds quantify over
  (`prEvent_randomOracle_le_of_bad_queries`).
-/

open ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Arith OracleComp OracleSpec

/-! ## Uniform samplers and the bridge to `prU` -/

/-- A uniform sampler of `n` bytes (for proofs; not executed). -/
noncomputable instance instSampleableBytes (n : ℕ) : SampleableType (Bytes n) :=
  SampleableType.ofFintype _

/-- A uniform sampler of `GF128` (for proofs; not executed). -/
noncomputable instance instSampleableGF128 : SampleableType GF128 :=
  SampleableType.ofFintype _

/-- **VCVio's uniform event probability is `prU`**, for every uniform sampler of `α`. -/
theorem prEvent_uniformSample_eq_prU {α : Type} [SampleableType α] [Fintype α] (P : α → Prop) :
    Pr{let x ← $ᵗ α}[P x] = prU α P := by
  classical
  rw [SampleableType.prEvent_uniformSample, prU_eq_card]

/-- A phase-A bound is a bound on the VCVio event. -/
theorem prEvent_uniformSample_le {α : Type} [SampleableType α] [Fintype α] {P : α → Prop}
    {ε : ℝ≥0∞} (h : prU α P ≤ ε) : Pr{let x ← $ᵗ α}[P x] ≤ ε :=
  (prEvent_uniformSample_eq_prU P).trans_le h

/-! ## The hash oracles -/

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
  | comb (M : ℕ)
  deriving DecidableEq

/-- The number of output bytes of each domain (the "Output" column of L0 §2.1). -/
def Kind.outLen : Kind → ℕ
  | .h1 | .mu | .muDelayed | .h3 => 32
  | .h4 => 16
  | .h5 => 4
  | .h21 => 136
  | .h22 => 56
  | .h23 => 16
  | .comb M => 16 * M

/-- An oracle query: the domain and the input string. -/
abbrev Dom := Kind × ByteArray

/-- The answer type of a query. -/
abbrev Ans (d : Dom) : Type := Bytes d.1.outLen

/-- **The hash oracles**, one VCVio oracle specification indexed by domain and input. -/
abbrev spec : OracleSpec Dom := OracleSpec.ofFn Ans

/-- A complete answer table: one answer per query (eager sampling). -/
abbrev Table := (d : Dom) → Ans d

/-- `H₂¹` at `x` in table `g`. -/
abbrev Table.chal1 (g : Table) (x : ByteArray) : Bytes 136 := g (.h21, x)

/-- `H₂²` at `x` in table `g`. -/
abbrev Table.chal2 (g : Table) (x : ByteArray) : Bytes 56 := g (.h22, x)

/-- `H₂³` at `x` in table `g`. -/
abbrev Table.chal3 (g : Table) (x : ByteArray) : Bytes 16 := g (.h23, x)

end VoleMole.ROM
