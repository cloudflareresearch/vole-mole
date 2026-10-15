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
  `Dom = Kind × ByteArray`, a domain of `L0-L2-commitments.md` §2.1 (`Kind`, defined with the
  verifier's hash record in `Verifier/Hashes.lean`) and the input string. Each domain answers with
  a fixed number of bytes (`Kind.outLen`). Under `randomOracle` each cell `(k, x)` is an
  independent uniform answer: L0's disjointness of the domains (final byte, and the lengths of the
  three `H₁` shapes; `Protocols/DomainSeparation.lean`) is what justifies splitting SHAKE128 into
  these independent oracles (`ROM/DomainSep.lean`: one oracle with a domain rule is equivalent;
  `ROM/SingleOracle.lean`: L0's rule and the verifier).
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

/-! The domains `Kind` and their output lengths `Kind.outLen` are `Verifier/Hashes.lean`'s: the
verifier is parametrised by one hash function per domain, and here each domain is answered by the
random oracle. -/

export VoleMole.Verifier (Kind)

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
