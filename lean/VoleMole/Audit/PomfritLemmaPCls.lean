import VoleMole.ROM.LemmaPClsBound
import VoleMole.Audit.Nonvacuous

/-!
# Non-vacuity of Lemma P^cls for the executable verifier

`lean/docs/security/pomfrit-lemmap-tight.md` §6A. The statements of
`Verifier/Bridge/MaskSlices.lean`, `ROM/LemmaPClassDet.lean`, `ROM/LemmaPCls.lean` and
`ROM/LemmaPClsBound.lean` at real objects.

* **The structure of the response** (`chain_affineOn`, `chain_twoLabelOn`) has one hypothesis: the
  trees of a set have the same label rows. It holds for every singleton, for every chain, so both
  theorems apply to every chain of every statement whose label rows are corrected rows
  (PomFRIT's: `pomfrit_hlab`).
* **Parallelism** (`Seed.KOSPar` on `DisjQuads`): for every chain with at most 1441 hashed rows
  some `chal1` is good for parallelism (`exists_kosPar_chain`; all but a fraction `2⁻¹³⁴` are).
* **Coverage** (`ClsCovered`): it holds when the class extractor decodes no class
  (`clsCovered_of_tgt_none`); otherwise it asks for the decoder's `H₅` queries in the prover's log.
* **The adaptive bound** `pomfritT_accept_le_cls` at the prover that makes no query, and the
  numbers: `2⁶⁴·2⁵⁰/2¹²⁸ = 2⁻¹⁴`, `2⁶⁴·2⁻¹³⁴ = 2⁻⁷⁰`.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Prob VoleMole.PomFRIT VoleMole.Seed
open scoped ENNReal

set_option maxRecDepth 8000

namespace VoleMole.Audit.PomfritLemmaPCls

/-! ## The structure of the response -/

section Structure

variable [HasPrg] (st : Statement) (ch : Chain) (T : CrtTables)
  (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
include hlab

/-- The response of every chain is affine on the slices of every tree. -/
example (i : Fin BAVC.tau) (S : Finset (Fin BAVC.tau)) (hd g : Blocks) :
    AffineOn ({Δ : Blocks | ∀ k ∉ S, Δ k = hd k} ∩ slice {i} g) (ch.kosQ st T) (ch.kosD st T) :=
  chain_affineOn st ch T hlab (fun k hk k' hk' => by
    rw [Finset.mem_singleton.1 hk, Finset.mem_singleton.1 hk']) S hd g

/-- The response of every chain is two-label for every two distinct trees. -/
example {i i' : Fin BAVC.tau} (h : i ≠ i') (Sb : Set Blocks) :
    TwoLabelOn Sb {i} {i'} (ch.kosQ st T) (ch.kosD st T) :=
  chain_twoLabelOn st ch T hlab (Finset.disjoint_singleton.2 h)
    (fun k hk k' hk' => by rw [Finset.mem_singleton.1 hk, Finset.mem_singleton.1 hk'])
    (fun k hk k' hk' => by rw [Finset.mem_singleton.1 hk, Finset.mem_singleton.1 hk']) Sb

end Structure

/-- PomFRIT's label rows are corrected rows, in both layouts. -/
example (lr : Bool) :
    (pomfritParams lr).labelRowOffset + 128 ≤ (pomfritParams lr).correctionRows :=
  pomfrit_hlab lr

/-! ## Parallelism -/

/-- **Some `chal1` is good for parallelism**, for every chain with at most 1441 hashed rows. -/
theorem exists_kosPar_chain [HasPrg] (st : Statement) (ch : Chain) (T : CrtTables)
    (hL : Chain.kosL st ≤ 1441) :
    ∃ b : Bytes 136, Seed.KOSPar (chOf gfId mem_shortKeys b.ba) DQ (lift T) (ch.kosQ st T)
      (ch.kosD st T) := by
  by_contra hno
  push Not at hno
  have h1 : prU (Bytes 136) (fun b => ¬Seed.KOSPar (chOf gfId mem_shortKeys b.ba) DQ (lift T)
      (ch.kosQ st T) (ch.kosD st T)) = 1 := by
    classical
    rw [prU_eq_card, Finset.filter_true_of_mem fun b _ => hno b, Finset.card_univ]
    exact ENNReal.div_self (by simp) (by simp)
  have h2 := (prU_kos_par_le T (ch.kosQ st T) (ch.kosD st T)).trans (parEps_le hL)
  rw [h1] at h2
  exact absurd h2 (not_le.2 (ENNReal.inv_lt_one.2 (by norm_num)))

/-- PomFRIT's chains have at most 1441 hashed rows. -/
example (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray) (lr : Bool) :
    Chain.kosL (OneMore.Pomfrit.pomfritRedeemT pk h b1 b2 lr) ≤ 1441 := by
  cases lr <;>
    norm_num [Chain.kosL, OneMore.Pomfrit.pomfritRedeemT, pomfritParams, Params.correctionRows,
      Params.witnessBits]

/-! ## Coverage -/

/-- **Coverage holds when the class extractor decodes no class** (no two classes of width at
least 51 with different prefixes). -/
theorem clsCovered_of_tgt_none {β : Type} (E : CTable) (st : Statement) (T : CrtTables)
    (r : Out (β × QueryLog specIC))
    (h : @tgtC (VoleMole.ZK.Sim.icPrg E.cipher) st (outChain r) (aliveR E r) = none) :
    ClsCovered E st T r := by
  intro i hi
  rw [h] at hi
  cases hi

/-! ## The adaptive bound -/

/-- **Lemma P^cls's adaptive bound** at the prover that makes no query. -/
example (pk : UovPk) (lr : Bool) (pf : ByteArray) :=
  pomfritT_accept_le_cls (ι := Unit) (β := Unit) pk (fun _ _ => ByteArray.empty)
    (fun _ => ByteArray.empty) (fun _ => ByteArray.empty) lr (pure (pf, ((), ()))) 0 trivial 0
    trivial 0 trivial

/-- `2⁶⁴` queries to `H₂³`: `2⁶⁴·2⁵⁰/2¹²⁸ = 2⁻¹⁴`. -/
example : (2 : ℝ≥0∞) ^ 64 * ((2 ^ 50 : ℝ≥0∞) / 2 ^ 128) = (2 ^ 14 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ 64), mul_assoc, ← pow_add,
    show (2 : ℝ≥0∞) ^ 128 = 2 ^ 14 * 2 ^ (50 + 64) by rw [← pow_add],
    ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- `2⁶⁴` queries to `H₂¹`: `2⁶⁴·2⁻¹³⁴ = 2⁻⁷⁰`. -/
example : (2 : ℝ≥0∞) ^ 64 * (2 ^ 134 : ℝ≥0∞)⁻¹ = (2 ^ 70 : ℝ≥0∞)⁻¹ := by
  rw [show (2 : ℝ≥0∞) ^ 134 = 2 ^ 70 * 2 ^ 64 by rw [← pow_add],
    ENNReal.mul_inv (by simp) (by simp), mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

end VoleMole.Audit.PomfritLemmaPCls
