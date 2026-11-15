import VoleMole.ZK.HopsH4PtPerm
import VoleMole.ZK.InvValue
import VoleMole.ZK.ValOverlap
import VoleMole.Theft.NumTerms
import VoleMole.Theft.DeltaBound

/-!
# Audit of the permutation-row point hop with value charges (zk-permpt)

What is proved (`ZK/IdealCipherPtPerm.lean`, `ZK/HopsH4PtPerm.lean`, `ZK/InvValue.lean`,
`ZK/ValOverlap.lean`):

* **The charge is non-vacuous and catches the zk-perm attack.** The counterexample of
  `ZK/InvPoint.lean` is an instance of `IC.puncturePtPm_real` (`IC.inv_vbound`), its reads are
  charged `q` (`IC.inv_vcharge_eq`), and the resulting bound `(q + 4)/(2¹²⁸ − q)` is above the
  attack's advantage `≥ 2⁻⁶⁴ − 2⁻¹²⁸` at `q = 2⁶⁴` (`attack_consistent`).
* **The same attack against the BAVC is charged in full**: inverse queries at a hidden leaf's
  commitment block read keys at a value of the hidden tree, so the charge of `|S|` such queries is
  `|S|` (`com_attack_charged`).
* **The hypotheses of `hide_rom_query_ptPm_num` hold for a real parameter set** (Ratatouille's
  issuance relation, `nHi = 1`, at most `56` VOLE column blocks), with the empty reader
  (`ptPm_pI_empty`).

Not proved: the chain (`zk_rom_ic_h23_exp`, `zk_ro_exp`, `ZKExp`) with permutation rows and this
charge. The value set `hidVals` is a function of the hidden tree, not of the proof (see
`docs/zk.md` §10.8).

The theorems' axioms are `propext`, `Classical.choice`, `Quot.sound` only (checked in a scratch
file). No `sorry`, no `axiom`.
-/

namespace VoleMole.Audit.ZKPermPt

open Finset VoleMole.Privacy VoleMole.ZK.IC VoleMole.ZK.Sim VoleMole.Verifier

/-- **The zk-perm attack against the BAVC is charged `|S|`**: inverse queries, under the keys of
`S`, at the first commitment block of a hidden leaf read every key of `S` at a value of the hidden
tree. -/
theorem com_attack_charged (p : Params) (iv delta : ByteArray) (π : PCipher) (seed : Blk)
    (i : Fin BAVC.tau) (S : Finset Blk) :
    vkeys (InY iv) (hidVals p iv delta π seed)
      (qInv S (rowAt (xIn iv) nN ∅ (cf π) (fun _ _ => seed) seed (hLeaf delta i) (comPt iv i 0)) π)
      π = S := by
  refine qInv_vkeys _ S ?_ π
  simp only [hidVals, valsP, mem_biUnion, mem_filter, mem_range, mem_image]
  exact ⟨hLeaf delta i, ⟨hLeaf_lt delta i.isLt, hid_hLeaf delta i.isLt⟩, comPt iv i 0,
    comPt_mem_PnB p iv delta i (by norm_num), rfl⟩

/-- **The counterexample under the value charge, at `q = 2⁶⁴`**: its reads are charged `2⁶⁴`; the
permutation-row hop bounds the advantage by `(2⁶⁴ + 4)/(2¹²⁸ − 2⁶⁴)`; the attack's advantage (against
the permutation-row replacement) is `≥ 2⁻⁶⁴ − 2⁻¹²⁸`. The two are consistent:
`2⁻⁶⁴ − 2⁻¹²⁸ < (2⁶⁴ + 4)/(2¹²⁸ − 2⁶⁴)`. -/
theorem attack_consistent (x : ℕ → Blk) (z0 : Blk) :
    ∃ S : Finset Blk, S.card = 2 ^ 64 ∧
      exP (Coins Blk Blk 1 × (Blk → Equiv.Perm Blk)) (fun p =>
        ((vkeys (pInv x z0) (valsP 1 (fun n => n = 0) (pnInv x z0) (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1))
          (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ)) = 2 ^ 64 ∧
      |pr (Coins Blk Blk 1 × (Blk → Equiv.Perm Blk)) (fun p =>
          aInv S z0 (phiInv z0 (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1)) p.2) -
        pr (Coins Blk Blk 1 × (Blk → Equiv.Perm Blk)) (fun p =>
          aInv S z0 (phiInv z0 (rowAt x 1 ((range 1).filter fun n => n = 0) (cf p.2) p.1.2 p.1.1))
            p.2)| ≤ (2 ^ 64 + 4) / (2 ^ 128 - 2 ^ 64) ∧
      (1 : ℝ) / 2 ^ 64 - 1 / 2 ^ 128 ≤
        experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) -
          experPm x 1 {0} (phiInv z0) (fun y π => aInv S z0 y π) ∧
      (1 : ℝ) / 2 ^ 64 - 1 / 2 ^ 128 < (2 ^ 64 + 4) / (2 ^ 128 - 2 ^ 64) := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Blk))
    (n := 2 ^ 64) (by rw [Finset.card_univ, card_blk]; norm_num)
  refine ⟨S, hS, ?_, ?_, ?_, by norm_num⟩
  · rw [inv_vcharge_eq x S z0, hS]; norm_num
  · have h := inv_vbound x S z0 (by rw [hS, card_blk]; norm_num)
    rw [hS, card_blk] at h
    refine h.trans (le_of_eq ?_)
    norm_num
  · have h := inv_adv_ge x S z0
    rw [hS, card_blk] at h
    refine le_trans (le_of_eq ?_) h
    norm_num

/-- **The hypotheses of `hide_rom_query_ptPm_num` hold for Ratatouille's issuance parameters**,
with the empty reader. -/
theorem ptPm_pI_empty (iv delta : ByteArray) (A : Hidden Privacy.Ratatouille.pI → Prop) :
    |realPrPm (fun seed π => hiddenOutE (cf π) Privacy.Ratatouille.pI iv delta seed)
        (fun o (_ : PCipher) => A o) -
      idealPrPm (hiddenIdeal (p := Privacy.Ratatouille.pI) delta) (fun o (_ : PCipher) => A o)| ≤
      (1422577 + 221 * expVKeys Privacy.Ratatouille.pI iv delta (fun _ _ => ∅)) /
        (2 ^ 128 - 221 * 2 ^ 64) :=
  hide_rom_query_ptPm_num Privacy.Ratatouille.pI iv delta Theft.Ratatouille.smallParams_pI'
    Theft.permOk_pIR.1 Theft.permOk_pIR.2 (fun o (_ : PCipher) => A o) (fun _ _ => ∅)
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl) (qm := 0) (fun _ _ _ => by simp [vkeys])
    (by norm_num)

end VoleMole.Audit.ZKPermPt
