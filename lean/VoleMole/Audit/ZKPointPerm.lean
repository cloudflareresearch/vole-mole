import VoleMole.ZK.InvPoint

/-!
# Audit of the point-level hop with permutation rows (zk-perm)

The permutation-row variants of the many-token joint bounds (`noTheftN_lean_numJP`,
`noRedirectN_lean_numJP`, `nmUN_lean_numJP`) are **not** proved. What is proved is the obstacle
to the direct port of the point-level hop (`ZK/InvPoint.lean`):

* **The counterexample is an instance of the hop's hypotheses.** One secret node, the root
  (`sec = {0}`, upward closed), `P = {z₀}`; the hidden part `phiInv` reads the secret row only at
  `z₀` (`phiInv_reads`); the distinguisher's reads `qInv` (inverse queries written as forward
  points) are consistent (`qInv_cons`) and at most `qm = |S|` keys on `P` (`qInv_qkeys_le`); and a
  set `S` of `2⁶⁴` blocks exists (`exists_S`).
* **The bound fails there** (`inv_point_charge_fails`, applied in `fails_at`): the advantage is
  `≥ 2⁻⁶⁴ − 2⁻¹²⁸`, above the point-level form `(N + E_real[#keys read on P])/(|K| − qm)`.

The theorems' axioms are `propext`, `Classical.choice`, `Quot.sound` only (checked in a scratch
file). No `sorry`, no `axiom`.
-/

namespace VoleMole.Audit.ZKPointPerm

open VoleMole.Privacy VoleMole.ZK.IC
open VoleMole.ZK.Sim (Blk card_blk)

/-- **The hidden part reads the secret row only at `z₀`**, and no other row. -/
theorem phiInv_reads (z0 : Blk) (ρ ρ' : ℕ → Blk → Blk) (h : ρ 0 z0 = ρ' 0 z0) :
    phiInv z0 ρ = phiInv z0 ρ' := h

/-- **A set of `2⁶⁴` keys exists.** -/
theorem exists_S : ∃ S : Finset Blk, S.card = 2 ^ 64 := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Blk))
    (n := 2 ^ 64) (by rw [Finset.card_univ, card_blk]; norm_num)
  exact ⟨S, hS⟩

/-- **The point-level hop fails for permutation rows** at an explicit set of `2⁶⁴` keys. -/
theorem fails_at (x : ℕ → Blk) (z0 : Blk) :
    ∃ S : Finset Blk, S.card = 2 ^ 64 ∧
      (1 + exP (PCoins Blk 1 × (Blk → Equiv.Perm Blk)) (fun p => ((qkeys (fun z => z = z0)
          (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) (cf p.1.2) p.1.1)) p.2)).card : ℝ))) /
          ((2 : ℝ) ^ 128 - 1 * 2 ^ 64) <
        experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) -
          experPm x 1 {0} (phiInv z0) (fun y π => aInv S z0 y π) := by
  obtain ⟨S, hS⟩ := exists_S
  exact ⟨S, hS, inv_point_charge_fails x S hS z0⟩

end VoleMole.Audit.ZKPointPerm
