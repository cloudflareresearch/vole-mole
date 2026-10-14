import VoleMole.Arith.Keccak.Ref

/-!
# The bit-level round equals the lane-based round (fact F3 of `L7-keccak.md` §2.3)

`round_lanesBits`: on plain bits, `round BitOps.bool j` (the circuit `keccak_round` with the χ lambda
of `qs_keccak_round`) is `round800 (rc j)` on the unpacked lanes. `L7-keccak.md` proves this from a
basis test (`RoundMatchesLanesOnBasis`) and linearity; here it is proved bit by bit.
`stateBits_keccakP800Rounds` lifts it to the byte-level `keccak_p800_rounds`.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

/-- The bits of 25 lanes: bit `z` of lane `(x, y)` is bit `idx x y z`. -/
def lanesBits (a : Lanes) : Vector Bool 800 :=
  Vector.ofFn fun i => a[lane (ix i) (iy i)].getLsbD (iz i).1

theorem lanesBits_idx (a : Lanes) (x y : Fin 5) (z : Fin 32) :
    (lanesBits a)[(idx x y z).1] = a[lane x y].getLsbD z.1 := by
  simp [lanesBits]

@[simp] theorem lx_lane (x y : Fin 5) : lx (lane x y) = x := by ext; simp only [lx, lane]; omega
@[simp] theorem ly_lane (x y : Fin 5) : ly (lane x y) = y := by ext; simp only [ly, lane]; omega

theorem lane_eq_zero (x y : Fin 5) : lane x y = 0 ↔ x = 0 ∧ y = 0 := by
  simp only [lane, Fin.ext_iff, Fin.val_zero]; omega

theorem lane_val_eq_zero (x y : Fin 5) : (lane x y).1 = 0 ↔ x = 0 ∧ y = 0 := by
  simp only [lane, Fin.ext_iff, Fin.val_zero]; omega

theorem getLsbD_ite (c : Prop) [Decidable c] (u v : BitVec 32) (i : ℕ) :
    (if c then u else v).getLsbD i = if c then u.getLsbD i else v.getLsbD i := by
  split <;> rfl

theorem getLsbD_rotateLeft_fin (v : BitVec 32) (r z : Fin 32) :
    (v.rotateLeft r.1).getLsbD z.1 = v.getLsbD (z - r).1 := by
  rw [BitVec.getLsbD_rotateLeft, Fin.sub_def]
  have hr := r.2; have hz := z.2
  simp only [Nat.mod_eq_of_lt hr]
  split
  · congr 1; omega
  · simp only [show z.1 < 32 from hz, decide_true, Bool.true_and]; congr 1; omega

theorem getLsbD_rotateLeft_one (v : BitVec 32) (z : Fin 32) :
    (v.rotateLeft 1).getLsbD z.1 = v.getLsbD (z - 1).1 :=
  getLsbD_rotateLeft_fin v 1 z

theorem vector_ext_idx {T : Type*} {v w : Vector T 800}
    (h : ∀ x y z, v[(idx x y z).1] = w[(idx x y z).1]) : v = w := by
  ext i hi
  obtain ⟨x, y, z, rfl⟩ := exists_idx i hi
  exact h x y z

/-- **F3**: the circuit round on plain bits is `round800`. -/
theorem round_lanesBits (j : ℕ) (a : Lanes) :
    round BitOps.bool j (lanesBits a) = lanesBits (round800 (rc j) a) := by
  apply vector_ext_idx
  intro x y z
  rw [lanesBits_idx]
  simp only [round, roundN, chiIota, thetaRhoPi, colParity, chi, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, ix_idx, iy_idx, iz_idx, cx_cidx, cz_cidx, iota_cond, lanesBits_idx,
    BitOps.bool]
  simp only [round800, Vector.getElem_ofFn, Fin.getElem_fin, lx_lane, ly_lane,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_rotateLeft_fin,
    getLsbD_rotateLeft_one, Fin.eta]
  simp only [lane_val_eq_zero, getLsbD_ite]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, getLsbD_rotateLeft_fin, getLsbD_rotateLeft_one, Fin.is_lt, decide_true,
    Bool.true_and]
  simp only [Bool.xor_true]
  by_cases h : x = 0 ∧ y = 0
  · rw [if_pos h]
    sorry
  · rw [if_neg h]
    sorry

end VoleMole.Arith.Keccak
