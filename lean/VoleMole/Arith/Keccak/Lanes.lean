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

@[simp] theorem lane_val (x y : Fin 5) : (lane x y).1 = x.1 + 5 * y.1 := rfl

theorem lane_eq_zero (x y : Fin 5) : lane x y = 0 ↔ x = 0 ∧ y = 0 := by
  simp only [lane, Fin.ext_iff, Fin.val_zero]; omega

theorem lane_val_eq_zero (x y : Fin 5) : (lane x y).1 = 0 ↔ x = 0 ∧ y = 0 := by
  simp only [lane, Fin.ext_iff, Fin.val_zero]; omega

theorem getLsbD_ite (c : Prop) [Decidable c] (u v : BitVec 32) (i : ℕ) :
    (if c then u else v).getLsbD i = if c then u.getLsbD i else v.getLsbD i := by
  split <;> rfl

theorem iota_bool (P Q : Prop) [Decidable P] [Decidable Q] (c e₁ e₂ : Bool) (he : e₁ = e₂) :
    (if P ∧ Q ∧ c = true then !e₁ else e₁) = (if P ∧ Q then xor e₂ c else e₂) := by
  subst he; by_cases hp : P <;> by_cases hq : Q <;> cases c <;> simp [hp, hq]

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
  simp only [round800, Vector.getElem_ofFn, Fin.getElem_fin, lx_lane, ly_lane, Fin.eta]
  simp only [lane_val_eq_zero, getLsbD_ite]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, getLsbD_rotateLeft_fin, getLsbD_rotateLeft_one, Fin.is_lt, decide_true,
    Bool.true_and]
  simp only [Bool.xor_true]
  exact iota_bool (x = 0) (y = 0) ((rc j).getLsbD z.1) _ _ rfl

theorem rounds_lanesBits (first num : ℕ) (a : Lanes) :
    rounds BitOps.bool first num (lanesBits a) = lanesBits (keccakRounds first num a) := by
  induction num generalizing first a with
  | zero => rfl
  | succ num ih => rw [rounds, round_lanesBits, ih, keccakRounds]

theorem lanesBits_toLanes (s : State) : lanesBits (toLanes s) = stateBits s := by
  apply vector_ext_idx
  intro x y z
  rw [lanesBits_idx]
  have hz := z.2
  have h100 : (32 * (5 * y.1 + x.1) + z.1) / 8 < 100 := by omega
  simp only [toLanes, stateBits, stateBit, Fin.getElem_fin, Vector.getElem_ofFn, idx, lane_val, h100,
    ↓reduceDIte]
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append]
  have e : (32 * (5 * y.1 + x.1) + z.1) / 8 = 4 * (x.1 + 5 * y.1) + z.1 / 8 := by omega
  have e' : (32 * (5 * y.1 + x.1) + z.1) % 8 = z.1 % 8 := by omega
  simp only [e, e']
  rcases (by omega : z.1 / 8 = 0 ∨ z.1 / 8 = 1 ∨ z.1 / 8 = 2 ∨ z.1 / 8 = 3) with h | h | h | h <;>
  · simp only [h]
    split_ifs <;> first | omega | (congr 1; omega)

theorem stateBits_fromLanes (a : Lanes) : stateBits (fromLanes a) = lanesBits a := by
  apply vector_ext_idx
  intro x y z
  rw [lanesBits_idx]
  have hz := z.2
  have h100 : (32 * (5 * y.1 + x.1) + z.1) / 8 < 100 := by omega
  simp only [fromLanes, stateBits, stateBit, Vector.getElem_ofFn, idx, h100, ↓reduceDIte,
    UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb']
  have h8 : (32 * (5 * y.1 + x.1) + z.1) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [h8, decide_true, Bool.true_and]
  have e : (32 * (5 * y.1 + x.1) + z.1) / 8 / 4 = (lane x y).1 := by simp only [lane]; omega
  have e' : 8 * ((32 * (5 * y.1 + x.1) + z.1) / 8 % 4) + (32 * (5 * y.1 + x.1) + z.1) % 8 = z.1 := by
    omega
  simp only [e, e', Fin.getElem_fin]

/-- Fact F3 at the byte level: `keccak_p800_rounds` on bits is the circuit's rounds. -/
theorem stateBits_keccakP800Rounds (first num : ℕ) (s : State) :
    stateBits (keccakP800Rounds first num s) = rounds BitOps.bool first num (stateBits s) := by
  rw [keccakP800Rounds, stateBits_fromLanes, ← rounds_lanesBits, lanesBits_toLanes]

end VoleMole.Arith.Keccak
