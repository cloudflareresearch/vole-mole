import VoleMole.Theft.JointTheft
import VoleMole.Theft.JointSumA
import VoleMole.Theft.JointNum

/-!
# The `iv` structure of the simulated theft game

`theft_joint_le` (`Theft/JointTheft.lean`) leaves `J`, a bound on the summed charges of the active
slots in the simulated game. `exU_sum_nZKA_le` (`Theft/JointSumA.lean`) bounds such a sum for views
whose `iv`s are the blocks of a uniform table at inputs `d` that do not read it (`IvsOf`), or
absent. Here this is set up for the simulated theft game:

* a simulated proof's `iv` is `H₄(iv_pre ‖ μ₁ ‖ 4)` (`ivA_simJ`), with `iv_pre` the simulation's
  coin (`outOf_ivPre`), `μ₁` read off `H₂⁰` (not `H₄`: `mu1_setH4`) and `H₄` the table of the extra
  table on these 49-byte inputs (`hbX_h4`);
* a refused slot `j` gets the `iv` `H₄(rsv j)` at a reserved 4-byte input (`ivR`, `rsvK`): it makes
  no proof and reads nothing, so any `iv` confines it, and with an `iv` it is no longer an
  "absent `iv`" that every other slot is charged for (**correction**: with no `iv`, `M` refused
  spends cost `2N·M·(w_E·4607 + w₅·624) ≈ 2⁻⁴⁵` at `N = 2³¹`);
* **`ivs_view`**: the view's `iv`s are `T(d j)` or absent, `T` the `H₄` table and `d` (`dIv`) a
  function of the rest of the tape (`splitT`);
* the absent `iv`s are failed simulations only (`ivAt_none`).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.Theft.Hit VoleMole.ZK.IC

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section H4

variable {L : ℕ}

/-- The extra table with another `H₄` table. -/
def setH4 (T : KL L → ZK.Sim.Bytes 16) (x : XR L) : XR L := (x.1, x.2.1, x.2.2.1, T, x.2.2.2.2)

lemma hbX_agreeOff_h4 (T T' : KL L → ZK.Sim.Bytes 16) (x : XR L) :
    (hbX (setH4 T x)).AgreeOff .h4 (hbX (setH4 T' x)) := by
  unfold hbX setH4
  simp only
  exact agreeOff_withTable (agreeOff_withTable (agreeOff_withTable
    (agreeOff_withTable_self _ _ _ _ _) _ _) _ _) _ _

/-- **`μ₁` does not read `H₄`.** -/
lemma mu1_setH4 (st : Statement) (T T' : KL L → ZK.Sim.Bytes 16) (x : XR L) :
    st.mu1 (hbX (setH4 T x)) = st.mu1 (hbX (setH4 T' x)) := by
  unfold Statement.mu1 mu
  rw [hbX_agreeOff_h4 T T' x .mu (by decide), hbX_agreeOff_h4 T T' x .muDelayed (by decide)]

lemma mu1_size' {Hs : Hashes} (hHs : HashesWF Hs) (st : Statement) : (st.mu1 Hs).size = 32 := by
  unfold Statement.mu1 mu
  split_ifs
  · exact hHs _ _
  · exact hHs _ _

/-- **`H₄` is the table**, on inputs of at most `L` bytes. -/
lemma hbX_h4 (x : XR L) {b : ByteArray} {k : KL L} (h : keyL L b = some k) :
    (hbX x).hash .h4 b = ba (x.2.2.2.1 k) := by
  have e := encL_of_keyL h
  subst e
  exact (Hashes.withTable_ne _ (.comb Arith.Ratatouille.uovM) .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ .h22 .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ .h21 .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h4 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl))))

/-- **A reserved `H₄` input of 4 bytes** for slot `j` (the empty input if `L < 4`). -/
def rsvK (j : ℕ) : KL L :=
  if h : 4 ≤ L then ⟨⟨4, by omega⟩, fun i => UInt8.ofNat (j / 256 ^ i.val)⟩ else ⟨0, fun i => i.elim0⟩

lemma rsvK_size (hL : 4 ≤ L) (j : ℕ) : (encL (rsvK (L := L) j)).size = 4 := by
  simp only [rsvK, hL, ↓reduceDIte, encL, size_ba]

lemma rsvK_inj (hL : 4 ≤ L) {i j : ℕ} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32)
    (h : rsvK (L := L) i = rsvK j) : i = j := by
  simp only [rsvK, hL, ↓reduceDIte, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  have h0 := congrArg UInt8.toNat (congrFun h 0)
  have h1 := congrArg UInt8.toNat (congrFun h 1)
  have h2 := congrArg UInt8.toNat (congrFun h 2)
  have h3 := congrArg UInt8.toNat (congrFun h 3)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    Nat.div_one] at h0 h1 h2 h3
  have h3' : (3 : Fin 4).val = 3 := rfl
  rw [h3'] at h3
  norm_num at h0 h1 h2 h3
  omega

/-- **The `iv` of a refused slot**: `H₄` at its reserved input. -/
def ivR (x : XR L) (j : ℕ) : Option ByteArray := some (ba (x.2.2.2.1 (rsvK j)))

end H4

/-! ## The `iv` of a simulated log entry -/

section Sim

variable {L : ℕ}

/-- The statement of an instance. -/
def stR : RI → Statement
  | .inl x => Privacy.Ratatouille.stI x
  | .inr x => Privacy.Ratatouille.stS x

/-- The simulation's `iv_pre` coin. -/
def coinIv : RI → SimCoins pI × SimCoins pS → ZK.Sim.Bytes 16
  | .inl _, c => c.1.1.1
  | .inr _, c => c.2.1.1

/-- The simulation fails (grinding finds no accepted counter). -/
def simFail : RI → SimCoins pI × SimCoins pS → Prop
  | .inl _, c => firstHit c.1.1.2.1 = none
  | .inr _, c => firstHit c.2.1.2.1 = none

instance (y : RI) (c : SimCoins pI × SimCoins pS) : Decidable (simFail y c) := by
  rcases y with y | y <;> exact inferInstanceAs (Decidable (_ = none))

/-- **The `H₄` input of a simulated proof**: `iv_pre ‖ μ₁ ‖ 4`. -/
noncomputable def inp4 (x : XR L) (y : RI) (c : SimCoins pI × SimCoins pS) : ByteArray :=
  (ba (coinIv y c) ++ (stR y).mu1 (hbX x)).push 4

lemma inp4_size (x : XR L) (y : RI) (c : SimCoins pI × SimCoins pS) : (inp4 x y c).size = 49 := by
  simp only [inp4, ByteArray.size_push, ByteArray.size_append, size_ba, mu1_size' (hbX_wf x)]

lemma inp4_setH4 (x : XR L) (y : RI) (c : SimCoins pI × SimCoins pS) :
    inp4 x y c = inp4 (setH4 (fun _ => 0) x) y c := by
  unfold inp4
  rw [show x = setH4 x.2.2.2.1 x from rfl, mu1_setH4 (stR y) x.2.2.2.1 (fun _ => 0) x]
  rfl

/-- **The `iv` of a simulated entry**: none if the simulation fails, else `H₄(iv_pre ‖ μ₁ ‖ 4)`. -/
lemma ivA_simJ (x : XR L) (j : ℕ) (y : RI) (c : SimCoins pI × SimCoins pS) :
    ivA x y (simJ (j, some y) c) = if simFail y c then none else some ((hbX x).hash .h4 (inp4 x y c)) := by
  rcases y with xI | xS
  · rw [simJ_inl]
    rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, δ⟩
    · have hs : simulate pI c.1 = .error "grinding failed" := by simp only [simulate, hf]
      simp [simI, φI, hs, vecOf, ivA, simFail, hf]
    · obtain ⟨b, hs⟩ : ∃ b, simulate pI c.1 = .ok b := ⟨_, by unfold simulate; rw [hf]⟩
      have hsz : b.size = Sizes.labelRows.issue := (simulate_ok_size hs).trans (by decide)
      obtain ⟨e1, e2⟩ := vecOf_ok_bOf hsz
      have hiv : (⟨pI, b⟩ : Proof).ivPre = ba c.1.1.1 :=
        outOf_ivPre (st := Privacy.Ratatouille.stI xI) (f := c.1.2)
          ((simulate_eq_outOf (Privacy.Ratatouille.stI xI) c.1.1 c.1.2).symm.trans hs)
      simp only [simI, φI, hs, e1, Option.map_some, ivA, e2, simFail, hf, reduceCtorEq,
        ↓reduceIte, Option.some.injEq]
      unfold ivOf inp4
      rw [hiv]
      rfl
  · rw [simJ_inr]
    rcases hf : firstHit c.2.1.2.1 with _ | ⟨ctr, δ⟩
    · have hs : simulate pS c.2 = .error "grinding failed" := by simp only [simulate, hf]
      simp [simS, φS, hs, vecOf, ivA, simFail, hf]
    · obtain ⟨b, hs⟩ : ∃ b, simulate pS c.2 = .ok b := ⟨_, by unfold simulate; rw [hf]⟩
      have hsz : b.size = Sizes.labelRows.spend := (simulate_ok_size hs).trans (by decide)
      obtain ⟨e1, e2⟩ := vecOf_ok_bOf hsz
      have hiv : (⟨pS, b⟩ : Proof).ivPre = ba c.2.1.1 :=
        outOf_ivPre (st := Privacy.Ratatouille.stS xS) (f := c.2.2)
          ((simulate_eq_outOf (Privacy.Ratatouille.stS xS) c.2.1 c.2.2).symm.trans hs)
      simp only [simS, φS, hs, e1, Option.map_some, ivA, e2, simFail, hf, reduceCtorEq,
        ↓reduceIte, Option.some.injEq]
      unfold ivOf inp4
      rw [hiv]
      rfl

end Sim

/-! ## The simulated log -/

section SimPre

variable {Ω O C S : Type*} (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S) (ω : Ω)
  (cs : ℕ → C)

lemma simPre_take : ∀ n j, j ≤ n → (simPre Sm pg ω cs n).1.take j = (simPre Sm pg ω cs j).1
  | 0, j, h => by obtain rfl : j = 0 := by omega
                  rfl
  | n + 1, j, h => by
    rcases Nat.lt_or_ge j (n + 1) with hj | hj
    · rw [simPre_succ_fst, List.take_append_of_le_length (by rw [simPre_length]; omega),
        simPre_take n j (by omega)]
    · obtain rfl : j = n + 1 := by omega
      rw [List.take_of_length_le (by rw [simPre_length])]

lemma simPre_getElem? : ∀ n j, j < n →
    (simPre Sm pg ω cs n).1[j]? = some (Sm ω (simPre Sm pg ω cs j).1 (cs j))
  | 0, j, h => by omega
  | n + 1, j, h => by
    rw [simPre_succ_fst]
    rcases Nat.lt_or_ge j n with hj | hj
    · rw [List.getElem?_append_left (by rw [simPre_length]; exact hj), simPre_getElem? n j hj]
    · obtain rfl : j = n := by omega
      rw [List.getElem?_append_right (by rw [simPre_length]), simPre_length, Nat.sub_self]
      rfl

end SimPre

/-! ## The view's `iv`s are blocks of the `H₄` table -/

section View

variable {U M L : ℕ}

/-- The extra table without `H₄`. -/
abbrev XRm (L : ℕ) := (KL L → ZK.Sim.Bytes 32) × (KL L → ZK.Sim.Bytes 32) ×
  (KL L → ZK.Sim.Bytes 32) × (KL L → ZK.Sim.Bytes 136) × (KL L → ZK.Sim.Bytes 56) ×
  (KL L → ZK.Sim.Bytes (16 * Arith.Ratatouille.uovM))

/-- The extra table from its other tables and an `H₄` table. -/
def joinX (m : XRm L) (T : KL L → ZK.Sim.Bytes 16) : XR L := (m.1, m.2.1, m.2.2.1, T, m.2.2.2)

/-- The theft game's tape (slots with `Bytes 16` real coins). -/
abbrev TapeJ (U M L : ℕ) :=
  (SecN U M × (Fin (U + M) → Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3)) × TabR L

/-- The tape without the `H₄` table. -/
abbrev RestJ (U M L : ℕ) :=
  (SecN U M × (Fin (U + M) → Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3)) ×
    (Tab2G pI × ((Tab5F × (Blk → Blk → Blk)) × XRm L))

/-- **The tape is the rest and the `H₄` table.** -/
def splitT : TapeJ U M L ≃ RestJ U M L × (KL L → ZK.Sim.Bytes 16) where
  toFun z := ((z.1, (z.2.1, (z.2.2.1, (z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.2)))),
    z.2.2.2.2.2.2.1)
  invFun y := (y.1.1, (y.1.2.1, (y.1.2.2.1, joinX y.1.2.2.2 y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

variable (A : ThiefN Sizes.labelRows U M Tab3 (TabR L))

/-- **The `H₄` input of slot `j`** in the simulated game, from the rest of the tape: the
simulation's input `iv_pre ‖ μ₁ ‖ 4` if the slot is active, its reserved input otherwise. -/
noncomputable def dIv (ω' : RestJ U M L) (j : Fin (U + M)) : KL L :=
  match xN A (pubOf ω'.1.1) (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) ω'.1.1 (tapeC ω'.1.2) j).1 with
  | none => rsvK j
  | some y => (keyL L (inp4 (joinX ω'.2.2.2 fun _ => 0) y (tapeC ω'.1.2 j))).getD (rsvK j)

/-- The view of the simulated game. -/
noncomputable abbrev viewJ (z : TapeJ U M L) :=
  viewN (C := SimCoins pI × SimCoins pS) (ρ := ZK.Sim.Bytes 16) (gP proveJ (xJ A) (wJ A))
    (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) (U + M) z

lemma viewJ_log (z : TapeJ U M L) :
    (viewJ A z).2.1 = (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) (U + M)).1 := by
  simp only [viewJ, viewN, Nat.sub_self, realFrom]

lemma viewJ_x (z : TapeJ U M L) : (viewJ A z).2.2.2.2.2 = z.2.2.2 := by
  simp only [viewJ, viewN]
  rw [show z.2 = atX (shOf z.2) z.2.2.2 from rfl, simPre_atX]
  rfl

/-- **The `iv` of slot `j` in the simulated game.** -/
lemma ivAt_view (z : TapeJ U M L) (j : Fin (U + M)) :
    ivAt (ivJ ivR) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1 j =
      match xN A (pubOf z.1.1) (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 with
      | none => ivR z.2.2.2 j
      | some y => if simFail y (tapeC z.1.2 j) then none
          else some ((hbX z.2.2.2).hash .h4 (inp4 z.2.2.2 y (tapeC z.1.2 j))) := by
  rw [viewJ_x, viewJ_log]
  unfold ivAt
  rw [simPre_getElem? _ _ _ _ _ _ j.isLt]
  simp only [simPre_take _ _ _ _ _ _ j.isLt.le]
  show ivJ ivR z.2.2.2 (xJ A z.1.1 _) (simJ (xJ A z.1.1 _) _) = _
  have e : xJ A z.1.1 (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 =
      ((j : ℕ), xN A (pubOf z.1.1)
        (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1) := by
    unfold xJ; rw [simPre_length]
  rw [e]
  generalize xN A (pubOf z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 = o
  cases o with
  | none => rfl
  | some y => exact ivA_simJ _ _ _ _

/-- **The simulated game's `iv`s are the `H₄` table's blocks at `dIv`, or absent**
(`L ≥ 49`: the simulations' inputs are short). -/
theorem ivs_view (hL : 49 ≤ L) (z : TapeJ U M L) :
    IvsOf (ivAt (ivJ ivR) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1)
      (fun j => (splitT z).2 (dIv A (splitT z).1 j)) := by
  intro j
  rw [ivAt_view]
  unfold dIv
  show _ ∨ _ = some (ba (z.2.2.2.2.2.2.1 (match xN A (pubOf z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 with
    | none => rsvK j
    | some y => (keyL L (inp4 (joinX (splitT z).1.2.2.2 fun _ => 0) y (tapeC z.1.2 j))).getD
        (rsvK j))))
  generalize xN A (pubOf z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 = o
  cases o with
  | none => exact Or.inr rfl
  | some y =>
    simp only
    split_ifs
    · exact Or.inl rfl
    · right
      obtain ⟨k, hk⟩ := exists_encL (L := L) (b := inp4 z.2.2.2 y (tapeC z.1.2 j))
        (by rw [inp4_size]; exact hL)
      have hkey : keyL L (inp4 z.2.2.2 y (tapeC z.1.2 j)) = some k := by rw [← hk, keyL_encL]
      rw [hbX_h4 _ hkey]
      have e : inp4 (joinX (splitT z).1.2.2.2 fun _ => 0) y (tapeC z.1.2 j) =
          inp4 z.2.2.2 y (tapeC z.1.2 j) := (inp4_setH4 _ _ _).symm
      rw [e, hkey]
      rfl

end View

/-! ## Expectations of coordinates -/

section Coord

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma exP_prod_snd' [Nonempty α] (f : β → ℝ) : exP (α × β) (fun p => f p.2) = exP β f := by
  rw [exP_prod]; exact exP_const (exP β f)

/-- **The expectation of a function of one coordinate of a tape.** -/
lemma exP_coord {N : ℕ} [Nonempty α] [Nonempty β] [Nonempty γ] (j : Fin N) (F : β → ℝ) :
    exP ((α × (Fin N → β)) × γ) (fun z => F (z.1.2 j)) = exP β F := by
  rw [exP_prod_fst (fun a : α × (Fin N → β) => F (a.2 j)),
    exP_prod_snd' (fun τ : Fin N → β => F (τ j))]
  classical
  rw [← exP_equiv (Equiv.funSplitAt j β).symm (fun τ => F (τ j))]
  have e0 : ∀ (b : β) (r : {k // k ≠ j} → β), (Equiv.funSplitAt j β).symm (b, r) j = b :=
    fun b r => by simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [e0]
  exact exP_prod_fst (β := {k // k ≠ j} → β) F

/-- **The expectation of a function of two coordinates of a tape.** -/
lemma exP_coord2 {N : ℕ} [Nonempty α] [Nonempty β] [Nonempty γ] {i j : Fin N} (hij : i ≠ j)
    (F : β → β → ℝ) {c : ℝ} (hF : ∀ b, exP β (fun b' => F b' b) ≤ c) :
    exP ((α × (Fin N → β)) × γ) (fun z => F (z.1.2 i) (z.1.2 j)) ≤ c := by
  rw [exP_prod_fst (fun a : α × (Fin N → β) => F (a.2 i) (a.2 j)),
    exP_prod_snd' (fun τ : Fin N → β => F (τ i) (τ j))]
  classical
  rw [← exP_equiv (Equiv.funSplitAt i β).symm (fun τ => F (τ i) (τ j)), exP_prod]
  have e : ∀ (b : β) (r : {k // k ≠ i} → β), (Equiv.funSplitAt i β).symm (b, r) j = r ⟨j, hij.symm⟩ :=
    fun b r => by simp [Equiv.funSplitAt, Equiv.piSplitAt, hij.symm]
  have e0 : ∀ (b : β) (r : {k // k ≠ i} → β), (Equiv.funSplitAt i β).symm (b, r) i = b :=
    fun b r => by simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [e, e0]
  calc exP β (fun b => exP ({k // k ≠ i} → β) (fun r => F b (r ⟨j, hij.symm⟩)))
      = exP ({k // k ≠ i} → β) (fun r => exP β (fun b => F b (r ⟨j, hij.symm⟩))) := by
        simp only [exP]
        rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
        ring
    _ ≤ exP ({k // k ≠ i} → β) (fun _ => c) := exP_mono fun r => hF _
    _ = c := exP_const c

/-- A uniform `16`-byte coin equals a given value with probability `2⁻¹²⁸`. -/
lemma exP_eq_bytes (v : ZK.Sim.Bytes 16) :
    exP (ZK.Sim.Bytes 16) (fun u => if u = v then 1 else 0) = 1 / 2 ^ 128 := by
  classical
  simp only [exP, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show Fintype.card (ZK.Sim.Bytes 16) = 2 ^ 128 from card_blk]
  norm_num

end Coord

/-! ## Collisions of the `H₄` inputs -/

section Dup

variable {U M L : ℕ}

/-- The two `iv_pre` coins of a slot. -/
def coin1 (b : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3) : ZK.Sim.Bytes 16 :=
  b.1.2.1.1.1
def coin2 (b : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3) : ZK.Sim.Bytes 16 :=
  b.1.2.2.1.1

/-- **A slot's coin equals a given value with probability `2⁻¹²⁸`.** -/
lemma exP_coin1_eq (v : ZK.Sim.Bytes 16) :
    exP (Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3)
      (fun b => if coin1 b = v then 1 else 0) = 1 / 2 ^ 128 := by
  classical
  unfold coin1
  rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins pI × SimCoins pS) =>
      if a.2.1.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins pI × SimCoins pS => if c.1.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : SimCoins pI => if c.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : Shared => if c.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun u : ZK.Sim.Bytes 16 => if u = v then (1 : ℝ) else 0)]
  exact exP_eq_bytes v

lemma exP_coin2_eq (v : ZK.Sim.Bytes 16) :
    exP (Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3)
      (fun b => if coin2 b = v then 1 else 0) = 1 / 2 ^ 128 := by
  classical
  unfold coin2
  rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins pI × SimCoins pS) =>
      if a.2.2.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins pI × SimCoins pS => if c.2.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins pS => if c.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : Shared => if c.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun u : ZK.Sim.Bytes 16 => if u = v then (1 : ℝ) else 0)]
  exact exP_eq_bytes v

/-- The coin of a statement's simulation is one of the slot's two coins. -/
lemma coinIv_mem (y : RI) (b : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3) :
    coinIv y b.1.2 = coin1 b ∨ coinIv y b.1.2 = coin2 b := by
  rcases y with y | y
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Equal `H₄` inputs have equal coins. -/
lemma coin_of_inp4 {x x' : XR L} {y y' : RI} {c c' : SimCoins pI × SimCoins pS}
    (h : inp4 x y c = inp4 x' y' c') : coinIv y c = coinIv y' c' := by
  funext i
  have hi := i.isLt
  have s1 : ∀ (u : ZK.Sim.Bytes 16) (m : ByteArray), i.val < (ba u ++ m).size := fun u m => by
    rw [ByteArray.size_append, size_ba]; omega
  have key : ∀ (u : ZK.Sim.Bytes 16) (m : ByteArray), ((ba u ++ m).push 4).get! i = u i := by
    intro u m
    rw [get!_push]
    simp only [s1 u m, ↓reduceIte]
    rw [get!_append_left (by rw [size_ba]; exact hi), get!_ba _ hi]
  have := congrArg (fun b : ByteArray => b.get! i) h
  simp only [inp4, key] at this
  exact this

variable (A : ThiefN Sizes.labelRows U M Tab3 (TabR L))

/-- **A collision of the `H₄` inputs of two slots is a collision of their coins** (or none). -/
lemma dIv_eq (hL : 49 ≤ L) (hN : U + M ≤ 2 ^ 32) (ω' : RestJ U M L) {i j : Fin (U + M)}
    (hij : i ≠ j) (h : dIv A ω' i = dIv A ω' j) :
    (coin1 (ω'.1.2 i) = coin1 (ω'.1.2 j) ∨ coin1 (ω'.1.2 i) = coin2 (ω'.1.2 j)) ∨
      (coin2 (ω'.1.2 i) = coin1 (ω'.1.2 j) ∨ coin2 (ω'.1.2 i) = coin2 (ω'.1.2 j)) := by
  have hL4 : 4 ≤ L := by omega
  have hkey : ∀ (y : RI) (k : Fin (U + M)), ∃ a, keyL L (inp4 (joinX ω'.2.2.2 fun _ => 0) y
      (tapeC ω'.1.2 k)) = some a ∧ (encL a).size = 49 := fun y k => by
    obtain ⟨a, ha⟩ := exists_encL (L := L) (b := inp4 (joinX ω'.2.2.2 fun _ => 0) y (tapeC ω'.1.2 k))
      (by rw [inp4_size]; exact hL)
    exact ⟨a, by rw [← ha, keyL_encL], by rw [ha, inp4_size]⟩
  have hne : ∀ (a : KL L) (k : ℕ), (encL a).size = 49 → a ≠ rsvK k := fun a k ha e => by
    have := rsvK_size hL4 k
    rw [← e, ha] at this
    omega
  have hti : tapeC ω'.1.2 i = (ω'.1.2 i).1.2 := extN_val _ i
  have htj : tapeC ω'.1.2 j = (ω'.1.2 j).1.2 := extN_val _ j
  unfold dIv at h
  generalize xN A (pubOf ω'.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) ω'.1.1 (tapeC ω'.1.2) i).1 = oi at h
  generalize xN A (pubOf ω'.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) ω'.1.1 (tapeC ω'.1.2) j).1 = oj at h
  rcases oi with _ | yi <;> rcases oj with _ | yj
  · exact absurd (Fin.ext (rsvK_inj hL4 (by omega) (by omega) h)) hij
  · obtain ⟨a, ha, hs⟩ := hkey yj j
    simp only [ha, Option.getD_some] at h
    exact absurd h.symm (hne a i hs)
  · obtain ⟨a, ha, hs⟩ := hkey yi i
    simp only [ha, Option.getD_some] at h
    exact absurd h (hne a j hs)
  · obtain ⟨a, ha, -⟩ := hkey yi i
    obtain ⟨b, hb, -⟩ := hkey yj j
    simp only [ha, hb, Option.getD_some] at h
    subst h
    have e := coin_of_inp4 ((encL_of_keyL ha).symm.trans (encL_of_keyL hb))
    rw [hti, htj] at e
    rcases coinIv_mem yi (ω'.1.2 i) with h1 | h1 <;> rcases coinIv_mem yj (ω'.1.2 j) with h2 | h2
    · exact Or.inl (Or.inl (h1.symm.trans (e.trans h2)))
    · exact Or.inl (Or.inr (h1.symm.trans (e.trans h2)))
    · exact Or.inr (Or.inl (h1.symm.trans (e.trans h2)))
    · exact Or.inr (Or.inr (h1.symm.trans (e.trans h2)))

/-- **`E[#dupPairs] ≤ 4·N²·2⁻¹²⁸`**: two slots' `H₄` inputs collide only if their uniform
`iv_pre` coins do. -/
theorem exP_dupPairs_le (hL : 49 ≤ L) (hN : U + M ≤ 2 ^ 32) :
    exP (RestJ U M L) (fun ω' => ((dupPairs (dIv A ω')).card : ℝ)) ≤
      4 * ((U + M : ℕ) : ℝ) ^ 2 / 2 ^ 128 := by
  classical
  let C : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3 →
      Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pS) Tab3 → ℝ := fun a b =>
    (if coin1 a = coin1 b then 1 else 0) + (if coin1 a = coin2 b then 1 else 0) +
      ((if coin2 a = coin1 b then 1 else 0) + (if coin2 a = coin2 b then 1 else 0))
  have hC0 : ∀ a b, 0 ≤ C a b := fun a b => by simp only [C]; positivity
  have hpt : ∀ ω' : RestJ U M L, ((dupPairs (dIv A ω')).card : ℝ) ≤
      ∑ ij : Fin (U + M) × Fin (U + M), if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2) else 0 := by
    intro ω'
    unfold dupPairs
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_le_sum fun ij _ => ?_
    by_cases hlt : ij.1 < ij.2
    · simp only [hlt, true_and, ↓reduceIte]
      split_ifs with he
      · have hd := dIv_eq A hL hN ω' (ne_of_lt hlt) he
        simp only [C]
        rcases hd with (h | h) | (h | h) <;> simp only [h, ↓reduceIte] <;>
          split_ifs <;> norm_num
      · simp only [Nat.cast_zero]; exact hC0 _ _
    · simp [hlt]
  refine (exP_mono hpt).trans ?_
  rw [show (fun ω' : RestJ U M L => ∑ ij : Fin (U + M) × Fin (U + M),
      if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2) else 0) =
      fun ω' => ∑ ij : Fin (U + M) × Fin (U + M), (if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2)
        else 0) from rfl]
  have hsum : exP (RestJ U M L) (fun ω' => ∑ ij : Fin (U + M) × Fin (U + M),
      if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2) else 0) =
      ∑ ij : Fin (U + M) × Fin (U + M), exP (RestJ U M L) (fun ω' =>
        if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2) else 0) := by
    simp only [exP]
    rw [← Finset.sum_div, Finset.sum_comm]
  rw [hsum]
  have hone : ∀ ij : Fin (U + M) × Fin (U + M), exP (RestJ U M L) (fun ω' =>
      if ij.1 < ij.2 then C (ω'.1.2 ij.1) (ω'.1.2 ij.2) else 0) ≤ 4 / 2 ^ 128 := by
    intro ij
    by_cases hlt : ij.1 < ij.2
    · simp only [hlt, ↓reduceIte]
      refine exP_coord2 (ne_of_lt hlt) C fun b => ?_
      simp only [C]
      rw [exP_add, exP_add, exP_add]
      have e1 := exP_coin1_eq (coin1 b)
      have e2 := exP_coin1_eq (coin2 b)
      have e3 := exP_coin2_eq (coin1 b)
      have e4 := exP_coin2_eq (coin2 b)
      linarith
    · simp only [hlt, ↓reduceIte, exP_const]
      positivity
  refine (Finset.sum_le_sum fun ij _ => hone ij).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Dup

end Ratatouille

end VoleMole.Theft
