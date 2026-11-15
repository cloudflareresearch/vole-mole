import VoleMole.Theft.JointUnbInst
import VoleMole.Theft.JointIv

/-!
# The `iv` structure of the simulated unbound game, and `J`

`nmU_joint_le` (`Theft/JointUnbInst.lean`) leaves `J`, a bound on the summed charges of the active
slots in the simulated game. As `Theft/JointIv.lean` does for Ratatouille's theft game, it is
bounded by `exU_sum_nZKA_le` (`Theft/JointSumA.lean`) for views whose `iv`s are blocks of the `H₄`
table at inputs that do not read it:

* (any `M`) `setH4X`, `mu1_setH4X`, `hbX_h4X`: `μ₁` does not read `H₄`, and `H₄` is the extra
  table's on inputs of at most `L` bytes; **`ivRX`**: a refused slot `j` gets the `iv`
  `H₄(rsv j)` at a reserved 4-byte input (`rsvK`), as Ratatouille's `ivR`;
* (any parameters) `coinA`, `coinB`, `exP_coinA_eq`, `exP_coinB_eq`: a slot's two `iv_pre` coins
  are uniform; `failSG`, `exP_failSG`: a slot's two simulations fail with probability
  `≤ 2·pFail`;
* `ivA_simJ`: a simulated proof's `iv` is `H₄(iv_pre ‖ μ₁ ‖ 4)` (none if the simulation fails);
* **`ivs_view`**: the simulated game's `iv`s are `T(d j)` or absent, `T` the `H₄` table and `d`
  (`dIv`) a function of the rest of the tape (`splitT`);
* **`exP_dupPairs_le`**: `E[#dupPairs] ≤ 4N²·2⁻¹²⁸`; **`exU_nNone_le`**: the absent `iv`s are
  failed simulations, `E[#absent] ≤ 2N·pFail`;
* **`nmU_J_le`**: `J` for the simulated unbound game.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.Theft.Hit VoleMole.ZK.IC

open VoleMole.Theft.Ratatouille (rsvK rsvK_size rsvK_inj mu1_size' failG pFail failG_nonneg
  exP_prod_snd' exP_coord exP_coord2 exP_eq_bytes simPre_take simPre_getElem?)

/-! ## `H₄` of an extra table, for any `M` -/

section H4X

variable {L M : ℕ}

/-- The extra table with another `H₄` table. -/
def setH4X (T : KL L → ZK.Sim.Bytes 16) (x : XTab L M) : XTab L M :=
  (x.1, x.2.1, x.2.2.1, T, x.2.2.2.2)

lemma hbX_agreeOff_h4X (T T' : KL L → ZK.Sim.Bytes 16) (x : XTab L M) :
    (hbX (setH4X T x)).AgreeOff .h4 (hbX (setH4X T' x)) := by
  unfold hbX setH4X
  simp only
  exact agreeOff_withTable (agreeOff_withTable (agreeOff_withTable
    (agreeOff_withTable_self _ _ _ _ _) _ _) _ _) _ _

/-- **`μ₁` does not read `H₄`.** -/
lemma mu1_setH4X (st : Statement) (T T' : KL L → ZK.Sim.Bytes 16) (x : XTab L M) :
    st.mu1 (hbX (setH4X T x)) = st.mu1 (hbX (setH4X T' x)) := by
  unfold Statement.mu1 mu
  rw [hbX_agreeOff_h4X T T' x .mu (by decide), hbX_agreeOff_h4X T T' x .muDelayed (by decide)]

/-- **`H₄` is the table**, on inputs of at most `L` bytes. -/
lemma hbX_h4X (x : XTab L M) {b : ByteArray} {k : KL L} (h : keyL L b = some k) :
    (hbX x).hash .h4 b = ba (x.2.2.2.1 k) := by
  have e := encL_of_keyL h
  subst e
  exact (Hashes.withTable_ne _ (.comb M) .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ .h22 .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ .h21 .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h4 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl))))

/-- **The `iv` of a refused slot**: `H₄` at its reserved input. -/
def ivRX (x : XTab L M) (j : ℕ) : Option ByteArray := some (ba (x.2.2.2.1 (rsvK j)))

end H4X

/-! ## A slot's coins, for any parameters -/

section CoinsG

variable {p₁ p₂ : Params}

/-- The two `iv_pre` coins of a slot. -/
def coinA (b : Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3) : ZK.Sim.Bytes 16 :=
  b.1.2.1.1.1
def coinB (b : Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3) : ZK.Sim.Bytes 16 :=
  b.1.2.2.1.1

/-- **A slot's first coin equals a given value with probability `2⁻¹²⁸`.** -/
lemma exP_coinA_eq (v : ZK.Sim.Bytes 16) :
    exP (Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3)
      (fun b => if coinA b = v then 1 else 0) = 1 / 2 ^ 128 := by
  classical
  unfold coinA
  rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins p₁ × SimCoins p₂) =>
      if a.2.1.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins p₁ × SimCoins p₂ => if c.1.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : SimCoins p₁ => if c.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : Shared => if c.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun u : ZK.Sim.Bytes 16 => if u = v then (1 : ℝ) else 0)]
  exact exP_eq_bytes v

/-- **A slot's second coin equals a given value with probability `2⁻¹²⁸`.** -/
lemma exP_coinB_eq (v : ZK.Sim.Bytes 16) :
    exP (Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3)
      (fun b => if coinB b = v then 1 else 0) = 1 / 2 ^ 128 := by
  classical
  unfold coinB
  rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins p₁ × SimCoins p₂) =>
      if a.2.2.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins p₁ × SimCoins p₂ => if c.2.1.1 = v then (1 : ℝ) else 0),
    exP_prod_snd' (fun c : SimCoins p₂ => if c.1.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun c : Shared => if c.1 = v then (1 : ℝ) else 0),
    exP_prod_fst (fun u : ZK.Sim.Bytes 16 => if u = v then (1 : ℝ) else 0)]
  exact exP_eq_bytes v

/-- A slot's two simulations' grinding failures. -/
noncomputable def failSG (b : Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3) : ℝ :=
  failG b.1.2.1.1.2.1 + failG b.1.2.2.1.2.1

lemma failSG_nonneg (b : Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3) :
    0 ≤ failSG b :=
  add_nonneg (failG_nonneg _) (failG_nonneg _)

/-- **A slot fails with probability at most `2·pFail`.** -/
lemma exP_failSG :
    exP (Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3) failSG = 2 * pFail := by
  unfold failSG
  rw [exP_add]
  have h1 : exP (Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3)
      (fun b => failG b.1.2.1.1.2.1) = pFail := by
    rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins p₁ × SimCoins p₂) => failG a.2.1.1.2.1),
      exP_prod_snd' (fun c : SimCoins p₁ × SimCoins p₂ => failG c.1.1.2.1),
      exP_prod_fst (fun c : SimCoins p₁ => failG c.1.2.1),
      exP_prod_fst (fun c : Shared => failG c.2.1),
      exP_prod_snd' (fun c : Grind × (Fin BAVC.tau → ZK.Sim.Bytes 32) × (Fin 105 → ZK.Sim.Bytes 16) =>
        failG c.1),
      exP_prod_fst failG]
    rfl
  have h2 : exP (Slot (ZK.Sim.Bytes 16) (SimCoins p₁ × SimCoins p₂) Tab3)
      (fun b => failG b.1.2.2.1.2.1) = pFail := by
    rw [exP_prod_fst (fun a : ZK.Sim.Bytes 16 × (SimCoins p₁ × SimCoins p₂) => failG a.2.2.1.2.1),
      exP_prod_snd' (fun c : SimCoins p₁ × SimCoins p₂ => failG c.2.1.2.1),
      exP_prod_snd' (fun c : SimCoins p₂ => failG c.1.2.1),
      exP_prod_fst (fun c : Shared => failG c.2.1),
      exP_prod_snd' (fun c : Grind × (Fin BAVC.tau → ZK.Sim.Bytes 32) × (Fin 105 → ZK.Sim.Bytes 16) =>
        failG c.1),
      exP_prod_fst failG]
    rfl
  rw [h1, h2]; ring

end CoinsG

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## The `iv` of a simulated log entry -/

section Sim

variable {L : ℕ}

/-- The statement of an instance. -/
def stU : UI → Statement
  | .inl x => Privacy.MoussakaUnbound.stI x
  | .inr x => Privacy.MoussakaUnbound.stR x

/-- The simulation's `iv_pre` coin. -/
def coinIv : UI → SimCoins pI × SimCoins pR → ZK.Sim.Bytes 16
  | .inl _, c => c.1.1.1
  | .inr _, c => c.2.1.1

/-- The simulation fails (grinding finds no accepted counter). -/
def simFail : UI → SimCoins pI × SimCoins pR → Prop
  | .inl _, c => firstHit c.1.1.2.1 = none
  | .inr _, c => firstHit c.2.1.2.1 = none

instance (y : UI) (c : SimCoins pI × SimCoins pR) : Decidable (simFail y c) := by
  rcases y with y | y <;> exact inferInstanceAs (Decidable (_ = none))

/-- **The `H₄` input of a simulated proof**: `iv_pre ‖ μ₁ ‖ 4`. -/
noncomputable def inp4 (x : XU L) (y : UI) (c : SimCoins pI × SimCoins pR) : ByteArray :=
  (ba (coinIv y c) ++ (stU y).mu1 (hbX x)).push 4

lemma inp4_size (x : XU L) (y : UI) (c : SimCoins pI × SimCoins pR) : (inp4 x y c).size = 49 := by
  simp only [inp4, ByteArray.size_push, ByteArray.size_append, size_ba, mu1_size' (hbX_wf x)]

lemma inp4_setH4 (x : XU L) (y : UI) (c : SimCoins pI × SimCoins pR) :
    inp4 x y c = inp4 (setH4X (fun _ => 0) x) y c := by
  unfold inp4
  rw [show x = setH4X x.2.2.2.1 x from rfl, mu1_setH4X (stU y) x.2.2.2.1 (fun _ => 0) x]
  rfl

/-- **The `iv` of a simulated entry**: none if the simulation fails, else `H₄(iv_pre ‖ μ₁ ‖ 4)`. -/
lemma ivA_simJ (x : XU L) (j : ℕ) (y : UI) (c : SimCoins pI × SimCoins pR) :
    ivA x y (simJ (j, some y) c) =
      if simFail y c then none else some ((hbX x).hash .h4 (inp4 x y c)) := by
  rcases y with xI | xR
  · rw [simJ_inl]
    rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, δ⟩
    · have hs : simulate pI c.1 = .error "grinding failed" := by simp only [simulate, hf]
      have h0 : ¬ (0 = pI.proofBytes) := fun h => pI_proofBytes_pos h.symm
      simp only [simI, φI, hs, ivA, Except.toOption, Option.getD_none, length_toL,
        ByteArray.size_empty, h0, ↓reduceIte, simFail, hf]
    · obtain ⟨b, hs⟩ : ∃ b, simulate pI c.1 = .ok b := ⟨_, by unfold simulate; rw [hf]⟩
      have hsz : b.size = pI.proofBytes := simulate_ok_size hs
      have hiv : (⟨pI, b⟩ : Proof).ivPre = ba c.1.1.1 :=
        outOf_ivPre (st := Privacy.MoussakaUnbound.stI xI) (f := c.1.2)
          ((simulate_eq_outOf (Privacy.MoussakaUnbound.stI xI) c.1.1 c.1.2).symm.trans hs)
      simp only [simI, φI, hs, ivA, Except.toOption, Option.getD_some, length_toL, hsz,
        toBA_toL', ↓reduceIte, simFail, hf, reduceCtorEq, Option.some.injEq]
      unfold ivOf inp4
      rw [hiv]
      rfl
  · rw [simJ_inr]
    rcases hf : firstHit c.2.1.2.1 with _ | ⟨ctr, δ⟩
    · have hs : simulate pR c.2 = .error "grinding failed" := by simp only [simulate, hf]
      have h0 : ¬ (0 = pR.proofBytes) := fun h => pR_proofBytes_pos h.symm
      simp only [simR, φR, hs, ivA, Except.toOption, Option.getD_none, length_toL,
        ByteArray.size_empty, h0, ↓reduceIte, simFail, hf]
    · obtain ⟨b, hs⟩ : ∃ b, simulate pR c.2 = .ok b := ⟨_, by unfold simulate; rw [hf]⟩
      have hsz : b.size = pR.proofBytes := simulate_ok_size hs
      have hiv : (⟨pR, b⟩ : Proof).ivPre = ba c.2.1.1 :=
        outOf_ivPre (st := Privacy.MoussakaUnbound.stR xR) (f := c.2.2)
          ((simulate_eq_outOf (Privacy.MoussakaUnbound.stR xR) c.2.1 c.2.2).symm.trans hs)
      simp only [simR, φR, hs, ivA, Except.toOption, Option.getD_some, length_toL, hsz,
        toBA_toL', ↓reduceIte, simFail, hf, reduceCtorEq, Option.some.injEq]
      unfold ivOf inp4
      rw [hiv]
      rfl

end Sim

/-! ## The view's `iv`s are blocks of the `H₄` table -/

section View

variable {U M L : ℕ}

/-- The extra table without `H₄`. -/
abbrev XUm (L : ℕ) := (KL L → ZK.Sim.Bytes 32) × (KL L → ZK.Sim.Bytes 32) ×
  (KL L → ZK.Sim.Bytes 32) × (KL L → ZK.Sim.Bytes 136) × (KL L → ZK.Sim.Bytes 56) ×
  (KL L → ZK.Sim.Bytes (16 * Arith.Moussaka.M))

/-- The extra table from its other tables and an `H₄` table. -/
def joinX (m : XUm L) (T : KL L → ZK.Sim.Bytes 16) : XU L := (m.1, m.2.1, m.2.2.1, T, m.2.2.2)

/-- The game's tape (slots with `Bytes 16` real coins). -/
abbrev TapeJ (U M L : ℕ) :=
  (SecN U × (Fin (U + M) → Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pR) Tab3)) × TabU L

/-- The tape without the `H₄` table. -/
abbrev RestJ (U M L : ℕ) :=
  (SecN U × (Fin (U + M) → Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pR) Tab3)) ×
    (Tab2G Privacy.Moussaka.pI × ((Tab5F × (Blk → Blk → Blk)) × XUm L))

/-- **The tape is the rest and the `H₄` table.** -/
def splitT : TapeJ U M L ≃ RestJ U M L × (KL L → ZK.Sim.Bytes 16) where
  toFun z := ((z.1, (z.2.1, (z.2.2.1, (z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.2)))),
    z.2.2.2.2.2.2.1)
  invFun y := (y.1.1, (y.1.2.1, (y.1.2.2.1, joinX y.1.2.2.2 y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

variable (A : ThiefN U M Tab3 (TabU L))

/-- **The `H₄` input of slot `j`** in the simulated game, from the rest of the tape: the
simulation's input `iv_pre ‖ μ₁ ‖ 4` if the slot is active, its reserved input otherwise. -/
noncomputable def dIv (ω' : RestJ U M L) (j : Fin (U + M)) : KL L :=
  match xN A (pubOf A ω'.1.1)
      (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) ω'.1.1 (tapeC ω'.1.2) j).1 with
  | none => rsvK j
  | some y => (keyL L (inp4 (joinX ω'.2.2.2 fun _ => 0) y (tapeC ω'.1.2 j))).getD (rsvK j)

/-- The view of the simulated game. -/
noncomputable abbrev viewJ (z : TapeJ U M L) :=
  VoleMole.Theft.viewN (C := SimCoins pI × SimCoins pR) (ρ := ZK.Sim.Bytes 16)
    (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) (U + M) z

lemma viewJ_log (z : TapeJ U M L) :
    (viewJ A z).2.1 =
      (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) (U + M)).1 := by
  simp only [viewJ, VoleMole.Theft.viewN, Nat.sub_self, realFrom]

lemma viewJ_x (z : TapeJ U M L) : (viewJ A z).2.2.2.2.2 = z.2.2.2 := by
  simp only [viewJ, VoleMole.Theft.viewN]
  rw [show z.2 = atX (shOf z.2) z.2.2.2 from rfl, simPre_atX]
  rfl

/-- **The `iv` of slot `j` in the simulated game.** -/
lemma ivAt_view (z : TapeJ U M L) (j : Fin (U + M)) :
    ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1 j =
      match xN A (pubOf A z.1.1)
          (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 with
      | none => ivRX z.2.2.2 j
      | some y => if simFail y (tapeC z.1.2 j) then none
          else some ((hbX z.2.2.2).hash .h4 (inp4 z.2.2.2 y (tapeC z.1.2 j))) := by
  rw [viewJ_x, viewJ_log]
  unfold ivAt
  rw [simPre_getElem? _ _ _ _ _ _ j.isLt]
  simp only [simPre_take _ _ _ _ _ _ j.isLt.le]
  show ivJ ivRX z.2.2.2 (xJ A z.1.1 _) (simJ (xJ A z.1.1 _) _) = _
  have e : xJ A z.1.1
      (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 =
      ((j : ℕ), xN A (pubOf A z.1.1)
        (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1) := by
    unfold xJ; rw [simPre_length]
  rw [e]
  generalize xN A (pubOf A z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 = o
  cases o with
  | none => rfl
  | some y => exact ivA_simJ _ _ _ _

/-- **The simulated game's `iv`s are the `H₄` table's blocks at `dIv`, or absent**
(`L ≥ 49`: the simulations' inputs are short). -/
theorem ivs_view (hL : 49 ≤ L) (z : TapeJ U M L) :
    IvsOf (ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1)
      (fun j => (splitT z).2 (dIv A (splitT z).1 j)) := by
  intro j
  rw [ivAt_view]
  unfold dIv
  show _ ∨ _ = some (ba (z.2.2.2.2.2.2.1 (match xN A (pubOf A z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 with
    | none => rsvK j
    | some y => (keyL L (inp4 (joinX (splitT z).1.2.2.2 fun _ => 0) y (tapeC z.1.2 j))).getD
        (rsvK j))))
  generalize xN A (pubOf A z.1.1)
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
      rw [hbX_h4X _ hkey]
      have e : inp4 (joinX (splitT z).1.2.2.2 fun _ => 0) y (tapeC z.1.2 j) =
          inp4 z.2.2.2 y (tapeC z.1.2 j) := (inp4_setH4 _ _ _).symm
      rw [e, hkey]
      rfl

end View

/-! ## Collisions of the `H₄` inputs -/

section Dup

variable {U M L : ℕ}

/-- The coin of a statement's simulation is one of the slot's two coins. -/
lemma coinIv_mem (y : UI) (b : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pR) Tab3) :
    coinIv y b.1.2 = coinA b ∨ coinIv y b.1.2 = coinB b := by
  rcases y with y | y
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Equal `H₄` inputs have equal coins. -/
lemma coin_of_inp4 {x x' : XU L} {y y' : UI} {c c' : SimCoins pI × SimCoins pR}
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

variable (A : ThiefN U M Tab3 (TabU L))

/-- **A collision of the `H₄` inputs of two slots is a collision of their coins** (or none). -/
lemma dIv_eq (hL : 49 ≤ L) (hN : U + M ≤ 2 ^ 32) (ω' : RestJ U M L) {i j : Fin (U + M)}
    (hij : i ≠ j) (h : dIv A ω' i = dIv A ω' j) :
    (coinA (ω'.1.2 i) = coinA (ω'.1.2 j) ∨ coinA (ω'.1.2 i) = coinB (ω'.1.2 j)) ∨
      (coinB (ω'.1.2 i) = coinA (ω'.1.2 j) ∨ coinB (ω'.1.2 i) = coinB (ω'.1.2 j)) := by
  have hL4 : 4 ≤ L := by omega
  have hkey : ∀ (y : UI) (k : Fin (U + M)), ∃ a, keyL L (inp4 (joinX ω'.2.2.2 fun _ => 0) y
      (tapeC ω'.1.2 k)) = some a ∧ (encL a).size = 49 := fun y k => by
    obtain ⟨a, ha⟩ := exists_encL (L := L)
      (b := inp4 (joinX ω'.2.2.2 fun _ => 0) y (tapeC ω'.1.2 k)) (by rw [inp4_size]; exact hL)
    exact ⟨a, by rw [← ha, keyL_encL], by rw [ha, inp4_size]⟩
  have hne : ∀ (a : KL L) (k : ℕ), (encL a).size = 49 → a ≠ rsvK k := fun a k ha e => by
    have := rsvK_size hL4 k
    rw [← e, ha] at this
    omega
  have hti : tapeC ω'.1.2 i = (ω'.1.2 i).1.2 := extN_val _ i
  have htj : tapeC ω'.1.2 j = (ω'.1.2 j).1.2 := extN_val _ j
  unfold dIv at h
  generalize xN A (pubOf A ω'.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) ω'.1.1 (tapeC ω'.1.2) i).1 = oi at h
  generalize xN A (pubOf A ω'.1.1)
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
  let C : Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pR) Tab3 →
      Slot (ZK.Sim.Bytes 16) (SimCoins pI × SimCoins pR) Tab3 → ℝ := fun a b =>
    (if coinA a = coinA b then 1 else 0) + (if coinA a = coinB b then 1 else 0) +
      ((if coinB a = coinA b then 1 else 0) + (if coinB a = coinB b then 1 else 0))
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
      have e1 := exP_coinA_eq (p₁ := pI) (p₂ := pR) (coinA b)
      have e2 := exP_coinA_eq (p₁ := pI) (p₂ := pR) (coinB b)
      have e3 := exP_coinB_eq (p₁ := pI) (p₂ := pR) (coinA b)
      have e4 := exP_coinB_eq (p₁ := pI) (p₂ := pR) (coinB b)
      linarith
    · simp only [hlt, ↓reduceIte, exP_const]
      positivity
  refine (Finset.sum_le_sum fun ij _ => hone ij).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Dup

/-! ## Failed simulations -/

section Fail

variable {U M L : ℕ} (A : ThiefN U M Tab3 (TabU L))

/-- **The absent `iv`s are failed simulations.** -/
lemma nNone_view_le (z : TapeJ U M L) :
    (nNone (ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1)
        (U + M) : ℝ) ≤ ∑ j : Fin (U + M), failSG (z.1.2 j) := by
  rw [← ind_none_sum, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
    (fun j => (((if ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1 j =
      none then 1 else 0 : ℕ)) : ℝ))]
  refine Finset.sum_le_sum fun j _ => ?_
  have hS : 0 ≤ failSG (z.1.2 j) := failSG_nonneg _
  rw [ivAt_view]
  have ht : tapeC z.1.2 j = (z.1.2 j).1.2 := extN_val _ j
  generalize xN A (pubOf A z.1.1)
    (simPre (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) z.1.1 (tapeC z.1.2) j).1 = o
  rcases o with _ | y
  · simp [ivRX, hS]
  · simp only
    by_cases hf : simFail y (tapeC z.1.2 j)
    · simp only [hf, ↓reduceIte, Nat.cast_one]
      rw [ht] at hf
      unfold failSG failG
      rcases y with y | y <;> simp only [simFail] at hf <;> simp only [hf, ↓reduceIte] <;>
        split_ifs <;> norm_num
    · simp only [hf, ↓reduceIte, reduceCtorEq, Nat.cast_zero]
      exact hS

/-- **`E[#absent ivs] ≤ 2N·pFail`.** -/
theorem exU_nNone_le :
    exU (TapeJ U M L) (fun z => (nNone (ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1
      (viewJ A z).2.1) (U + M) : ℝ)) ≤ 2 * (U + M : ℕ) * pFail := by
  refine (exP_mono (nNone_view_le A)).trans (le_of_eq ?_)
  have e : exP (TapeJ U M L) (fun z => ∑ j : Fin (U + M), failSG (z.1.2 j)) =
      ∑ j : Fin (U + M), exP (TapeJ U M L) (fun z => failSG (z.1.2 j)) := by
    simp only [exP]
    rw [← Finset.sum_div, Finset.sum_comm]
  rw [e]
  simp only [exP_coord _ failSG, exP_failSG, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **`E[#active slots with absent ivs] ≤ 2N·pFail`.** -/
theorem exU_nNoneA_le :
    exU (TapeJ U M L) (fun z => (nNoneA (actAt actJ (xJ A) (viewJ A z))
      (ivAt (ivJ ivRX) (xJ A) (viewJ A z).2.2.2.2.2 (viewJ A z).1 (viewJ A z).2.1) (U + M) : ℝ)) ≤
      2 * (U + M : ℕ) * pFail := by
  refine le_trans (exP_mono fun z => ?_) (exU_nNone_le A)
  unfold nNoneA nNone
  exact_mod_cast card_le_card fun j hj => by
    simp only [mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.2⟩

end Fail

/-! ## The summed charges of the simulated unbound game -/

section J

variable {U M L : ℕ} (A : ThiefN U M Tab3 (TabU L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds))

/-- **`J` for the simulated unbound game**: the summed charges of the active slots are at most the
game reader's budget once (`T₃ = q h3`, `c_E = a_E`, `a₅`), times the overlap
`N²·2⁻⁶⁴ + E[#dupPairs] ≤ N²·2⁻⁶⁴ + 4N²·2⁻¹²⁸`, plus the failed simulations
(`E[#absent ivs] ≤ 2N·pFail`). -/
theorem nmU_J_le (hL : 49 ≤ L) (hN : U + M ≤ 2 ^ 32) (w : Fin 3 → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∑ i ∈ range (U + M), ∑ k, w k * exU _ (fun z => (nZKA actJ (ivJ ivRX) (xJ A) (badGRd A hA)
        (max 312 624) (max 4607 4607) i k (viewJ A z) : ℝ)) ≤
      w 0 * q .h3 + w 1 * aEU (U + M) qE + w 2 * a5U (U + M) q +
        (w 1 * (aEU (U + M) qE + 2 * (max 4607 4607 : ℕ)) +
            w 2 * (a5U (U + M) q + 2 * (max 312 624 : ℕ))) *
          (((U + M : ℕ) : ℝ) ^ 2 / 2 ^ 64 + 4 * ((U + M : ℕ) : ℝ) ^ 2 / 2 ^ 128) +
        (w 1 * aEU (U + M) qE + w 2 * a5U (U + M) q) * (2 * (U + M : ℕ) * pFail) +
        2 * (U + M : ℕ) * (w 1 * (max 4607 4607 : ℕ) + w 2 * (max 312 624 : ℕ)) *
          (2 * (U + M : ℕ) * pFail) := by
  have hb := badGRd_bnd A hA
  rw [show (U + M) * 312 + q .h5 + 312 = a5U (U + M) q by unfold a5U; ring,
    show 2 * ((U + M) * verifyCellBound pR + qE) + 9215 = aEU (U + M) qE from rfl] at hb
  have h := exU_sum_nZKA_le actJ (ivJ ivRX) (xJ A) (badGRd A hA) hb
    (badGRd_T3 A hA) (badGRd_cls A hA) (max 312 624) (max 4607 4607) w hw (viewJ A) splitT
    (dIv A) (ivs_view A hL)
  refine h.trans ?_
  have hw1 := hw 1
  have hw2 := hw 2
  have hd := exP_dupPairs_le A hL hN
  have hA' := exU_nNoneA_le A
  have hn := exU_nNone_le A
  unfold aEU a5U at h ⊢
  gcongr

end J

end MoussakaUnbound

end VoleMole.Theft
