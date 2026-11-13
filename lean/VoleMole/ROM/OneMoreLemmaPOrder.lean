import VoleMole.ROM.OneMoreLemmaPIdent

/-!
# Lemma P's ordering step: `E₁` at query time is the widest group at the end

`lean/docs/security/pomfrit.md` §5, §6.4 (gap G8). The reduction programs the target at `x` with
`E₁(x)` (`e1P`), computed from the log at `x`'s first target query: the first `H₂¹` preimage `x₁` of
`x`'s `chal1`, the trees with no committed dead leaf at `x₁`, and the widest prefix group of their
candidates computed from the committed keys. Lemma P's extraction (`MajorExtracted`) is about the
end of the run: the trees alive at the verifier's `H₂¹` input and the extractor's keys. This file
shows that they agree when `x₁` was queried before `x` (`e1P_eq_major`), and that otherwise the
answer at `x₁` hits the `chal1` field of an earlier marker query `H₃(x)` (`OrderHit`).

* Byte layout: `hash_to_target`'s input has `chal1` at bytes `39 … 175` and `d[0..45)` at bytes
  `239 … 284` for a 32-byte key digest (`xChal1_tgtIn`, `xDpre_tgtIn`).
* `preB_congr`: a candidate's prefix reads its first 360 bits.
* `tableOfLog_eq`: a table read off a consistent log is the table on the logged cells.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim

/-! ## Byte layout of `hash_to_target`'s input -/

section Bytes

lemma toL_extract_toBA (l : List UInt8) (a b : ℕ) :
    toL ((toBA l).extract a b) = (l.drop a).take (b - a) := by
  simp only [VoleMole.Privacy.toL_eq, ByteArray.data_extract, Array.toList_extract, toBA,
    List.extract_eq_take_drop]

lemma targetDst_length : (Spec.PomFRIT.targetDst).length = 7 := by decide

/-- **`chal1` in `hash_to_target`'s input**, for a 32-byte key digest. -/
lemma xChal1_tgtIn {pk : UovPk} {lr : Bool} {sg m c1 : ByteArray} (hd : pk.digest.size = 32)
    (hc : c1.size = 136) : xChal1 (tgtIn pk lr sg m c1) = c1 := by
  refine toL_injective ?_
  rw [xChal1, tgtIn, toL_extract_toBA]
  simp only [Spec.PomFRIT.targetInput, List.append_assoc]
  have h1 : (Spec.PomFRIT.targetDst ++ toL pk.digest).length = 39 := by
    rw [List.length_append, targetDst_length, VoleMole.Privacy.length_toL, hd]
  rw [← List.append_assoc Spec.PomFRIT.targetDst, List.drop_left' h1]
  rw [List.take_left' (by rw [VoleMole.Privacy.length_toL, hc])]

/-- **`d[0..45)` in `hash_to_target`'s input**, for a 32-byte key digest, a 136-byte `chal1` and a
proof of the right length. -/
lemma xDpre_tgtIn {pk : UovPk} {lr : Bool} {sg m c1 : ByteArray} (hd : pk.digest.size = 32)
    (hc : c1.size = 136)
    (hs : (sg.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes) :
    xDpre (tgtIn pk lr sg m c1) =
      (({ params := pomfritParams lr, bytes := sg.extract 0 (pomfritParams lr).proofBytes } :
        Proof).correction.extract 0 45) := by
  refine toL_injective ?_
  rw [xDpre, tgtIn, toL_extract_toBA]
  simp only [Spec.PomFRIT.targetInput, List.append_assoc]
  have h1 : (Spec.PomFRIT.targetDst ++ toL pk.digest ++ toL c1 ++
      toL ({ params := pomfritParams lr, bytes := sg.extract 0 (pomfritParams lr).proofBytes } :
        Proof).voleCheck).length = 239 := by
    simp only [List.length_append, targetDst_length, VoleMole.Privacy.length_toL, hd, hc,
      size_voleCheck hs]
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.drop_left' h1]
  rw [List.take_left' (by rw [VoleMole.Privacy.length_toL, size_correction hs])]

end Bytes

/-! ## A candidate's prefix reads its first 360 bits -/

section PreB

lemma witByte_congr {w w' : ℕ → Bool} {b : ℕ} (h : ∀ j < 8, w (8 * b + j) = w' (8 * b + j)) :
    Keccak.witByte w b = Keccak.witByte w' b := by
  unfold Keccak.witByte
  congr 3
  refine List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

/-- **`preB` reads the first 360 values.** -/
lemma preB_congr {w w' : ℕ → GF128} (h : ∀ n < 360, w n = w' n) : preB w = preB w' := by
  unfold preB bytesOf
  congr 1
  funext k
  refine witByte_congr fun j hj => ?_
  simp only [bitsOf]
  rw [h _ (by omega)]

end PreB

/-! ## A table read off a consistent log -/

lemma tableOfLog_eq {g : Table} {L : QueryLog spec} (hL : ∀ e ∈ L, e = ⟨e.1, g e.1⟩) {d : Dom}
    (hd : d ∈ L.map Sigma.fst) : tableOfLog L d = g d := by
  classical
  have hex : ∃ u, (⟨d, u⟩ : (t : Dom) × Ans t) ∈ L := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact ⟨e.2, he⟩
  unfold tableOfLog
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have h := hL _ hex.choose_spec
  exact eq_of_heq (Sigma.mk.inj h).2

lemma get!_extract_zero {b : ByteArray} {n k : ℕ} (hk : k < n) :
    (b.extract 0 n).get! k = b.get! k := by
  rw [Bridge.byteArray_get!_eq, Bridge.byteArray_get!_eq, ByteArray.data_extract,
    Array.getElem?_extract]
  by_cases hb : k < b.data.size
  · have hb' : k < b.size := hb
    simp [hk, hb']
  · simp only [Nat.zero_add]
    rw [Array.getElem?_eq_none (by omega)]
    split_ifs <;> simp

/-! ## The log at a target query -/

section Aux

lemma firstIn_append_of_some {k : Kind} {ok : ByteArray → Bool} {a w : ByteArray}
    {A B : QueryLog spec} (h : firstIn k ok a A = some w) : firstIn k ok a (A ++ B) = some w := by
  unfold firstIn at h ⊢
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.find?_append, he]
  rfl

variable (g : Table) (lr : Bool)

/-- The reduction's queries at `x`, when `x`'s `chal1` has the `H₂¹` preimage `x₁` in the log. -/
lemma axT_of_some {L : QueryLog specIC} {x x1 : ByteArray} (h : x1Of L x = some x1) :
    axT g lr L x = [⟨.inl (.h3, x), g (.h3, x)⟩, ⟨.inl muCell, g muCell⟩,
      ⟨.inl (ivCell lr x1 (g muCell).ba), g (ivCell lr x1 (g muCell).ba)⟩] := by
  unfold axT auxSpec
  rw [h]
  simp

/-- The reduction's queries at `x`, when `x`'s `chal1` has no `H₂¹` preimage in the log. -/
lemma axT_of_none {L : QueryLog specIC} {x : ByteArray} (h : x1Of L x = none) :
    axT g lr L x = [⟨.inl (.h3, x), g (.h3, x)⟩, ⟨.inl muCell, g muCell⟩] := by
  unfold axT auxSpec
  rw [h]
  simp

lemma hashEnt_consistent {E : CTable} {J : QueryLog specIC}
    (hJ : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩) : ∀ e ∈ hashEnt J, e = ⟨e.1, g e.1⟩ := by
  induction J with
  | nil => simp [hashEnt]
  | cons e J ih =>
    obtain ⟨t, u⟩ := e
    have ih' := ih fun e he => hJ e (List.mem_cons_of_mem _ he)
    cases t with
    | inl d =>
      intro e he
      simp only [hashEnt, List.mem_cons] at he
      rcases he with rfl | he
      · have h := hJ _ List.mem_cons_self
        have := eq_of_heq (Sigma.mk.inj h).2
        simp only at this ⊢
        rw [this]; rfl
      · exact ih' e he
    | inr x => exact ih'

lemma axT_consistent (L : QueryLog specIC) (x : ByteArray) :
    ∀ e ∈ hashEnt (axT g lr L x), e = ⟨e.1, g e.1⟩ := by
  cases h : x1Of L x with
  | some x1 => rw [axT_of_some g lr h]; simp [hashEnt]
  | none => rw [axT_of_none g lr h]; simp [hashEnt]

end Aux

/-! ## `iv` and `mu₁` of PomFRIT's statements -/

section Iv

lemma mu1_stE (lr : Bool) (Hs : Hashes) : (stE lr).mu1 Hs = Hs.hash .muDelayed muCell.2 := by
  simp only [Statement.mu1, stE, mu, muCell, ite_true]

lemma mu1_pomfritRedeemT (pk : UovPk) (hF : ByteArray → ByteArray) (b1 b2 : ByteArray) (lr : Bool)
    (Hs : Hashes) : (pomfritRedeemT pk hF b1 b2 lr).mu1 Hs = Hs.hash .muDelayed muCell.2 := by
  simp only [Statement.mu1, pomfritRedeemT, mu, muCell, ite_true]

lemma ivX_stE (pk : UovPk) (hF : ByteArray → ByteArray) (b1 b2 : ByteArray) (lr : Bool)
    (x1 : ByteArray) (g : Table) :
    ivX (stE lr) x1 g = ivX (pomfritRedeemT pk hF b1 b2 lr) x1 g := by
  simp only [ivX, mu1_stE, mu1_pomfritRedeemT]
  rfl

/-- **`iv` read off the log at a target query** is the table's, when the reduction's queries put
`mu₁` and `iv` there. -/
lemma ivX_tableOfLog (g : Table) (lr : Bool) {Pfx : QueryLog specIC} {x x1 : ByteArray}
    (hx : x1Of Pfx x = some x1) (hc : ∀ e ∈ hashEnt Pfx, e = ⟨e.1, g e.1⟩) :
    ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = ivX (stE lr) x1 g := by
  have hcons : ∀ e ∈ hashEnt (Pfx ++ axT g lr Pfx x), e = ⟨e.1, g e.1⟩ := by
    rw [hashEnt_append]
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hc e he
    · exact axT_consistent g lr Pfx x e he
  have hax := axT_of_some g lr hx
  have hmu : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) muCell = g muCell := by
    refine tableOfLog_eq hcons ?_
    rw [hashEnt_append, List.map_append, hax]
    simp [hashEnt]
  have hiv : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) (ivCell lr x1 (g muCell).ba) =
      g (ivCell lr x1 (g muCell).ba) := by
    refine tableOfLog_eq hcons ?_
    rw [hashEnt_append, List.map_append, hax]
    simp [hashEnt]
  have hmu' : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) (Kind.muDelayed, muCell.2) =
      g (Kind.muDelayed, muCell.2) := hmu
  simp only [ivX, mu1_stE, Hashes.ofTable]
  rw [hmu']
  exact congrArg Prob.Bytes.ba hiv

end Iv

/-! ## The chain of `E₁` -/

section Pcd

lemma size_zerosBA (n : ℕ) : (zerosBA n).size = n := by
  simp [zerosBA, ByteArray.size]

variable {p : Params} {π A D : ByteArray}

/-- The corrections of `E₁`'s chain (the first `o₂` bytes, then anything) are the proof's. -/
lemma corrections_pcd (hA : A = π.extract 0 p.o₂) (hπ : p.o₂ ≤ π.size) (R : ByteArray) :
    (⟨p, A ++ R⟩ : Proof).corrections = (⟨p, π⟩ : Proof).corrections := by
  have hAs : A.size = p.o₂ := by rw [hA, ByteArray.size_extract]; omega
  rw [corrections_eq, corrections_eq]
  simp only
  rw [extract_append_of_le (by have := o₂_le p; omega), hA, ByteArray.extract_extract]
  rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (o₂_le p)]

/-- **The correction bits `j < 360` of `E₁`'s chain** are the proof's, when the chain carries
`d[0..45)` after `o₂ + 64` bytes. -/
lemma corrBit_pcd (hA : A.size = p.o₂) (hπ : p.o₄ ≤ π.size) (hw : 45 ≤ p.witnessBytes)
    (hD : D = (⟨p, π⟩ : Proof).correction.extract 0 45) {j : ℕ} (hj : j < 360) :
    Bridge.corrBit ⟨p, A ++ zerosBA 64 ++ D ++ zerosBA 119⟩ j = Bridge.corrBit ⟨p, π⟩ j := by
  have hcs : (⟨p, π⟩ : Proof).correction.size = p.witnessBytes := by
    rw [correction_eq, ByteArray.size_extract]
    simp only
    unfold Params.o₄ at hπ ⊢
    omega
  have hDs : D.size = 45 := by
    rw [hD, ByteArray.size_extract, hcs]
    omega
  have key : (⟨p, A ++ zerosBA 64 ++ D ++ zerosBA 119⟩ : Proof).correction.get! (j / 8) =
      (⟨p, π⟩ : Proof).correction.get! (j / 8) := by
    rw [correction_eq]
    simp only
    rw [ByteArray.append_assoc, extract_append_right' (by rw [ByteArray.size_append, hA,
      size_zerosBA])]
    rw [ByteArray.size_append, hA, size_zerosBA, Nat.sub_self,
      get!_extract_zero (by unfold Params.o₄; omega), get!_append_left (by rw [hDs]; omega), hD,
      get!_extract_zero (by omega)]
  unfold Bridge.corrBit
  rw [key]

end Pcd

end VoleMole.ROM.OneMore.Pomfrit
