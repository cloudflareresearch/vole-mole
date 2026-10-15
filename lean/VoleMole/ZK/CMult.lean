import VoleMole.ZK.ByteLemmas
import VoleMole.ZK.CrtMask

/-!
# `c_mult` is a one-time pad of the sibling hashes (`lean/docs/zk.md` H6, `Masking.cmultEquiv`)

`Prover.cMultOf` (`compute_v_gate`) writes bit `e` of row `m` of `c_mult` as bit `m` of
`h⁰_e ⊕ h¹_e`, plus `⟨F[e], u_mask[m]⟩`. On the ideal tape one of `h⁰_e`, `h¹_e` is the tape's
`H₅` answer at the sibling label (`Sim.gateHashesIdeal`), the other a function of everything else.

* `cMultOf_eq`: `c_mult`, byte by byte (`cmultByte`: byte `k` of row `m` collects the bits of
  gates `8k … 8k + 7`).
* `cmultIdeal_bit`: bit `b` of byte `39 m + k` of the ideal prover's `c_mult` is bit `m` of the
  sibling answer of gate `8k + b`, XOR a function of the rest of the tape.
* **`upush_cmult`**: for every value of the rest of the tape, uniform sibling answers give a uniform
  `c_mult` (`N_MASK ≤ 32`: each mask reads its own bit of the 32-bit `H₅` output, patch 0002).
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK

/-! ## Bits of small words -/

lemma u32_bit (x : UInt32) (s : ℕ) (hs : s < 32) :
    ((x >>> s.toUInt32) &&& 1 == 1) = x.toNat.testBit s := by
  have h1 : ((x >>> s.toUInt32) &&& 1).toNat = x.toNat / 2 ^ s % 2 := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
    simp [Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have key : ∀ y : UInt32, (y == 1) = decide (y.toNat = 1) := fun y => by
    by_cases hy : y = 1
    · subst hy; rfl
    · rw [beq_false_of_ne hy]
      exact (decide_eq_false fun h => hy (UInt32.toNat_inj.1 (h.trans rfl))).symm
  rw [Nat.testBit_eq_decide_div_mod_eq, key, h1]

lemma testBit_byte_shift32 (x : UInt8) (j s : ℕ) (hj : j < 4) (hs : s < 32) :
    ((x.toUInt32 <<< (8 * j).toUInt32).toNat.testBit s) =
      (decide (s / 8 = j) && x.toNat.testBit (s % 8)) := by
  have hx : x.toNat < 256 := x.toNat_lt
  have h8 : (8 * j).toUInt32.toNat % 32 = 8 * j := by
    simp [Nat.toUInt32, UInt32.toNat_ofNat]; omega
  rw [UInt32.toNat_shiftLeft, h8, UInt8.toNat_toUInt32, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  by_cases hsj : s / 8 = j
  · have : s - 8 * j = s % 8 := by omega
    simp [hs, hsj, this, show 8 * j ≤ s by omega]
  · simp only [hsj, decide_false, Bool.false_and]
    by_cases hle : 8 * j ≤ s
    · have h2 : 8 ≤ s - 8 * j := by omega
      have : x.toNat.testBit (s - 8 * j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
          calc 256 = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ (s - 8 * j) := Nat.pow_le_pow_right (by norm_num) h2))
      simp [this]
    · simp [hle]

/-- Bit `s < 32` of `getLE32 b 0` is bit `s % 8` of byte `s / 8`. -/
lemma getLE32_testBit (b : ByteArray) {s : ℕ} (hs : s < 32) :
    (AES.getLE32 b 0).toNat.testBit s = (b.get! (s / 8)).toNat.testBit (s % 8) := by
  have e0 : ((b.get! 0).toUInt32).toNat.testBit s = (decide (s / 8 = 0) &&
      (b.get! 0).toNat.testBit (s % 8)) := by
    have := testBit_byte_shift32 (b.get! 0) 0 s (by norm_num) hs
    simpa using this
  simp only [AES.getLE32, UInt32.toNat_or, Nat.testBit_or, e0,
    show (8 : UInt32) = (8 * 1 : ℕ).toUInt32 from rfl, show (16 : UInt32) = (8 * 2 : ℕ).toUInt32 from rfl,
    show (24 : UInt32) = (8 * 3 : ℕ).toUInt32 from rfl,
    testBit_byte_shift32 _ 1 s (by norm_num) hs, testBit_byte_shift32 _ 2 s (by norm_num) hs,
    testBit_byte_shift32 _ 3 s (by norm_num) hs, Nat.zero_add]
  have : s / 8 < 4 := by omega
  interval_cases h : s / 8 <;> simp

/-! ## `c_mult`, byte by byte -/

/-- A byte from its 8 bits. -/
def byteOf (f : ℕ → Bool) : UInt8 :=
  (List.range 8).foldl (fun byte b => if f b then byte ||| ((1 : UInt8) <<< b.toUInt8) else byte) 0

lemma byteOf_testBit (f : ℕ → Bool) {b : ℕ} (hb : b < 8) : (byteOf f).toNat.testBit b = f b := by
  have key : ∀ (l : List ℕ) (acc : UInt8), (∀ j ∈ l, j < 8) →
      (l.foldl (fun byte b => if f b then byte ||| ((1 : UInt8) <<< b.toUInt8) else byte)
        acc).toNat.testBit b = (acc.toNat.testBit b || l.any fun j => decide (j = b) && f j) := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      intro acc hl
      rw [List.foldl_cons, ih _ fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')]
      have hj := hl j (by simp)
      have hsh : ((1 : UInt8) <<< j.toUInt8).toNat = 2 ^ j := by
        rw [UInt8.toNat_shiftLeft]
        simp only [UInt8.toNat_one]
        have : j.toUInt8.toNat % 8 = j := by simp [Nat.toUInt8]; omega
        rw [this, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]
      split_ifs with hf
      · simp only [UInt8.toNat_or, Nat.testBit_or, hsh, Nat.testBit_two_pow, List.any_cons]
        by_cases hjb : j = b
        · subst hjb; simp [hf]
        · simp [hjb]
      · simp only [List.any_cons]
        by_cases hjb : j = b
        · subst hjb; simp [hf]
        · simp [hjb]
  rw [byteOf, key _ _ fun j hj => List.mem_range.1 hj]
  simp only [UInt8.toNat_zero, Nat.zero_testBit, Bool.false_or]
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨j, _, hj⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    rw [← hj.1]; exact hj.2
  · intro h
    exact ⟨b, List.mem_range.2 hb, by simp [h]⟩

/-- Bit `e` of row `m` of `c_mult`. -/
def cmultBit (h0 h1 : Array UInt32) (uMask : Array W128) (m e : ℕ) : Bool :=
  (((h0[e]! ^^^ h1[e]!) >>> m.toUInt32) &&& 1 == 1) ^^ Prover.dot Prover.fRows[e]! uMask[m]!

/-- Byte `k` of row `m`. -/
def cmultByte (h0 h1 : Array UInt32) (uMask : Array W128) (m k : ℕ) : UInt8 :=
  byteOf fun b => cmultBit h0 h1 uMask m (8 * k + b)

lemma map_range_mul_flatMap {α : Type} (f : ℕ → ℕ → α) (n q : ℕ) :
    (List.range n).flatMap (fun m => (List.range q).map (f m)) =
      (List.range (n * q)).map fun j => f (j / q) (j % q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append,
      List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.1 hk
    simp only [Function.comp_apply]
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- **`c_mult`, byte by byte**: byte `39 m + k` is `cmultByte m k`. -/
theorem cMultOf_eq (p : Params) (h0 h1 : Array UInt32) (uMask : Array W128) :
    Prover.cMultOf p h0 h1 uMask =
      ba (fun j : Fin (p.nMask * p.nMultBytes) =>
        cmultByte h0 h1 uMask (j / p.nMultBytes) (j % p.nMultBytes)) := by
  have hinner : ∀ m k, (Id.run do
      let mut byte : UInt8 := 0
      for b in [0:8] do
        let e := 8 * k + b
        let bit := (((h0[e]! ^^^ h1[e]!) >>> m.toUInt32) &&& 1 == 1) ^^
          Prover.dot Prover.fRows[e]! uMask[m]!
        if bit then byte := byte ||| ((1 : UInt8) <<< b.toUInt8)
      return byte) = cmultByte h0 h1 uMask m k := by
    intro m k
    simp only [Id.run, bind_pure]
    rw [forIn_range_foldl _ _ _ (fun b byte =>
      if cmultBit h0 h1 uMask m (8 * k + b) then byte ||| ((1 : UInt8) <<< b.toUInt8) else byte)
      fun b byte => by simp only [cmultBit]; split_ifs <;> simp_all]
    rfl
  apply ByteArray.ext
  simp only [Prover.cMultOf, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun m out =>
      (List.range p.nMultBytes).foldl (fun o k => o.push (cmultByte h0 h1 uMask m k)) out)
    fun m out => by
      rw [forIn_range_foldl _ _ _ (fun k o => o.push (cmultByte h0 h1 uMask m k))
        fun k o => by rw [← hinner m k]; rfl]
      rfl]
  have hout : ∀ (l : List ℕ) (o : ByteArray),
      (l.foldl (fun out m => (List.range p.nMultBytes).foldl
        (fun o k => o.push (cmultByte h0 h1 uMask m k)) out) o).data =
      o.data ++ (l.flatMap fun m => (List.range p.nMultBytes).map (cmultByte h0 h1 uMask m)).toArray := by
    intro l
    induction l with
    | nil => intro o; simp
    | cons m l ih =>
      intro o
      rw [List.foldl_cons, ih, foldl_push_data, List.flatMap_cons]
      simp
  erw [hout, map_range_mul_flatMap]
  have he : (ByteArray.emptyWithCapacity (p.nMask * p.nMultBytes)).data = #[] := rfl
  rw [he, Array.empty_append]
  apply Array.ext
  · simp [ba]
  intro j h1 h2
  simp [ba]

/-! ## The ideal prover's `c_mult` -/

lemma gateWords_get (hs : List ByteArray) {e : ℕ} (he : e < hs.length) :
    (gateWords hs)[e]! = AES.getLE32 (hs[e]) 0 := by
  rw [gateWords, getElem!_pos _ _ (by simpa using he)]
  simp

/-- The sibling answers' bit: bit `m` of the `H₅` answer of gate `e`. -/
def sibBit (sib : Fin 312 → Bytes 4) (e m : ℕ) : Bool :=
  if h : e < 312 then (AES.getLE32 (ba (sib ⟨e, h⟩)) 0).toNat.testBit m else false

lemma gateHashesIdeal_get (Hs : Hashes) (gamma : Array UInt64) (b : Bool) (ins : List ByteArray)
    (sib : Fin 312 → Bytes 4) {e : ℕ} (he : e < 312) :
    (gateHashesIdeal Hs gamma b ins sib)[e]! =
      if wbit gamma e == b then AES.getLE32 (Hs.hash .h5 (ins.getD e ByteArray.empty)) 0
      else AES.getLE32 (ba (sib ⟨e, he⟩)) 0 := by
  rw [gateHashesIdeal, gateWords_get _ (by simpa using he)]
  simp only [List.getElem_map, List.getElem_range]
  split_ifs <;> rfl

/-- **Bit `(m, e)` of the ideal `c_mult`** is the sibling answer's bit `m` of gate `e`, XOR the
forced hash's bit and `⟨F[e], u_mask[m]⟩` (which do not read the sibling answers). -/
theorem cmultIdeal_bit (Hs : Hashes) (T : CrtTables) (st : Statement) (P : Pub)
    (delta : Bytes 16) (qcols : Array (Array UInt64)) (u : Array UInt64) (uMask : Array W128)
    (sib : Fin 312 → Bytes 4) {m e : ℕ} (hm : m < 32) (he : e < 312) :
    let p := st.params
    let dbit := BAVC.deltaBit (ba delta)
    let cols := tagCols dbit qcols u
    let uPre : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩
    let gamma := gammaOf T dbit
    let ins := if wbit gamma e then Prover.gateInputsOff p T P.iv cols uPre
      else Prover.gateInputsOff p T P.iv cols W128.zero
    cmultBit (gateHashesIdeal Hs gamma false (Prover.gateInputsOff p T P.iv cols W128.zero) sib)
        (gateHashesIdeal Hs gamma true (Prover.gateInputsOff p T P.iv cols uPre) sib) uMask m e =
      (sibBit sib e m ^^
        ((AES.getLE32 (Hs.hash .h5 (ins.getD e ByteArray.empty)) 0).toNat.testBit m ^^
          Prover.dot Prover.fRows[e]! uMask[m]!)) := by
  intro p dbit cols uPre gamma ins
  simp only [cmultBit, gateHashesIdeal_get _ _ _ _ _ he, u32_bit _ _ hm, UInt32.toNat_xor,
    Nat.testBit_xor, sibBit, he, dite_true, ins]
  cases hg : wbit gamma e <;> simp only [beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, beq_false, beq_true, Bool.not_true] <;>
    cases Prover.dot Prover.fRows[e]! uMask[m]! <;> simp [Bool.xor_comm]

/-! ## Uniform sibling answers give a uniform `c_mult` -/

/-- The bit vector of a byte block. -/
noncomputable def bitsE (n : ℕ) : Bytes n ≃ (Fin n → Fin 8 → Bool) :=
  Equiv.arrowCongr (Equiv.refl _) byteBitsEquiv

/-- The sibling answers' bits, moved to the positions of `c_mult`'s bits. -/
def sibSel (nM : ℕ) (hnm : nM ≤ 32) : (Fin 312 → Fin 4 → Fin 8 → Bool) →+
    (Fin (nM * 39) → Fin 8 → Bool) where
  toFun x j b := x ⟨8 * (j % 39) + b, by omega⟩ ⟨j / 39 / 8, by
    have := j.isLt; have : j / 39 < nM := Nat.div_lt_of_lt_mul (by linarith); omega⟩
    ⟨j / 39 % 8, Nat.mod_lt _ (by norm_num)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma sibSel_surjective (nM : ℕ) (hnm : nM ≤ 32) : Function.Surjective (sibSel nM hnm) := by
  intro y
  refine ⟨fun e q r => if h : 8 * q.val + r.val < nM then
    y ⟨39 * (8 * q.val + r.val) + e.val / 8, by have := e.isLt; omega⟩
      ⟨e.val % 8, Nat.mod_lt _ (by norm_num)⟩ else false, ?_⟩
  funext j b
  have hj := j.isLt
  have hm : j / 39 < nM := Nat.div_lt_of_lt_mul (by linarith)
  simp only [sibSel, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have e1 : 8 * (j.val / 39 / 8) + j.val / 39 % 8 = j.val / 39 := by omega
  rw [dite_eq_left_of_eq_true (eq_true (by rw [e1]; exact hm))]
  have hb := b.isLt
  congr 1
  · apply Fin.ext
    show 39 * (8 * (j.val / 39 / 8) + j.val / 39 % 8) + (8 * (j.val % 39) + b.val) / 8 = j.val
    rw [e1]; omega
  · apply Fin.ext
    show (8 * (j.val % 39) + b.val) % 8 = b.val
    omega

/-- **Uniform sibling answers give a uniform `c_mult`**, for every value of the rest of the tape. -/
theorem upush_cmult (Hs : Hashes) (T : CrtTables) (st : Statement) (P : Pub) (delta : Bytes 16)
    (qcols : Array (Array UInt64)) (u : Array UInt64) (uMask : Array W128)
    (hnm : st.params.nMask ≤ 32) :
    UPush (fun sib : Fin 312 → Bytes 4 =>
      blk (st.params.nMask * st.params.nMultBytes)
        (cmultIdeal Hs T st P delta qcols u uMask sib)) := by
  set p := st.params
  set dbit := BAVC.deltaBit (ba delta)
  set cols := tagCols dbit qcols u
  set uPre : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩
  set gamma := gammaOf T dbit
  -- The bits of `c_mult` that do not come from the sibling answers.
  let K : Fin (p.nMask * 39) → Fin 8 → Bool := fun j b =>
    let e := 8 * (j.val % 39) + b.val
    let ins := if wbit gamma e then Prover.gateInputsOff p T P.iv cols uPre
      else Prover.gateInputsOff p T P.iv cols W128.zero
    (AES.getLE32 (Hs.hash .h5 (ins.getD e ByteArray.empty)) 0).toNat.testBit (j.val / 39) ^^
      Prover.dot Prover.fRows[e]! uMask[j.val / 39]!
  let E2 : (Fin 312 → Bytes 4) ≃ (Fin 312 → Fin 4 → Fin 8 → Bool) :=
    Equiv.arrowCongr (Equiv.refl _) (bitsE 4)
  have key : ∀ sib, blk (p.nMask * p.nMultBytes) (cmultIdeal Hs T st P delta qcols u uMask sib) =
      (bitsE (p.nMask * 39)).symm (sibSel p.nMask hnm (E2 sib) + K) := by
    intro sib
    apply (bitsE (p.nMask * 39)).injective
    rw [Equiv.apply_symm_apply]
    funext j b
    have hj := j.isLt
    have hm : j.val / 39 < p.nMask := Nat.div_lt_of_lt_mul (by linarith)
    have he : 8 * (j.val % 39) + b.val < 312 := by omega
    show byteBits (blk _ (cmultIdeal Hs T st P delta qcols u uMask sib) j) b = _
    rw [get_blk, cmultIdeal, cMultOf_eq,
      get!_ba _ (show j.val < st.params.nMask * st.params.nMultBytes from hj)]
    simp only [byteBits, cmultByte, Params.nMultBytes]
    have hbit := cmultIdeal_bit Hs T st P delta qcols u uMask sib (m := j.val / 39) (by omega) he
    simp only at hbit
    rw [byteOf_testBit _ b.isLt, hbit]
    simp only [Pi.add_apply, Bool.add_eq_xor, sibSel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, E2, K,
      Equiv.arrowCongr_apply, Function.comp_apply, bitsE, byteBitsEquiv_apply,
      sibBit, he, dite_true]
    rw [getLE32_testBit _ (by omega), get!_ba _ (by omega)]
    rfl
  have hb : Balanced (fun sib : Fin 312 → Bytes 4 =>
      (bitsE (p.nMask * 39)).symm (sibSel p.nMask hnm (E2 sib) + K)) :=
    ((balanced_addHom (sibSel p.nMask hnm) (sibSel_surjective _ hnm) K).equiv_comp E2).comp_equiv
      (bitsE (p.nMask * 39)).symm
  exact hb.upush.congr key

end VoleMole.ZK.Sim
