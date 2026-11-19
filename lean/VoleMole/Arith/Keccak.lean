import VoleMole.Arith.Keccak.Segmented
import VoleMole.Arith.Keccak.Lanes

/-!
# Arithmetization of Keccak-p[800, 12]: soundness and completeness (`src/keccak/segmented.hpp`)

Mechanizes §2 of `lean/docs/extraction/L7-keccak.md` ("Keccak segments"): Lemmas 2.1 and 2.2, the
facts F1-F3 (proved, not tested), and the interface used by the relations.

## The generator

* `qsInput pub map` is `qs_input(qs, public_state, map)` (`segmented.hpp:225-239`), with the C++
  `InputMap` entry `-1` written `none` and a witness byte index `b ≥ 0` written `some b`.
* `qsKeccak wOff n hn input` is `qs_keccak(qs, input, wit_off_states, n)` (`segmented.hpp:284-293`):
  the `NUM_SEGMENT_CONSTRAINTS = 1600` constraint expressions, in `add_constraint` order, and the
  first `n` output bits. It is the generic generator `qsKeccakG` (`Keccak/Segmented.lean`) at
  `T = Expr F`, so the same definition at `T = F` (`BitOps.field`) evaluates it with sharing:
  `qsKeccak_values` says `System.values` equals that evaluation, which is what a differential test
  should run (evaluating the `Expr` trees directly is exponential in the number of layers).
* `qsByte β out k` is `qs_byte(out, k)` (`segmented.hpp:299-307`), with `β j = from_8_byte(2^j)`
  (`β 0` is unused: the C++ starts from `state[8k]`).

## Results (for any field `F` of characteristic 2; the honest witness is a bit vector `w`)

* `qsKeccak_holds_iff` (Lemma 2.1 twice, both directions): at a bit vector, the constraints hold iff
  the committed states are `s₅ = R₄⋯R₀(s₀)` and `s₉ = R₈⋯R₅(s₅)`.
* `qsKeccak_sound`, `qsKeccak_complete`: byte-level forms for an input built by `qsInput`: the
  output bits are the bits of `keccakP800 (inputState pub map w)`; honest committed states
  (`keccakP800Rounds 0 5`, `keccakP800Rounds 0 9`) satisfy all constraints.
* `eval_qsByte_sound`: `qs_byte(out, k)` evaluates to `Σ_j β_j · bit j of byte k` of the output
  (with `β 0 = 1`), the form of `L7-keccak.md` §4.2's interface to `L7-uov.md`.
* `qsKeccak_degree`: constraints of degree `≤ 9` and outputs of degree `≤ 8` (`QS_DEGREE`,
  `OUTPUT_DEGREE`, `segmented.hpp:88-104`).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

open VoleMole.Arith

variable {F : Type*}

/-! ## The generator on `Expr F` -/

/-- `qs_input(qs, public_state, map)` (`segmented.hpp:225-239`): bit `i` is witness bit
`8 b + i % 8` if byte `⌊i/8⌋` maps to witness byte `b`, else the constant bit of `pub`. -/
def qsInput [Zero F] [One F] (pub : State) (map : Fin 100 → Option ℕ) : Vector (Expr F) 800 :=
  Vector.ofFn fun i =>
    match map ⟨i.1 / 8, by omega⟩ with
    | some b => Expr.wit (8 * b + i.1 % 8)
    | none => Expr.const (bitF (stateBit pub i.1))

/-- `qs_keccak(qs, input, wit_off_states, n)` (`segmented.hpp:284-293`) with the default layout:
the 1600 constraints and the first `n` output bits. -/
def qsKeccak [One F] (wOff n : ℕ) (hn : n ≤ 800) (input : Vector (Expr F) 800) :
    System F × Vector (Expr F) n :=
  qsKeccakG BitOps.expr Expr.wit layout finalRounds wOff n hn input

/-- `qs_byte(state, k)` (`segmented.hpp:299-307`): `state[8k] + Σ_{j=1}^{7} state[8k+j] · β_j`,
summed left to right, with `β j = from_8_byte(2^j)`. -/
def qsByte {n : ℕ} (β : Fin 8 → F) (s : Vector (Expr F) n) (k : ℕ) (hk : 8 * k + 8 ≤ n) : Expr F :=
  s[8 * k] + s[8 * k + 1] * Expr.const (β 1) + s[8 * k + 2] * Expr.const (β 2) +
    s[8 * k + 3] * Expr.const (β 3) + s[8 * k + 4] * Expr.const (β 4) +
    s[8 * k + 5] * Expr.const (β 5) + s[8 * k + 6] * Expr.const (β 6) +
    s[8 * k + 7] * Expr.const (β 7)

/-- Field arithmetic as a bit algebra (to evaluate the generator with sharing). -/
def BitOps.field [Add F] [Mul F] [One F] : BitOps F := ⟨(· + ·), (· * ·), 1⟩

/-- The constraint values, computed with sharing: `qsKeccakG` at `T = F`. -/
def qsKeccakValues [Add F] [Mul F] [One F] (w : ℕ → F) (wOff n : ℕ) (hn : n ≤ 800)
    (input : Vector F 800) : List F × Vector F n :=
  qsKeccakG BitOps.field w layout finalRounds wOff n hn input

/-- `NUM_SEGMENT_CONSTRAINTS = 1600` (`segmented.hpp:110`). -/
theorem qsKeccak_length [One F] (wOff n : ℕ) (hn : n ≤ 800) (input : Vector (Expr F) 800) :
    (qsKeccak wOff n hn input).1.length = 1600 := by
  simp [qsKeccak, qsKeccakG, layout, segmentConstraints, segmentConstraint, meetConstraints]

/-! ## Evaluation is a homomorphism -/

theorem rel_eval [Add F] [Mul F] [One F] (w : ℕ → F) :
    BitOps.Rel BitOps.expr BitOps.field (fun (e : Expr F) (v : F) => e.eval w = v) where
  add ha hb := by simp only [BitOps.expr, BitOps.field, Expr.eval, ha, hb]
  mul ha hb := by simp only [BitOps.expr, BitOps.field, Expr.eval, ha, hb]
  one := rfl

theorem list_forall₂_eq_map {T U : Type*} {f : T → U} {l : List T} {l' : List U}
    (h : List.Forall₂ (fun a b => f a = b) l l') : l.map f = l' := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

/-- The differential-test form: `System.values` of the generator is `qsKeccakValues`. -/
theorem qsKeccak_values [Add F] [Mul F] [One F] (w : ℕ → F) (wOff n : ℕ) (hn : n ≤ 800)
    (input : Vector (Expr F) 800) :
    (qsKeccak wOff n hn input).1.values w =
      (qsKeccakValues w wOff n hn (input.map (Expr.eval w))).1 ∧
    (qsKeccak wOff n hn input).2.map (Expr.eval w) =
      (qsKeccakValues w wOff n hn (input.map (Expr.eval w))).2 := by
  have h := qsKeccakG_rel (rel_eval w) (wit := Expr.wit) (wit' := w) (fun _ => rfl) layout
    finalRounds wOff n hn (s := input) (s' := input.map (Expr.eval w))
    (fun i hi => by simp)
  refine ⟨list_forall₂_eq_map h.1, ?_⟩
  ext i hi
  rw [Vector.getElem_map]
  exact h.2 i hi

/-! ## Bits -/

section Bits

variable [Field F] [CharP F 2]

theorem bitF_xor (a b : Bool) : (bitF (xor a b) : F) = bitF a + bitF b := by
  cases a <;> cases b <;> simp [bitF, CharTwo.add_self_eq_zero]

theorem bitF_and (a b : Bool) : (bitF (a && b) : F) = bitF a * bitF b := by
  cases a <;> cases b <;> simp [bitF]

theorem bitF_eq_zero_iff (a : Bool) : (bitF a : F) = 0 ↔ a = false := by
  cases a <;> simp [bitF]

/-- On bit vectors, expressions evaluate to bits: the relation used for soundness. -/
theorem rel_bits (w : ℕ → Bool) :
    BitOps.Rel BitOps.expr BitOps.bool (fun (e : Expr F) (b : Bool) => e.eval (ofBits w) = bitF b) where
  add ha hb := by simp only [BitOps.expr, BitOps.bool, Expr.eval, ha, hb, bitF_xor]
  mul ha hb := by simp only [BitOps.expr, BitOps.bool, Expr.eval, ha, hb, bitF_and]
  one := by simp [BitOps.expr, BitOps.bool, bitF]

theorem holds_iff_of_forall₂ {cs : System F} {bs : List Bool} (w : ℕ → Bool)
    (h : List.Forall₂ (fun (e : Expr F) (b : Bool) => e.eval (ofBits w) = bitF b) cs bs) :
    cs.Holds (ofBits w) ↔ ∀ b ∈ bs, b = false := by
  induction h with
  | nil => simp [System.Holds]
  | cons hab _ ih =>
    simp only [System.Holds, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [hab, bitF_eq_zero_iff, ih]

/-- The plain-bit instance of the generator. -/
def qsKeccakBool (w : ℕ → Bool) (wOff n : ℕ) (hn : n ≤ 800) (input : Vector Bool 800) :
    List Bool × Vector Bool n :=
  qsKeccakG BitOps.bool w layout finalRounds wOff n hn input

theorem qsKeccak_rel_bool (w : ℕ → Bool) (wOff n : ℕ) (hn : n ≤ 800)
    {input : Vector (Expr F) 800} {inputB : Vector Bool 800}
    (hin : ∀ i (hi : i < 800), input[i].eval (ofBits w) = bitF inputB[i]) :
    ((qsKeccak wOff n hn input).1.Holds (ofBits w) ↔
      ∀ b ∈ (qsKeccakBool w wOff n hn inputB).1, b = false) ∧
    ∀ i (hi : i < n), (qsKeccak wOff n hn input).2[i].eval (ofBits w) =
      bitF (qsKeccakBool w wOff n hn inputB).2[i] := by
  have h := qsKeccakG_rel (rel_bits (F := F) w) (wit := Expr.wit) (wit' := w) (fun _ => rfl)
    layout finalRounds wOff n hn hin
  exact ⟨holds_iff_of_forall₂ w h.1, h.2⟩

theorem segsLen_layout : segsLen layout = 9 := rfl

/-- **Lemma 2.1 for both segments, both directions**: at a bit vector, the 1600 segment
constraints hold iff the committed states are the true intermediate states `s₅` and `s₉`. -/
theorem qsKeccak_holds_iff (w : ℕ → Bool) (wOff n : ℕ) (hn : n ≤ 800)
    {input : Vector (Expr F) 800} {inputB : Vector Bool 800}
    (hin : ∀ i (hi : i < 800), input[i].eval (ofBits w) = bitF inputB[i]) :
    (qsKeccak wOff n hn input).1.Holds (ofBits w) ↔
      witVec w (8 * wOff) = rounds BitOps.bool 0 5 inputB ∧
      witVec w (8 * (wOff + 100)) = rounds BitOps.bool 5 4 (witVec w (8 * wOff)) := by
  rw [(qsKeccak_rel_bool w wOff n hn hin).1]
  have := (segmentConstraints_bool w wOff layout 0 0 inputB).1
  simp only [qsKeccakBool, qsKeccakG]
  rw [this]
  simp [Chain, layout, Segment.len]

/-- **Lemma 2.2**: if the constraints hold at a bit vector, output bit `i` is bit `i` of
Keccak-p[800, 12] (on the circuit's bit-level rounds) of the input. -/
theorem qsKeccak_out (w : ℕ → Bool) (wOff n : ℕ) (hn : n ≤ 800)
    {input : Vector (Expr F) 800} {inputB : Vector Bool 800}
    (hin : ∀ i (hi : i < 800), input[i].eval (ofBits w) = bitF inputB[i])
    (hs : (qsKeccak wOff n hn input).1.Holds (ofBits w)) (i : ℕ) (hi : i < n) :
    (qsKeccak wOff n hn input).2[i].eval (ofBits w) =
      bitF (rounds BitOps.bool 0 12 inputB)[i] := by
  rw [(qsKeccak_rel_bool w wOff n hn hin).2 i hi]
  have hc : Chain w wOff layout 0 0 inputB := by
    rw [← (segmentConstraints_bool w wOff layout 0 0 inputB).1]
    have := (qsKeccak_rel_bool w wOff n hn hin).1.1 hs
    simpa [qsKeccakBool, qsKeccakG] using this
  obtain ⟨-, h2, h3⟩ := segmentConstraints_bool w wOff layout 0 0 inputB
  simp only [qsKeccakBool, qsKeccakG, h2, h3 hc, segsLen_layout, finalRounds]
  show bitF (roundsOut BitOps.bool (0 + 9) (2 + 1) n hn (rounds BitOps.bool 0 9 inputB))[i] = _
  rw [roundsOut_getElem, ← rounds_add]

/-! ## Byte-level interface -/

/-- Byte `b` of a bit vector (bit `j` is `w (8b + j)`). -/
def witByte (w : ℕ → Bool) (b : ℕ) : UInt8 :=
  UInt8.ofBitVec (BitVec.cast (by simp) (BitVec.ofBoolListLE ((List.range 8).map fun j => w (8 * b + j))))

/-- The input state that `qsInput pub map` encodes at `w`: witness bytes where `map` says so,
public bytes elsewhere. -/
def inputState (pub : State) (map : Fin 100 → Option ℕ) (w : ℕ → Bool) : State :=
  Vector.ofFn fun k =>
    match map k with
    | some b => witByte w b
    | none => pub[k]

theorem eval_qsInput (pub : State) (map : Fin 100 → Option ℕ) (w : ℕ → Bool) (i : ℕ)
    (hi : i < 800) :
    (qsInput (F := F) pub map)[i].eval (ofBits w) = bitF (stateBits (inputState pub map w))[i] := by
  have h8 : i / 8 < 100 := by omega
  simp only [qsInput, stateBits, stateBit, inputState, Vector.getElem_ofFn, h8, ↓reduceDIte]
  rcases hm : map ⟨i / 8, h8⟩ with _ | b
  · simp
  · have h8' : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    simp only [Expr.eval, ofBits, witByte, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_cast,
      BitVec.getLsbD_ofBoolListLE]
    simp [h8']

theorem stateBits_keccakP800 (s : State) :
    stateBits (keccakP800 s) = rounds BitOps.bool 0 12 (stateBits s) :=
  stateBits_keccakP800Rounds 0 12 s

/-- **Soundness** (`L7-keccak.md` Lemma 2.2 with §2.5): if the constraints of
`qs_keccak(qs_input(pub, map), wOff, n)` hold at a bit vector `w`, output bit `i` is bit `i` of
`keccak_p800` of the input state. -/
theorem qsKeccak_sound (pub : State) (map : Fin 100 → Option ℕ) (w : ℕ → Bool) (wOff n : ℕ)
    (hn : n ≤ 800) (hs : (qsKeccak wOff n hn (qsInput (F := F) pub map)).1.Holds (ofBits w))
    (i : ℕ) (hi : i < n) :
    (qsKeccak wOff n hn (qsInput (F := F) pub map)).2[i].eval (ofBits w) =
      bitF (stateBit (keccakP800 (inputState pub map w)) i) := by
  rw [qsKeccak_out w wOff n hn (eval_qsInput pub map w) hs i hi, ← stateBits_keccakP800]
  simp [stateBits]

/-- The constraints of `qs_keccak` at a bit vector, in byte form: they hold iff the committed
states are `keccak_p800_rounds(input, 0, 5)` and `keccak_p800_rounds(input, 0, 9)`
(`encode_committed_states`, `segmented.hpp:113-119`). -/
theorem qsKeccak_holds_iff_bytes (pub : State) (map : Fin 100 → Option ℕ) (w : ℕ → Bool)
    (wOff n : ℕ) (hn : n ≤ 800) :
    (qsKeccak wOff n hn (qsInput (F := F) pub map)).1.Holds (ofBits w) ↔
      witVec w (8 * wOff) = stateBits (keccakP800Rounds 0 5 (inputState pub map w)) ∧
      witVec w (8 * (wOff + 100)) = stateBits (keccakP800Rounds 0 9 (inputState pub map w)) := by
  rw [qsKeccak_holds_iff w wOff n hn (eval_qsInput pub map w), stateBits_keccakP800Rounds,
    stateBits_keccakP800Rounds, show (9 : ℕ) = 5 + 4 from rfl, rounds_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, h1]⟩

/-- **Completeness**: honest committed states satisfy every constraint. -/
theorem qsKeccak_complete (pub : State) (map : Fin 100 → Option ℕ) (w : ℕ → Bool) (wOff n : ℕ)
    (hn : n ≤ 800)
    (h5 : ∀ i < 800, w (8 * wOff + i) = stateBit (keccakP800Rounds 0 5 (inputState pub map w)) i)
    (h9 : ∀ i < 800,
      w (8 * (wOff + 100) + i) = stateBit (keccakP800Rounds 0 9 (inputState pub map w)) i) :
    (qsKeccak wOff n hn (qsInput (F := F) pub map)).1.Holds (ofBits w) := by
  rw [qsKeccak_holds_iff_bytes]
  constructor <;> ext i hi <;> simp [witState, stateBits, h5, h9]

/-- **Byte output** (`L7-keccak.md` §4.2): `qs_byte(out, k)` is `Σ_j β_j · (bit j of byte k)` of
`keccak_p800` of the input, when `β 0 = 1`. -/
theorem eval_qsByte_sound (β : Fin 8 → F) (hβ : β 0 = 1) (pub : State) (map : Fin 100 → Option ℕ)
    (w : ℕ → Bool) (wOff n : ℕ) (hn : n ≤ 800)
    (hs : (qsKeccak wOff n hn (qsInput (F := F) pub map)).1.Holds (ofBits w)) (k : ℕ)
    (hk : 8 * k + 8 ≤ n) :
    (qsByte β (qsKeccak wOff n hn (qsInput (F := F) pub map)).2 k hk).eval (ofBits w) =
      ∑ j : Fin 8, β j * bitF (stateBit (keccakP800 (inputState pub map w)) (8 * k + j)) := by
  have e := fun j (hj : j < 8) => qsKeccak_sound pub map w wOff n hn hs (8 * k + j) (by omega)
  simp only [qsByte, Expr.eval_add, Expr.eval_mul, Expr.eval_const, Fin.sum_univ_eight]
  rw [qsKeccak_sound pub map w wOff n hn hs (8 * k) (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), hβ]
  simp [mul_comm]

end Bits

/-! ## Degrees (`segmented.hpp:88-104`) -/

section Degree

theorem rel_degree [One F] :
    BitOps.Rel (BitOps.expr (F := F)) BitOps.deg (fun e n => e.degree ≤ n) where
  add ha hb := by simp only [BitOps.expr, BitOps.deg, Expr.degree]; omega
  mul ha hb := by simp only [BitOps.expr, BitOps.deg, Expr.degree]; omega
  one := by simp [BitOps.expr, BitOps.deg, Expr.degree]

/-- Constant degree vectors. -/
abbrev rep (n d : ℕ) : Vector ℕ n := Vector.replicate n d

theorem colParity_deg (d : ℕ) : colParity BitOps.deg (rep 800 d) = rep 160 d := by
  ext i hi; simp [colParity, BitOps.deg]

theorem thetaRhoPi_deg (d : ℕ) : thetaRhoPi BitOps.deg (rep 800 d) = rep 800 d := by
  ext i hi; simp only [thetaRhoPi, colParity_deg]; simp [BitOps.deg]

theorem chiIota_deg (j n : ℕ) (hn : n ≤ 800) (d : ℕ) :
    chiIota BitOps.deg j n hn (rep 800 d) = rep n (2 * d) := by
  ext i hi
  simp only [chiIota, chi, BitOps.deg, Vector.getElem_ofFn, Fin.getElem_fin,
    Vector.getElem_replicate]
  split_ifs <;> omega

theorem rounds_deg (first k d : ℕ) : rounds BitOps.deg first k (rep 800 d) = rep 800 (2 ^ k * d) := by
  induction k generalizing first d with
  | zero => simp [rounds]
  | succ k ih =>
    rw [rounds, round, roundN, thetaRhoPi_deg, chiIota_deg, ih]
    congr 1; ring

theorem foldl_thetaInvStep_deg (l : List ℕ) (d : ℕ) :
    l.foldl (thetaInvStep BitOps.deg) (rep 160 d) = rep 160 d := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.foldl_cons]
    have : thetaInvStep BitOps.deg (rep 160 d) s = rep 160 d := by
      ext i hi; simp [thetaInvStep, BitOps.deg]
    rw [this, ih]

theorem foldl_thetaInvAcc_deg (l : List ℕ) (d : ℕ) (j : Fin 160) :
    l.foldl (thetaInvAcc BitOps.deg (rep 160 d) j) d = d := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : thetaInvAcc BitOps.deg (rep 160 d) j d i = d := by
      simp only [thetaInvAcc, BitOps.deg, Vector.getElem_replicate, Fin.getElem_fin, max_self,
        ite_self]
    rw [this, ih]

theorem thetaRhoPiInv_deg (d : ℕ) : thetaRhoPiInv BitOps.deg (rep 800 d) = rep 800 d := by
  have ha : (Vector.ofFn fun i : Fin 800 =>
      (rep 800 d)[idx (iy i) (2 * (ix i - iy i)) (iz i + rho (ix i) (iy i))]) = rep 800 d := by
    ext i hi; simp
  ext i hi
  simp only [thetaRhoPiInv]
  simp only [ha, colParity_deg, foldl_thetaInvStep_deg]
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_replicate, foldl_thetaInvAcc_deg]
  simp [BitOps.deg]

theorem iotaChiInv_deg (j d : ℕ) : iotaChiInv BitOps.deg j (rep 800 d) = rep 800 (3 * d) := by
  have hi : iota BitOps.deg j (rep 800 d) = rep 800 d := by
    ext i hi
    simp only [iota, BitOps.deg, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_replicate]
    split_ifs <;> simp
  ext i h
  simp only [iotaChiInv, hi]
  simp only [chiInv, BitOps.deg, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_replicate]
  omega

theorem roundsInvPartial_deg (b e d : ℕ) :
    roundsInvPartial BitOps.deg b e (rep 800 d) = rep 800 (3 ^ b * d) := by
  induction b using Nat.strong_induction_on generalizing e d with
  | _ b ih =>
    match b with
    | 0 => simp [roundsInvPartial]
    | 1 => simp [roundsInvPartial, iotaChiInv_deg]
    | b + 2 =>
      rw [roundsInvPartial, iotaChiInv_deg, thetaRhoPiInv_deg, ih (b + 1) (by omega)]
      congr 1; ring

theorem witState_deg (off : ℕ) : witState (fun _ => (1 : ℕ)) off = rep 800 1 := by
  ext i hi; simp [witState]

theorem meetConstraints_deg (start : ℕ) (seg : Segment) :
    ∀ c ∈ meetConstraints BitOps.deg start seg (rep 800 (2 ^ seg.forward)) (rep 800 1),
      c ≤ max (2 ^ seg.forward) (3 ^ seg.backward) := by
  unfold meetConstraints
  split_ifs with hb
  · intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    simp [BitOps.deg, hb]
  · simp only [thetaRhoPi_deg, roundsInvPartial_deg]
    intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    simp [BitOps.deg]

theorem forall₂_exists_of_mem_left {T U : Type*} {R : T → U → Prop} {l : List T} {l' : List U}
    (h : List.Forall₂ R l l') {a : T} (ha : a ∈ l) : ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- The segment constraints have degree at most `max(2^f, 3^b) = 9`, and the output degree at most
`2³ = 8`, given an input of degree at most `1` (`QS_DEGREE`, `OUTPUT_DEGREE`). -/
theorem qsKeccak_degree [One F] (wOff n : ℕ) (hn : n ≤ 800) (input : Vector (Expr F) 800)
    (hin : ∀ i (hi : i < 800), input[i].degree ≤ 1) :
    (∀ e ∈ (qsKeccak wOff n hn input).1, e.degree ≤ 9) ∧
      ∀ i (hi : i < n), (qsKeccak wOff n hn input).2[i].degree ≤ 8 := by
  have h := qsKeccakG_rel (rel_degree (F := F)) (wit := Expr.wit) (wit' := fun _ => 1)
    (fun _ => le_refl 1) layout finalRounds wOff n hn (s' := rep 800 1)
    (fun i hi => by simpa using hin i hi)
  have hcs : ∀ c ∈ (qsKeccakG BitOps.deg (fun _ => 1) layout finalRounds wOff n hn
      (rep 800 1)).1, c ≤ 9 := by
    simp only [qsKeccakG, layout, segmentConstraints, segmentConstraint, rounds_deg, witState_deg,
      List.append_nil, List.mem_append]
    rintro c (hc | hc)
    · have := meetConstraints_deg 0 ⟨3, 2⟩ c (by simpa using hc)
      simpa using this
    · have := meetConstraints_deg (0 + Segment.len ⟨3, 2⟩) ⟨2, 2⟩ c (by simpa using hc)
      simpa using this
  have hout : (qsKeccakG BitOps.deg (fun _ => 1) layout finalRounds wOff n hn (rep 800 1)).2 =
      rep n 8 := by
    simp only [qsKeccakG, layout, segmentConstraints, witState_deg, finalRounds]
    show roundsOut BitOps.deg _ (2 + 1) n hn (rep 800 1) = _
    rw [roundsOut, rounds_deg, roundN, thetaRhoPi_deg, chiIota_deg]
    rfl
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · obtain ⟨c, hc, hec⟩ := forall₂_exists_of_mem_left h.1 he
    exact hec.trans (hcs c hc)
  · have := h.2 i hi
    rw [hout] at this
    simpa [qsKeccak] using this

theorem qsInput_degree [Zero F] [One F] (pub : State) (map : Fin 100 → Option ℕ) (i : ℕ)
    (hi : i < 800) : (qsInput (F := F) pub map)[i].degree ≤ 1 := by
  simp only [qsInput, Vector.getElem_ofFn]
  split <;> simp [Expr.degree]

end Degree

end VoleMole.Arith.Keccak
