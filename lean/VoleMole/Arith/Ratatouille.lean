import VoleMole.Arith.Adder
import VoleMole.Arith.UOV

/-!
# Ratatouille issue and spend (`src/ratatouille/issue.hpp`, `src/ratatouille/spend.hpp`)

Executable models of `IssueRelation::constraints` and `SpendRelation::constraints`, with
completeness and soundness proofs against the relations the protocol proofs use
(`lean/docs/security/ratatouille.md` §2.4):

* issue: `c = Com(nf, ctx, T_init, r)` (`IssueRel`);
* spend (`SpendRel`): V1 `P(s) = Tag(Com(nf, ctx, t, r), x)`, V2 `c' = Com(nf', ctx, t', r')`,
  V3 `t + x = t' + d` over ℕ, V4 `t, x, t', d < 2⁶⁴`.

This mechanizes `lean/docs/extraction/L7-keccak.md` §4.3-4.4 and `L7-uov.md` §6, on top of the
Keccak (`Arith/Keccak.lean`), adder (`Arith/Adder.lean`) and UOV (`Arith/UOV.lean`) gadgets.

## Model

* `comState`, `tagState` are `encode_com_state`, `encode_tag_state` (`commit.hpp:56-93`) over
  byte strings `ℕ → UInt8`, with `encodeCredits` little-endian; `commit` and `tagTarget` are `Com`
  and `Tag` (`keccakP800` of these states, truncated to 32 and `M = 45` bytes; `tagTarget` as an
  element of `K^M` via the GF(256) decoder `ofByte`).
* The input maps `issueComMap`, `spendComMap`, `spendTagMap`, `spendComNextMap` are the C++
  `InputMap`s. The wiring lemmas `inputState_issue`, `inputState_spendCom`, `inputState_spendTag`,
  `inputState_spendComNext` prove that `qs_input(public_state, map)` encodes the full commitment /
  tag input with the secret fields read from the witness (`bytesAt`, `creditAt`), for every
  witness: this replaces the C++ tests `KeccakInput(s)Is…Input` (L7-keccak.md §2.5) by a proof.
  `encodeCredits_creditAt` ties the adder's bitwise reading `credit_bit(o, i) = 8o + i` to the
  bytes that enter Keccak.
* Generators: `issueSystem c T_init ctx` and `spendSystem β toBits pk nf d c' ctx l`, in
  `add_constraint` order (3776 and 12282 constraints, `issueSystem_length`,
  `spendSystem_length`). `issueValues` / `spendValues` compute the same values with sharing
  (`issueSystem_values`, `spendSystem_values`, for any `F` with `+ * 0 1`, so also `GF128`); the
  harness (`Arith/VectorsRatatouille.lean`) runs them against the C++.

## Main results (`[Field F] [CharP F 2]`; `hι : IsEmbedding β toBits ofByte`, `hβ : β 0 = 1`)

* Issue: `issue_holds_iff` (at a bit vector: honest committed states ∧ `IssueRel`),
  `issue_complete`, `issue_sound` (any `w ∈ F^ℓ`: all witness bits are bits and the decoded
  witness satisfies `IssueRel`).
* Spend: `spend_holds_iff` (at a bit vector, for every `l`: honest states and carries, `t + x =
  t' + d` over ℕ, committed `c = Com(nf, ctx, t, r)`, the combined UOV equation, and
  `c' = Com(nf', ctx, t', r')`), `spend_complete`, `spend_sound` (any `w ∈ F^ℓ`), and
  `spend_sound_card`: for `w` fixed before `l`, either `w` encodes a witness of `SpendRel`, or
  `#{l | constraints hold} · |F| ≤ |F^M|`. V3's 64-bit edge cases are covered: the sums are exact
  65-bit values (`conservation_holds_iff`), and `t' < 2⁶⁴` holds by construction (`creditAt_lt`).
  The public `d` enters as its bits `d.testBit i`, `i < 64`, so `d < 2⁶⁴` (a `uint64_t` in C++) is
  a hypothesis.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Ratatouille

open VoleMole.Arith VoleMole.Arith.Keccak VoleMole.Arith.Adder VoleMole.Arith.UOV

/-! ## Byte-level model of `src/ratatouille/commit.hpp` -/

/-- `RATATOUILLE_COM_DST = make_dst("rata", 0, 'c', '0')` (`src/dst.hpp:48`). -/
def comDst : List UInt8 := [0x72, 0x61, 0x74, 0x61, 0, 0x63, 0x30]

/-- `RATATOUILLE_TAG_DST = make_dst("rata", 0, 't', '0')` (`src/dst.hpp:54`). -/
def tagDst : List UInt8 := [0x72, 0x61, 0x74, 0x61, 0, 0x74, 0x30]

/-- `encode_credits(v)[i] = uint8_t(v >> 8i)` (`commit.hpp:36-42`). -/
def encodeCredits (v i : ℕ) : UInt8 := UInt8.ofNat (v >>> (8 * i))

/-- `encode_com_state(nf, ctx, t, r)` (`commit.hpp:56-77`):
`DST ‖ r ‖ 0⁹ ‖ ctx ‖ ⟨t⟩₈ ‖ nf ‖ 0²⁰`, with `COM_OFF_R = 7`, `COM_OFF_CTX = 32`,
`COM_OFF_T = 48`, `COM_OFF_NF = 56`. -/
def comState (nf ctx : ℕ → UInt8) (t : ℕ) (r : ℕ → UInt8) : State :=
  Vector.ofFn fun k =>
    if k.1 < 7 then comDst.getD k.1 0
    else if k.1 < 23 then r (k.1 - 7)
    else if k.1 < 32 then 0
    else if k.1 < 48 then ctx (k.1 - 32)
    else if k.1 < 56 then encodeCredits t (k.1 - 48)
    else if k.1 < 80 then nf (k.1 - 56)
    else 0

/-- `encode_tag_state(c, x)` (`commit.hpp:79-93`): `DST ‖ 0²⁵ ‖ c ‖ ⟨x⟩₈ ‖ 0²⁸`, with
`TAG_OFF_C = 32`, `TAG_OFF_X = 64`. -/
def tagState (c : ℕ → UInt8) (x : ℕ) : State :=
  Vector.ofFn fun k =>
    if k.1 < 7 then tagDst.getD k.1 0
    else if k.1 < 32 then 0
    else if k.1 < 64 then c (k.1 - 32)
    else if k.1 < 72 then encodeCredits x (k.1 - 64)
    else 0

/-- Byte `k` of a state (`0` beyond the end). -/
def stateByte (s : State) (k : ℕ) : UInt8 := if h : k < 100 then s[k] else 0

/-- `Com(nf, ctx, t, r)`: the first `COMMITMENT_BYTES = 32` bytes of
`keccak_p800(encode_com_state(nf, ctx, t, r))` (`ratatouille.cpp:94-100`). Only bytes `k < 32`
are meaningful. -/
def commit (nf ctx : ℕ → UInt8) (t : ℕ) (r : ℕ → UInt8) : ℕ → UInt8 :=
  stateByte (keccakP800 (comState nf ctx t r))

/-- Bit `i` of a byte string: `(b[i / 8] >> (i % 8)) & 1`. -/
def byteBit (b : ℕ → UInt8) (i : ℕ) : Bool := (b (i / 8)).toBitVec.getLsbD (i % 8)

/-- A byte as an element of the GF(256) model `K`. -/
def ofUInt8 {K : Type*} (ofByte : (Fin 8 → Bool) → K) (b : UInt8) : K :=
  ofByte fun j => b.toBitVec.getLsbD j.1

/-- UOV parameters (`include/vole_mole/uov.hpp:17-18`). -/
def uovN : ℕ := 119
def uovM : ℕ := 45

/-- `Tag(c, x)`: the first `M = 45` bytes of `keccak_p800(encode_tag_state(c, x))`
(`ratatouille.cpp:102-107`), as a UOV target over `K`. -/
def tagTarget {K : Type*} (ofByte : (Fin 8 → Bool) → K) (c : ℕ → UInt8) (x : ℕ) : Fin uovM → K :=
  fun k => ofUInt8 ofByte (stateByte (keccakP800 (tagState c x)) k.1)

/-! ## Witness decoding -/

/-- The witness bytes starting at witness byte `o`. -/
def bytesAt (w : ℕ → Bool) (o : ℕ) : ℕ → UInt8 := fun i => witByte w (o + i)

/-- The credit value whose little-endian encoding starts at witness byte `o`: bit `i` is witness
bit `credit_bit(o, i) = 8o + i` (`commit.hpp:54`). -/
def creditAt (w : ℕ → Bool) (o : ℕ) : ℕ := val (fun i => w (8 * o + i)) 64

/-! ## Bit-level lemmas -/

theorem val_lt (f : ℕ → Bool) (n : ℕ) : val f n < 2 ^ n := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    simp only [val, pow_succ]
    cases f n <;> simp <;> omega

theorem testBit_val (f : ℕ → Bool) (n k : ℕ) : (val f n).testBit k = (decide (k < n) && f k) := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    have h : val f (n + 1) = 2 ^ n * (f n).toNat + val f n := by simp only [val]; ring
    rw [h, Nat.testBit_two_pow_mul_add _ (val_lt f n)]
    split_ifs with hk
    · rw [ih]; simp [hk, show k < n + 1 by omega]
    · rcases Nat.lt_or_ge k (n + 1) with h1 | h1
      · have : k = n := by omega
        subst this
        cases f k <;> simp
      · have h2 : k - n ≠ 0 := by omega
        have hk1 : ¬ k < n + 1 := by omega
        cases f n <;> simp [hk1, Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow h2)]

theorem val_testBit (d n : ℕ) : val (fun i => d.testBit i) n = d % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_val, Nat.testBit_mod_two_pow]

theorem val_eq_of_bits (f : ℕ → Bool) {d n : ℕ} (hd : d < 2 ^ n) (hf : ∀ i < n, f i = d.testBit i) :
    val f n = d := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_val]
  by_cases hk : k < n
  · simp [hk, hf k hk]
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem bits_eq_of_val_eq {f g : ℕ → Bool} {n : ℕ} (h : val f n = val g n) (i : ℕ) (hi : i < n) :
    f i = g i := by
  have := congrArg (fun v => v.testBit i) h
  simpa [testBit_val, hi] using this

theorem uint8_ext {a b : UInt8} (h : ∀ j < 8, a.toBitVec.getLsbD j = b.toBitVec.getLsbD j) :
    a = b := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact h j hj

theorem witByte_bit (w : ℕ → Bool) (b j : ℕ) (hj : j < 8) :
    (witByte w b).toBitVec.getLsbD j = w (8 * b + j) := by
  simp only [witByte, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [hj]

theorem encodeCredits_bit (v i j : ℕ) (hj : j < 8) :
    (encodeCredits v i).toBitVec.getLsbD j = v.testBit (8 * i + j) := by
  rw [encodeCredits, UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat]
  simp [hj, Nat.testBit_shiftRight]

/-- The credit decoded from the witness re-encodes to the witness bytes. -/
theorem encodeCredits_creditAt (w : ℕ → Bool) (o i : ℕ) (hi : i < 8) :
    encodeCredits (creditAt w o) i = witByte w (o + i) := by
  apply uint8_ext
  intro j hj
  rw [encodeCredits_bit _ _ _ hj, witByte_bit _ _ _ hj, creditAt, testBit_val]
  simp only [show 8 * i + j < 64 by omega, decide_true, Bool.true_and]
  congr 1; ring

theorem creditAt_lt (w : ℕ → Bool) (o : ℕ) : creditAt w o < 2 ^ 64 := val_lt _ _

theorem byteBit_eq (b : ℕ → UInt8) (k j : ℕ) (hj : j < 8) :
    byteBit b (8 * k + j) = (b k).toBitVec.getLsbD j := by
  simp only [byteBit]
  rw [show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega]

theorem stateBit_eq (s : State) (k j : ℕ) (hk : k < 100) (hj : j < 8) :
    stateBit s (8 * k + j) = (stateByte s k).toBitVec.getLsbD j := by
  have h1 : (8 * k + j) / 8 = k := by omega
  have h2 : (8 * k + j) % 8 = j := by omega
  simp only [stateBit, stateByte, h1, h2, hk, dite_true]

/-! ## Input maps (`keccak::detail::InputMap`, `-1 ↦ none`) and their wiring -/

/-- `ISSUE_COM_TO_WIT` (`issue.hpp:64-75`): `r` from witness byte `ISSUE_WIT_OFF_R = 0`, `nf` from
`ISSUE_WIT_OFF_NF = 16`. -/
def issueComMap : Fin 100 → Option ℕ := fun k =>
  if 7 ≤ k.1 ∧ k.1 < 23 then some (0 + (k.1 - 7))
  else if 56 ≤ k.1 ∧ k.1 < 80 then some (16 + (k.1 - 56))
  else none

/-- `SPEND_COM_TO_WIT` (`spend.hpp:113-126`): `r` from `SPEND_WIT_OFF_R = 0`, `⟨t⟩` from
`SPEND_WIT_OFF_T = 16`. -/
def spendComMap : Fin 100 → Option ℕ := fun k =>
  if 7 ≤ k.1 ∧ k.1 < 23 then some (0 + (k.1 - 7))
  else if 48 ≤ k.1 ∧ k.1 < 56 then some (16 + (k.1 - 48))
  else none

/-- `SPEND_TAG_TO_WIT` (`spend.hpp:130-143`): `c` from `SPEND_WIT_OFF_C = 32`, `⟨x⟩` from
`SPEND_WIT_OFF_X = 24`. -/
def spendTagMap : Fin 100 → Option ℕ := fun k =>
  if 32 ≤ k.1 ∧ k.1 < 64 then some (32 + (k.1 - 32))
  else if 64 ≤ k.1 ∧ k.1 < 72 then some (24 + (k.1 - 64))
  else none

/-- `SPEND_COM_NEXT_TO_WIT` (`spend.hpp:147-163`): `nf'` from `SPEND_WIT_OFF_NF_NEXT = 64`,
`⟨t'⟩` from `SPEND_WIT_OFF_T_NEXT = 88`, `r'` from `SPEND_WIT_OFF_R_NEXT = 96`. -/
def spendComNextMap : Fin 100 → Option ℕ := fun k =>
  if 56 ≤ k.1 ∧ k.1 < 80 then some (64 + (k.1 - 56))
  else if 48 ≤ k.1 ∧ k.1 < 56 then some (88 + (k.1 - 48))
  else if 7 ≤ k.1 ∧ k.1 < 23 then some (96 + (k.1 - 7))
  else none

/-- The all-zero byte string (`{}` in the C++). -/
def zeros : ℕ → UInt8 := fun _ => 0

/-- Issue wiring: `qs_input(encode_com_state({}, ctx, T_init, {}), ISSUE_COM_TO_WIT)` encodes
`encode_com_state(nf, ctx, T_init, r)` with `r`, `nf` read from the witness. -/
theorem inputState_issue (ctx : ℕ → UInt8) (tInit : ℕ) (w : ℕ → Bool) :
    inputState (comState zeros ctx tInit zeros) issueComMap w =
      comState (bytesAt w 16) ctx tInit (bytesAt w 0) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, comState, issueComMap, bytesAt, zeros, Vector.getElem_ofFn,
    Fin.getElem_fin]
  split_ifs <;> first | omega | rfl

/-- Spend wiring (V1, Com): `qs_input(encode_com_state(nf, ctx, 0, {}), SPEND_COM_TO_WIT)`
encodes `encode_com_state(nf, ctx, t, r)`. -/
theorem inputState_spendCom (nf ctx : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (comState nf ctx 0 zeros) spendComMap w =
      comState nf ctx (creditAt w 16) (bytesAt w 0) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, comState, spendComMap, bytesAt, zeros, Vector.getElem_ofFn,
    Fin.getElem_fin]
  split_ifs <;> first | omega | rfl | rw [encodeCredits_creditAt _ _ _ (by omega)]

/-- Spend wiring (V1, Tag): `qs_input(encode_tag_state({}, 0), SPEND_TAG_TO_WIT)` encodes
`encode_tag_state(c, x)`. -/
theorem inputState_spendTag (w : ℕ → Bool) :
    inputState (tagState zeros 0) spendTagMap w = tagState (bytesAt w 32) (creditAt w 24) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, tagState, spendTagMap, bytesAt, zeros, Vector.getElem_ofFn,
    Fin.getElem_fin]
  split_ifs <;> first | omega | rfl | rw [encodeCredits_creditAt _ _ _ (by omega)]

/-- Spend wiring (V2): `qs_input(encode_com_state({}, ctx, 0, {}), SPEND_COM_NEXT_TO_WIT)` encodes
`encode_com_state(nf', ctx, t', r')`. -/
theorem inputState_spendComNext (ctx : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (comState zeros ctx 0 zeros) spendComNextMap w =
      comState (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, comState, spendComNextMap, bytesAt, zeros, Vector.getElem_ofFn,
    Fin.getElem_fin]
  split_ifs <;> first | omega | rfl | rw [encodeCredits_creditAt _ _ _ (by omega)]

/-! ## Generic lemmas -/

theorem holds_iff_values {F : Type*} [Add F] [Mul F] [Zero F] (cs : System F) (w : ℕ → F) :
    cs.Holds w ↔ ∀ v ∈ cs.values w, v = 0 := by
  simp [System.Holds, System.values]

/-- `Expr.eval` only reads the witness indices in the support. -/
theorem eval_congr {F : Type*} [Add F] [Mul F] (e : Expr F) {w w' : ℕ → F}
    (h : ∀ i ∈ e.support, w i = w' i) : e.eval w = e.eval w' := by
  induction e with
  | wit i => exact h i (by simp [Expr.support])
  | const c => rfl
  | add a b iha ihb =>
    simp only [Expr.support, List.mem_append] at h
    simp only [Expr.eval, iha fun i hi => h i (Or.inl hi), ihb fun i hi => h i (Or.inr hi)]
  | mul a b iha ihb =>
    simp only [Expr.support, List.mem_append] at h
    simp only [Expr.eval, iha fun i hi => h i (Or.inl hi), ihb fun i hi => h i (Or.inr hi)]

/-- The Keccak values read only the committed states `[8 wOff, 8 wOff + 1600)` of the witness. -/
theorem qsKeccakValues_congr {F : Type*} [Add F] [Mul F] [One F] {w w' : ℕ → F} (wOff n : ℕ)
    (hn : n ≤ 800) (input : Vector F 800) (h : ∀ i < 8 * wOff + 1600, w i = w' i) :
    qsKeccakValues w wOff n hn input = qsKeccakValues w' wOff n hn input := by
  have hs : ∀ k < 2, witState w (8 * (wOff + 100 * k)) = witState w' (8 * (wOff + 100 * k)) := by
    intro k hk
    apply Vector.ext
    intro i hi
    simp only [witState, Vector.getElem_ofFn]
    exact h _ (by omega)
  have h0 := hs 0 (by norm_num)
  have h1 := hs (0 + 1) (by norm_num)
  simp only [qsKeccakValues, qsKeccakG, layout, segmentConstraints, segmentConstraint]
  rw [h0, h1]

/-- The evaluated `qs_input` reads only the witness bytes named by the map. -/
theorem qsInput_eval_congr {F : Type*} [Add F] [Mul F] [Zero F] [One F] (pub : State)
    (map : Fin 100 → Option ℕ) (B : ℕ) (hmap : ∀ k b, map k = some b → b < B) {w w' : ℕ → F}
    (h : ∀ i < 8 * B, w i = w' i) :
    (qsInput (F := F) pub map).map (Expr.eval w) =
      (qsInput (F := F) pub map).map (Expr.eval w') := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, qsInput, Vector.getElem_ofFn]
  rcases hm : map ⟨i / 8, by omega⟩ with _ | b
  · rfl
  · have := hmap _ _ hm
    exact h _ (by have := Nat.mod_lt i (show 8 > 0 by norm_num); omega)

/-- `linComb` evaluates entrywise. -/
theorem eval_linComb_congr {F : Type*} [Add F] [Mul F] [Zero F] [One F] {M : ℕ} (l : Fin M → F)
    {T T' : Fin M → Expr F} {w w' : ℕ → F} (h : ∀ k, (T k).eval w = (T' k).eval w') :
    (linComb l T).eval w = (linComb l T').eval w' := by
  have : ∀ (L : List (Fin M)) (a a' : Expr F), a.eval w = a'.eval w' →
      (L.foldl (fun acc k => acc + Expr.const (l k) * T k) a).eval w =
        (L.foldl (fun acc k => acc + Expr.const (l k) * T' k) a').eval w' := by
    intro L
    induction L with
    | nil => exact fun _ _ h => h
    | cons k L ih =>
      intro a a' ha
      exact ih _ _ (by simp only [Expr.eval_add, Expr.eval_mul, Expr.eval_const, ha, h k])
  exact this _ _ _ rfl

theorem eval_qsByte_congr {F : Type*} [Add F] [Mul F] {n : ℕ} (β : Fin 8 → F)
    {s s' : Vector (Expr F) n} {w w' : ℕ → F} (h : ∀ j (hj : j < n), s[j].eval w = s'[j].eval w')
    (k : ℕ) (hk : 8 * k + 8 ≤ n) : (qsByte β s k hk).eval w = (qsByte β s' k hk).eval w' := by
  simp only [qsByte, Expr.eval_add, Expr.eval_mul, Expr.eval_const]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega), h _ (by omega)]

section Field

variable {F : Type*} [Field F] [CharP F 2]

theorem bitF_inj {a b : Bool} (h : (bitF a : F) = bitF b) : a = b := by
  cases a <;> cases b <;> simp_all [bitF]

theorem bitF_add_eq_zero_iff (a b : Bool) : (bitF a + bitF b : F) = 0 ↔ a = b := by
  rw [CharTwo.add_eq_zero]
  exact ⟨bitF_inj, fun h => h ▸ rfl⟩

end Field

theorem stateBit_eq_byteBit (s : State) (i : ℕ) (hi : i < 800) :
    stateBit s i = byteBit (stateByte s) i := by
  have := stateBit_eq s (i / 8) (i % 8) (by omega) (Nat.mod_lt _ (by norm_num))
  rw [show 8 * (i / 8) + i % 8 = i by omega] at this
  rw [this, byteBit]

/-- Byte strings agree on `[0, n)` iff their bits agree on `[0, 8n)`. -/
theorem bytes_eq_iff_bits (b b' : ℕ → UInt8) (n : ℕ) :
    (∀ i < 8 * n, byteBit b i = byteBit b' i) ↔ ∀ k < n, b k = b' k := by
  constructor
  · intro h k hk
    apply uint8_ext
    intro j hj
    rw [← byteBit_eq _ _ _ hj, ← byteBit_eq _ _ _ hj]
    exact h _ (by omega)
  · intro h i hi
    simp only [byteBit, h (i / 8) (by omega)]

/-! ## Ratatouille issue (`src/ratatouille/issue.hpp`) -/

/-- `R_iss((c, T_init, ctx), (nf, r)) ⇔ c = Com(nf, ctx, T_init, r)`
(`security/ratatouille.md` §2.4, `issue.hpp:1-5`). -/
def IssueRel (c : ℕ → UInt8) (tInit : ℕ) (ctx nf r : ℕ → UInt8) : Prop :=
  ∀ k < 32, c k = commit nf ctx tInit r k

section IssueGenerator

variable {F : Type*} [Add F] [Mul F] [Zero F] [One F]

/-- The bit constraints `qs_add_bit_constraint(get_witness_bit(i))`, `i < B`. -/
def bitConstraints (B : ℕ) : System F := (List.range B).map fun i => bitConstraint (Expr.wit i)

/-- `ISSUE_WITNESS_BYTES = 16 + 24 + 200` (`issue.hpp:55-59`). -/
def issueWitnessBytes : ℕ := 240

/-- `qs_keccak(qs, qs_input(qs, encode_com_state({}, ctx, T_init, {}), ISSUE_COM_TO_WIT),
ISSUE_WIT_OFF_STATES = 40, 256)` (`issue.hpp:170-174`). -/
def issueKeccak (ctx : ℕ → UInt8) (tInit : ℕ) : System F × Vector (Expr F) 256 :=
  qsKeccak 40 256 (by norm_num) (qsInput (comState zeros ctx tInit zeros) issueComMap)

/-- `IssueRelation::constraints(qs, {c, t_init, ctx_iss}, chal2)` (`issue.hpp:158-181`): the
`8 · 240` bit constraints, the 1600 segment constraints, and `out[i] + c_i` for `i < 256`. -/
def issueSystem (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) : System F :=
  bitConstraints (8 * issueWitnessBytes) ++ (issueKeccak ctx tInit).1 ++
    (List.finRange 256).map fun i : Fin 256 =>
      (issueKeccak ctx tInit).2[i] + Expr.const (bitF (byteBit c i.1))

/-- The constraint values of `issueSystem`, computed with sharing (`issueSystem_values`). -/
def issueValues (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → F) : List F :=
  let kc := qsKeccakValues w 40 256 (by norm_num)
    ((qsInput (F := F) (comState zeros ctx tInit zeros) issueComMap).map (Expr.eval w))
  (List.range (8 * issueWitnessBytes)).map (fun i => w i * (w i + 1)) ++ kc.1 ++
    (List.finRange 256).map fun i : Fin 256 => kc.2[i] + bitF (byteBit c i.1)

theorem issueSystem_length (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) :
    (issueSystem (F := F) c tInit ctx).length = 3776 := by
  simp only [issueSystem, bitConstraints, List.length_append, List.length_map, List.length_range,
    List.length_finRange, issueKeccak, qsKeccak_length, issueWitnessBytes]

theorem issueSystem_values (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → F) :
    (issueSystem c tInit ctx).values w = issueValues c tInit ctx w := by
  obtain ⟨h1, h2⟩ := qsKeccak_values w 40 256 (by norm_num)
    (qsInput (F := F) (comState zeros ctx tInit zeros) issueComMap)
  have hb : ((bitConstraints (F := F) (8 * issueWitnessBytes)).map fun e => e.eval w) =
      (List.range (8 * issueWitnessBytes)).map (fun i => w i * (w i + 1)) := by
    simp only [bitConstraints, List.map_map]; rfl
  have ho : ((List.finRange 256).map fun i : Fin 256 =>
      (issueKeccak (F := F) ctx tInit).2[i] + Expr.const (bitF (byteBit c i.1))).map
        (fun e => e.eval w) =
      (List.finRange 256).map fun i : Fin 256 => (qsKeccakValues w 40 256 (by norm_num)
        ((qsInput (F := F) (comState zeros ctx tInit zeros) issueComMap).map
          (Expr.eval w))).2[i] + bitF (byteBit c i.1) := by
    rw [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, Expr.eval_add, Expr.eval_const, issueKeccak, Fin.getElem_fin]
    rw [← h2, Vector.getElem_map]
  simp only [issueSystem, issueValues, System.values, List.map_append, hb, ho]
  rw [← h1]
  rfl

end IssueGenerator

section IssueProofs

variable {F : Type*} [Field F] [CharP F 2]

theorem bitConstraints_holds (B : ℕ) (w : ℕ → Bool) :
    (bitConstraints (F := F) B).Holds (ofBits w) := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact bitConstraint_bits w i

theorem bits_of_bitConstraints [DecidableEq F] {B : ℕ} {w : ℕ → F}
    (h : (bitConstraints (F := F) B).Holds w) : ∀ i < B, w i = bitF (decide (w i = 1)) :=
  fun i hi => eq_bitF_of_bitConstraint (h _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

theorem issueComMap_lt : ∀ k b, issueComMap k = some b → b < 40 := by
  intro k b h
  simp only [issueComMap] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

/-- The values read only the `8 · 240` witness bits. -/
theorem issueValues_congr (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) {w w' : ℕ → F}
    (h : ∀ i < 8 * issueWitnessBytes, w i = w' i) :
    issueValues c tInit ctx w = issueValues c tInit ctx w' := by
  have hw : ∀ i < 8 * 40, w i = w' i := fun i hi => h i (by unfold issueWitnessBytes; omega)
  have hb : (List.range (8 * issueWitnessBytes)).map (fun i => w i * (w i + 1)) =
      (List.range (8 * issueWitnessBytes)).map (fun i => w' i * (w' i + 1)) :=
    List.map_congr_left fun i hi => by rw [h i (List.mem_range.1 hi)]
  simp only [issueValues]
  rw [qsInput_eval_congr _ _ 40 issueComMap_lt hw,
    qsKeccakValues_congr (w := w) (w' := w') 40 256 _ _
      (fun i hi => h i (by unfold issueWitnessBytes; omega)), hb]

/-- Constraints that hold at any committed values also hold at the bit vector they encode. -/
theorem issue_holds_ofBits [DecidableEq F] (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8)
    {w : ℕ → F} (h : (issueSystem c tInit ctx).Holds w) :
    (∀ i < 8 * issueWitnessBytes, w i = bitF (decide (w i = 1))) ∧
      (issueSystem c tInit ctx).Holds (ofBits fun i => decide (w i = 1) : ℕ → F) := by
  have hbit : ∀ i < 8 * issueWitnessBytes, w i = bitF (decide (w i = 1)) := by
    have h' := h
    rw [issueSystem, System.holds_append, System.holds_append] at h'
    exact bits_of_bitConstraints h'.1.1
  refine ⟨hbit, ?_⟩
  rw [holds_iff_values, issueSystem_values] at h ⊢
  rwa [issueValues_congr c tInit ctx (w' := ofBits fun i => decide (w i = 1)) hbit] at h

/-- Characterization at a bit vector `w`: the constraints hold iff the committed states are the
true intermediate states of `encode_com_state(nf, ctx, T_init, r)` (with `r`, `nf` decoded from
`w`) and `c = Com(nf, ctx, T_init, r)`. -/
theorem issue_holds_iff (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → Bool) :
    (issueSystem c tInit ctx).Holds (ofBits w : ℕ → F) ↔
      (witVec w (8 * 40) = stateBits (keccakP800Rounds 0 5
          (comState (bytesAt w 16) ctx tInit (bytesAt w 0))) ∧
        witVec w (8 * (40 + 100)) = stateBits (keccakP800Rounds 0 9
          (comState (bytesAt w 16) ctx tInit (bytesAt w 0)))) ∧
      IssueRel c tInit ctx (bytesAt w 16) (bytesAt w 0) := by
  rw [issueSystem, System.holds_append, System.holds_append, ← inputState_issue, issueKeccak,
    ← qsKeccak_holds_iff_bytes (F := F) _ _ w 40 256 (by norm_num)]
  simp only [bitConstraints_holds, true_and]
  refine and_congr_right fun hk => ?_
  have hout : ∀ i (hi : i < 256),
      (((qsKeccak 40 256 (by norm_num) (qsInput (F := F) (comState zeros ctx tInit zeros)
        issueComMap)).2[i] + Expr.const (bitF (byteBit c i))).eval (ofBits w) = 0 ↔
        byteBit (commit (bytesAt w 16) ctx tInit (bytesAt w 0)) i = byteBit c i) := by
    intro i hi
    rw [Expr.eval_add, qsKeccak_sound _ _ w 40 256 _ hk i hi, Expr.eval_const,
      bitF_add_eq_zero_iff, inputState_issue, stateBit_eq_byteBit _ _ (by omega), commit]
  rw [IssueRel, ← bytes_eq_iff_bits]
  constructor
  · intro ho i hi
    exact ((hout i hi).1 (ho _ (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩))).symm
  · intro hr e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact (hout i.1 i.2).2 (hr i.1 i.2).symm

/-- **Completeness.** If `c = Com(nf, ctx, T_init, r)` for the decoded `r`, `nf`, and the
committed states are honest (`encode_committed_states`), every constraint holds. -/
theorem issue_complete (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → Bool)
    (hrel : IssueRel c tInit ctx (bytesAt w 16) (bytesAt w 0))
    (h5 : witVec w (8 * 40) = stateBits (keccakP800Rounds 0 5
      (comState (bytesAt w 16) ctx tInit (bytesAt w 0))))
    (h9 : witVec w (8 * (40 + 100)) = stateBits (keccakP800Rounds 0 9
      (comState (bytesAt w 16) ctx tInit (bytesAt w 0)))) :
    (issueSystem c tInit ctx).Holds (ofBits w : ℕ → F) :=
  (issue_holds_iff c tInit ctx w).2 ⟨⟨h5, h9⟩, hrel⟩

/-- **Soundness.** If the constraints hold at any committed values `w ∈ F^ℓ`, then every witness
bit is a bit, and the decoded `(nf, r)` satisfy `c = Com(nf, ctx, T_init, r)`. -/
theorem issue_sound [DecidableEq F] (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → F)
    (h : (issueSystem c tInit ctx).Holds w) :
    (∀ i < 8 * issueWitnessBytes, w i = bitF (decide (w i = 1))) ∧
      IssueRel c tInit ctx (bytesAt (fun i => decide (w i = 1)) 16)
        (bytesAt (fun i => decide (w i = 1)) 0) := by
  obtain ⟨hbit, hb⟩ := issue_holds_ofBits c tInit ctx h
  exact ⟨hbit, ((issue_holds_iff c tInit ctx _).1 hb).2⟩

end IssueProofs

/-! ## Ratatouille spend (`src/ratatouille/spend.hpp`) -/

section SpendGenerator

variable {F K : Type*} [Add F] [Mul F] [Zero F] [One F]

/-- `SPEND_WITNESS_BYTES = 847` (`spend.hpp:92-109`). -/
def spendWitnessBytes : ℕ := 847

/-- A credit value read bit by bit from the witness byte offset `o`
(`witness_credit(off)`, `spend.hpp:347-349`). -/
def creditWit (o : ℕ) : ℕ → Expr F := fun i => Expr.wit (8 * o + i)

/-- The public `d` bit by bit: `poly1((d >> i) & 1)` (`spend.hpp:354`). -/
def dBits (d : ℕ) : ℕ → Expr F := fun i => Expr.const (bitF (d.testBit i))

/-- `sum1 = qs_add_credits(t, x, SPEND_WIT_OFF_K1 = 231)` (`spend.hpp:350-351`). -/
def spendSum1 : System F × Vector (Expr F) 65 := addCredits (creditWit 16) (creditWit 24) 231

/-- `sum2 = qs_add_credits(t', d, SPEND_WIT_OFF_K2 = 239)` (`spend.hpp:352-354`). -/
def spendSum2 (d : ℕ) : System F × Vector (Expr F) 65 := addCredits (creditWit 88) (dBits d) 239

/-- The conservation constraints `sum1[i] + sum2[i]`, `i ≤ 64` (`spend.hpp:357-359`). -/
def conservation (d : ℕ) : System F :=
  (List.finRange 65).map fun i : Fin 65 => (spendSum1 (F := F)).2[i] + (spendSum2 d).2[i]

/-- V1, Com: `qs_keccak(qs_input(encode_com_state(nf, ctx, 0, {}), SPEND_COM_TO_WIT),
SPEND_WIT_OFF_COM_STATES = 247, 256)` (`spend.hpp:362-366`). -/
def spendCom (nf ctx : ℕ → UInt8) : System F × Vector (Expr F) 256 :=
  qsKeccak 247 256 (by norm_num) (qsInput (comState nf ctx 0 zeros) spendComMap)

/-- V1, Tag: `qs_keccak(qs_input(encode_tag_state({}, 0), SPEND_TAG_TO_WIT),
SPEND_WIT_OFF_TAG_STATES = 447, 8M)` (`spend.hpp:372-374`). -/
def spendTag : System F × Vector (Expr F) 360 :=
  qsKeccak 447 360 (by norm_num) (qsInput (tagState zeros 0) spendTagMap)

/-- V2: `qs_keccak(qs_input(encode_com_state({}, ctx, 0, {}), SPEND_COM_NEXT_TO_WIT),
SPEND_WIT_OFF_COM_NEXT_STATES = 647, 256)` (`spend.hpp:392-396`). -/
def spendComNext (ctx : ℕ → UInt8) : System F × Vector (Expr F) 256 :=
  qsKeccak 647 256 (by norm_num) (qsInput (comState zeros ctx 0 zeros) spendComNextMap)

/-- `ly = poly1(0); ly += l.coeff(k) * qs_byte(tag_out, k)` (`spend.hpp:385-388`). -/
def tagCombination (β : Fin 8 → F) (l : Fin uovM → F) (out : Vector (Expr F) 360) : Expr F :=
  linComb l fun k => qsByte β out k.1 (by have := k.isLt; unfold uovM at this; omega)

/-- The combined constraint `ly + qs_lift(lp)` with `lp = qs_eval_combined_public_map(pk, s, l)`
and `s_i = load_witness_8_bits_and_combine(8 (SPEND_WIT_OFF_S + i))`, `SPEND_WIT_OFF_S = 112`
(`spend.hpp:379-389`). -/
def combinedConstraint (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K) (l : Fin uovM → F)
    (out : Vector (Expr F) 360) : Expr F :=
  tagCombination β l out +
    evalCombinedPublicMap β toBits uovN uovM pk (fun i => byteLoad β (112 + i)) l

/-- `SpendRelation::constraints(qs, {pk, nf, d, c', ctx}, chal2)` (`spend.hpp:330-401`), in
`add_constraint` order: the `8 · 847` bit constraints; the carry constraints of `t + x` and of
`t' + d`; the 65 conservation constraints; Com's 1600 segment constraints and `com_out[i] + c_i`
(`i < 256`); Tag's 1600 segment constraints; the combined UOV constraint; Com''s 1600 segment
constraints and `com_next_out[i] + c'_i` (`i < 256`).

Arguments: the embedding constants `β`, the GF(256) bits `toBits`, the expanded key `pk`, the
public nullifier `nf`, the spent credits `d`, the new commitment `c'` (`cNext`), the issuance
context `ctx`, and the combination coefficients `l` (`Combination(chal2,
RATATOUILLE_SPEND_COMBINE_DST)`). -/
def spendSystem (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K) (nf : ℕ → UInt8)
    (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) : System F :=
  bitConstraints (8 * spendWitnessBytes) ++ (spendSum1 (F := F)).1 ++ (spendSum2 d).1 ++
    conservation d ++
    (spendCom nf ctx).1 ++
    (List.finRange 256).map (fun i : Fin 256 => (spendCom nf ctx).2[i] + Expr.wit (8 * 32 + i.1)) ++
    (spendTag (F := F)).1 ++ [combinedConstraint β toBits pk l spendTag.2] ++
    (spendComNext ctx).1 ++
    (List.finRange 256).map (fun i : Fin 256 =>
      (spendComNext ctx).2[i] + Expr.const (bitF (byteBit cNext i.1)))

/-- The constraint values of `spendSystem`, computed with sharing (`spendSystem_values`): the
Keccak parts by `qsKeccakValues`, the rest by `Expr.eval` (with the Tag output as constants). -/
def spendValues (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K) (nf : ℕ → UInt8)
    (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) (w : ℕ → F) : List F :=
  let com := qsKeccakValues w 247 256 (by norm_num)
    ((qsInput (F := F) (comState nf ctx 0 zeros) spendComMap).map (Expr.eval w))
  let tag := qsKeccakValues w 447 360 (by norm_num)
    ((qsInput (F := F) (tagState zeros 0) spendTagMap).map (Expr.eval w))
  let nxt := qsKeccakValues w 647 256 (by norm_num)
    ((qsInput (F := F) (comState zeros ctx 0 zeros) spendComNextMap).map (Expr.eval w))
  (List.range (8 * spendWitnessBytes)).map (fun i => w i * (w i + 1)) ++
    (spendSum1 (F := F)).1.map (Expr.eval w) ++ (spendSum2 d).1.map (Expr.eval w) ++
    (conservation d).map (Expr.eval w) ++
    com.1 ++ (List.finRange 256).map (fun i : Fin 256 => com.2[i] + w (8 * 32 + i.1)) ++
    tag.1 ++ [(combinedConstraint β toBits pk l (tag.2.map Expr.const)).eval w] ++
    nxt.1 ++ (List.finRange 256).map (fun i : Fin 256 => nxt.2[i] + bitF (byteBit cNext i.1))

end SpendGenerator

section SpendValues

variable {F K : Type*} [Add F] [Mul F] [Zero F] [One F]

theorem spendSystem_length (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K)
    (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) :
    (spendSystem β toBits pk nf d cNext ctx l).length = 12282 := by
  simp only [spendSystem, bitConstraints, conservation, spendSum1, spendSum2, addCredits,
    spendCom, spendTag, spendComNext, List.length_append, List.length_map, List.length_range,
    List.length_finRange, qsKeccak_length, List.length_cons, List.length_nil, spendWitnessBytes]

theorem eval_combinedConstraint_congr (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K)
    (l : Fin uovM → F) {out out' : Vector (Expr F) 360} (w : ℕ → F)
    (h : ∀ j (hj : j < 360), out[j].eval w = out'[j].eval w) :
    (combinedConstraint β toBits pk l out).eval w =
      (combinedConstraint β toBits pk l out').eval w := by
  simp only [combinedConstraint, tagCombination, Expr.eval_add]
  rw [eval_linComb_congr l fun k => eval_qsByte_congr β h _ _]

theorem spendSystem_values (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K)
    (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) (w : ℕ → F) :
    (spendSystem β toBits pk nf d cNext ctx l).values w =
      spendValues β toBits pk nf d cNext ctx l w := by
  obtain ⟨c1, c2⟩ := qsKeccak_values w 247 256 (by norm_num)
    (qsInput (F := F) (comState nf ctx 0 zeros) spendComMap)
  obtain ⟨t1, t2⟩ := qsKeccak_values w 447 360 (by norm_num)
    (qsInput (F := F) (tagState zeros 0) spendTagMap)
  obtain ⟨n1, n2⟩ := qsKeccak_values w 647 256 (by norm_num)
    (qsInput (F := F) (comState zeros ctx 0 zeros) spendComNextMap)
  have hb : ((bitConstraints (F := F) (8 * spendWitnessBytes)).map fun e => e.eval w) =
      (List.range (8 * spendWitnessBytes)).map (fun i => w i * (w i + 1)) := by
    simp only [bitConstraints, List.map_map]; rfl
  have hc : ((List.finRange 256).map fun i : Fin 256 =>
      (spendCom (F := F) nf ctx).2[i] + Expr.wit (8 * 32 + i.1)).map (fun e => e.eval w) =
      (List.finRange 256).map fun i : Fin 256 => (qsKeccakValues w 247 256 (by norm_num)
        ((qsInput (F := F) (comState nf ctx 0 zeros) spendComMap).map
          (Expr.eval w))).2[i] + w (8 * 32 + i.1) := by
    rw [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, Expr.eval_add, Expr.eval_wit, spendCom, Fin.getElem_fin]
    rw [← c2, Vector.getElem_map]
  have hn : ((List.finRange 256).map fun i : Fin 256 =>
      (spendComNext (F := F) ctx).2[i] + Expr.const (bitF (byteBit cNext i.1))).map
        (fun e => e.eval w) =
      (List.finRange 256).map fun i : Fin 256 => (qsKeccakValues w 647 256 (by norm_num)
        ((qsInput (F := F) (comState zeros ctx 0 zeros) spendComNextMap).map
          (Expr.eval w))).2[i] + bitF (byteBit cNext i.1) := by
    rw [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, Expr.eval_add, Expr.eval_const, spendComNext, Fin.getElem_fin]
    rw [← n2, Vector.getElem_map]
  have ht : (combinedConstraint β toBits pk l (spendTag (F := F)).2).eval w =
      (combinedConstraint β toBits pk l ((qsKeccakValues w 447 360 (by norm_num)
        ((qsInput (F := F) (tagState zeros 0) spendTagMap).map (Expr.eval w))).2.map
          Expr.const)).eval w := by
    refine eval_combinedConstraint_congr β toBits pk l w fun j hj => ?_
    rw [Vector.getElem_map, Expr.eval_const, ← t2, Vector.getElem_map, spendTag]
  simp only [spendSystem, spendValues, System.values, List.map_append, List.map_cons,
    List.map_nil, hb, hc, hn, ht]
  rw [← c1, ← t1, ← n1]
  rfl

end SpendValues

section SpendProofs

variable {F K : Type*} [Field F] [CharP F 2]

theorem eval_congr_lt (e : Expr F) {B : ℕ} (hs : ∀ j ∈ e.support, j < B) {w w' : ℕ → F}
    (h : ∀ i < B, w i = w' i) : e.eval w = e.eval w' :=
  eval_congr e fun j hj => h j (hs j hj)

theorem support_carry {off i j : ℕ} (hi : i ≤ 64) (hj : j ∈ (carry (F := F) off i).support) :
    j < 8 * off + 64 := by
  unfold carry at hj
  split_ifs at hj
  · simp [Expr.support] at hj
  · simp only [Expr.support, List.mem_singleton] at hj; omega

theorem support_spendSum1 : ∀ e ∈ (spendSum1 (F := F)).1, ∀ j ∈ e.support, j < 8 * 847 := by
  intro e he j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  have hi := List.mem_range.1 hi
  simp only [creditWit, Expr.support, List.mem_append, List.mem_singleton] at hj
  rcases hj with ((((h | h) | h | h) | h | h) | h) <;>
    first | omega | (have := support_carry (by omega) h; omega)

theorem support_spendSum2 (d : ℕ) :
    ∀ e ∈ (spendSum2 (F := F) d).1, ∀ j ∈ e.support, j < 8 * 847 := by
  intro e he j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  have hi := List.mem_range.1 hi
  simp only [creditWit, dBits, Expr.support, List.mem_append, List.mem_singleton,
    List.not_mem_nil] at hj
  rcases hj with ((((h | h) | h | h) | h | h) | h) <;>
    first | omega | (exact h.elim) | (have := support_carry (by omega) h; omega)

theorem support_conservation (d : ℕ) :
    ∀ e ∈ conservation (F := F) d, ∀ j ∈ e.support, j < 8 * 847 := by
  intro e he j hj
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  simp only [spendSum1, spendSum2, addCredits, Fin.getElem_fin, Vector.getElem_ofFn] at hj
  simp only [Expr.support, List.mem_append] at hj
  split_ifs at hj with h1
  · simp only [creditWit, dBits, Expr.support, List.mem_append, List.mem_singleton,
      List.not_mem_nil] at hj
    rcases hj with ((h | h) | h) | ((h | h) | h) <;>
      first | omega | (exact h.elim) | (have := support_carry (by omega) h; omega)
  · rcases hj with h | h <;> (have := support_carry (le_refl 64) h; omega)

theorem spendComMap_lt : ∀ k b, spendComMap k = some b → b < 24 := by
  intro k b h
  simp only [spendComMap] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

theorem spendTagMap_lt : ∀ k b, spendTagMap k = some b → b < 64 := by
  intro k b h
  simp only [spendTagMap] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

theorem spendComNextMap_lt : ∀ k b, spendComNextMap k = some b → b < 112 := by
  intro k b h
  simp only [spendComNextMap] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

variable [Add K] [Mul K] [Zero K]

/-- The values read only the `8 · 847` witness bits. -/
theorem spendValues_congr (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K)
    (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) {w w' : ℕ → F}
    (h : ∀ i < 8 * spendWitnessBytes, w i = w' i) :
    spendValues β toBits pk nf d cNext ctx l w = spendValues β toBits pk nf d cNext ctx l w' := by
  have h' : ∀ i < 8 * 847, w i = w' i := h
  have hmap : ∀ (L : System F), (∀ e ∈ L, ∀ j ∈ e.support, j < 8 * 847) →
      L.map (Expr.eval w) = L.map (Expr.eval w') := fun L hL =>
    List.map_congr_left fun e he => eval_congr_lt e (hL e he) h'
  have hb : (List.range (8 * spendWitnessBytes)).map (fun i => w i * (w i + 1)) =
      (List.range (8 * spendWitnessBytes)).map (fun i => w' i * (w' i + 1)) :=
    List.map_congr_left fun i hi => by rw [h i (List.mem_range.1 hi)]
  have hcom : ∀ i : Fin 256, w (8 * 32 + i.1) = w' (8 * 32 + i.1) := fun i => h' _ (by omega)
  simp only [spendValues]
  rw [qsInput_eval_congr _ _ 24 spendComMap_lt (fun i hi => h' i (by omega)),
    qsInput_eval_congr _ _ 64 spendTagMap_lt (fun i hi => h' i (by omega)),
    qsInput_eval_congr _ _ 112 spendComNextMap_lt (fun i hi => h' i (by omega)),
    qsKeccakValues_congr (w := w) (w' := w') 247 256 _ _ (fun i hi => h' i (by omega)),
    qsKeccakValues_congr (w := w) (w' := w') 447 360 _ _ (fun i hi => h' i (by omega)),
    qsKeccakValues_congr (w := w) (w' := w') 647 256 _ _ (fun i hi => h' i (by omega)),
    hb, hmap _ support_spendSum1, hmap _ (support_spendSum2 d), hmap _ (support_conservation d)]
  have hcomb : ∀ v : Vector F 360, (combinedConstraint β toBits pk l (v.map Expr.const)).eval w =
      (combinedConstraint β toBits pk l (v.map Expr.const)).eval w' := by
    intro v
    have hs : ∀ i < uovN, (byteLoad β (112 + i)).eval w = (byteLoad β (112 + i)).eval w' := by
      intro i hi
      refine eval_congr_lt _ (B := 8 * 847) (fun j hj => ?_) h'
      simp only [byteLoad, Expr.support, List.mem_append, List.mem_singleton, List.not_mem_nil,
        false_or] at hj
      unfold uovN at hi
      omega
    simp only [combinedConstraint, tagCombination, Expr.eval_add]
    rw [eval_linComb_congr (w' := w') l fun k =>
        eval_qsByte_congr β (s := v.map Expr.const) (s' := v.map Expr.const)
          (fun j hj => by simp) _ _,
      eval_evalCombinedPublicMap_congr β toBits uovN uovM pk _ l w w' hs]
  simp only [hcom, hcomb]

end SpendProofs

/-! ### The relation and the honest auxiliary witness -/

section SpendRelation

variable {K : Type*} [Add K] [Mul K] [Zero K]

/-- `R_spend((P, nf, d, c', ctx), (t, r, x, s, nf', t', r'))` (`security/ratatouille.md` §2.4,
`spend.hpp:1-10`): V1 `P(s) = Tag(Com(nf, ctx, t, r), x)`, V2 `c' = Com(nf', ctx, t', r')`, V3
`t + x = t' + d` over ℕ, V4 `t, x, t', d ∈ [0, 2⁶⁴)`. -/
def SpendRel (ofByte : (Fin 8 → Bool) → K) (pk : ℕ → K) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (t : ℕ) (r : ℕ → UInt8) (x : ℕ) (σ : ℕ → K) (nf' : ℕ → UInt8)
    (t' : ℕ) (r' : ℕ → UInt8) : Prop :=
  publicMap uovN uovM pk σ = tagTarget ofByte (commit nf ctx t r) x ∧
    (∀ k < 32, cNext k = commit nf' ctx t' r' k) ∧
    t + x = t' + d ∧ t < 2 ^ 64 ∧ x < 2 ^ 64 ∧ t' < 2 ^ 64 ∧ d < 2 ^ 64

/-- `SpendRel` at the witness decoded from a bit vector (`spend.hpp:92-102`): `r` at byte 0,
`t` at 16, `x` at 24, `nf'` at 64, `t'` at 88, `r'` at 96, `s` at 112. -/
def SpendRelOf (ofByte : (Fin 8 → Bool) → K) (pk : ℕ → K) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (w : ℕ → Bool) : Prop :=
  SpendRel ofByte pk nf d cNext ctx (creditAt w 16) (bytesAt w 0) (creditAt w 24)
    (decode ofByte w 112) (bytesAt w 64) (creditAt w 88) (bytesAt w 96)

end SpendRelation

/-- `maj(a, b, k)` over GF(2): `ab + ak + bk`. -/
def maj (a b k : Bool) : Bool := (a && b) ^^ (a && k) ^^ (b && k)

/-- The committed carries are the true carries of `t + x` (`SPEND_WIT_OFF_K1 = 231`) and of
`t' + d` (`SPEND_WIT_OFF_K2 = 239`): `carries` (`spend.hpp:175-184`). -/
def SpendCarries (d : ℕ) (w : ℕ → Bool) : Prop :=
  (∀ i < 64, carryB w 231 (i + 1) = maj (w (8 * 16 + i)) (w (8 * 24 + i)) (carryB w 231 i)) ∧
    ∀ i < 64, carryB w 239 (i + 1) = maj (w (8 * 88 + i)) (d.testBit i) (carryB w 239 i)

/-- The committed states at `wOff` are `s₅`, `s₉` of `S` (`encode_committed_states`). -/
def StatesOK (w : ℕ → Bool) (wOff : ℕ) (S : State) : Prop :=
  witVec w (8 * wOff) = stateBits (keccakP800Rounds 0 5 S) ∧
    witVec w (8 * (wOff + 100)) = stateBits (keccakP800Rounds 0 9 S)

/-- The three pairs of committed states are honest (`encode_spend_witness`, `spend.hpp:228-262`). -/
def SpendStates (nf ctx : ℕ → UInt8) (w : ℕ → Bool) : Prop :=
  StatesOK w 247 (comState nf ctx (creditAt w 16) (bytesAt w 0)) ∧
    StatesOK w 447 (tagState (bytesAt w 32) (creditAt w 24)) ∧
    StatesOK w 647 (comState (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96))

/-- The combined equation `Σ_k l_k (ι(P(σ)_k) + ι(Tag(c, x)_k)) = 0` (L7-uov.md §6), with `c`
the committed commitment bytes. -/
def CombinedEq {F K : Type*} [CommRing F] [Add K] [Mul K] [Zero K] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (ofByte : (Fin 8 → Bool) → K)
    (pk : ℕ → K) (l : Fin uovM → F) (w : ℕ → Bool) : Prop :=
  ∑ k, l k * (embed β (toBits (publicMap uovN uovM pk (decode ofByte w 112) k)) +
    embed β (toBits (tagTarget ofByte (bytesAt w 32) (creditAt w 24) k))) = 0

/-! ### The parts of the system at a bit vector -/

section SpendBits

variable {F K : Type*} [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

theorem val_congr {f g : ℕ → Bool} {n : ℕ} (h : ∀ i < n, f i = g i) : val f n = val g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [val, ih fun i hi => h i (by omega), h n (by omega)]

theorem sum1_holds_iff (w : ℕ → Bool) :
    (spendSum1 (F := F)).1.Holds (ofBits w) ↔
      ∀ i < 64, carryB w 231 (i + 1) = maj (w (8 * 16 + i)) (w (8 * 24 + i)) (carryB w 231 i) := by
  constructor
  · intro h i hi
    exact (constraint_iff (creditWit 16) (creditWit 24) (fun i => w (8 * 16 + i))
      (fun i => w (8 * 24 + i)) w 231 i rfl rfl).1
      (h _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  · intro h
    exact addCredits_complete _ _ (fun i => w (8 * 16 + i)) (fun i => w (8 * 24 + i)) w 231
      (fun _ _ => rfl) (fun _ _ => rfl) h

theorem sum2_holds_iff (d : ℕ) (w : ℕ → Bool) :
    (spendSum2 (F := F) d).1.Holds (ofBits w) ↔
      ∀ i < 64, carryB w 239 (i + 1) = maj (w (8 * 88 + i)) (d.testBit i) (carryB w 239 i) := by
  constructor
  · intro h i hi
    exact (constraint_iff (creditWit 88) (dBits d) (fun i => w (8 * 88 + i))
      (fun i => d.testBit i) w 239 i rfl rfl).1
      (h _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  · intro h
    exact addCredits_complete _ _ (fun i => w (8 * 88 + i)) (fun i => d.testBit i) w 239
      (fun _ _ => rfl) (fun _ _ => rfl) h

/-- V3: with honest carries, the 65 conservation constraints hold iff `t + x = t' + d` over ℕ
(the adders are exact, `addCredits_sound`; no wrap-around since both sums have 65 bits). -/
theorem conservation_holds_iff (d : ℕ) (hd : d < 2 ^ 64) (w : ℕ → Bool) (hc : SpendCarries d w) :
    (conservation (F := F) d).Holds (ofBits w) ↔
      creditAt w 16 + creditAt w 24 = creditAt w 88 + d := by
  obtain ⟨e1, v1⟩ := addCredits_sound (F := F) (creditWit 16) (creditWit 24)
    (fun i => w (8 * 16 + i)) (fun i => w (8 * 24 + i)) w 231 (fun _ _ => rfl) (fun _ _ => rfl)
    ((sum1_holds_iff w).2 hc.1)
  obtain ⟨e2, v2⟩ := addCredits_sound (F := F) (creditWit 88) (dBits d)
    (fun i => w (8 * 88 + i)) (fun i => d.testBit i) w 239 (fun _ _ => rfl) (fun _ _ => rfl)
    ((sum2_holds_iff d w).2 hc.2)
  rw [val_testBit, Nat.mod_eq_of_lt hd] at v2
  rw [creditAt, creditAt, creditAt, ← v1, ← v2]
  have hi : ∀ i (hi : i < 65), ((spendSum1 (F := F)).2[i] + (spendSum2 d).2[i]).eval (ofBits w) =
      0 ↔ sumB (fun i => w (8 * 16 + i)) (fun i => w (8 * 24 + i)) w 231 i =
        sumB (fun i => w (8 * 88 + i)) (fun i => d.testBit i) w 239 i := by
    intro i hi
    rw [Expr.eval_add, spendSum1, spendSum2, e1 i hi, e2 i hi, bitF_add_eq_zero_iff]
  constructor
  · intro h
    refine val_congr fun i hi' =>
      (hi i hi').1 (h _ (List.mem_map.2 ⟨⟨i, hi'⟩, List.mem_finRange _, ?_⟩))
    rfl
  · intro h e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact (hi i.1 i.2).2 (bits_eq_of_val_eq h i.1 i.2)

theorem byteBit_bytesAt (w : ℕ → Bool) (o i : ℕ) : byteBit (bytesAt w o) i = w (8 * o + i) := by
  have := byteBit_eq (bytesAt w o) (i / 8) (i % 8) (Nat.mod_lt _ (by norm_num))
  rw [show 8 * (i / 8) + i % 8 = i by omega] at this
  rw [this, bytesAt, witByte_bit _ _ _ (Nat.mod_lt _ (by norm_num))]
  congr 1; omega

/-- V1, Com: given the segment constraints, `com_out[i] + c_i` (`i < 256`) hold iff the committed
`c` is `Com(nf, ctx, t, r)`. -/
theorem comOut_holds_iff (nf ctx : ℕ → UInt8) (w : ℕ → Bool)
    (hk : (spendCom (F := F) nf ctx).1.Holds (ofBits w)) :
    System.Holds ((List.finRange 256).map fun i : Fin 256 =>
        (spendCom (F := F) nf ctx).2[i] + Expr.wit (8 * 32 + i.1)) (ofBits w) ↔
      ∀ k < 32, bytesAt w 32 k = commit nf ctx (creditAt w 16) (bytesAt w 0) k := by
  have hout : ∀ i (hi : i < 256), (((spendCom (F := F) nf ctx).2[i] +
      Expr.wit (8 * 32 + i)).eval (ofBits w) = 0 ↔
        byteBit (bytesAt w 32) i = byteBit (commit nf ctx (creditAt w 16) (bytesAt w 0)) i) := by
    intro i hi
    rw [Expr.eval_add, spendCom, qsKeccak_sound _ _ w 247 256 _ hk i hi, Expr.eval_wit,
      show ofBits w (8 * 32 + i) = (bitF (w (8 * 32 + i)) : F) from rfl, bitF_add_eq_zero_iff,
      inputState_spendCom, stateBit_eq_byteBit _ _ (by omega), commit,
      byteBit_bytesAt]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [← bytes_eq_iff_bits]
  constructor
  · intro ho i hi
    exact (hout i hi).1 (ho _ (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩))
  · intro hr e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact (hout i.1 i.2).2 (hr i.1 i.2)

/-- V2: given the segment constraints, `com_next_out[i] + c'_i` hold iff
`c' = Com(nf', ctx, t', r')`. -/
theorem comNextOut_holds_iff (cNext ctx : ℕ → UInt8) (w : ℕ → Bool)
    (hk : (spendComNext (F := F) ctx).1.Holds (ofBits w)) :
    System.Holds ((List.finRange 256).map fun i : Fin 256 =>
        (spendComNext (F := F) ctx).2[i] + Expr.const (bitF (byteBit cNext i.1))) (ofBits w) ↔
      ∀ k < 32, cNext k = commit (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96) k := by
  have hout : ∀ i (hi : i < 256), (((spendComNext (F := F) ctx).2[i] +
      Expr.const (bitF (byteBit cNext i))).eval (ofBits w) = 0 ↔
        byteBit cNext i =
          byteBit (commit (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96)) i) := by
    intro i hi
    rw [Expr.eval_add, spendComNext, qsKeccak_sound _ _ w 647 256 _ hk i hi, Expr.eval_const,
      bitF_add_eq_zero_iff, inputState_spendComNext, stateBit_eq_byteBit _ _ (by omega), commit]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [← bytes_eq_iff_bits]
  constructor
  · intro ho i hi
    exact (hout i hi).1 (ho _ (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩))
  · intro hr e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact (hout i.1 i.2).2 (hr i.1 i.2)

/-- V1, Tag and UOV: given Tag's segment constraints, the combined constraint's value at a bit
vector is `Σ_k l_k (ι(P(σ)_k) + ι(Tag(c, x)_k))` (L7-uov.md §6, L7-keccak.md §4.4). -/
theorem eval_combinedConstraint_bits (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (pk : ℕ → K) (l : Fin uovM → F) (w : ℕ → Bool) (hk : (spendTag (F := F)).1.Holds (ofBits w)) :
    (combinedConstraint β toBits pk l (spendTag (F := F)).2).eval (ofBits w) =
      ∑ k, l k * (embed β (toBits (publicMap uovN uovM pk (decode ofByte w 112) k)) +
        embed β (toBits (tagTarget ofByte (bytesAt w 32) (creditAt w 24) k))) := by
  have htag : ∀ k : Fin uovM, (qsByte β (spendTag (F := F)).2 k.1
      (by have := k.isLt; unfold uovM at this; omega)).eval (ofBits w) =
      embed β (toBits (tagTarget ofByte (bytesAt w 32) (creditAt w 24) k)) := by
    intro k
    have hk8 : k.1 < 45 := k.isLt
    rw [spendTag, eval_qsByte_sound β hβ _ _ w 447 360 _ hk, inputState_spendTag, tagTarget,
      ofUInt8, hι.toBits_ofByte, embed_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [stateBit_eq _ _ _ (by omega) j.isLt]
  simp only [combinedConstraint, tagCombination, Expr.eval_add, eval_linComb, htag,
    eval_evalCombinedPublicMap_bits hι]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end SpendBits

/-! ### Completeness and soundness -/

section SpendMain

variable {F K : Type*} [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

theorem tagState_congr {c c' : ℕ → UInt8} (x : ℕ) (h : ∀ k < 32, c k = c' k) :
    tagState c x = tagState c' x := by
  apply Vector.ext
  intro k hk
  simp only [tagState, Vector.getElem_ofFn]
  split_ifs <;> first | rfl | exact h _ (by omega)

theorem holds_singleton {e : Expr F} {w : ℕ → F} : System.Holds [e] w ↔ e.eval w = 0 := by
  simp [System.Holds]

/-- **Characterization at a bit vector** (for every `l`): the constraints hold iff the committed
states and carries are honest, `t + x = t' + d` over ℕ, the committed `c` is
`Com(nf, ctx, t, r)`, the combined UOV equation holds, and `c' = Com(nf', ctx, t', r')`. -/
theorem spend_holds_iff (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1) (pk : ℕ → K)
    (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F)
    (w : ℕ → Bool) :
    (spendSystem β toBits pk nf d cNext ctx l).Holds (ofBits w) ↔
      SpendStates nf ctx w ∧ SpendCarries d w ∧
        creditAt w 16 + creditAt w 24 = creditAt w 88 + d ∧
        (∀ k < 32, bytesAt w 32 k = commit nf ctx (creditAt w 16) (bytesAt w 0) k) ∧
        CombinedEq β toBits ofByte pk l w ∧
        (∀ k < 32, cNext k = commit (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96) k) := by
  have hk1 : (spendCom (F := F) nf ctx).1.Holds (ofBits w) ↔
      StatesOK w 247 (comState nf ctx (creditAt w 16) (bytesAt w 0)) := by
    rw [spendCom, qsKeccak_holds_iff_bytes, inputState_spendCom]; rfl
  have hk2 : (spendTag (F := F)).1.Holds (ofBits w) ↔
      StatesOK w 447 (tagState (bytesAt w 32) (creditAt w 24)) := by
    rw [spendTag, qsKeccak_holds_iff_bytes, inputState_spendTag]; rfl
  have hk3 : (spendComNext (F := F) ctx).1.Holds (ofBits w) ↔
      StatesOK w 647 (comState (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96)) := by
    rw [spendComNext, qsKeccak_holds_iff_bytes, inputState_spendComNext]; rfl
  simp only [spendSystem, System.holds_append]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    have hc : SpendCarries d w := ⟨(sum1_holds_iff w).1 h1, (sum2_holds_iff d w).1 h2⟩
    refine ⟨⟨hk1.1 h4, hk2.1 h6, hk3.1 h8⟩, hc, (conservation_holds_iff d hd w hc).1 h3,
      (comOut_holds_iff nf ctx w h4).1 h5, ?_, (comNextOut_holds_iff cNext ctx w h8).1 h9⟩
    have := holds_singleton.1 h7
    rwa [eval_combinedConstraint_bits hι hβ pk l w h6] at this
  · rintro ⟨⟨s1, s2, s3⟩, hc, hcons, hcom, hcomb, hnext⟩
    have h4 := hk1.2 s1
    have h6 := hk2.2 s2
    have h8 := hk3.2 s3
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨bitConstraints_holds _ w, (sum1_holds_iff w).2 hc.1⟩,
      (sum2_holds_iff d w).2 hc.2⟩, (conservation_holds_iff d hd w hc).2 hcons⟩, h4⟩,
      (comOut_holds_iff nf ctx w h4).2 hcom⟩, h6⟩, ?_⟩, h8⟩,
      (comNextOut_holds_iff cNext ctx w h8).2 hnext⟩
    rw [holds_singleton, eval_combinedConstraint_bits hι hβ pk l w h6]
    exact hcomb

/-- Given `c = Com(nf, ctx, t, r)` for the committed `c`, the decoded witness satisfies `SpendRel`
iff `P(σ) = Tag(c, x)`, `c' = Com(nf', ctx, t', r')` and `t + x = t' + d` (V4 holds by
construction, given `d < 2⁶⁴`). -/
theorem spendRelOf_iff (pk : ℕ → K) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64)
    (cNext ctx : ℕ → UInt8) (w : ℕ → Bool)
    (hcom : ∀ k < 32, bytesAt w 32 k = commit nf ctx (creditAt w 16) (bytesAt w 0) k) :
    SpendRelOf ofByte pk nf d cNext ctx w ↔
      publicMap uovN uovM pk (decode ofByte w 112) =
          tagTarget ofByte (bytesAt w 32) (creditAt w 24) ∧
        (∀ k < 32, cNext k = commit (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96) k) ∧
        creditAt w 16 + creditAt w 24 = creditAt w 88 + d := by
  have ht : tagTarget ofByte (bytesAt w 32) (creditAt w 24) =
      tagTarget ofByte (commit nf ctx (creditAt w 16) (bytesAt w 0)) (creditAt w 24) := by
    unfold tagTarget; rw [tagState_congr _ hcom]
  rw [SpendRelOf, SpendRel, ht]
  constructor
  · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, creditAt_lt _ _, creditAt_lt _ _, creditAt_lt _ _, hd⟩

/-- **Completeness.** If the decoded witness satisfies `SpendRel`, the committed `c` is
`Com(nf, ctx, t, r)`, and the carries and committed states are honest (as
`encode_spend_witness` computes them), every constraint holds, for every `l`. -/
theorem spend_complete (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1) (pk : ℕ → K)
    (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8) (w : ℕ → Bool)
    (hrel : SpendRelOf ofByte pk nf d cNext ctx w)
    (hcom : ∀ k < 32, bytesAt w 32 k = commit nf ctx (creditAt w 16) (bytesAt w 0) k)
    (hc : SpendCarries d w) (hs : SpendStates nf ctx w) (l : Fin uovM → F) :
    (spendSystem β toBits pk nf d cNext ctx l).Holds (ofBits w) := by
  obtain ⟨hp, hn, hcons⟩ := (spendRelOf_iff pk nf hd cNext ctx w hcom).1 hrel
  refine (spend_holds_iff hι hβ pk nf hd cNext ctx l w).2 ⟨hs, hc, hcons, hcom, ?_, hn⟩
  rw [CombinedEq, hp]
  simp [CharTwo.add_self_eq_zero]

/-- Constraints that hold at any committed values also hold at the bit vector they encode. -/
theorem spend_holds_ofBits [DecidableEq F] (pk : ℕ → K) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) {w : ℕ → F}
    (h : (spendSystem β toBits pk nf d cNext ctx l).Holds w) :
    (∀ i < 8 * spendWitnessBytes, w i = bitF (decide (w i = 1))) ∧
      (spendSystem β toBits pk nf d cNext ctx l).Holds (ofBits fun i => decide (w i = 1)) := by
  have hbit : ∀ i < 8 * spendWitnessBytes, w i = bitF (decide (w i = 1)) := by
    have h' := h
    simp only [spendSystem, System.holds_append] at h'
    exact bits_of_bitConstraints h'.1.1.1.1.1.1.1.1.1
  refine ⟨hbit, ?_⟩
  rw [holds_iff_values, spendSystem_values] at h ⊢
  rwa [spendValues_congr β toBits pk nf d cNext ctx l
    (w' := ofBits fun i => decide (w i = 1)) hbit] at h

/-- **Soundness (deterministic).** If the constraints hold at any committed values `w ∈ F^ℓ`, then
every witness bit is a bit, and for the decoded witness: `c = Com(nf, ctx, t, r)`,
`c' = Com(nf', ctx, t', r')`, `t + x = t' + d` over ℕ, and the combined UOV equation holds. -/
theorem spend_sound [DecidableEq F] (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (pk : ℕ → K) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8)
    (l : Fin uovM → F) (w : ℕ → F) (h : (spendSystem β toBits pk nf d cNext ctx l).Holds w) :
    let wb := fun i => decide (w i = 1)
    (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
      (∀ k < 32, bytesAt wb 32 k = commit nf ctx (creditAt wb 16) (bytesAt wb 0) k) ∧
      (∀ k < 32, cNext k = commit (bytesAt wb 64) ctx (creditAt wb 88) (bytesAt wb 96) k) ∧
      creditAt wb 16 + creditAt wb 24 = creditAt wb 88 + d ∧
      CombinedEq β toBits ofByte pk l wb := by
  obtain ⟨hbit, hb⟩ := spend_holds_ofBits pk nf d cNext ctx l h
  obtain ⟨-, -, hcons, hcom, hcomb, hn⟩ := (spend_holds_iff hι hβ pk nf hd cNext ctx l _).1 hb
  exact ⟨hbit, hcom, hn, hcons, hcomb⟩

open Classical Finset in
/-- **Soundness, end to end.** Fix the committed values `w ∈ F^ℓ` and the instance before drawing
`l`. Either `w` is a bit vector on the `8 · 847` witness bits whose decoded witness satisfies
`SpendRel` (V1–V4), or at most a `1/|F|` fraction of the `l` make every constraint hold. -/
theorem spend_sound_card [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    (hβ : β 0 = 1) (pk : ℕ → K) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64)
    (cNext ctx : ℕ → UInt8) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
        SpendRelOf ofByte pk nf d cNext ctx wb) ∨
      #{l : Fin uovM → F | (spendSystem β toBits pk nf d cNext ctx l).Holds w} *
          Fintype.card F ≤ Fintype.card (Fin uovM → F) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  by_cases hne : ∃ l0, (spendSystem β toBits pk nf d cNext ctx l0).Holds w
  · obtain ⟨l0, h0⟩ := hne
    obtain ⟨hbit, hcom, hn, hcons, -⟩ := spend_sound hι hβ pk nf hd cNext ctx l0 w h0
    by_cases hp : publicMap uovN uovM pk (decode ofByte wb 112) =
        tagTarget ofByte (bytesAt wb 32) (creditAt wb 24)
    · exact Or.inl ⟨wb, hbit, (spendRelOf_iff pk nf hd cNext ctx wb hcom).2 ⟨hp, hn, hcons⟩⟩
    right
    rw [← uov_card_bad hι hp]
    refine Nat.mul_le_mul_right _ (Finset.card_le_card fun l hl => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact (spend_sound hι hβ pk nf hd cNext ctx l w hl).2.2.2.2
  · right
    have : #{l : Fin uovM → F | (spendSystem β toBits pk nf d cNext ctx l).Holds w} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun l _ hl => hne ⟨l, hl⟩
    rw [this, zero_mul]
    exact Nat.zero_le _

end SpendMain

end VoleMole.Arith.Ratatouille
