import VoleMole.ZK.Sim
import VoleMole.ZK.ByteLemmas
import VoleMole.Verifier.Bridge.BAVCComplete
import VoleMole.Verifier.Bridge.Columns

/-!
# The size of the grinding acceptance set (`lean/docs/zk.md` §10.1)

`grind_and_open` accepts a `Δ` iff its grinding byte is zero and the BAVC opening at `Δ` needs at
most `T_OPEN = 105` seeds (`Sim.accepts`). This file proves

    2¹¹¹ ≤ |A|,   A = {Δ ∈ (F₂⁸)¹⁶ : accepts Δ}           (`card_accSet_ge`)

(the true value is about `0.4 · 2¹²⁰ ≈ 2¹¹⁸·⁷` by sampling; the proof loses about 7.5 bits, see
below). An exact count is out of reach of the kernel: the `17` hidden leaves are interleaved
across one tree, so a dynamic program over the tree needs the subset of vectors placed below each
node as state.

**The open count.** `openCount Δ` (the number of seeds opened) is the number of internal nodes `n`
of the heap of `2L − 1 = 4607` nodes exactly one of whose children `2n + 1`, `2n + 2` lies on a
hidden path (`openCount_eq_sum`, from the walk of `Bridge.walk_spec`). A node `v` lies on a hidden
path iff some hidden leaf `treePos i Δ_i` is a descendant of `v` (`hid_iff`), where `w` descends
from `v` iff `(w + 1) / 2^t = v + 1` for some `t` (`Desc`).

**Counting.** The `17` hidden indices `Δ_i ∈ [0, 2^{k_i})` are free (`enc`: any tuple of indices
is the `Δ` of a 16-byte string with zero grinding byte, `deltaIndex_enc`). On the product set
`S = [0, 120)¹⁷` of index tuples, the number of tuples in which `v` is off every hidden path is
`U v = Π_i (120 − c_i v)`, with `c_i v` the number of leaves `j < 120` of vector `i` below `v`. So
`Σ_{Δ ∈ S} openCount Δ = Σ_n (U(2n+1) + U(2n+2) − 2 U(n))` (`sum_openCount`), a sum the kernel
evaluates in one pass over the tree (`go`, `go_val`: `B = 23136435978897242271657863412906256048`,
i.e. an average open count `≈ 104.28` on `S`; `decide +kernel`, a few seconds). Markov's
inequality then gives at least `120¹⁷ − B/106 ≈ 2¹¹¹·⁵` tuples in `S` with `openCount ≤ 105`, and
`enc` is injective. (On all `2¹²⁰` tuples the average is `≈ 106.38 > 105`, so Markov needs the
restriction to `S`; `[0, 120)¹⁷` is the best box of the form `[0, m)¹⁷`, and splitting into a few
boxes gains less than a tenth of a bit.)
-/

open Finset

namespace VoleMole.ZK.Accept

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

/-! ## Descendants in the heap -/

/-- `w` is `v` or a descendant of `v` in the heap (`v`'s children are `2v + 1`, `2v + 2`). -/
def Desc (v w : ℕ) : Prop := ∃ t, (w + 1) / 2 ^ t = v + 1

lemma div_pow_add (x a b : ℕ) : x / 2 ^ a / 2 ^ b = x / 2 ^ (a + b) := by
  rw [Nat.div_div_eq_div_mul, pow_add]

lemma desc_self (v : ℕ) : Desc v v := ⟨0, by simp⟩

lemma desc_iff (v w : ℕ) : Desc v w ↔ w = v ∨ Desc (2 * v + 1) w ∨ Desc (2 * v + 2) w := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => left; simpa using ht
    | succ s =>
      right
      rw [← div_pow_add, pow_one] at ht
      have : (w + 1) / 2 ^ s = 2 * v + 2 ∨ (w + 1) / 2 ^ s = 2 * v + 3 := by omega
      rcases this with h | h
      · exact Or.inl ⟨s, by rw [h]⟩
      · exact Or.inr ⟨s, by rw [h]⟩
  · rintro (rfl | ⟨t, ht⟩ | ⟨t, ht⟩)
    · exact desc_self w
    · exact ⟨t + 1, by rw [← div_pow_add, ht]; omega⟩
    · exact ⟨t + 1, by rw [← div_pow_add, ht]; omega⟩

lemma desc_le {v w : ℕ} (h : Desc v w) : v ≤ w := by
  obtain ⟨t, ht⟩ := h
  have := Nat.div_le_self (w + 1) (2 ^ t)
  omega

lemma two_le_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)

/-- The two children's subtrees are disjoint. -/
lemma desc_disj (v w : ℕ) : ¬ (Desc (2 * v + 1) w ∧ Desc (2 * v + 2) w) := by
  rintro ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
  rcases lt_trichotomy t s with h | rfl | h
  · obtain ⟨k, rfl⟩ : ∃ k, s = t + (k + 1) := ⟨s - t - 1, by omega⟩
    rw [← div_pow_add, ht] at hs
    have := Nat.div_le_div_left (two_le_pow (k := k + 1) (by omega)) (by norm_num : 0 < 2)
      (a := 2 * v + 1 + 1)
    have e : (2 * v + 1 + 1) / 2 = v + 1 := by omega
    omega
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, t = s + (k + 1) := ⟨t - s - 1, by omega⟩
    rw [← div_pow_add, hs] at ht
    have := Nat.div_le_div_left (two_le_pow (k := k + 1) (by omega)) (by norm_num : 0 < 2)
      (a := 2 * v + 2 + 1)
    have e : (2 * v + 2 + 1) / 2 = v + 1 := by omega
    omega

/-- Every node descends from the root. -/
lemma desc_zero (w : ℕ) : Desc 0 w := by
  refine ⟨Nat.log 2 (w + 1), ?_⟩
  have h1 := Nat.pow_log_le_self 2 (show w + 1 ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (w + 1)
  rw [pow_succ] at h2
  refine Nat.div_eq_of_lt_le ?_ ?_ <;> generalize 2 ^ Nat.log 2 (w + 1) = P at * <;> omega

lemma numNodes_val : BAVC.numNodes = 4607 := rfl
lemma numLeaves_val : BAVC.numLeaves = 2304 := rfl

/-- A leaf's only descendant (among the nodes) is itself. -/
lemma desc_leaf {v w : ℕ} (hv : BAVC.numLeaves - 1 ≤ v) (hw : w < BAVC.numNodes) :
    Desc v w ↔ w = v := by
  rw [numLeaves_val] at hv
  rw [numNodes_val] at hw
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => simpa using ht
    | succ s =>
      have h1 := Nat.div_mul_le_self (w + 1) (2 ^ (s + 1))
      rw [ht] at h1
      have h2 : (v + 1) * 2 ≤ (v + 1) * 2 ^ (s + 1) :=
        Nat.mul_le_mul_left _ (two_le_pow (by omega))
      omega
  · rintro rfl; exact desc_self w

/-! ## The hidden paths -/

/-- **A node is on a hidden path iff a hidden leaf descends from it.** -/
theorem hid_iff (delta : ByteArray) {v : ℕ} (hv : v < BAVC.numNodes) :
    hid delta v = true ↔ ∃ i < BAVC.tau, Desc v (BAVC.treePos i (BAVC.deltaIndex delta i)) := by
  induction h : BAVC.numNodes - v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    subst h
    by_cases hi : v < BAVC.numLeaves - 1
    · have hN := numNodes_val
      have hL := numLeaves_val
      rw [hid_internal delta hi, Bool.or_eq_true,
        ih _ (by omega) (show 2 * v + 1 < BAVC.numNodes by omega) rfl,
        ih _ (by omega) (show 2 * v + 2 < BAVC.numNodes by omega) rfl]
      constructor
      · rintro (⟨i, hi', h⟩ | ⟨i, hi', h⟩)
        · exact ⟨i, hi', (desc_iff _ _).2 (Or.inr (Or.inl h))⟩
        · exact ⟨i, hi', (desc_iff _ _).2 (Or.inr (Or.inr h))⟩
      · rintro ⟨i, hi', h⟩
        rcases (desc_iff _ _).1 h with h | h | h
        · have := treePos_ge i (BAVC.deltaIndex delta i); omega
        · exact Or.inl ⟨i, hi', h⟩
        · exact Or.inr ⟨i, hi', h⟩
    · rw [hid_leaf delta (by omega), (hiddenLeafMarks_spec delta).2, decide_eq_true_iff]
      refine exists_congr fun i => and_congr_right fun hi' => ?_
      rw [desc_leaf (by omega) (treePos_lt hi' (deltaIndex_lt delta i))]

/-! ## The open count as a sum over the internal nodes -/

lemma length_filterMap {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length = (l.map fun x => if (f x).isSome then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases f a <;> simp [ih, Nat.add_comm]

/-- The number of seeds opened at `Δ`, with the walk of `openNodes` read off. -/
theorem openCount_eq_sum (delta : ByteArray) :
    openCount delta = ∑ n ∈ range (BAVC.numLeaves - 1),
      if hid delta (2 * n + 1) != hid delta (2 * n + 2) then 1 else 0 := by
  have h1 : openCount delta = (BAVC.openNodes delta).size := by
    simp [openCount, BAVC.openSeeds]
  rw [h1, ← Array.length_toList, openNodes_toList, length_filterMap, list_sum_range,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  have e : BAVC.numLeaves - 2 - (BAVC.numLeaves - 1 - 1 - m) = m := by
    rw [numLeaves_val] at hm ⊢; omega
  simp only [opened, e]
  split <;> simp_all

instance (v w : ℕ) : Decidable (Desc v w) :=
  decidable_of_iff (∃ t < w + 1, (w + 1) / 2 ^ t = v + 1) <| by
    refine ⟨fun ⟨t, _, h⟩ => ⟨t, h⟩, fun ⟨t, h⟩ => ⟨t, ?_, h⟩⟩
    have h1 : 2 ^ t ≤ w + 1 := by
      by_contra hc
      rw [Nat.div_eq_of_lt (by omega)] at h
      omega
    have := Nat.lt_two_pow_self (n := t)
    omega

/-! ## Tuples of hidden indices -/

/-- The hidden indices `Δ_i ∈ [0, 2^{k_i})` of the `17` small VOLEs. -/
abbrev Idx := (i : Fin BAVC.tau) → Fin (2 ^ BAVC.kOf i)

/-- Bit `c < 120` of the `Δ` whose hidden indices are `d`. -/
def dbitD (d : Idx) (c : ℕ) : Bool :=
  if h : c < 120 then
    (d ⟨BAVC.treeOf c, (treeOf_spec h).1⟩).val.testBit (c - BAVC.bitOffset (BAVC.treeOf c))
  else false

/-- The byte with bits `f 0, …, f 7`. -/
def byteOf (f : ℕ → Bool) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun x d => if f d then x + 2 ^ d else x) 0)

theorem byte_bits : ∀ n : Fin 256, ∀ t : Fin 8,
    ((UInt8.ofNat n.val >>> t.val.toUInt8) &&& 1 == 1) = n.val.testBit t.val := by
  decide +kernel

theorem byte_zero : ∀ n : Fin 256,
    (∀ t : Fin 8, ((UInt8.ofNat n.val >>> t.val.toUInt8) &&& 1 == 1) = false) → n.val = 0 := by
  decide +kernel

lemma byteOf_bit (f : ℕ → Bool) {t : ℕ} (ht : t < 8) :
    ((byteOf f >>> t.toUInt8) &&& 1 == 1) = f t := by
  obtain ⟨hlt, hbit⟩ := foldl_pow_two f 8
  have := byte_bits ⟨_, hlt⟩ ⟨t, ht⟩
  simp only at this
  rw [byteOf, this, hbit]
  simp [ht]

/-- **The encoder**: a 16-byte `Δ` with zero grinding byte and hidden indices `d`. -/
def enc (d : Idx) : Bytes 16 :=
  fun b => if b.val < 15 then byteOf (fun t => dbitD d (8 * b.val + t)) else 0

lemma deltaBit_enc (d : Idx) {c : ℕ} (hc : c < 120) :
    BAVC.deltaBit (ba (enc d)) c = dbitD d c := by
  unfold BAVC.deltaBit
  rw [get!_ba (enc d) (show c / 8 < 16 by omega)]
  simp only [enc, show c / 8 < 15 by omega, ite_true, decide_eq_true hc, Bool.true_and]
  rw [byteOf_bit _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod]

lemma enc_15 (d : Idx) : (ba (enc d)).get! 15 = 0 := by
  rw [get!_ba (enc d) (by norm_num)]
  simp [enc]

theorem deltaIndex_enc (d : Idx) (i : Fin BAVC.tau) :
    BAVC.deltaIndex (ba (enc d)) i = (d i).val := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < BAVC.kOf i
  · rw [BAVC.deltaIndex, testBit_hiddenIndex _ _ hb, deltaBit_enc d (pos_lt i.isLt hb), dbitD]
    split_ifs with hc
    swap; · exact absurd (pos_lt i.isLt hb) hc
    have e : (⟨BAVC.treeOf (BAVC.bitOffset i + b), (treeOf_spec (pos_lt i.isLt hb)).1⟩ :
        Fin BAVC.tau) = i := Fin.ext (treeOf_pos hb)
    rw [e, treeOf_pos hb, Nat.add_sub_cancel_left]
  · have h1 : 2 ^ BAVC.kOf i ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (deltaIndex_lt _ _) h1),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (d i).isLt h1)]

theorem enc_injective : Function.Injective enc := by
  intro d d' h
  funext i
  apply Fin.ext
  rw [← deltaIndex_enc d i, ← deltaIndex_enc d' i, h]

/-- On the encoded `Δ`, a node is on a hidden path iff a hidden leaf `treePos i (d i)` descends
from it. -/
theorem hid_enc (d : Idx) {v : ℕ} (hv : v < BAVC.numNodes) :
    hid (ba (enc d)) v = true ↔ ∃ i : Fin BAVC.tau, Desc v (BAVC.treePos i (d i)) := by
  rw [hid_iff _ hv]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, by rwa [deltaIndex_enc d ⟨i, hi⟩] at h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, i.isLt, by rwa [deltaIndex_enc d i]⟩

/-! ## Counting on the product set `[0, 120)¹⁷` -/

/-- The indices `j < 120` of vector `i`. -/
def inS (i : Fin BAVC.tau) : Finset (Fin (2 ^ BAVC.kOf i)) := univ.filter fun j => j.val < 120

/-- The product set `S = [0, 120)¹⁷` of index tuples. -/
def S : Finset Idx := Fintype.piFinset inS

lemma two_pow_kOf (i : ℕ) : 128 ≤ 2 ^ BAVC.kOf i := by
  rw [kOf_eq]; split_ifs <;> norm_num

lemma card_inS (i : Fin BAVC.tau) : #(inS i) = 120 := by
  have h : inS i = Finset.Iio ⟨120, by have := two_pow_kOf i; omega⟩ := by
    ext j; simp [inS, Fin.lt_def]
  rw [h, Fin.card_Iio]

lemma card_S : #S = 120 ^ 17 := by
  rw [S, Fintype.card_piFinset]
  simp only [card_inS, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- The number of leaves `j < 120` of vector `i` below `v`. -/
def cnt (i : Fin BAVC.tau) (v : ℕ) : ℕ := #((inS i).filter fun j => Desc v (BAVC.treePos i j.val))

/-- The number of tuples in `S` for which `v` is off every hidden path. -/
def U (v : ℕ) : ℕ := ∏ i, (120 - cnt i v)

lemma card_off (v : ℕ) :
    #(S.filter fun d => ∀ i : Fin BAVC.tau, ¬ Desc v (BAVC.treePos i (d i).val)) = U v := by
  have h : (S.filter fun d => ∀ i : Fin BAVC.tau, ¬ Desc v (BAVC.treePos i (d i).val)) =
      Fintype.piFinset fun i => (inS i).filter fun j => ¬ Desc v (BAVC.treePos i j.val) := by
    ext d; simp [S, Fintype.mem_piFinset, forall_and]
  rw [h, Fintype.card_piFinset, U]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := Finset.card_filter_add_card_filter_not (s := inS i)
    (fun j => Desc v (BAVC.treePos i j.val))
  rw [card_inS] at this
  rw [cnt]
  omega

lemma treePos_ge' (i : Fin BAVC.tau) (j : ℕ) : 2303 ≤ BAVC.treePos i j := treePos_ge i j

lemma cnt_internal (i : Fin BAVC.tau) {v : ℕ} (hv : v < 2303) :
    cnt i v = cnt i (2 * v + 1) + cnt i (2 * v + 2) := by
  rw [cnt, cnt, cnt, ← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [mem_filter, mem_union]
    rw [desc_iff]
    have := treePos_ge' i j
    constructor
    · rintro ⟨hj, h | h | h⟩
      · omega
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
    · rintro (⟨hj, h⟩ | ⟨hj, h⟩)
      · exact ⟨hj, Or.inr (Or.inl h)⟩
      · exact ⟨hj, Or.inr (Or.inr h)⟩
  · rw [Finset.disjoint_filter]
    intro j _ h1 h2
    exact desc_disj v _ ⟨h1, h2⟩

/-- The leaf `v` holds a leaf `j < 120` of vector `i`. -/
def leafCnt (i v : ℕ) : ℕ := if (v - 2303) % 17 = i ∧ (v - 2303) / 17 < 120 then 1 else 0

lemma cnt_leaf (i : Fin BAVC.tau) {v : ℕ} (hv : 2303 ≤ v) (hv' : v < 4607) :
    cnt i v = leafCnt i v := by
  have hi := i.isLt
  simp only [BAVC.tau] at hi
  have hk := two_pow_kOf i
  rw [cnt, leafCnt]
  have hd : ∀ j : Fin (2 ^ BAVC.kOf i), Desc v (BAVC.treePos i j) ↔ BAVC.treePos i j = v :=
    fun j => desc_leaf (by rw [numLeaves_val]; omega) (treePos_lt i.isLt j.isLt)
  rw [Finset.filter_congr (fun j _ => hd j)]
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨(v - 2303) / 17, by omega⟩, ?_⟩
    ext j
    simp only [mem_filter, inS, mem_univ, true_and, mem_singleton, BAVC.treePos, numLeaves_val,
      BAVC.tau, Fin.ext_iff]
    constructor
    · rintro ⟨hj, he⟩
      split_ifs at he <;> omega
    · intro hj
      rw [hj]
      refine ⟨by omega, ?_⟩
      split_ifs <;> omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hjS
    have hj := (mem_filter.1 hjS).2
    simp only [BAVC.treePos, numLeaves_val, BAVC.tau]
    split_ifs <;> omega

/-! ## The kernel's pass over the tree -/

structure V17 where
  x0 : ℕ
  x1 : ℕ
  x2 : ℕ
  x3 : ℕ
  x4 : ℕ
  x5 : ℕ
  x6 : ℕ
  x7 : ℕ
  x8 : ℕ
  x9 : ℕ
  x10 : ℕ
  x11 : ℕ
  x12 : ℕ
  x13 : ℕ
  x14 : ℕ
  x15 : ℕ
  x16 : ℕ

namespace V17

/-- Componentwise sum. -/
def add (a b : V17) : V17 :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4, a.x5 + b.x5, a.x6 + b.x6,
    a.x7 + b.x7, a.x8 + b.x8, a.x9 + b.x9, a.x10 + b.x10, a.x11 + b.x11, a.x12 + b.x12,
    a.x13 + b.x13, a.x14 + b.x14, a.x15 + b.x15, a.x16 + b.x16⟩

/-- The zero vector. -/
def zero : V17 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The unit vector `e_k`. -/
def unit (k : ℕ) : V17 :=
  ⟨if k = 0 then 1 else 0, if k = 1 then 1 else 0, if k = 2 then 1 else 0, if k = 3 then 1 else 0,
    if k = 4 then 1 else 0, if k = 5 then 1 else 0, if k = 6 then 1 else 0, if k = 7 then 1 else 0,
    if k = 8 then 1 else 0, if k = 9 then 1 else 0, if k = 10 then 1 else 0,
    if k = 11 then 1 else 0, if k = 12 then 1 else 0, if k = 13 then 1 else 0,
    if k = 14 then 1 else 0, if k = 15 then 1 else 0, if k = 16 then 1 else 0⟩

/-- `Π_i (120 − a_i)`. -/
def u (a : V17) : ℕ :=
  (120 - a.x0) * (120 - a.x1) * (120 - a.x2) * (120 - a.x3) * (120 - a.x4) * (120 - a.x5) *
    (120 - a.x6) * (120 - a.x7) * (120 - a.x8) * (120 - a.x9) * (120 - a.x10) * (120 - a.x11) *
    (120 - a.x12) * (120 - a.x13) * (120 - a.x14) * (120 - a.x15) * (120 - a.x16)

/-- Component `i`. -/
def get (a : V17) : ℕ → ℕ
  | 0 => a.x0
  | 1 => a.x1
  | 2 => a.x2
  | 3 => a.x3
  | 4 => a.x4
  | 5 => a.x5
  | 6 => a.x6
  | 7 => a.x7
  | 8 => a.x8
  | 9 => a.x9
  | 10 => a.x10
  | 11 => a.x11
  | 12 => a.x12
  | 13 => a.x13
  | 14 => a.x14
  | 15 => a.x15
  | 16 => a.x16
  | _ => 0

end V17

lemma V17.get_add (a b : V17) {i : ℕ} (hi : i < 17) : (a.add b).get i = a.get i + b.get i := by
  interval_cases i <;> rfl

lemma V17.get_unit (k : ℕ) {i : ℕ} (hi : i < 17) : (V17.unit k).get i = if k = i then 1 else 0 := by
  interval_cases i <;> rfl

lemma V17.get_zero {i : ℕ} (hi : i < 17) : V17.zero.get i = 0 := by
  interval_cases i <;> rfl

lemma V17.u_eq (a : V17) : a.u = ∏ i : Fin BAVC.tau, (120 - a.get i) := by
  show _ = ∏ i : Fin 17, (120 - a.get i)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, V17.u]
  simp [V17.get, mul_assoc]

/-- The counts at a leaf. -/
def leafVec (v : ℕ) : V17 :=
  if (v - 2303) / 17 < 120 then V17.unit ((v - 2303) % 17) else V17.zero

lemma leafVec_get (v : ℕ) {i : ℕ} (hi : i < 17) : (leafVec v).get i = leafCnt i v := by
  rw [leafVec, leafCnt]
  split_ifs with h1 h2 h2
  · rw [V17.get_unit _ hi]; simp [h2.1]
  · rw [V17.get_unit _ hi]; simp only [ite_eq_right_iff]; exact fun h => absurd ⟨h, h1⟩ h2
  · exact absurd h2.2 h1
  · exact V17.get_zero hi

/-- **One pass over the subtree of `v`** (with `f` levels of fuel): the counts `c_i v`, and the
sum over the internal nodes `n` below `v` of `U(2n+1) + U(2n+2) − 2 U(n)`. -/
def go : ℕ → ℕ → V17 × ℕ
  | 0, v => (leafVec v, 0)
  | f + 1, v =>
    if v < 2303 then
      match go f (2 * v + 1), go f (2 * v + 2) with
      | (a, s), (b, t) =>
        let c := a.add b
        (c, s + t + (a.u + b.u - 2 * c.u))
    else (leafVec v, 0)

/-- The kernel's value of the root's sum. -/
theorem go_val : (go 13 0).2 = 23136435978897242271657863412906256048 := by decide +kernel

/-- The term of the internal node `n`. -/
def term (n : ℕ) : ℕ := U (2 * n + 1) + U (2 * n + 2) - 2 * U n

/-- The sum of the terms of the internal nodes below `v`. -/
def T (v : ℕ) : ℕ := ∑ n ∈ (range 2303).filter (Desc v), term n

lemma T_leaf {v : ℕ} (hv : 2303 ≤ v) : T v = 0 := by
  rw [T, Finset.sum_eq_zero]
  intro n hn
  simp only [mem_filter, mem_range] at hn
  have := desc_le hn.2
  omega

lemma T_internal {v : ℕ} (hv : v < 2303) : T v = term v + T (2 * v + 1) + T (2 * v + 2) := by
  have e : (range 2303).filter (Desc v) =
      insert v ((range 2303).filter (Desc (2 * v + 1)) ∪
        (range 2303).filter (Desc (2 * v + 2))) := by
    ext n
    simp only [mem_filter, mem_range, mem_insert, mem_union]
    rw [desc_iff]
    constructor
    · rintro ⟨hn, h | h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hn, h⟩)
      · exact Or.inr (Or.inr ⟨hn, h⟩)
    · rintro (rfl | ⟨hn, h⟩ | ⟨hn, h⟩)
      · exact ⟨hv, Or.inl rfl⟩
      · exact ⟨hn, Or.inr (Or.inl h)⟩
      · exact ⟨hn, Or.inr (Or.inr h)⟩
  rw [T, e, Finset.sum_insert, Finset.sum_union, T, T, add_assoc]
  · rw [Finset.disjoint_filter]
    intro n _ h1 h2
    exact desc_disj v _ ⟨h1, h2⟩
  · simp only [mem_union, mem_filter, not_or, not_and]
    exact ⟨fun _ h => by have := desc_le h; omega, fun _ h => by have := desc_le h; omega⟩

theorem go_spec : ∀ f v, v < 4607 → 4608 ≤ (v + 1) * 2 ^ f →
    (∀ i : Fin BAVC.tau, (go f v).1.get i = cnt i v) ∧ (go f v).2 = T v := by
  intro f
  induction f with
  | zero =>
    intro v hv hf
    simp at hf
    omega
  | succ f ih =>
    intro v hv hf
    by_cases hi : v < 2303
    · have h1 := ih (2 * v + 1) (by omega) (by rw [pow_succ] at hf; nlinarith)
      have h2 := ih (2 * v + 2) (by omega) (by rw [pow_succ] at hf; nlinarith)
      rcases hga : go f (2 * v + 1) with ⟨a, s⟩
      rcases hgb : go f (2 * v + 2) with ⟨b, t⟩
      rw [hga] at h1
      rw [hgb] at h2
      simp only at h1 h2
      have hc : ∀ i : Fin BAVC.tau, (a.add b).get i = cnt i v := fun i => by
        rw [V17.get_add _ _ i.isLt, h1.1, h2.1, cnt_internal i hi]
      have hU : ∀ (x : V17) (w : ℕ), (∀ i : Fin BAVC.tau, x.get i = cnt i w) → x.u = U w :=
        fun x w h => by rw [V17.u_eq, U]; exact Finset.prod_congr rfl fun i _ => by rw [h i]
      simp only [go, hi, ite_true, hga, hgb]
      refine ⟨hc, ?_⟩
      rw [T_internal hi, h1.2, h2.2, hU _ _ h1.1, hU _ _ h2.1, hU _ _ hc, term]
      ring
    · simp only [go, hi, ite_false]
      refine ⟨fun i => ?_, (T_leaf (by omega)).symm⟩
      rw [leafVec_get _ i.isLt, cnt_leaf i (by omega) hv]

theorem T_zero : T 0 = 23136435978897242271657863412906256048 := by
  rw [← go_val, (go_spec 13 0 (by norm_num) (by norm_num)).2]

/-! ## The sum of the open counts on `S`, and Markov -/

lemma hid_false_enc (d : Idx) {v : ℕ} (hv : v < BAVC.numNodes) :
    hid (ba (enc d)) v = false ↔ ∀ i : Fin BAVC.tau, ¬ Desc v (BAVC.treePos i (d i).val) := by
  rw [← Bool.not_eq_true, hid_enc d hv, not_exists]

lemma sum_off {v : ℕ} (hv : v < BAVC.numNodes) :
    ∑ d ∈ S, (if hid (ba (enc d)) v = false then 1 else 0) = U v := by
  rw [← card_off, Finset.card_filter]
  exact Finset.sum_congr rfl fun d _ => by simp only [hid_false_enc d hv]

lemma xor_count (x y : Bool) :
    (if (x != y) = true then 1 else 0) + 2 * (if (x || y) = false then 1 else 0) =
      (if x = false then 1 else 0) + (if y = false then 1 else 0) := by
  cases x <;> cases y <;> rfl

/-- **The sum of the open counts over `S`** is the root's sum of the terms. -/
theorem sum_openCount : ∑ d ∈ S, openCount (ba (enc d)) = T 0 := by
  have hT : T 0 = ∑ n ∈ range 2303, term n := by
    rw [T, Finset.filter_true_of_mem fun n _ => desc_zero n]
  simp only [openCount_eq_sum, numLeaves_val]
  rw [Finset.sum_comm, hT]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  have key := Finset.sum_congr rfl fun d (_ : d ∈ S) =>
    xor_count (hid (ba (enc d)) (2 * n + 1)) (hid (ba (enc d)) (2 * n + 2))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at key
  simp only [← hid_internal _ (show n < BAVC.numLeaves - 1 by rw [numLeaves_val]; omega)] at key
  rw [sum_off (by rw [numNodes_val]; omega), sum_off (by rw [numNodes_val]; omega),
    sum_off (by rw [numNodes_val]; omega)] at key
  rw [term]
  omega

/-- **Markov's inequality** for the open count on a set `S'` of index tuples. -/
lemma markov (S' : Finset Idx) {B : ℕ} (hB : ∑ d ∈ S', openCount (ba (enc d)) = B) :
    #S' * 106 ≤ #(S'.filter fun d => openCount (ba (enc d)) ≤ 105) * 106 + B := by
  have h1 := Finset.card_filter_add_card_filter_not (s := S')
    (fun d => openCount (ba (enc d)) ≤ 105)
  have h2 : #(S'.filter fun d => ¬ openCount (ba (enc d)) ≤ 105) * 106 ≤
      ∑ d ∈ S'.filter (fun d => ¬ openCount (ba (enc d)) ≤ 105), openCount (ba (enc d)) := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun d hd => ?_
    rw [mem_filter] at hd
    omega
  have h3 : ∑ d ∈ S'.filter (fun d => ¬ openCount (ba (enc d)) ≤ 105), openCount (ba (enc d)) ≤
      ∑ d ∈ S', openCount (ba (enc d)) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

/-- The grinding acceptance set. (Irreducible: elaboration otherwise unfolds membership in this
concrete subset of a `2¹²⁸`-element type.) -/
@[irreducible] def accSet : Finset (Bytes 16) := univ.filter fun x => accepts (ba x) = true

lemma mem_accSet (x : Bytes 16) : x ∈ accSet ↔ accepts (ba x) = true := by
  unfold accSet
  rw [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨@Finset.mem_univ _ _ _, h⟩⟩

lemma enc_mem {d : Idx} (h : openCount (ba (enc d)) ≤ 105) : enc d ∈ accSet := by
  rw [mem_accSet]
  have e : accepts (ba (enc d)) =
      ((ba (enc d)).get! 15 == 0 && decide (openCount (ba (enc d)) ≤ 105)) := rfl
  rw [e, enc_15, decide_eq_true h]
  rfl

lemma card_good_le (S' : Finset Idx) (A : Finset (Bytes 16))
    (hA : ∀ {d : Idx}, openCount (ba (enc d)) ≤ 105 → enc d ∈ A) :
    #(S'.filter fun d => openCount (ba (enc d)) ≤ 105) ≤ #A :=
  Finset.card_le_card_of_injOn enc (fun _ hd => Finset.mem_coe.2 (hA (Finset.mem_filter.1 hd).2))
    enc_injective.injOn

/-- **`2¹¹¹ ≤ |A|`**: at least `2¹¹¹` of the `2¹²⁸` values of `Δ` are accepted by
`grind_and_open` (zero grinding byte, at most `105` opened seeds). By Markov on `S`, at least
`120¹⁷ − B/106` tuples of `S` open at most `105` seeds. -/
theorem card_accSet_ge : 2 ^ 111 ≤ #accSet := by
  have h := markov S (sum_openCount.trans T_zero)
  have h' := card_good_le S accSet enc_mem
  rw [card_S] at h
  have h4 : (120 : ℕ) ^ 17 = 221861110674043699200000000000000000 := by norm_num
  have h5 : (2 : ℕ) ^ 111 = 2596148429267413814265248164610048 := by norm_num
  rw [h4] at h
  rw [h5]
  omega

end VoleMole.ZK.Accept
