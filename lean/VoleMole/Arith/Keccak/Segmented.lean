import VoleMole.Arith.Keccak.Inverse

/-!
# The segmented constraint generator `qs_keccak` (`src/keccak/segmented.hpp`)

The generator is written once over a bit algebra (`BitOps T`) and a witness accessor
`wit : ℕ → T` (`get_witness_bit`), like the C++ template over `QS`:

* `segmentConstraint` is `segment_constraint<k>` (`segmented.hpp:241-270`): the committed state
  `next` is the 800 witness bits at `8 (wit_off_states + 100 k)`; the constraints are
  `fwd[i] + next[i]` if `backward = 0`, else `L(fwd)[i] + bwd[i]`, in index order.
* `segmentConstraints` runs the segments of a layout in order (`segment_constraints`), and
  `qsKeccakG` adds the final forward rounds, of which only the last is truncated to `numOut` bits
  (`qs_keccak`, `segmented.hpp:284-293`).
* `layout` is `SEGMENTS = {{3, 2}, {2, 2}}`, `FINAL_ROUNDS = 3` (`segmented.hpp:69-70`).

The instance `T = Bool` is the plain semantics. Its key property (`segmentConstraint_bool`) is an
*iff*: the constraint bits of a segment all vanish exactly when the committed state is the true
round output, which gives soundness and completeness at once (`segmentConstraints_bool`).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

/-- A segment: `forward` rounds forward meet `backward` rounds backward (`segmented.hpp:62-65`). -/
structure Segment where
  forward : ℕ
  backward : ℕ
  deriving DecidableEq, Repr

/-- The number of rounds of a segment. -/
def Segment.len (s : Segment) : ℕ := s.forward + s.backward

/-- `SEGMENTS` (`segmented.hpp:69`). -/
def layout : List Segment := [⟨3, 2⟩, ⟨2, 2⟩]

/-- `FINAL_ROUNDS` (`segmented.hpp:70`). -/
def finalRounds : ℕ := 3

section Generic

variable {T : Type*} (O : BitOps T)

/-- `qs_keccak_rounds_inverse_partial<b>(s, e)` (`segmented.hpp:171-186`): `N_{e-b}⁻ ∘ L⁻ ∘ ⋯ ∘
L⁻ ∘ N_{e-1}⁻`. (`b = 0` is not used: the C++ `static_assert`s `b ≥ 1`.) -/
def roundsInvPartial : ℕ → ℕ → Vector T 800 → Vector T 800
  | 0, _, s => s
  | 1, e, s => iotaChiInv O (e - 1) s
  | b + 2, e, s => roundsInvPartial (b + 1) (e - 1) (thetaRhoPiInv O (iotaChiInv O (e - 1) s))

/-- `qs_keccak_rounds<num>(in, first, n)` (`segmented.hpp:141-154`): only the last round is
truncated to `n` bits. (`num = 0` returns the input; the C++ `static_assert`s `FINAL_ROUNDS ≥ 1`.) -/
def roundsOut (first : ℕ) : ℕ → (n : ℕ) → n ≤ 800 → Vector T 800 → Vector T n
  | 0, n, hn, a => Vector.ofFn fun i => a[i.1]
  | k + 1, n, hn, a => roundN O (first + k) n hn (rounds O first k a)

/-- The committed state at bit offset `off`. -/
def witState (wit : ℕ → T) (off : ℕ) : Vector T 800 := Vector.ofFn fun i => wit (off + i.1)

/-- `segment_constraint<k>` (`segmented.hpp:241-270`), starting at round `start` from state `s`:
the constraints and the next state (committed state `k`). -/
def segmentConstraint (wit : ℕ → T) (wOff k start : ℕ) (seg : Segment) (s : Vector T 800) :
    List T × Vector T 800 :=
  let next := witState wit (8 * (wOff + 100 * k))
  let fwd := rounds O start seg.forward s
  if seg.backward = 0 then
    ((List.finRange 800).map fun i => O.add fwd[i] next[i], next)
  else
    let lin := thetaRhoPi O fwd
    let bwd := roundsInvPartial O seg.backward (start + seg.len) next
    ((List.finRange 800).map fun i => O.add lin[i] bwd[i], next)

/-- `segment_constraints` (`segmented.hpp:272-276`): the constraints, the last committed state
and the first round after it. -/
def segmentConstraints (wit : ℕ → T) (wOff : ℕ) :
    List Segment → ℕ → ℕ → Vector T 800 → List T × Vector T 800 × ℕ
  | [], _, start, s => ([], s, start)
  | seg :: segs, k, start, s =>
    let r := segmentConstraint O wit wOff k start seg s
    let r' := segmentConstraints wit wOff segs (k + 1) (start + seg.len) r.2
    (r.1 ++ r'.1, r'.2)

/-- `qs_keccak` for a layout (`segmented.hpp:284-293`): the constraints and the first `n` output
bits. -/
def qsKeccakG (wit : ℕ → T) (segs : List Segment) (final wOff n : ℕ) (hn : n ≤ 800)
    (input : Vector T 800) : List T × Vector T n :=
  let r := segmentConstraints O wit wOff segs 0 0 input
  (r.1, roundsOut O r.2.2 final n hn r.2.1)

end Generic

/-! ## Relational lemmas -/

section Rel

variable {T U : Type*} {O : BitOps T} {P : BitOps U} {R : T → U → Prop}

theorem roundsInvPartial_rel (hR : BitOps.Rel O P R) (b e : ℕ) {s : Vector T 800}
    {s' : Vector U 800} (h : VRel R s s') :
    VRel R (roundsInvPartial O b e s) (roundsInvPartial P b e s') := by
  induction b using Nat.strong_induction_on generalizing e s s' with
  | _ b ih =>
    match b with
    | 0 => exact h
    | 1 => exact iotaChiInv_rel hR _ h
    | b + 2 =>
      exact ih (b + 1) (by omega) _ (thetaRhoPiInv_rel hR.toAddRel (iotaChiInv_rel hR _ h))

theorem roundsOut_rel (hR : BitOps.Rel O P R) (first num n : ℕ) (hn : n ≤ 800)
    {a : Vector T 800} {a' : Vector U 800} (h : VRel R a a') :
    VRel R (roundsOut O first num n hn a) (roundsOut P first num n hn a') := by
  cases num with
  | zero => intro i hi; simp only [roundsOut, Vector.getElem_ofFn]; exact h _ _
  | succ k => exact roundN_rel hR _ n hn (rounds_rel hR first k h)

theorem witState_rel {wit : ℕ → T} {wit' : ℕ → U} (hw : ∀ i, R (wit i) (wit' i)) (off : ℕ) :
    VRel R (witState wit off) (witState wit' off) := by
  intro i hi; simp only [witState, Vector.getElem_ofFn]; exact hw _

theorem forall₂_map_finRange {n : ℕ} {f : Fin n → T} {g : Fin n → U} (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R ((List.finRange n).map f) ((List.finRange n).map g) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun i _ => h i

theorem segmentConstraint_rel (hR : BitOps.Rel O P R) {wit : ℕ → T} {wit' : ℕ → U}
    (hw : ∀ i, R (wit i) (wit' i)) (wOff k start : ℕ) (seg : Segment) {s : Vector T 800}
    {s' : Vector U 800} (h : VRel R s s') :
    List.Forall₂ R (segmentConstraint O wit wOff k start seg s).1
        (segmentConstraint P wit' wOff k start seg s').1 ∧
      VRel R (segmentConstraint O wit wOff k start seg s).2
        (segmentConstraint P wit' wOff k start seg s').2 := by
  have hn := witState_rel hw (8 * (wOff + 100 * k))
  have hf := rounds_rel hR start seg.forward h
  unfold segmentConstraint
  split_ifs
  · exact ⟨forall₂_map_finRange fun i => hR.add (hf.get i) (hn.get i), hn⟩
  · exact ⟨forall₂_map_finRange fun i => hR.add ((thetaRhoPi_rel hR.toAddRel hf).get i)
      ((roundsInvPartial_rel hR _ _ hn).get i), hn⟩

theorem segmentConstraints_rel (hR : BitOps.Rel O P R) {wit : ℕ → T} {wit' : ℕ → U}
    (hw : ∀ i, R (wit i) (wit' i)) (wOff : ℕ) (segs : List Segment) (k start : ℕ)
    {s : Vector T 800} {s' : Vector U 800} (h : VRel R s s') :
    List.Forall₂ R (segmentConstraints O wit wOff segs k start s).1
        (segmentConstraints P wit' wOff segs k start s').1 ∧
      VRel R (segmentConstraints O wit wOff segs k start s).2.1
        (segmentConstraints P wit' wOff segs k start s').2.1 ∧
      (segmentConstraints O wit wOff segs k start s).2.2 =
        (segmentConstraints P wit' wOff segs k start s').2.2 := by
  induction segs generalizing k start s s' with
  | nil => exact ⟨List.Forall₂.nil, h, rfl⟩
  | cons seg segs ih =>
    obtain ⟨h1, h2⟩ := segmentConstraint_rel hR hw wOff k start seg h
    obtain ⟨h3, h4, h5⟩ := ih (k + 1) (start + seg.len) h2
    exact ⟨List.rel_append h1 h3, h4, h5⟩

theorem qsKeccakG_rel (hR : BitOps.Rel O P R) {wit : ℕ → T} {wit' : ℕ → U}
    (hw : ∀ i, R (wit i) (wit' i)) (segs : List Segment) (final wOff n : ℕ) (hn : n ≤ 800)
    {s : Vector T 800} {s' : Vector U 800} (h : VRel R s s') :
    List.Forall₂ R (qsKeccakG O wit segs final wOff n hn s).1
        (qsKeccakG P wit' segs final wOff n hn s').1 ∧
      VRel R (qsKeccakG O wit segs final wOff n hn s).2 (qsKeccakG P wit' segs final wOff n hn s').2 := by
  obtain ⟨h1, h2, h3⟩ := segmentConstraints_rel hR hw wOff segs 0 0 h
  refine ⟨h1, ?_⟩
  simp only [qsKeccakG]
  rw [h3]
  exact roundsOut_rel hR _ final n hn h2

end Rel

/-! ## Plain semantics -/

section Bool

theorem rounds_succ_right {T : Type*} (O : BitOps T) (first k : ℕ) (a : Vector T 800) :
    rounds O first (k + 1) a = round O (first + k) (rounds O first k a) := by
  induction k generalizing first a with
  | zero => rfl
  | succ k ih =>
    rw [rounds, ih, rounds]
    congr 1; omega

theorem rounds_add {T : Type*} (O : BitOps T) (first a b : ℕ) (s : Vector T 800) :
    rounds O first (a + b) s = rounds O (first + a) b (rounds O first a s) := by
  induction a generalizing first s with
  | zero => rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, rounds, rounds, ih]
    congr 1; omega

/-- `N_j` on plain bits. -/
abbrev chiIotaB (j : ℕ) (b : Vector Bool 800) : Vector Bool 800 := chiIota BitOps.bool j 800 le_rfl b

theorem round_bool (j : ℕ) (a : Vector Bool 800) :
    round BitOps.bool j a = chiIotaB j (thetaRhoPi BitOps.bool a) := rfl

/-- Meeting in the middle: `L(x) = B_b(s)` iff `s` is `b` rounds forward from `x`, ending before
round `e` (Lemma 2.1 of `L7-keccak.md`, both directions). -/
theorem thetaRhoPi_eq_roundsInvPartial_iff (b e : ℕ) (hb : 1 ≤ b) (he : b ≤ e)
    (x s : Vector Bool 800) :
    thetaRhoPi BitOps.bool x = roundsInvPartial BitOps.bool b e s ↔
      s = rounds BitOps.bool (e - b) b x := by
  induction b using Nat.strong_induction_on generalizing e x s with
  | _ b ih =>
    match b, hb with
    | 1, _ =>
      simp only [roundsInvPartial, rounds]
      constructor
      · intro h
        rw [round_bool, h]
        exact (chiIota_iotaChiInv _ s).symm
      · intro h
        rw [h, round_bool, show e - 1 + 0 = e - 1 by omega]
        exact (iotaChiInv_chiIota _ _).symm
    | b + 2, _ =>
      simp only [roundsInvPartial]
      rw [ih (b + 1) (by omega) (e - 1) (by omega) (by omega)]
      rw [show e - 1 - (b + 1) = e - (b + 2) by omega, rounds_succ_right BitOps.bool _ (b + 1),
        show e - (b + 2) + (b + 1) = e - 1 by omega, round_bool]
      constructor
      · intro h
        rw [← h, thetaRhoPi_thetaRhoPiInv, chiIota_iotaChiInv]
      · intro h
        rw [h, iotaChiInv_chiIota, thetaRhoPiInv_thetaRhoPi]

/-- The committed state at bit offset `off` of a bit vector. -/
abbrev witVec (w : ℕ → Bool) (off : ℕ) : Vector Bool 800 := witState w off

theorem map_add_eq_false_iff (u v : Vector Bool 800) :
    (∀ c ∈ (List.finRange 800).map (fun i => BitOps.bool.add u[i] v[i]), c = false) ↔ u = v := by
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, BitOps.bool, Bool.xor_eq_false_iff]
  constructor
  · intro h; ext i hi; exact h ⟨i, hi⟩
  · rintro rfl i; rfl

/-- **One segment** (Lemma 2.1 of `L7-keccak.md`, both directions): the constraint bits vanish iff
the committed state is the output of the segment's rounds. -/
theorem segmentConstraint_bool (w : ℕ → Bool) (wOff k start : ℕ) (seg : Segment)
    (s : Vector Bool 800) :
    (∀ c ∈ (segmentConstraint BitOps.bool w wOff k start seg s).1, c = false) ↔
      witVec w (8 * (wOff + 100 * k)) = rounds BitOps.bool start seg.len s := by
  unfold segmentConstraint
  split_ifs with hb
  · rw [map_add_eq_false_iff, Segment.len, hb, Nat.add_zero, eq_comm]
  · rw [map_add_eq_false_iff, thetaRhoPi_eq_roundsInvPartial_iff _ _ (by omega)
      (by simp [Segment.len]), Segment.len, rounds_add]
    congr 2; simp [Segment.len]

/-- The committed states of a layout are the true intermediate states. -/
def Chain (w : ℕ → Bool) (wOff : ℕ) : List Segment → ℕ → ℕ → Vector Bool 800 → Prop
  | [], _, _, _ => True
  | seg :: segs, k, start, s =>
    witVec w (8 * (wOff + 100 * k)) = rounds BitOps.bool start seg.len s ∧
      Chain w wOff segs (k + 1) (start + seg.len) (witVec w (8 * (wOff + 100 * k)))

/-- The total number of rounds of a list of segments. -/
def segsLen (segs : List Segment) : ℕ := (segs.map Segment.len).sum

theorem segmentConstraints_bool (w : ℕ → Bool) (wOff : ℕ) (segs : List Segment) (k start : ℕ)
    (s : Vector Bool 800) :
    ((∀ c ∈ (segmentConstraints BitOps.bool w wOff segs k start s).1, c = false) ↔
      Chain w wOff segs k start s) ∧
    (segmentConstraints BitOps.bool w wOff segs k start s).2.2 = start + segsLen segs ∧
    (Chain w wOff segs k start s →
      (segmentConstraints BitOps.bool w wOff segs k start s).2.1 =
        rounds BitOps.bool start (segsLen segs) s) := by
  induction segs generalizing k start s with
  | nil => exact ⟨by simp [segmentConstraints, Chain], by simp [segmentConstraints, segsLen],
      fun _ => rfl⟩
  | cons seg segs ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (k + 1) (start + seg.len)
      (segmentConstraint BitOps.bool w wOff k start seg s).2
    have e2 : (segmentConstraint BitOps.bool w wOff k start seg s).2 =
        witVec w (8 * (wOff + 100 * k)) := by
      unfold segmentConstraint; split_ifs <;> rfl
    rw [e2] at ih1 ih2 ih3
    refine ⟨?_, ?_, ?_⟩
    · simp only [segmentConstraints, List.mem_append, Chain]
      rw [← ih1, ← segmentConstraint_bool]
      constructor
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
      · rintro ⟨h1, h2⟩ c (hc | hc); exacts [h1 c hc, h2 c hc]
    · simp only [segmentConstraints, ih2, segsLen, List.map_cons, List.sum_cons]; omega
    · rintro ⟨h1, h2⟩
      simp only [segmentConstraints]
      rw [ih3 h2, h1, ← rounds_add]
      simp [segsLen]

theorem roundN_getElem {T : Type*} (O : BitOps T) (j n : ℕ) (hn : n ≤ 800) (a : Vector T 800)
    (i : ℕ) (hi : i < n) : (roundN O j n hn a)[i] = (round O j a)[i] := by
  simp [roundN, round, chiIota]

theorem roundsOut_getElem {T : Type*} (O : BitOps T) (first k n : ℕ) (hn : n ≤ 800)
    (a : Vector T 800) (i : ℕ) (hi : i < n) :
    (roundsOut O first (k + 1) n hn a)[i] = (rounds O first (k + 1) a)[i] := by
  rw [roundsOut, roundN_getElem, rounds_succ_right]

end Bool

end VoleMole.Arith.Keccak
