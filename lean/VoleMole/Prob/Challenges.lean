import VoleMole.Prob.Bytes

/-!
# Single-challenge bounds for L3 and L4 at the executable encoding (plan M2)

The counts `Seed.card_not_kosGood_le` (L3) and `EndToEnd.card_qs_bad_le`, `*_comb_bad_gf128` (L4)
turned into probabilities over the uniform byte strings the random oracle returns, decoded as the
executable verifier decodes them (`Prob/Bytes.lean`). No oracle model is involved: each statement
is about one uniform challenge drawn independently of data fixed before it.

## L3 (`hkos`)

* `prU_not_kosGood`: over a uniform VOLEHash challenge, `Pr[¬KOSGood] ≤ |S|³(|F|⁴|T| +
  (L−1)⁵|F|⁴)/(|F|⁸|T|)`, for response functions fixed before it.
* `prU_kos_bad_le`, `chain_kos_bad_le`: the same over a uniform 136-byte `chal1`, at `GF128` and the
  `2⁶⁴` short keys: `≤ epsKOS |S| L`. The committed responses `Chain.kosQ`, `Chain.kosD` do not read
  `chal1` (`kosQ_withChal1`, `kosD_withChal1`, by `rfl`).
* `epsKOS_le`: `epsKOS s L ≤ 2⁻¹⁵⁰` for `s ≤ 2¹²⁰`, `L ≤ 2¹³` (the Lean `|S|³` is `6×` looser than
  `C(|S|, 3)`); every relation has `L ≤ 6912`.

## The canonical slope (L4 §5)

`*_extract_chain`'s `hQS`, `hcomb` quantify over every slope `u*` of the witness rows on `A`, and
`A` depends on `chal2` (through `z`). L4 §5 replaces them by one event about a slope fixed before
`chal2`:
* `Chain.AV st T ch S`: the challenges of `S` on which the VOLE check passes with the chain's `h_V`
  (no `chal2`); `mem_AV_of_onChain`: the chain's challenges lie in it.
* `Chain.uCanon`: a slope of the committed witness rows on `A_V` if one exists, else `0`.
* `slope_eq_uCanon`: on a KOS-good `chal1`, every slope on a set `A ⊆ A_V` with `|A| ≥ 2` is
  `uCanon` (`lift_injective`); `forall_slope_of_uCanon` turns a property of `uCanon` into
  `hQS`/`hcomb`'s form.

## L4 (`hQS`, `hcomb`)

* `prU_qs_bad_le`: over a uniform 56-byte `chal2` decoded into the `zkCoeff` arguments, a system
  failing at `w` has `zkHash = 0` with probability `≤ ε_QS(n) = 2⁻¹²⁸ + (n−1)²2⁻¹⁹²`.
* `prU_comb_bad_le`: over a uniform `l`, a system holding without the relation has probability
  `≤ 2⁻¹²⁸` given the `*_comb_bad_gf128` count.
* `prU_qs_comb_bad_le`: both, over independent uniform `(chal2, l)`: `≤ ε_QS(n) + ε_c` (for each
  fixed `l`, then averaging; the L4 paper proof's product-space argument). `epsQS_le`:
  `ε_QS(n) ≤ 2⁻¹²⁷` for `n ≤ 2³²` (every relation has `n ≤ 12282`).
-/

open Finset ENNReal

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

instance : Nonempty shortKeys := ⟨⟨_, mem_shortKeys 0⟩⟩

/-! ## L3 -/

/-- **L3, probability form.** For response functions `(Q, D)` fixed before the challenge, a
uniform VOLEHash challenge is bad with probability `≤ |S|³(|F|⁴|T| + (L−1)⁵|F|⁴)/(|F|⁸|T|)`. -/
theorem prU_not_kosGood {F X : Type*} [Field F] [Fintype F] [DecidableEq F] (T' : Finset F)
    [Nonempty T'] {L : ℕ} (S : Finset X) {e : X → F} (he : Set.InjOn e S) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) :
    prU (Seed.Ch F T') (fun c => ¬Seed.KOSGood c (S : Set X) e Q D) ≤
      ((#S ^ 3 * (Fintype.card F ^ 4 * #T' + (L - 1) ^ 5 * Fintype.card F ^ 4) : ℕ) : ℝ≥0∞) /
        Fintype.card (Seed.Ch F T') := by
  classical
  exact prU_le_of_card_le _ (Seed.card_not_kosGood_le T' S he Q D)

/-- `ε_KOS(s, L) = s³(|F|⁴|T| + (L−1)⁵|F|⁴)/(|F|⁸|T|)` at `|F| = 2¹²⁸`, `|T| = 2⁶⁴`. -/
noncomputable def epsKOS (s L : ℕ) : ℝ≥0∞ :=
  ((s ^ 3 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (L - 1) ^ 5 * (2 ^ 128) ^ 4) : ℕ) : ℝ≥0∞) /
    ((2 ^ (8 * 136) : ℕ) : ℝ≥0∞)

lemma epsKOS_mono {s s' L : ℕ} (h : s ≤ s') : epsKOS s L ≤ epsKOS s' L := by
  unfold epsKOS
  gcongr

/-- **L3 at the executable encoding**: a uniform 136-byte `chal1`, parsed as `chOf` parses it, is
bad for response functions fixed before it with probability `≤ epsKOS |S| L`. -/
theorem prU_kos_bad_le {T : CrtTables} (hT : liftInvOk T = true) {L : ℕ} (S : Finset Blocks)
    (Q : Blocks → Fin L → GF128) (D : Blocks → Fin 4 → GF128) :
    prU (Bytes 136) (fun b => ¬Seed.KOSGood (chOf gfId mem_shortKeys b.ba) (S : Set Blocks)
      (lift T) Q D) ≤ epsKOS #S L := by
  have h := prU_not_kosGood shortKeys S (e := lift T) (lift_injective hT).injOn Q D
  rw [prU_map_equiv chal1Equiv, card_ch, GF128.card_eq, card_shortKeys] at h
  exact h

end VoleMole.Prob

namespace VoleMole.Verifier.Bridge.Chain

open VoleMole.Prob

/-- The chain with `chal1` replaced. -/
def withChal1 (ch : Chain) (c : ByteArray) : Chain := { ch with chal1 := c }

variable (st : Statement) (ch : Chain) (T : CrtTables)

/-- The committed responses do not read `chal1`. -/
@[simp] lemma kosQ_withChal1 (c : ByteArray) : (ch.withChal1 c).kosQ st T = ch.kosQ st T := rfl
@[simp] lemma kosD_withChal1 (c : ByteArray) : (ch.withChal1 c).kosD st T = ch.kosD st T := rfl
@[simp] lemma kosCh_withChal1 (c : ByteArray) :
    (ch.withChal1 c).kosCh = chOf gfId mem_shortKeys c := rfl

end VoleMole.Verifier.Bridge.Chain

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

/-- **L3 for a chain**: over a uniform `chal1`, the chain's committed responses are KOS-bad with
probability `≤ epsKOS |S| L`. -/
theorem chain_kos_bad_le {T : CrtTables} (hT : liftInvOk T = true) (st : Statement) (ch : Chain)
    (S : Finset Blocks) :
    prU (Bytes 136) (fun b => ¬Seed.KOSGood (ch.withChal1 b.ba).kosCh (S : Set Blocks) (lift T)
      ((ch.withChal1 b.ba).kosQ st T) ((ch.withChal1 b.ba).kosD st T)) ≤
      epsKOS #S (Chain.kosL st) := by
  simp only [Chain.kosQ_withChal1, Chain.kosD_withChal1, Chain.kosCh_withChal1]
  exact prU_kos_bad_le hT S (ch.kosQ st T) (ch.kosD st T)

set_option exponentiation.threshold 1100 in
/-- **`ε_KOS ≤ 2⁻¹⁵⁰`** for at most `2¹²⁰` challenges and `L ≤ 2¹³` hashed rows. -/
theorem epsKOS_le {s L : ℕ} (hs : s ≤ 2 ^ 120) (hL : L ≤ 2 ^ 13) :
    epsKOS s L ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ := by
  have hN : s ^ 3 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (L - 1) ^ 5 * (2 ^ 128) ^ 4) ≤ 2 ^ 938 :=
    calc _ ≤ (2 ^ 120) ^ 3 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (2 ^ 13) ^ 5 * (2 ^ 128) ^ 4) := by
          gcongr; omega
      _ ≤ 2 ^ 938 := by norm_num
  refine ENNReal.div_le_of_le_mul ?_
  rw [Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) ^ (8 * 136) = 2 ^ 150 * 2 ^ 938 by rw [← pow_add],
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  exact_mod_cast hN

/-! ## The canonical slope -/

end VoleMole.Prob

namespace VoleMole.Verifier.Bridge.Chain

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd

variable (st : Statement) (T : CrtTables) (ch : Chain)

/-- **`A_V`**: the challenges of `S` on which the VOLE check of the committed responses passes with
the chain's `h_V`. It depends on `chal1`, `ũ`, `h_V` and the commitments, not on `chal2`. -/
noncomputable def AV (S : Finset Blocks) : Finset Blocks := by
  classical
  exact S.filter fun Δ => Seed.kosValue ch.kosCh (lift T) (ch.kosQ st T) (ch.kosD st T)
    (ch.kosU st) Δ = fun j : Fin 4 => ch.hV[(j : ℕ)]!

/-- `u` is a slope of the committed witness rows on `A` (the form of `hQS`, `hcomb`). -/
def IsSlope (A : Finset Blocks) (u : Fin st.params.witnessBits → GF128) : Prop :=
  ∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + u j * lift T Δ

/-- **The canonical slope** (L4 §5): a slope of the committed witness rows on `A_V`, or `0` if
there is none. Fixed before `chal2`. -/
noncomputable def uCanon (S : Finset Blocks) : Fin st.params.witnessBits → GF128 := by
  classical
  exact if h : ∃ u, ch.IsSlope st T (ch.AV st T S) u then h.choose else 0

lemma mem_AV {S : Finset Blocks} {Δ : Blocks} :
    Δ ∈ ch.AV st T S ↔ Δ ∈ S ∧ Seed.kosValue ch.kosCh (lift T) (ch.kosQ st T) (ch.kosD st T)
      (ch.kosU st) Δ = fun j : Fin 4 => ch.hV[(j : ℕ)]! := by
  classical
  unfold AV
  rw [Finset.mem_filter]

lemma AV_subset (S : Finset Blocks) : ch.AV st T S ⊆ S := fun _ h => ((ch.mem_AV st T).1 h).1

/-- The chain's challenges lie in `A_V`. -/
theorem mem_AV_of_onChain {S : Finset Blocks} {Δ : Blocks} (h : ch.OnChain st T Δ) (hS : Δ ∈ S) :
    Δ ∈ ch.AV st T S :=
  (ch.mem_AV st T).2 ⟨hS, kos_onChain st ch T h⟩

variable {st T ch}

/-- **A slope through two distinct challenges is unique** (the lift is injective). -/
theorem slope_unique (hT : liftInvOk T = true) {A : Finset Blocks} (h2 : 2 ≤ #A)
    {u u' : Fin st.params.witnessBits → GF128} (hu : ch.IsSlope st T A u)
    (hu' : ch.IsSlope st T A u') : u = u' := by
  obtain ⟨Δ₀, h₀, Δ₁, h₁, hne⟩ := Finset.one_lt_card.1 h2
  have hd : lift T Δ₀ - lift T Δ₁ ≠ 0 := sub_ne_zero.2 fun h => hne (lift_injective hT h)
  funext j
  obtain ⟨v, hv⟩ := hu j
  obtain ⟨v', hv'⟩ := hu' j
  have e₀ := (hv Δ₀ h₀).symm.trans (hv' Δ₀ h₀)
  have e₁ := (hv Δ₁ h₁).symm.trans (hv' Δ₁ h₁)
  have : (u j - u' j) * (lift T Δ₀ - lift T Δ₁) = 0 := by linear_combination e₀ - e₁
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)

/-- On a KOS-good `chal1` the committed witness rows have a slope on `A_V`. -/
theorem exists_slope_AV {S : Finset Blocks}
    (hkos : Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T)) :
    ∃ u, ch.IsSlope st T (ch.AV st T S) u := by
  obtain ⟨uQ, vQ, _, _, hline⟩ := hkos (ch.kosU st) (fun j : Fin 4 => ch.hV[(j : ℕ)]!)
    (ch.AV st T S) (fun Δ h => Finset.mem_coe.2 (ch.AV_subset st T S (Finset.mem_coe.1 h)))
    fun Δ h => ((ch.mem_AV st T).1 (Finset.mem_coe.1 h)).2
  have hk : ∀ j : Fin st.params.witnessBits, (j : ℕ) < kosL st := fun j => by
    have := witnessBits_le st.params; unfold kosL; omega
  refine ⟨fun j => uQ ⟨j, hk j⟩, fun j => ⟨vQ ⟨j, hk j⟩, fun Δ hΔ => ?_⟩⟩
  have := congrFun (hline Δ (Finset.mem_coe.2 hΔ)).1 ⟨j, hk j⟩
  rw [ch.kosQ_row st T Δ (lt_of_lt_of_le j.isLt (witnessBits_le _))] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [Qw, this, mul_comm]

/-- **Every slope on a set of at least two challenges in `A_V` is the canonical slope**, on a
KOS-good `chal1`. -/
theorem slope_eq_uCanon (hT : liftInvOk T = true) {S A : Finset Blocks}
    (hkos : Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T))
    (hAV : A ⊆ ch.AV st T S) (h2 : 2 ≤ #A) {uStar : Fin st.params.witnessBits → GF128}
    (hs : ch.IsSlope st T A uStar) : uStar = ch.uCanon st T S := by
  classical
  have hex := exists_slope_AV hkos
  have hc : ch.IsSlope st T (ch.AV st T S) (ch.uCanon st T S) := by
    unfold uCanon
    split_ifs
    exact hex.choose_spec
  exact slope_unique hT h2 hs fun j => (hc j).imp fun v hv Δ hΔ => hv Δ (hAV hΔ)

/-- **`hQS`, `hcomb` from one event about `uCanon`**: a property of the canonical slope holds for
every slope on a set `A ⊆ S` of challenges on the chain with `|A| ≥ 2`. -/
theorem forall_slope_of_uCanon (hT : liftInvOk T = true) {S A : Finset Blocks}
    (hkos : Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T))
    (hA : ∀ Δ ∈ A, ch.OnChain st T Δ) (hAS : A ⊆ S)
    (R : (Fin st.params.witnessBits → GF128) → Prop) (hR : R (ch.uCanon st T S)) :
    2 ≤ #A → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      R uStar := fun h2 uStar hs => by
  rwa [slope_eq_uCanon hT hkos (fun Δ hΔ => mem_AV_of_onChain st T ch (hA Δ hΔ) (hAS hΔ)) h2 hs]

end VoleMole.Verifier.Bridge.Chain

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

/-! ## L4 -/

/-- The `zkCoeff` arguments of `*_extract_chain` at `chal2 = b`. -/
lemma ch2Dec_coe (b : Bytes 56) :
    ((ch2Dec b).1, (ch2Dec b).2.1, (ch2Dec b).2.2.1, ((ch2Dec b).2.2.2 : GF128)) =
      (gfOfBytes b.ba 0, gfOfBytes b.ba 16, gfOfBytes b.ba 32, ⟨W128.word b.ba 48, 0⟩) := rfl

/-- **L4 (`hQS`), probability form at the executable encoding.** For a system failing at a `w`
fixed before `chal2`, a uniform 56-byte `chal2` gives `zkHash = 0` with probability
`≤ ε_QS(n) = 2⁻¹²⁸ + (n−1)²·2⁻¹⁹²`. -/
theorem prU_qs_bad_le (cs : System GF128) (w : ℕ → GF128) :
    prU (Bytes 56) (fun b => ¬cs.Holds w ∧
      Seed.zkHash cs.length (gfOfBytes b.ba 0) (gfOfBytes b.ba 16) (gfOfBytes b.ba 32)
        ⟨W128.word b.ba 48, 0⟩ (valVec cs w) = 0) ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) cs.length) := by
  classical
  by_cases hw : cs.Holds w
  · exact (prU_mono (P := fun b => ¬cs.Holds w ∧ _) fun _ h => h.1 hw).trans
      (le_of_eq prU_false) |>.trans (by simp)
  have hf : valVec cs w ≠ 0 := fun h => hw ((holds_iff_valVec_eq_zero cs w).2 h)
  let P : Chal2 → Prop := fun x =>
    Seed.zkHash cs.length x.1 x.2.1 x.2.2.1 x.2.2.2 (valVec cs w) = 0
  have hev : prU (Bytes 56) (fun b => ¬cs.Holds w ∧
      Seed.zkHash cs.length (gfOfBytes b.ba 0) (gfOfBytes b.ba 16) (gfOfBytes b.ba 32)
        ⟨W128.word b.ba 48, 0⟩ (valVec cs w) = 0) = prU Chal2 P := by
    rw [prU_map_equiv chal2Equiv]
    exact prU_congr fun b => ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩
  -- `Chal2 = F × F × F × shortKeys` is `chalSpace shortKeys` inside `F⁴`.
  let φ : Chal2 ↪ GF128 × GF128 × GF128 × GF128 :=
    ⟨fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2), fun x y h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 (Subtype.ext h.2.2.2)))⟩
  have hmap : (univ : Finset Chal2).map φ = Seed.chalSpace shortKeys := by
    ext ⟨a, b, c, t⟩
    simp only [Finset.mem_map, mem_univ, true_and, Seed.chalSpace, mem_product]
    constructor
    · rintro ⟨x, hx⟩
      have ht : (x.2.2.2 : GF128) = t := congrArg (fun y => y.2.2.2) hx
      exact ht ▸ x.2.2.2.2
    · intro ht; exact ⟨(a, b, c, ⟨t, ht⟩), rfl⟩
  have hcount : #{x : Chal2 | P x} =
      #{x ∈ Seed.chalSpace shortKeys | Seed.zkHash cs.length x.1 x.2.1 x.2.2.1 x.2.2.2
        (valVec cs w) = 0} := by
    rw [← hmap, Finset.filter_map, Finset.card_map]
    rfl
  have hcard : Fintype.card Chal2 = #(Seed.chalSpace shortKeys) := by
    rw [← hmap, Finset.card_map, Finset.card_univ]
  rw [hev, prU_eq_ofReal, hcount, hcard]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Seed.zkHash_prob_le hf shortKeys ⟨_, mem_shortKeys 0⟩
  rwa [GF128.card_eq, card_shortKeys] at this

/-- **L4, both events** (`hQS` and `hcomb`): for systems `cs l` of length `n` depending on a
combination vector `l`, a `w` and a witness predicate fixed before `chal2` and `l`, and `chal2`, `l`
uniform and independent, the system fails with `zkHash = 0` or holds without the relation with
probability `≤ ε_QS(n) + ε_c`. -/
theorem prU_qs_comb_bad_le {Λ : Type*} [Fintype Λ] [Nonempty Λ] (cs : Λ → System GF128) {n : ℕ}
    (hn : ∀ l, (cs l).length = n) (Wit : Prop) (w : ℕ → GF128) {εc : ℝ≥0∞}
    (hεc : prU Λ (fun l => (cs l).Holds w ∧ ¬Wit) ≤ εc) :
    prU (Bytes 56 × Λ) (fun x => (¬(cs x.2).Holds w ∧
      Seed.zkHash (cs x.2).length (gfOfBytes x.1.ba 0) (gfOfBytes x.1.ba 16) (gfOfBytes x.1.ba 32)
        ⟨W128.word x.1.ba 48, 0⟩ (valVec (cs x.2) w) = 0) ∨ ((cs x.2).Holds w ∧ ¬Wit)) ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) + εc :=
  (prU_or_le _ _).trans (add_le_add
    (prU_prod_le_left _ fun l => (prU_qs_bad_le (cs l) w).trans_eq (by rw [hn l]))
    (prU_snd_le (fun l => (cs l).Holds w ∧ ¬Wit) hεc))

/-- `ε_QS(n) ≤ 2⁻¹²⁷` for `n ≤ 2³²` constraints. -/
theorem epsQS_le {n : ℕ} (hn : n ≤ 2 ^ 32) : Seed.epsQS (2 ^ 128) (2 ^ 64) n ≤ 2 / 2 ^ 128 := by
  have h1 : ((n : ℝ) - 1) ^ 2 ≤ (2 ^ 64 : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · norm_num
    have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
    nlinarith
  unfold Seed.epsQS
  push_cast
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **L4 (`hcomb`), probability form.** If at most a `2⁻¹²⁸` fraction of the `l` make the system
hold at `w` without the relation (`*_comb_bad_gf128`), a uniform `l` does so with probability
`≤ 2⁻¹²⁸`. -/
theorem prU_comb_bad_le {M : ℕ} (sys : (Fin M → GF128) → System GF128) (Wit : Prop)
    (w : ℕ → GF128)
    (h : ¬Wit → open Classical in #{l | (sys l).Holds w} * 2 ^ 128 ≤ (2 ^ 128) ^ M) :
    prU (Fin M → GF128) (fun l => (sys l).Holds w ∧ ¬Wit) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hW : Wit
  · rw [prU_congr (R := fun _ => False) fun l => by simp [hW], prU_false]; simp
  have hc := h hW
  calc prU (Fin M → GF128) (fun l => (sys l).Holds w ∧ ¬Wit)
      ≤ prU (Fin M → GF128) (fun l => (sys l).Holds w) := prU_mono fun _ h => h.1
    _ = (#{l | (sys l).Holds w} : ℝ≥0∞) / (2 ^ 128) ^ M := by
        rw [prU_eq_card, card_fun_gf128, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
          ENNReal.le_div_iff_mul_le (by simp) (by simp)]
        exact_mod_cast hc

end VoleMole.Prob
