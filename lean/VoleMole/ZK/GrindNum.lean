import VoleMole.ZK.HopsIC
import VoleMole.ZK.TwoPhaseHops
import VoleMole.ZK.AcceptCount
import VoleMole.ZK.AcceptVar

/-!
# The bad grinding outcomes, numerically (`lean/docs/zk.md` §10.1)

`GrindBad` (`ZK/HopsH23.lean`): no grinding answer is accepted, or the lifted `Δ' = Δ·W_CRT` of the
accepted one is zero. With the `2³²` answers uniform and `|A| ≥ 2¹¹¹` (`Accept.card_accSet_ge`):

* **`noHitProb_le`**: `noHitProb = (1 − |A|/2¹²⁸)^{2³²} ≤ (1 − 2⁻¹⁷)^{2³²} ≤ 2^{−2¹⁵}`
  (`noHitProb_eq`, from `Grinding.card_noHit`; `(1 − 2⁻¹⁷)^{2¹⁷} ≤ e⁻¹ ≤ 1/2`).
* **`pr_hitZero_le`**: `Pr[the first accepted answer is 0] ≤ 1/|A| ≤ 2⁻¹¹¹`. Given a hit at counter
  `n`, the accepted answer is uniform on `A` (`Grinding.card_isFirstHit`), so the probability is
  `Σ_n |Aᶜ|ⁿ (2¹²⁸)^{N−1−n} / (2¹²⁸)^N = (1 − (|Aᶜ|/2¹²⁸)^N)/|A|`.
* **`tDL_eq_zero`**: an accepted `Δ` with `Δ' = 0` is `0`: `W_CRT` is injective
  (`Bridge.lift_injective`, the kernel-checked left inverse `liftInvOk_tables`), so `Δ' = 0` forces
  the `120` bits of `Δ` to vanish, and acceptance forces the grinding byte to `0`.
* **`grindBad_num`**: `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹¹`. So the "first accepted answer" is the
  right conditioning: `Δ' = 0` happens only at `Δ = 0`, and `0` is one point of `A`.
* **`pr_hitZero_le_114`, `grindBad_num_114`, `grindBad_le_113`**: with the second-moment bound
  `|A| ≥ 2¹¹⁴` (`Accept.card_accSet_ge_114`, `ZK/AcceptVar.lean`) in place of `2¹¹¹`,
  `Pr[Δ' = 0] ≤ 2⁻¹¹⁴` and `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³`. (`grindBad_le_110`, the
  Markov bound's `2⁻¹¹⁰`, is kept as a corollary.)

**`zk_rom_ic_h23_num`, `zk_rom_h23_num`**: the headline bounds `zk_rom_ic_h23` and `zk_rom_h23`
with `Pr[GrindBad]` replaced by `2⁻¹¹³`; every numeric error term downstream (`εRO`, `εROP`,
`εROPm`, `εROPmP`, `εAd*`, `h23*`) uses `grindBad_le_113`.

`Pr[Δ' = 0]` is `Pr[some answer is accepted]/|A|` exactly (given a hit, the accepted `Δ` is
uniform on `A`), and `|A| ≈ 0.397·2¹²⁰` by sampling, so its true value is `≈ 2⁻¹¹⁸·⁶⁷`, not the
`2⁻¹²⁰` of a uniform `Δ'`: grinding conditions `Δ'` on acceptance, and `|A| ≤ 2¹²⁰` makes
`2⁻¹²⁰` a lower bound, not an upper one. The proved `2⁻¹¹⁴` is the second-moment bound on `|A|`;
the remaining `≈ 4.7` bits are the box and the slack of Chebyshev (`ZK/AcceptVar.lean`).
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ZK.Accept

/-! ## The first hit -/

lemma findFirst_none_iff {α : Type} (f : ℕ → Option α) :
    ∀ n c, Prover.findFirst f n c = none ↔ ∀ k < n, f (c + k) = none
  | 0, c => by simp [Prover.findFirst]
  | n + 1, c => by
    simp only [Prover.findFirst]
    rcases h : f c with _ | a
    · rw [findFirst_none_iff f n (c + 1)]
      constructor
      · intro H k hk
        rcases k with _ | k
        · simpa using h
        · rw [show c + (k + 1) = c + 1 + k by omega]; exact H k (by omega)
      · intro H k hk
        rw [show c + 1 + k = c + (k + 1) by omega]; exact H (k + 1) (by omega)
    · simp only [reduceCtorEq, false_iff, not_forall]
      exact ⟨0, by omega, by simp [h]⟩

lemma findFirst_some_spec {α : Type} (f : ℕ → Option α) :
    ∀ n c {a : α}, Prover.findFirst f n c = some a →
      ∃ k < n, f (c + k) = some a ∧ ∀ k' < k, f (c + k') = none
  | 0, _, _, h => by simp [Prover.findFirst] at h
  | n + 1, c, a, h => by
    simp only [Prover.findFirst] at h
    rcases hc : f c with _ | b
    · rw [hc] at h
      obtain ⟨k, hk, h1, h2⟩ := findFirst_some_spec f n (c + 1) h
      refine ⟨k + 1, by omega, by rw [show c + (k + 1) = c + 1 + k by omega]; exact h1, ?_⟩
      intro k' hk'
      rcases k' with _ | k'
      · simpa using hc
      · rw [show c + (k' + 1) = c + 1 + k' by omega]; exact h2 k' (by omega)
    · rw [hc] at h
      cases h
      exact ⟨0, by omega, by simpa using hc, fun _ h => absurd h (by omega)⟩

/-- No answer is accepted iff no answer lies in `A`. -/
theorem firstHit_none_iff (g : Grind) : firstHit g = none ↔ ∀ i, g i ∉ accSet := by
  rw [firstHit, findFirst_none_iff]
  simp only [zero_add, mem_accSet]
  constructor
  · intro H i h
    have := H i i.isLt
    simp [i.isLt, h] at this
  · intro H k hk
    have := H ⟨k, hk⟩
    simp [hk, this]

/-- An accepted answer is the first hit of the answers in `A`. -/
theorem firstHit_some {g : Grind} {c : ℕ} {x : Bytes 16} (h : firstHit g = some (c, x)) :
    ∃ hc : c < nGrind, IsFirstHit accSet g ⟨c, hc⟩ x := by
  rw [firstHit] at h
  obtain ⟨k, hk, h1, h2⟩ := findFirst_some_spec _ _ _ h
  simp only [zero_add] at h1 h2
  simp only [hk, ↓reduceDIte] at h1
  split_ifs at h1 with ha
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  refine ⟨hk, fun i hi => ?_, rfl, (mem_accSet _).2 ha⟩
  have := h2 i hi
  rw [mem_accSet]
  have hi' : i.val < nGrind := i.isLt
  simp only [hi', dite_true] at this
  split_ifs at this with hh
  exact hh

/-! ## Sizes -/

lemma card_bytes16 : Fintype.card (Bytes 16) = 2 ^ 128 := by
  rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]; norm_num

lemma card_grind : Fintype.card Grind = (2 ^ 128) ^ nGrind := by
  rw [Fintype.card_fun, Fintype.card_fin, card_bytes16]

lemma card_accSet_le : #accSet ≤ 2 ^ 128 := card_bytes16 ▸ Finset.card_le_univ _

lemma card_compl_accSet : #accSetᶜ = 2 ^ 128 - #accSet := by
  rw [Finset.card_compl, card_bytes16]

/-! ## No accepted answer -/

/-- **The abort term exactly**: `noHitProb = (1 − |A|/2¹²⁸)^{2³²}`. -/
theorem noHitProb_eq : noHitProb = (1 - (#accSet : ℝ) / 2 ^ 128) ^ nGrind := by
  classical
  rw [noHitProb, pr_congr firstHit_none_iff, pr_def, card_noHit, card_grind]
  have h1 : ((#accSetᶜ : ℕ) : ℝ) = 2 ^ 128 - #accSet := by
    rw [card_compl_accSet, Nat.cast_sub card_accSet_le]; norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [h1, ← div_pow, sub_div, div_self (by positivity)]

lemma one_sub_pow_le : (1 - (1 : ℝ) / 2 ^ 17) ^ (2 ^ 17) ≤ 1 / 2 := by
  have h1 : (1 - (1 : ℝ) / 2 ^ 17) ^ (2 ^ 17) ≤ Real.exp (-(1 / 2 ^ 17)) ^ (2 ^ 17) :=
    pow_le_pow_left₀ (by norm_num) (Real.one_sub_le_exp_neg _) _
  rw [← Real.exp_nat_mul] at h1
  have h2 : ((2 ^ 17 : ℕ) : ℝ) * -(1 / 2 ^ 17) = -1 := by push_cast; ring
  rw [h2] at h1
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    have := Real.add_one_le_exp 1
    exact inv_anti₀ (by norm_num) (by linarith)
  exact h1.trans h3

/-- **`noHitProb ≤ 2^{−2¹⁵}`**: with `|A| ≥ 2¹¹¹`, i.e. acceptance probability `≥ 2⁻¹⁷` per
answer, none of the `2³²` answers is accepted with probability at most `(1 − 2⁻¹⁷)^{2³²}`. -/
theorem noHitProb_le : noHitProb ≤ (1 / 2) ^ (2 ^ 15) := by
  rw [noHitProb_eq]
  have hA : (2 : ℝ) ^ 111 ≤ #accSet := by exact_mod_cast card_accSet_ge
  have hA' : (#accSet : ℝ) ≤ 2 ^ 128 := by exact_mod_cast card_accSet_le
  have h1 : 1 - (#accSet : ℝ) / 2 ^ 128 ≤ 1 - 1 / 2 ^ 17 := by
    have : (1 : ℝ) / 2 ^ 17 ≤ #accSet / 2 ^ 128 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have h0 : 0 ≤ 1 - (#accSet : ℝ) / 2 ^ 128 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hA'
  calc (1 - (#accSet : ℝ) / 2 ^ 128) ^ nGrind ≤ (1 - 1 / 2 ^ 17) ^ nGrind :=
        pow_le_pow_left₀ h0 h1 _
    _ = ((1 - 1 / 2 ^ 17) ^ (2 ^ 17)) ^ (2 ^ 15) := by rw [← pow_mul]; rfl
    _ ≤ (1 / 2) ^ (2 ^ 15) := pow_le_pow_left₀ (by positivity) one_sub_pow_le _

/-! ## The first accepted answer is `0` -/

/-- The event that the first accepted answer is `0`. -/
def HitZero (g : Grind) : Prop := ∃ c, firstHit g = some (c, 0)

/-- Generic form: the sequences whose first hit in `A` is `x` number at most `|Ω|^N / |A|`. -/
lemma card_firstHit_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (A : Finset Ω) {N : ℕ} (x : Ω)
    (P : (Fin N → Ω) → Prop) [DecidablePred P] (hP : ∀ f, P f → ∃ n, IsFirstHit A f n x) :
    #(univ.filter P) * #A ≤ Fintype.card Ω ^ N := by
  classical
  have hab : #Aᶜ ≤ Fintype.card Ω := Finset.card_le_univ _
  have hba : Fintype.card Ω - #Aᶜ = #A := by
    rw [Finset.card_compl]; have := Finset.card_le_univ A; omega
  have hsub : (univ.filter P) ⊆
      univ.biUnion fun n : Fin N => univ.filter fun f => IsFirstHit A f n x := by
    intro f hf
    obtain ⟨n, hn⟩ := hP f (mem_filter.1 hf).2
    exact mem_biUnion.2 ⟨n, mem_univ _, mem_filter.2 ⟨mem_univ _, hn⟩⟩
  have hcard : #(univ.filter P) ≤
      ∑ i ∈ range N, #Aᶜ ^ i * Fintype.card Ω ^ (N - 1 - i) := by
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    rw [← Fin.sum_univ_eq_sum_range (fun i => #Aᶜ ^ i * Fintype.card Ω ^ (N - 1 - i))]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases h0 : x ∈ A
    · rw [card_isFirstHit _ _ _ h0]
    · rw [card_isFirstHit_of_not_mem _ _ _ h0]; exact Nat.zero_le _
  have hgeo := geom_sum₂_mul_of_le hab N
  rw [hba] at hgeo
  calc #(univ.filter P) * #A ≤ (∑ i ∈ range N, #Aᶜ ^ i * Fintype.card Ω ^ (N - 1 - i)) * #A :=
        Nat.mul_le_mul_right _ hcard
    _ = Fintype.card Ω ^ N - #Aᶜ ^ N := hgeo
    _ ≤ Fintype.card Ω ^ N := Nat.sub_le _ _

/-- Generic form, as a probability: `Pr[the first hit in A is x] ≤ 1/|A|`. -/
lemma pr_firstHit_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (A : Finset Ω) (hA : 0 < #A)
    {N : ℕ} (x : Ω) (P : (Fin N → Ω) → Prop) (hP : ∀ f, P f → ∃ n, IsFirstHit A f n x) :
    pr (Fin N → Ω) P ≤ 1 / #A := by
  classical
  have h := card_firstHit_le A x P hP
  rw [pr_def, Fintype.card_fun, Fintype.card_fin,
    div_le_div_iff₀ (by have := Fintype.card_pos_iff.2 ⟨x⟩; positivity) (by exact_mod_cast hA),
    one_mul, ← Nat.cast_mul]
  exact Nat.cast_le.2 h

/-- **`Pr[the first accepted answer is 0] ≤ 1/|A|`**. -/
theorem pr_hitZero_le : pr Grind HitZero ≤ 1 / #accSet :=
  pr_firstHit_le accSet (lt_of_lt_of_le (by positivity) card_accSet_ge) 0 HitZero
    fun _ ⟨_, hc⟩ => (firstHit_some hc).elim fun _ hf => ⟨_, hf⟩

/-! ## A zero lift -/

lemma dbitOf_zero (c : ℕ) : dbitOf 0 c = false := by
  simp [dbitOf]

/-- **An accepted `Δ` with `Δ' = Δ·W_CRT = 0` is `0`.** -/
theorem tDL_eq_zero {x : Bytes 16} (hx : accepts (ba x) = true)
    (h : tDL CrtGen.tables x = 0) : x = 0 := by
  have h1 : lift CrtGen.tables (blocksOf (BAVC.deltaBit (ba x))) = lift CrtGen.tables 0 := by
    rw [← rowMul_lift, map_zero]; exact h
  have h2 := lift_injective liftInvOk_tables h1
  have hbit : ∀ c < 120, BAVC.deltaBit (ba x) c = false := fun c hc => by
    have := dbitOf_blocksOf (BAVC.deltaBit (ba x)) hc
    rw [h2, dbitOf_zero] at this
    exact this.symm
  funext b
  by_cases hb : b.val < 15
  · have hb' : ∀ t : Fin 8, (((UInt8.ofNat (x b).toNat) >>> t.val.toUInt8) &&& 1 == 1) = false := by
      intro t
      have := hbit (8 * b.val + t.val) (by omega)
      unfold BAVC.deltaBit at this
      rw [get!_ba x (show (8 * b.val + t.val) / 8 < 16 by omega)] at this
      simp only [show 8 * b.val + t.val < 120 by omega, decide_true, Bool.true_and,
        show (8 * b.val + t.val) / 8 = b.val by omega,
        show (8 * b.val + t.val) % 8 = t.val by omega] at this
      rw [UInt8.ofNat_toNat]
      exact this
    have := byte_zero ⟨(x b).toNat, UInt8.toNat_lt _⟩ hb'
    apply UInt8.toNat_inj.1
    rw [show (0 : Bytes 16) b = 0 from rfl, UInt8.toNat_zero]
    exact this
  · have hb15 : b = 15 := Fin.ext (by have := b.isLt; show b.val = 15; omega)
    subst hb15
    have h15 : (ba x).get! 15 == 0 := by
      unfold accepts at hx
      simp only [Bool.and_eq_true] at hx
      exact hx.1
    rw [get!_ba x (by norm_num)] at h15
    simpa using h15

/-! ## The bad outcomes -/

lemma grindBad_imp {g : Grind} (h : GrindBad CrtGen.tables g) :
    firstHit g = none ∨ HitZero g := by
  rcases h with h | h
  · exact Or.inl h
  · rcases hf : firstHit g with _ | ⟨c, x⟩
    · exact Or.inl rfl
    · right
      have hd : deltaOf g = x := by rw [deltaOf, hf]; rfl
      rw [hd] at h
      exact ⟨c, by rw [hf, tDL_eq_zero (firstHit_accepts hf) h]⟩

lemma pr_mono {α : Type*} [Fintype α] {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    pr α P ≤ pr α Q := by
  classical
  rw [pr_def, pr_def]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Finset.card_le_card fun x hx => by
    rw [mem_filter] at hx ⊢; exact ⟨hx.1, h x hx.2⟩

/-- **`Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹¹`**, for faest-arch-opt's tables. -/
theorem grindBad_num : pr Grind (GrindBad CrtGen.tables) ≤ (1 / 2) ^ (2 ^ 15) + 1 / 2 ^ 111 := by
  have h1 : pr Grind (GrindBad CrtGen.tables) ≤
      pr Grind (fun g => firstHit g = none) + pr Grind HitZero :=
    (pr_mono fun _ hg => grindBad_imp hg).trans (pr_or_le _ _)
  have h2 : pr Grind HitZero ≤ 1 / 2 ^ 111 := by
    refine pr_hitZero_le.trans ?_
    rw [div_le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le (by positivity) card_accSet_ge)
      (by positivity), one_mul, one_mul]
    exact_mod_cast card_accSet_ge
  exact h1.trans (add_le_add noHitProb_le h2)

/-! ## With the second-moment bound `|A| ≥ 2¹¹⁴` -/

/-- **`Pr[the first accepted answer is 0] ≤ 2⁻¹¹⁴`** (`Accept.card_accSet_ge_114`). -/
theorem pr_hitZero_le_114 : pr Grind HitZero ≤ 1 / 2 ^ 114 := by
  refine pr_hitZero_le.trans ?_
  rw [div_le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le (by positivity) card_accSet_ge)
    (by positivity), one_mul, one_mul]
  exact_mod_cast card_accSet_ge_114

/-- **`Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴`**, for faest-arch-opt's tables. -/
theorem grindBad_num_114 :
    pr Grind (GrindBad CrtGen.tables) ≤ (1 / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 := by
  have h1 : pr Grind (GrindBad CrtGen.tables) ≤
      pr Grind (fun g => firstHit g = none) + pr Grind HitZero :=
    (pr_mono fun _ hg => grindBad_imp hg).trans (pr_or_le _ _)
  exact h1.trans (add_le_add noHitProb_le pr_hitZero_le_114)

lemma half_pow_le_114 : ((1 : ℝ) / 2) ^ (2 ^ 15) ≤ 1 / 2 ^ 114 := by
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- **`Pr[GrindBad] ≤ 2⁻¹¹³`.** The bound every numeric error term below uses. -/
theorem grindBad_le_113 : pr Grind (GrindBad CrtGen.tables) ≤ 1 / 2 ^ 113 := by
  refine grindBad_num_114.trans ?_
  calc ((1 : ℝ) / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 ≤ 1 / 2 ^ 114 + 1 / 2 ^ 114 :=
        add_le_add half_pow_le_114 le_rfl
    _ = 1 / 2 ^ 113 := by norm_num

/-- **`Pr[GrindBad] ≤ 2⁻¹¹⁰`** (Markov's `|A| ≥ 2¹¹¹`; implied by `grindBad_le_113`). -/
theorem grindBad_le_110 : pr Grind (GrindBad CrtGen.tables) ≤ 1 / 2 ^ 110 :=
  grindBad_le_113.trans (by norm_num)

/-! ## The headline bounds, numerically -/

-- (As in `ZK/HopsH23.lean`: the coin types' `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

section Headline

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **`zk_rom_ic_h23` with the grinding term numeric**: in the ROM (`H₃`, `H₂³`, `H₅` uniform
tables) and the ideal-cipher model (the cipher of the whole BAVC and VOLE expansion a uniform
table `E`), the executable prover is

    q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸

close to the programming simulator against a distinguisher that reads `H₃`, `H₅`, `E` at `q₃`,
`q₅`, `q_E` keys and `H₂³` freely. -/
theorem zk_rom_ic_h23_num {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + (qE + 4607)) / 2 ^ 128 + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_ic_h23 Hb st w hlr hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

/-- **`zk_rom_h23` with the grinding term numeric**: for any CTR PRG, with BAVC hiding assumed
(`ε_bavc`), the executable prover is `q₃·2⁻¹²⁸ + 2⁻¹¹³ + ε_bavc + (q₅ + 1)·2⁻¹²⁸`-close to the
programming simulator against a distinguisher that reads `H₃`, `H₅` at `q₃`, `q₅` keys and `H₂³`
freely. -/
theorem zk_rom_h23_num [HasPrg] {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) {εb : ℝ} (hH : HideHyp st.params εb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1)
          c.2.2.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + εb + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_h23 Hb st w hlr hzk hHb hH D Q3 hQ3 hq3 Q5 hQ5 hq5).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

end Headline

end VoleMole.ZK.Sim
