import VoleMole.ZK.HopsH4Pt

/-!
# How many proofs one cipher input concerns

`ZK/HopsH4Pt.lean` charges hop H4 of a proof with `iv` only for the distinguisher's reads at the
CTR blocks of `iv` (`InY iv`). In a game with `N` proofs, a read at an input `z` is charged to
every proof whose `iv` has `z` among its CTR blocks. This file bounds that number.

A CTR block `ctrBlock iv c t` keeps the middle 64 bits of `iv` (lanes 1 and 2: the counter is
added to lane 0 and the tweak to lane 3, `lanes_ctrBlock`). So two `iv`s that share a CTR block
have equal bytes `4 … 11` (`midB_of_inY`), and:

* **`sum_inY_le`** (deterministic, for any read set `Z`, chosen after seeing the `iv`s):
  `Σ_i #{z ∈ Z | InY iv_i z} ≤ |Z|·(1 + #collPairs)`, `collPairs` the pairs `i < j` whose `iv`s
  have equal middle bytes;
* **`exP_collPairs_le`**: for `N` independent uniform `iv`s, `E[#collPairs] ≤ N²·2⁻⁶⁴` (each pair
  `≤ 2⁻⁶⁴`, `pr_midB_eq_le`; `card_midB_le`: at most `2⁶⁴` blocks have given middle bytes);
* **`exP_sum_inY_le`**: hence, for reads `Z g` of at most `q` points (any function of the `iv`s
  `g`), `E[Σ_i #{z ∈ Z | InY iv_i z}] ≤ q·(1 + N²·2⁻⁶⁴)`.

So the total point charge of all `N` proofs is the read budget once, times `1 + N²·2⁻⁶⁴`
(`≤ 1 + 2⁻²` for `N ≤ 2³¹`). The factor is real: if two `iv`s share their middle bytes, every
read at a common CTR block concerns both proofs. Restricting the points to the counters and
tweaks the commitment uses (instead of all of `InY`) would lower it to about `N²·R·2⁻¹²⁸`; not done.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-! ## A shared CTR block means shared middle lanes -/

/-- The CTR blocks of `iv` all have `iv`'s third lane (as `lane1_of_ctrBlock_eq`). -/
theorem lane2_of_ctrBlock_eq {iv iv' : ByteArray} {c t c' t' : UInt32}
    (h : blk 16 (AES.ctrBlock iv c t) = blk 16 (AES.ctrBlock iv' c' t')) :
    AES.getLE32 iv 8 = AES.getLE32 iv' 8 := by
  have h' : AES.ctrBlock iv c t = AES.ctrBlock iv' c' t' :=
    blk16_inj (ctrBlock_size _ _ _) (ctrBlock_size _ _ _) h
  have := congrArg (fun b => lanes b 2) h'
  simp only [lanes_ctrBlock] at this
  simp only [Seed.Commitments.ctrInput, lanes] at this
  exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _) (UInt32.toNat_lt _)
    (by simpa using this))

/-- The bytes `4 … 11` of a block (its lanes 1 and 2). -/
def midB (u : Bytes 16) : Fin 8 → UInt8 := fun i => u ⟨i.val + 4, by omega⟩

lemma getLE32_ba_toNat (u : Bytes 16) {o : ℕ} (ho : o + 3 < 16) :
    (AES.getLE32 (ba u) o).toNat = (u ⟨o, by omega⟩).toNat + 2 ^ 8 * (u ⟨o + 1, by omega⟩).toNat +
      2 ^ 16 * (u ⟨o + 2, by omega⟩).toNat + 2 ^ 24 * (u ⟨o + 3, by omega⟩).toNat := by
  unfold AES.getLE32
  rw [toNat_le32]
  simp only [get!_ba _ (show o < 16 by omega), get!_ba _ (show o + 1 < 16 by omega),
    get!_ba _ (show o + 2 < 16 by omega), get!_ba _ (show o + 3 < 16 by omega)]

/-- Equal words read at `o` mean equal bytes `o … o + 3`. -/
lemma bytes_of_getLE32_eq {u u' : Bytes 16} {o : ℕ} (ho : o + 3 < 16)
    (h : AES.getLE32 (ba u) o = AES.getLE32 (ba u') o) :
    ∀ j (hj : o ≤ j ∧ j < o + 4), u ⟨j, by omega⟩ = u' ⟨j, by omega⟩ := by
  have hn := congrArg UInt32.toNat h
  rw [getLE32_ba_toNat u ho, getLE32_ba_toNat u' ho] at hn
  have b0 := (u ⟨o, by omega⟩).toNat_lt; have b1 := (u ⟨o + 1, by omega⟩).toNat_lt
  have b2 := (u ⟨o + 2, by omega⟩).toNat_lt; have b3 := (u ⟨o + 3, by omega⟩).toNat_lt
  have b0' := (u' ⟨o, by omega⟩).toNat_lt; have b1' := (u' ⟨o + 1, by omega⟩).toNat_lt
  have b2' := (u' ⟨o + 2, by omega⟩).toNat_lt; have b3' := (u' ⟨o + 3, by omega⟩).toNat_lt
  intro j hj
  have : j = o ∨ j = o + 1 ∨ j = o + 2 ∨ j = o + 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact UInt8.toNat_inj.1 (by omega)
  · exact UInt8.toNat_inj.1 (by omega)
  · exact UInt8.toNat_inj.1 (by omega)
  · exact UInt8.toNat_inj.1 (by omega)

/-- **Two `iv`s with a common CTR block have equal middle bytes.** -/
theorem midB_of_inY {u u' : Bytes 16} {z : Blk} (h : InY (ba u) z) (h' : InY (ba u') z) :
    midB u = midB u' := by
  obtain ⟨c, t, rfl⟩ := h
  obtain ⟨c', t', hz⟩ := h'
  have h1 := bytes_of_getLE32_eq (o := 4) (by norm_num) (lane1_of_ctrBlock_eq hz)
  have h2 := bytes_of_getLE32_eq (o := 8) (by norm_num) (lane2_of_ctrBlock_eq hz)
  funext i
  obtain ⟨i, hi⟩ := i
  simp only [midB]
  by_cases hi4 : i < 4
  · exact h1 (i + 4) (by omega)
  · exact h2 (i + 4) (by omega)

/-! ## Few blocks have given middle bytes -/

/-- The bytes of a block other than its middle ones. -/
def idxOut (i : Fin 8) : Fin 16 := if h : i.val < 4 then ⟨i.val, by omega⟩ else ⟨i.val + 8, by omega⟩

set_option linter.constructorNameAsVariable false in
/-- **At most `2⁶⁴` blocks have given middle bytes.** -/
lemma card_midB_le (M : Fin 8 → UInt8) : (univ.filter fun u : Bytes 16 => midB u = M).card ≤ 2 ^ 64 := by
  classical
  let φ : Bytes 16 → Bytes 8 := fun u i => u (idxOut i)
  have hinj : Set.InjOn φ (univ.filter fun u : Bytes 16 => midB u = M) := by
    intro u hu u' hu' he
    simp only [coe_filter, mem_univ, true_and] at hu hu'
    have hm : midB u = midB u' := (show midB u = M from hu).trans (show midB u' = M from hu').symm
    funext j
    obtain ⟨jv, hjv⟩ := j
    by_cases hj : jv < 4
    · have := congrFun he ⟨jv, by omega⟩
      simpa only [φ, idxOut, hj, ↓reduceDIte] using this
    by_cases hj' : jv < 12
    · have := congrFun hm ⟨jv - 4, by omega⟩
      simp only [midB] at this
      have e : (⟨jv - 4 + 4, by omega⟩ : Fin 16) = ⟨jv, hjv⟩ := Fin.ext (by simp only; omega)
      rwa [e] at this
    · have := congrFun he ⟨jv - 8, by omega⟩
      have hn : ¬ (jv - 8 < 4) := by omega
      simp only [φ, idxOut, hn, ↓reduceDIte] at this
      have e : (⟨jv - 8 + 8, by omega⟩ : Fin 16) = ⟨jv, hjv⟩ := Fin.ext (by simp only; omega)
      rwa [e] at this
  have h := Finset.card_le_card_of_injOn φ (fun u _ => mem_univ (φ u)) hinj
  rw [Finset.card_univ, Prob.card_bytes] at h
  exact h.trans (le_of_eq (by norm_num))

/-- **Two independent uniform blocks share their middle bytes with probability `≤ 2⁻⁶⁴`.** -/
lemma pr_midB_eq_le {α : Type*} [Fintype α] [DecidableEq α] {a a' : α} (h : a ≠ a') :
    pr (α → Bytes 16) (fun g => midB (g a) = midB (g a')) ≤ 1 / 2 ^ 64 := by
  classical
  have hr := pr_mem_reset_le (α := α → Bytes 16) (K := Bytes 16) (fun g => g a)
    (fun g k => Function.update g a k)
    (fun g k => Function.update_self _ _ _) (fun g k k' => Function.update_idem _ _ _)
    (fun g => Function.update_eq_self _ _) (fun g => univ.filter fun u => midB u = midB (g a'))
    (fun g k => by rw [Function.update_of_ne h.symm]) (q := 2 ^ 64) (fun g => card_midB_le _)
  refine le_trans (le_of_eq (pr_congr fun g => ?_)) (hr.trans (le_of_eq ?_))
  · simp
  · rw [show Fintype.card (Bytes 16) = 2 ^ 128 from card_blk]; norm_num

/-! ## The number of proofs a read concerns -/

variable {N : ℕ}

/-- **The pairs of proofs whose `iv`s share their middle bytes.** -/
def collPairs (g : Fin N → Bytes 16) : Finset (Fin N × Fin N) :=
  univ.filter fun ij => ij.1 < ij.2 ∧ midB (g ij.1) = midB (g ij.2)

/-- **One input concerns at most `1 + #collPairs` proofs.** -/
lemma card_inY_le (g : Fin N → Bytes 16) (z : Blk) :
    (univ.filter fun i => InY (ba (g i)) z).card ≤ 1 + (collPairs g).card := by
  classical
  set S := univ.filter fun i => InY (ba (g i)) z
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty]; omega
  set i0 := S.min' hS
  have hi0 : i0 ∈ S := S.min'_mem hS
  have hmap : ∀ j ∈ S.erase i0, (i0, j) ∈ collPairs g := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.1 hj
    refine Finset.mem_filter.2 ⟨mem_univ _, lt_of_le_of_ne (S.min'_le j hjS) (Ne.symm hji), ?_⟩
    exact midB_of_inY (Finset.mem_filter.1 hi0).2 (Finset.mem_filter.1 hjS).2
  have h := Finset.card_le_card_of_injOn (fun j => (i0, j)) hmap
    (fun j _ j' _ e => (Prod.mk.inj e).2)
  rw [Finset.card_erase_of_mem hi0] at h
  omega

/-- **The reads charged to all proofs at once**: for any read set `Z` (which may depend on the
`iv`s), `Σ_i #{z ∈ Z | InY iv_i z} ≤ |Z|·(1 + #collPairs)`. -/
theorem sum_inY_le (g : Fin N → Bytes 16) (Z : Finset Blk) :
    ∑ i, (Z.filter fun z => InY (ba (g i)) z).card ≤ Z.card * (1 + (collPairs g).card) := by
  classical
  have e : ∑ i, (Z.filter fun z => InY (ba (g i)) z).card =
      ∑ z ∈ Z, (univ.filter fun i => InY (ba (g i)) z).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [e]
  calc ∑ z ∈ Z, (univ.filter fun i => InY (ba (g i)) z).card
      ≤ ∑ _z ∈ Z, (1 + (collPairs g).card) := Finset.sum_le_sum fun z _ => card_inY_le g z
    _ = Z.card * (1 + (collPairs g).card) := by rw [Finset.sum_const, smul_eq_mul]

/-- **`E[#collPairs] ≤ N²·2⁻⁶⁴`** for independent uniform `iv`s. -/
theorem exP_collPairs_le :
    exP (Fin N → Bytes 16) (fun g => ((collPairs g).card : ℝ)) ≤ (N : ℝ) ^ 2 / 2 ^ 64 := by
  classical
  have e : ∀ g : Fin N → Bytes 16, ((collPairs g).card : ℝ) =
      ∑ ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2),
        if midB (g ij.1) = midB (g ij.2) then (1 : ℝ) else 0 := by
    intro g
    rw [Finset.sum_boole, Finset.filter_filter]
    rfl
  have hpr : ∀ ij : Fin N × Fin N, ij.1 < ij.2 →
      exP (Fin N → Bytes 16) (fun g => if midB (g ij.1) = midB (g ij.2) then (1 : ℝ) else 0) ≤
        1 / 2 ^ 64 := by
    intro ij hij
    have h := pr_midB_eq_le (α := Fin N) hij.ne
    rw [pr_def, ← Finset.sum_boole] at h
    exact h
  simp only [exP] at hpr ⊢
  rw [Finset.sum_congr rfl fun g _ => e g, Finset.sum_comm, Finset.sum_div]
  calc ∑ ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2),
        (∑ g : Fin N → Bytes 16, if midB (g ij.1) = midB (g ij.2) then (1 : ℝ) else 0) /
          Fintype.card (Fin N → Bytes 16)
      ≤ ∑ _ij ∈ (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2), (1 : ℝ) / 2 ^ 64 :=
        Finset.sum_le_sum fun ij hij => hpr ij (Finset.mem_filter.1 hij).2
    _ ≤ ∑ _ij : Fin N × Fin N, (1 : ℝ) / 2 ^ 64 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    _ = (N : ℝ) ^ 2 / 2 ^ 64 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **The expected total point charge of `N` proofs is the read budget once, times
`1 + N²·2⁻⁶⁴`**: for independent uniform `iv`s and reads `Z g` of at most `q` points (any function
of the `iv`s), `E[Σ_i #{z ∈ Z g | InY iv_i z}] ≤ q·(1 + N²·2⁻⁶⁴)`. -/
theorem exP_sum_inY_le (Z : (Fin N → Bytes 16) → Finset Blk) {q : ℕ} (hq : ∀ g, (Z g).card ≤ q) :
    exP (Fin N → Bytes 16) (fun g => ((∑ i, ((Z g).filter fun z => InY (ba (g i)) z).card : ℕ) : ℝ)) ≤
      q * (1 + (N : ℝ) ^ 2 / 2 ^ 64) := by
  calc exP (Fin N → Bytes 16) (fun g => ((∑ i, ((Z g).filter fun z => InY (ba (g i)) z).card : ℕ) : ℝ))
      ≤ exP (Fin N → Bytes 16) (fun g => (q : ℝ) * (1 + ((collPairs g).card : ℝ))) :=
        exP_mono fun g => by
          have h := (sum_inY_le g (Z g)).trans (Nat.mul_le_mul_right _ (hq g))
          exact_mod_cast h
    _ = q * (1 + exP (Fin N → Bytes 16) (fun g => ((collPairs g).card : ℝ))) := by
        simp only [exP]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, mul_div_assoc, add_div,
          div_self (by exact_mod_cast Fintype.card_ne_zero)]
    _ ≤ q * (1 + (N : ℝ) ^ 2 / 2 ^ 64) := by
        gcongr
        exact exP_collPairs_le

end VoleMole.ZK.Sim
