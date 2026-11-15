import VoleMole.ZK.IvOverlap
import VoleMole.ZK.ChainExp

/-!
# How many proofs one cipher key read concerns, with `iv`s from a table

`ZK/IvOverlap.lean` counts **points**: `Σ_i #{z ∈ Z | InY iv_i z} ≤ |Z|·(1 + #collPairs)`. The
charge of the one-proof theorem (`chE`, `ZK/HopsICExp.lean`) counts **keys**: the keys `k` with
some read point `(k, z)` at a CTR block of the proof's `iv` (`qkeys (InY iv)`). A reader that
expands one key at many CTR blocks of one `iv` (the verifier, the extractor's candidates) makes
many points but concerns the proofs through one middle-bytes class only. This file counts the
keys by **classes** `(k, midB z)` and takes the `iv`s from a uniform table at inputs that may
collide:

* **`midB_of_inY_self`**: a CTR block of `ba u` has `u`'s middle bytes.
* **`ptCls`**: the classes `(key, middle bytes of the input)` of a set of points;
  `card_ptCls_le`: at most the number of points; `ptCls_prod`: a set of keys read at the CTR
  blocks of one `iv` has as many classes as keys.
* **`sum_qkeys_inY_le`** (deterministic, any read set): `Σ_i #qkeys(InY iv_i) Q ≤
  #ptCls Q·(1 + #collPairs)`.
* **`exP_collPairs_tab_le`**: for a uniform table `T : D → Bytes 16` and inputs `d : Fin N → D`,
  `E[#collPairs (T ∘ d)] ≤ N²·2⁻⁶⁴ + #dupPairs d` (the pairs with equal inputs).
* **`exP_sum_qkeys_tab_le`**: hence, for inputs `d ω` chosen by the rest of the tape `ω` and read
  sets `Q ω T` of at most `q` classes (any function of everything),

      E[Σ_i #qkeys(InY T(d_i)) Q] ≤ q·(1 + N²·2⁻⁶⁴ + E[#dupPairs d]).

This is the overlap count of the joint step (`Theft/JointZK.lean`) for the `iv`s of the theft
games, `H₄(iv_pre ‖ μ₁ ‖ 4)` with `H₄` a uniform table: two proofs have the same `iv` only if
their `H₄` inputs collide (the `iv_pre` collision term `E[#dupPairs]`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-! ## The class of a CTR block -/

/-- **A CTR block of `ba u` has `u`'s middle bytes.** -/
theorem midB_of_inY_self {u : Bytes 16} {z : Blk} (h : InY (ba u) z) : midB z = midB u := by
  obtain ⟨c, t, rfl⟩ := h
  have hs : (AES.ctrBlock (ba u) c t).size = 16 := ctrBlock_size _ _ _
  have hz : ba (blk 16 (AES.ctrBlock (ba u) c t)) = AES.ctrBlock (ba u) c t := ba_blk_of_size hs
  have hl := lanes_ctrBlock (ba u) c t
  have l1 : AES.getLE32 (ba (blk 16 (AES.ctrBlock (ba u) c t))) 4 = AES.getLE32 (ba u) 4 := by
    rw [hz]
    have := congrFun hl 1
    simp only [lanes, Seed.Commitments.ctrInput] at this
    exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _)
      (UInt32.toNat_lt _) (by simpa using this))
  have l2 : AES.getLE32 (ba (blk 16 (AES.ctrBlock (ba u) c t))) 8 = AES.getLE32 (ba u) 8 := by
    rw [hz]
    have := congrFun hl 2
    simp only [lanes, Seed.Commitments.ctrInput] at this
    exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _)
      (UInt32.toNat_lt _) (by simpa using this))
  have h1 := bytes_of_getLE32_eq (o := 4) (by norm_num) l1
  have h2 := bytes_of_getLE32_eq (o := 8) (by norm_num) l2
  funext i
  obtain ⟨i, hi⟩ := i
  simp only [midB]
  by_cases hi4 : i < 4
  · exact h1 (i + 4) (by omega)
  · exact h2 (i + 4) (by omega)

/-- **The classes of a set of points**: `(key, middle bytes of the input)`. -/
def ptCls (Q : Finset (Blk × Blk)) : Finset (Blk × (Fin 8 → UInt8)) :=
  Q.image fun kz => (kz.1, midB kz.2)

lemma card_ptCls_le (Q : Finset (Blk × Blk)) : (ptCls Q).card ≤ Q.card := card_image_le

lemma ptCls_mono {Q Q' : Finset (Blk × Blk)} (h : Q ⊆ Q') : ptCls Q ⊆ ptCls Q' :=
  image_subset_image h

lemma ptCls_union (Q Q' : Finset (Blk × Blk)) : ptCls (Q ∪ Q') = ptCls Q ∪ ptCls Q' :=
  image_union _ _

/-- **Keys read at CTR blocks of one `iv`**: as many classes as keys. -/
lemma card_ptCls_of_inY (Q : Finset (Blk × Blk)) (u : Bytes 16) (hQ : ∀ kz ∈ Q, InY (ba u) kz.2) :
    (ptCls Q).card ≤ (Q.image Prod.fst).card := by
  classical
  have : ptCls Q ⊆ (Q.image Prod.fst).image fun k => (k, midB u) := by
    intro c hc
    obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hc
    exact mem_image.2 ⟨kz.1, mem_image_of_mem _ hkz, by rw [midB_of_inY_self (hQ _ hkz)]⟩
  refine (card_le_card this).trans ?_
  exact card_image_le

/-! ## Keys charged to many proofs -/

variable {N : ℕ}

/-- **At most `1 + #collPairs` proofs have given middle bytes.** -/
lemma card_midB_eq_le (g : Fin N → Bytes 16) (m : Fin 8 → UInt8) :
    (univ.filter fun i => midB (g i) = m).card ≤ 1 + (collPairs g).card := by
  classical
  set S := univ.filter fun i => midB (g i) = m
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty]; omega
  set i0 := S.min' hS
  have hi0 : i0 ∈ S := S.min'_mem hS
  have hmap : ∀ j ∈ S.erase i0, (i0, j) ∈ collPairs g := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.1 hj
    refine Finset.mem_filter.2 ⟨mem_univ _, lt_of_le_of_ne (S.min'_le j hjS) (Ne.symm hji), ?_⟩
    exact (Finset.mem_filter.1 hi0).2.trans (Finset.mem_filter.1 hjS).2.symm
  have h := Finset.card_le_card_of_injOn (fun j => (i0, j)) hmap
    (fun j _ j' _ e => (Prod.mk.inj e).2)
  rw [Finset.card_erase_of_mem hi0] at h
  omega

/-- **The keys charged to all proofs at once**: for any read set `Q` (which may depend on the
`iv`s), `Σ_i #qkeys(InY iv_i) Q ≤ #ptCls Q·(1 + #collPairs)`. -/
theorem sum_qkeys_inY_le (g : Fin N → Bytes 16) (Q : Finset (Blk × Blk)) :
    ∑ i, (qkeys (InY (ba (g i))) Q).card ≤ (ptCls Q).card * (1 + (collPairs g).card) := by
  classical
  -- a key read at a CTR block of `iv_i` is a class with `iv_i`'s middle bytes
  have hk : ∀ i, (qkeys (InY (ba (g i))) Q).card ≤
      ((ptCls Q).filter fun c => c.2 = midB (g i)).card := by
    intro i
    refine Finset.card_le_card_of_injOn (fun k => (k, midB (g i))) ?_ ?_
    · intro k hk
      obtain ⟨kz, hkz, rfl⟩ := mem_image.1 (mem_coe.1 hk)
      obtain ⟨hkzQ, hz⟩ := mem_filter.1 hkz
      refine mem_coe.2 (mem_filter.2 ⟨mem_image.2 ⟨kz, hkzQ, ?_⟩, rfl⟩)
      rw [midB_of_inY_self hz]
    · intro k _ k' _ e
      exact (Prod.mk.inj e).1
  calc ∑ i, (qkeys (InY (ba (g i))) Q).card
      ≤ ∑ i, ((ptCls Q).filter fun c => c.2 = midB (g i)).card := Finset.sum_le_sum fun i _ => hk i
    _ = ∑ c ∈ ptCls Q, (univ.filter fun i => midB (g i) = c.2).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
        by_cases h : c.2 = midB (g i)
        · simp [h]
        · simp [h, Ne.symm h]
    _ ≤ ∑ _c ∈ ptCls Q, (1 + (collPairs g).card) :=
        Finset.sum_le_sum fun c _ => card_midB_eq_le g c.2
    _ = (ptCls Q).card * (1 + (collPairs g).card) := by rw [Finset.sum_const, smul_eq_mul]

/-! ## `iv`s from a uniform table -/

section Tab

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **The pairs of proofs with equal table inputs.** -/
def dupPairs (d : Fin N → D) : Finset (Fin N × Fin N) :=
  univ.filter fun ij => ij.1 < ij.2 ∧ d ij.1 = d ij.2

/-- **`E[#collPairs] ≤ N²·2⁻⁶⁴ + #dupPairs`** for the `iv`s `T(d_i)`, `T` a uniform table. -/
theorem exP_collPairs_tab_le (d : Fin N → D) :
    exP (D → Bytes 16) (fun T => ((collPairs (fun i => T (d i))).card : ℝ)) ≤
      (N : ℝ) ^ 2 / 2 ^ 64 + (dupPairs d).card := by
  classical
  set P := (univ.filter fun ij : Fin N × Fin N => ij.1 < ij.2)
  have e : ∀ T : D → Bytes 16, ((collPairs (fun i => T (d i))).card : ℝ) =
      ∑ ij ∈ P, if midB (T (d ij.1)) = midB (T (d ij.2)) then (1 : ℝ) else 0 := by
    intro T
    rw [Finset.sum_boole, Finset.filter_filter]
    rfl
  have hpr : ∀ ij ∈ P, exP (D → Bytes 16)
      (fun T => if midB (T (d ij.1)) = midB (T (d ij.2)) then (1 : ℝ) else 0) ≤
        1 / 2 ^ 64 + if d ij.1 = d ij.2 then 1 else 0 := by
    intro ij _
    by_cases hd : d ij.1 = d ij.2
    · simp only [hd, ↓reduceIte, exP_const]
      linarith [show (0 : ℝ) ≤ 1 / 2 ^ 64 by positivity]
    · simp only [hd, ↓reduceIte, add_zero]
      have h := pr_midB_eq_le (α := D) hd
      rw [pr_def, ← Finset.sum_boole] at h
      exact h
  have hsum : exP (D → Bytes 16) (fun T => ((collPairs (fun i => T (d i))).card : ℝ)) =
      ∑ ij ∈ P, exP (D → Bytes 16)
        (fun T => if midB (T (d ij.1)) = midB (T (d ij.2)) then (1 : ℝ) else 0) := by
    simp only [exP]
    rw [Finset.sum_congr rfl fun T _ => e T, Finset.sum_comm, Finset.sum_div]
  rw [hsum]
  refine (Finset.sum_le_sum hpr).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole]
  have hd : (P.filter fun ij => d ij.1 = d ij.2) = dupPairs d := by
    rw [Finset.filter_filter]; rfl
  rw [hd]
  gcongr
  calc ∑ _ij ∈ P, (1 : ℝ) / 2 ^ 64 ≤ ∑ _ij : Fin N × Fin N, (1 : ℝ) / 2 ^ 64 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    _ = (N : ℝ) ^ 2 / 2 ^ 64 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **The expected total key charge of `N` proofs with `iv`s from a table**: for inputs `d ω`
chosen by the rest of the tape (not reading the table) and read sets `Q ω T` of at most `q`
classes (any function of the tape and the table),

    E[Σ_i #qkeys(InY T(d_i)) Q] ≤ q·(1 + N²·2⁻⁶⁴ + E[#dupPairs d]). -/
theorem exP_sum_qkeys_tab_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (d : Ω → Fin N → D)
    (Q : Ω → (D → Bytes 16) → Finset (Blk × Blk)) {q : ℕ} (hq : ∀ ω T, (ptCls (Q ω T)).card ≤ q) :
    exP (Ω × (D → Bytes 16)) (fun z =>
        ((∑ i, (qkeys (InY (ba (z.2 (d z.1 i)))) (Q z.1 z.2)).card : ℕ) : ℝ)) ≤
      q * (1 + (N : ℝ) ^ 2 / 2 ^ 64 + exP Ω (fun ω => ((dupPairs (d ω)).card : ℝ))) := by
  classical
  have hpt : ∀ z : Ω × (D → Bytes 16),
      ((∑ i, (qkeys (InY (ba (z.2 (d z.1 i)))) (Q z.1 z.2)).card : ℕ) : ℝ) ≤
        q * (1 + ((collPairs (fun i => z.2 (d z.1 i))).card : ℝ)) := fun z => by
    have h := (sum_qkeys_inY_le (fun i => z.2 (d z.1 i)) (Q z.1 z.2)).trans
      (Nat.mul_le_mul_right _ (hq z.1 z.2))
    exact_mod_cast h
  refine (exP_mono hpt).trans ?_
  have hc : ∀ ω, exP (D → Bytes 16) (fun T => ((collPairs (fun i => T (d ω i))).card : ℝ)) ≤
      (N : ℝ) ^ 2 / 2 ^ 64 + (dupPairs (d ω)).card := fun ω => exP_collPairs_tab_le (d ω)
  have hprod : exP (Ω × (D → Bytes 16))
      (fun z => ((collPairs (fun i => z.2 (d z.1 i))).card : ℝ)) =
      exP Ω (fun ω => exP (D → Bytes 16) (fun T => ((collPairs (fun i => T (d ω i))).card : ℝ))) :=
    exP_prod _
  have hle : exP Ω (fun ω => exP (D → Bytes 16) (fun T => ((collPairs (fun i => T (d ω i))).card : ℝ)))
      ≤ (N : ℝ) ^ 2 / 2 ^ 64 + exP Ω (fun ω => ((dupPairs (d ω)).card : ℝ)) := by
    refine (exP_mono hc).trans (le_of_eq ?_)
    rw [exP_const_add]
  calc exP (Ω × (D → Bytes 16)) (fun z => (q : ℝ) * (1 + ((collPairs (fun i => z.2 (d z.1 i))).card : ℝ)))
      = q * (1 + exP (Ω × (D → Bytes 16))
          (fun z => ((collPairs (fun i => z.2 (d z.1 i))).card : ℝ))) := by
        rw [exP_mul_left, exP_const_add]
    _ ≤ q * (1 + ((N : ℝ) ^ 2 / 2 ^ 64 + exP Ω (fun ω => ((dupPairs (d ω)).card : ℝ)))) := by
        rw [hprod]; gcongr
    _ = q * (1 + (N : ℝ) ^ 2 / 2 ^ 64 + exP Ω (fun ω => ((dupPairs (d ω)).card : ℝ))) := by ring

end Tab

end VoleMole.ZK.Sim
