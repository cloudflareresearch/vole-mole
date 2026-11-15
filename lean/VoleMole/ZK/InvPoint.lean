import VoleMole.ZK.HopsH4Perm
import VoleMole.ZK.IdealCipherPt

/-!
# Inverse queries are not point reads: the point-level hop fails for permutation rows

The point-level hop H4 (`IC.hopPt`, `IC.puncturePt_real`, `ZK/IdealCipherPt.lean`) charges a
distinguisher of a GGM tree with **function** rows only for the keys it reads at the points `P`
at which the hidden part reads the secret rows:

    |real − fully replaced| ≤ |secret|·(N + E_real[#keys read on P]) / (|K| − |secret|·qm).

With **permutation** rows the distinguisher may also ask inverse queries. An inverse query at
`(k, y)` returns `z = π_k⁻¹(y)`, and the reader is consistent if it is written as the forward
point `(k, z)` (two tables that agree there answer the query alike, `qInv_cons`). So the natural
port of the hop would charge an inverse query when its **answer** is in `P`. That charge is not
enough, and here is a counterexample in the existing permutation-row experiment `IC.experPm`
(`ZK/IdealCipherPerm.lean`):

* one secret node, the root (`N = 1`), `P = {z₀}`; the hidden part outputs the root's row at `z₀`
  (`phiInv`), as the BAVC outputs a hidden leaf's commitment, two blocks of the leaf's row at CTR
  blocks of the proof's `iv` (`Hidden`, `comsOf`, `ZK/Hops.lean`);
* the distinguisher asks the inverse query at the revealed value `y` under every key of a set
  `S` of `q` keys and accepts if some answer is `z₀` (`aInv`; its reads `qInv`).

Then (`inv_adv_ge`, `inv_charge_le`, with `n = |K|`)

    real − replaced ≥ (q/n)·(1 − q/n),      E_real[#keys read on P] ≤ 2q/n:

in the real world the query under the root's key answers `z₀`, which happens with probability
`q/n`; in the replaced world the revealed value is independent of the table. A query under any
other key reads no point of `P`, yet each one is a guess of the secret key. At `n = 2¹²⁸`,
`q = 2⁶⁴` (**`inv_point_charge_fails`**): the advantage is `≥ 2⁻⁶⁴ − 2⁻¹²⁸`, while the form above
gives `(1 + E_real)/(2¹²⁸ − 2⁶⁴) < 2⁻¹²⁷`.

So for permutation rows an inverse query must be charged to a proof when its **input** is a value
the proof reveals (the hidden leaves' commitment blocks, and every block of the hidden part that
the output determines), not only when its answer is one of the proof's points. With function rows
the same attack needs forward queries at `z₀` under the `q` keys, which `IC.qkeys` charges.

* `pr_perm_apply_mem`: a uniform permutation maps `z` into `T` with probability `|T|/|K|`.
* `pr_update_row`: a uniform table is the table with one row replaced by an independent uniform
  permutation.
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-! ## Uniform permutations -/

section Uniform

variable {K : Type} [Fintype K] [DecidableEq K]

/-- **A uniform permutation maps `z` into `T` with probability `|T| / |K|`.** -/
theorem pr_perm_apply_mem (z : K) (T : Finset K) :
    pr (Equiv.Perm K) (fun u => u z ∈ T) = T.card / Fintype.card K := by
  classical
  -- every fibre of `u ↦ u z` has the size of the fibre at `z`
  have hfib : ∀ c, (univ.filter fun u : Equiv.Perm K => u z = c).card =
      (univ.filter fun u : Equiv.Perm K => u z = z).card := by
    intro c
    refine card_equiv (Equiv.mulLeft (Equiv.swap c z)) fun u => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulLeft, Equiv.Perm.coe_mul,
      Function.comp_apply]
    constructor
    · intro h
      rw [h, Equiv.swap_apply_left]
    · intro h
      have e := congrArg (Equiv.swap c z) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at e
  set f := (univ.filter fun u : Equiv.Perm K => u z = z).card with hf
  have hf0 : 0 < f := card_pos.2 ⟨1, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
  have hcount : ∀ T : Finset K, (univ.filter fun u : Equiv.Perm K => u z ∈ T).card = T.card * f := by
    intro T
    rw [card_eq_sum_card_fiberwise (f := fun u : Equiv.Perm K => u z) (t := T)
      (s := univ.filter fun u : Equiv.Perm K => u z ∈ T) (fun u hu => (mem_filter.1 hu).2)]
    have : ∀ c ∈ T, ((univ.filter fun u : Equiv.Perm K => u z ∈ T).filter
        fun u => u z = c).card = f := by
      intro c hc
      rw [← hfib c, filter_filter]
      congr 1
      exact filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
    rw [sum_congr rfl this, sum_const, smul_eq_mul]
  have htot : Fintype.card (Equiv.Perm K) = Fintype.card K * f := by
    have h := hcount univ
    rw [filter_true_of_mem fun _ _ => mem_univ _, card_univ, card_univ] at h
    exact h
  rw [pr_def, hcount T, htot]
  push_cast
  rw [mul_div_mul_right _ _ (by exact_mod_cast hf0.ne')]

/-- **Resampling a row**: a uniform table is the table with its row at `s` replaced by an
independent uniform permutation. -/
theorem pr_update_row (s : K) (D : (K → Equiv.Perm K) → Prop) :
    pr (K → Equiv.Perm K) D =
      pr ((K → Equiv.Perm K) × Equiv.Perm K) (fun p => D (Function.update p.1 s p.2)) := by
  let e : (K → Equiv.Perm K) × Equiv.Perm K ≃ (K → Equiv.Perm K) × Equiv.Perm K :=
    { toFun := fun p => (Function.update p.1 s p.2, p.1 s)
      invFun := fun p => (Function.update p.1 s p.2, p.1 s)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← pr_prod_fst (β := Equiv.Perm K) D, ← pr_equiv e (fun p => D p.1)]
  rfl

end Uniform

/-! ## The counterexample -/

section InvAttack

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]

/-- **The hidden part**: the root's row at `z₀`, a value the output reveals (as a hidden leaf's
commitment). It reads the secret row only at `z₀`. -/
def phiInv (z0 : K) (ρ : ℕ → K → K) : K := ρ 0 z0

/-- **The distinguisher**: the inverse query at the revealed value `y` under every key of `S`;
it accepts if an answer is `z₀`. -/
def aInv (S : Finset K) (z0 y : K) (π : K → Equiv.Perm K) : Prop :=
  ∃ k ∈ S, (π k).symm y = z0

/-- **Its reads**, the inverse queries written as forward points `(k, π_k⁻¹ y)`. -/
def qInv (S : Finset K) (y : K) (π : K → Equiv.Perm K) : Finset (K × K) :=
  S.image fun k => (k, (π k).symm y)

omit [Fintype K] [DecidableEq K] [Nonempty K] in
lemma symm_eq_of_agree {σ σ' : Equiv.Perm K} {y : K} (h : σ (σ.symm y) = σ' (σ.symm y)) :
    σ'.symm y = σ.symm y := by
  rw [Equiv.apply_symm_apply] at h
  rw [Equiv.symm_apply_eq]
  exact h

omit [Fintype K] [Nonempty K] in
/-- **The reader is consistent**: tables that agree at its forward points have the same reads
and the same answer (`IC.puncturePt_real`'s `hQ` and `hQc`, for permutation tables). -/
theorem qInv_cons (S : Finset K) (z0 y : K) (G G' : K → Equiv.Perm K)
    (h : ∀ kz ∈ qInv S y G, G kz.1 kz.2 = G' kz.1 kz.2) :
    (aInv S z0 y G ↔ aInv S z0 y G') ∧ qInv S y G = qInv S y G' := by
  have e : ∀ k ∈ S, (G' k).symm y = (G k).symm y := fun k hk =>
    symm_eq_of_agree (h (k, (G k).symm y) (mem_image_of_mem _ hk))
  refine ⟨⟨fun ⟨k, hk, hz⟩ => ⟨k, hk, by rw [e k hk]; exact hz⟩,
    fun ⟨k, hk, hz⟩ => ⟨k, hk, by rw [← e k hk]; exact hz⟩⟩, ?_⟩
  exact image_congr fun k hk => by simp only [e k hk]

omit [Fintype K] [Nonempty K] in
/-- It reads at most `|S|` keys on `P = {z₀}` (`IC.puncturePt_real`'s `qm`). -/
lemma qInv_qkeys_le (S : Finset K) (z0 y : K) (π : K → Equiv.Perm K) :
    (qkeys (fun z => z = z0) (qInv S y π)).card ≤ S.card :=
  card_image_le.trans ((card_filter_le _ _).trans card_image_le)

/-- **The ideal probability**: some key of `S` maps `z₀` to the value of an independent uniform
permutation at `z₀`. -/
noncomputable def iInv (S : Finset K) (z0 : K) : ℝ :=
  pr ((K → Equiv.Perm K) × Equiv.Perm K) (fun p => ∃ k ∈ S, p.1 k z0 = p.2 z0)

omit [Nonempty K] in
lemma iInv_le (S : Finset K) (z0 : K) : iInv S z0 ≤ S.card / Fintype.card K := by
  classical
  unfold iInv
  rw [pr_prod]
  have hT : (Fintype.card (K → Equiv.Perm K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_le_iff₀ (by positivity)]
  have hπ : ∀ π : K → Equiv.Perm K, pr (Equiv.Perm K) (fun u => ∃ k ∈ S, π k z0 = u z0) ≤
      S.card / Fintype.card K := by
    intro π
    have e : pr (Equiv.Perm K) (fun u => ∃ k ∈ S, π k z0 = u z0) =
        pr (Equiv.Perm K) (fun u => u z0 ∈ S.image fun k => π k z0) :=
      pr_congr fun u => by simp only [mem_image]
    rw [e, pr_perm_apply_mem]
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_image_le) (Nat.cast_nonneg _)
  calc ∑ π : K → Equiv.Perm K, pr (Equiv.Perm K) (fun u => ∃ k ∈ S, π k z0 = u z0)
      ≤ ∑ _π : K → Equiv.Perm K, (S.card / Fintype.card K : ℝ) := sum_le_sum fun π _ => hπ π
    _ = S.card / Fintype.card K * Fintype.card (K → Equiv.Perm K) := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

omit [Nonempty K] in
lemma iInv_nonneg (S : Finset K) (z0 : K) : 0 ≤ iInv S z0 := pr_nonneg _

omit [Nonempty K] in
/-- **A row off `S` is independent of the rows at `S`**: the probability that a key of `S` maps
`z₀` to the row at `s ∉ S` at `z₀` is `iInv`. -/
lemma pr_row_off (S : Finset K) (z0 : K) {s : K} (hs : s ∉ S) :
    pr (K → Equiv.Perm K) (fun π => ∃ k ∈ S, π k z0 = π s z0) = iInv S z0 := by
  rw [pr_update_row s]
  refine pr_congr fun p => ?_
  simp only [Function.update_self]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hs hk)]

omit [Nonempty K] in
/-- **The real experiment**: the root's key is uniform, and some key of `S` maps `z₀` where the
root's row does. -/
theorem experPm_inv_empty (x : ℕ → K) (S : Finset K) (z0 : K) :
    experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) =
      pr (K × (K → Equiv.Perm K)) (fun p => ∃ k ∈ S, p.2 k z0 = p.2 p.1 z0) := by
  let e : PCoins K 1 × (K → Equiv.Perm K) ≃ (K × (K → Equiv.Perm K)) × (Fin 1 → Equiv.Perm K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_prod_fst (β := Fin 1 → Equiv.Perm K), ← pr_equiv e, experPm]
  refine pr_congr fun c => ?_
  simp only [phiInv, aInv, e, Equiv.coe_fn_mk]
  rw [rowAt_of_not_mem (Finset.notMem_empty 0), keyAt_zero]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [Equiv.symm_apply_eq, eq_comm]
  rfl

/-- **The replaced experiment**: the root's row is an independent uniform permutation. -/
theorem experPm_inv_full (x : ℕ → K) (S : Finset K) (z0 : K) :
    experPm x 1 {0} (phiInv z0) (fun y π => aInv S z0 y π) = iInv S z0 := by
  let e : PCoins K 1 × (K → Equiv.Perm K) ≃ ((K → Equiv.Perm K) × Equiv.Perm K) × K :=
    { toFun := fun c => ((c.2, c.1.2 0), c.1.1)
      invFun := fun c => ((c.2, fun _ => c.1.2), c.1.1)
      left_inv := fun c => by
        obtain ⟨⟨s, R⟩, π⟩ := c
        simp only [Prod.mk.injEq, true_and, and_true]
        funext i
        rw [Subsingleton.elim i 0]
      right_inv := fun _ => rfl }
  rw [iInv, ← pr_prod_fst (β := K), ← pr_equiv e, experPm]
  refine pr_congr fun c => ?_
  simp only [phiInv, aInv, e, Equiv.coe_fn_mk]
  rw [rowAt_of_mem (Finset.mem_singleton_self 0) Nat.one_pos]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [Equiv.symm_apply_eq, eq_comm]
  rfl

omit [Nonempty K] in
/-- **The real probability**: `q/n` (the root's key in `S`) plus `(1 − q/n)·iInv`. -/
theorem experPm_inv_empty_eq (x : ℕ → K) (S : Finset K) (z0 : K) :
    experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) =
      (S.card + (Fintype.card K - S.card) * iInv S z0) / Fintype.card K := by
  classical
  rw [experPm_inv_empty, pr_prod]
  congr 1
  have hs : ∀ s, pr (K → Equiv.Perm K) (fun π => ∃ k ∈ S, π k z0 = π s z0) =
      if s ∈ S then 1 else iInv S z0 := by
    intro s
    split_ifs with h
    · rw [show (fun π : K → Equiv.Perm K => ∃ k ∈ S, π k z0 = π s z0) = fun _ => True from
        funext fun π => propext ⟨fun _ => trivial, fun _ => ⟨s, h, rfl⟩⟩, pr_const]
      simp
    · exact pr_row_off S z0 h
  rw [sum_congr rfl fun s _ => hs s, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_one]
  have h1 : (univ.filter fun s => s ∈ S).card = S.card := by
    rw [filter_mem_eq_inter, univ_inter]
  have h2 : ((univ.filter fun s => s ∉ S).card : ℝ) = Fintype.card K - S.card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset K)) (fun s => s ∈ S)
    rw [h1, card_univ] at this
    rw [← this]
    push_cast
    ring
  rw [h1, h2]

/-- **The advantage**: `real − replaced ≥ (q/n)·(1 − q/n)`. -/
theorem inv_adv_ge (x : ℕ → K) (S : Finset K) (z0 : K) :
    S.card / Fintype.card K * (1 - S.card / Fintype.card K) ≤
      experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) -
        experPm x 1 {0} (phiInv z0) (fun y π => aInv S z0 y π) := by
  rw [experPm_inv_empty_eq, experPm_inv_full]
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hI := iInv_le S z0
  have hI0 := iInv_nonneg S z0
  set I := iInv S z0
  set q : ℝ := (S.card : ℝ)
  set n : ℝ := (Fintype.card K : ℝ)
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have e : (q + (n - q) * I) / n - I = q / n * (1 - I) := by field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hq0 hn.le)

omit [Nonempty K] in
lemma exP_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    exP α (fun a => if P a then (1 : ℝ) else 0) = pr α P := by
  rw [exP, pr_def, sum_boole]

omit [Nonempty K] in
lemma exP_finset_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    exP α (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, exP α (f i) := by
  simp only [exP]
  rw [sum_comm, sum_div]

/-- One key of `S` maps `z₀` where the root's row does with probability `≤ 2/n`: the root's key
is that key, or the two rows are independent. -/
lemma pr_key_hit_le (z0 k : K) :
    pr (K × (K → Equiv.Perm K)) (fun p => p.2 k z0 = p.2 p.1 z0) ≤ 2 / Fintype.card K := by
  classical
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_div_iff_of_pos_right hn]
  have hs : ∀ s, pr (K → Equiv.Perm K) (fun π => π k z0 = π s z0) ≤
      (if s = k then 1 else 0) + 1 / Fintype.card K := by
    intro s
    by_cases h : s = k
    · simp only [h, ↓reduceIte]
      exact (pr_le_one _).trans (le_add_of_nonneg_right (by positivity))
    · simp only [h, ↓reduceIte, zero_add]
      have e := pr_row_off {k} z0 (s := s) (by simpa [eq_comm] using h)
      rw [show (fun π : K → Equiv.Perm K => π k z0 = π s z0) =
        fun π => ∃ k' ∈ ({k} : Finset K), π k' z0 = π s z0 from
          funext fun π => propext (by simp), e]
      simpa using iInv_le {k} z0
  calc ∑ s, pr (K → Equiv.Perm K) (fun π => π k z0 = π s z0)
      ≤ ∑ s : K, ((if s = k then 1 else 0) + 1 / Fintype.card K : ℝ) := sum_le_sum fun s _ => hs s
    _ = 2 := by
        rw [sum_add_distrib, sum_ite_eq' univ k, sum_const, card_univ, nsmul_eq_mul,
          mul_one_div_cancel hn.ne']
        simp only [mem_univ, ↓reduceIte]
        norm_num

/-- **The charge of the point-level hop is small**: in the real experiment the distinguisher
reads, in expectation, at most `2q/n` keys on `P = {z₀}`. -/
theorem inv_charge_le (x : ℕ → K) (S : Finset K) (z0 : K) :
    exP (PCoins K 1 × (K → Equiv.Perm K)) (fun p => ((qkeys (fun z => z = z0)
      (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) (cf p.1.2) p.1.1)) p.2)).card : ℝ)) ≤
      2 * S.card / Fintype.card K := by
  classical
  -- the keys read on `P` are keys of `S` that map `z₀` where the root's row does
  have hpt : ∀ p : PCoins K 1 × (K → Equiv.Perm K),
      ((qkeys (fun z => z = z0)
        (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) (cf p.1.2) p.1.1)) p.2)).card : ℝ) ≤
      ∑ k ∈ S, if p.2 k z0 = p.2 p.1.1 z0 then (1 : ℝ) else 0 := by
    intro p
    rw [sum_boole]
    refine Nat.cast_le.2 (card_le_card fun k hk => ?_)
    obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hk
    obtain ⟨hkz, hz⟩ := mem_filter.1 hkz
    obtain ⟨k', hk', rfl⟩ := mem_image.1 hkz
    refine mem_filter.2 ⟨hk', ?_⟩
    simp only [phiInv] at hz
    rw [rowAt_of_not_mem (Finset.notMem_empty 0), keyAt_zero, Equiv.symm_apply_eq] at hz
    exact hz.symm
  refine (exP_mono hpt).trans ?_
  rw [exP_finset_sum]
  have hk : ∀ k ∈ S, exP (PCoins K 1 × (K → Equiv.Perm K))
      (fun p => if p.2 k z0 = p.2 p.1.1 z0 then (1 : ℝ) else 0) ≤ 2 / Fintype.card K := by
    intro k _
    rw [exP_indicator]
    let e : PCoins K 1 × (K → Equiv.Perm K) ≃ (K × (K → Equiv.Perm K)) × (Fin 1 → Equiv.Perm K) :=
      { toFun := fun c => ((c.1.1, c.2), c.1.2)
        invFun := fun c => ((c.1.1, c.2), c.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h := pr_equiv e (fun c => c.1.2 k z0 = c.1.2 c.1.1 z0)
    rw [pr_prod_fst (fun p : K × (K → Equiv.Perm K) => p.2 k z0 = p.2 p.1 z0)] at h
    rw [show pr (PCoins K 1 × (K → Equiv.Perm K)) (fun p => p.2 k z0 = p.2 p.1.1 z0) =
      pr (K × (K → Equiv.Perm K)) (fun p => p.2 k z0 = p.2 p.1 z0) from h]
    exact pr_key_hit_le z0 k
  refine (sum_le_sum hk).trans (le_of_eq ?_)
  rw [sum_const, nsmul_eq_mul]
  ring

end InvAttack

section Num

open VoleMole.ZK.Sim (Blk card_blk)

/-- **The point-level hop is false for permutation rows with inverse queries charged at their
answers.** With `K` the blocks (`2¹²⁸`), one secret node (the root), `P = {z₀}` and the
distinguisher's `2⁶⁴` inverse queries at the revealed value (`qInv`: a consistent reader,
`qInv_cons`, of at most `qm = 2⁶⁴` keys on `P`, `qInv_qkeys_le`), the advantage exceeds what
`IC.puncturePt_real`'s bound would give, `|secret|·(N + E_real[#keys read on P])/(|K| − |secret|·qm)`
with `|secret| = N = 1`: it is `≥ 2⁻⁶⁴ − 2⁻¹²⁸`, the bound `< 2⁻¹²⁷`. -/
theorem inv_point_charge_fails (x : ℕ → Blk) (S : Finset Blk) (hS : S.card = 2 ^ 64) (z0 : Blk) :
    (1 + exP (PCoins Blk 1 × (Blk → Equiv.Perm Blk)) (fun p => ((qkeys (fun z => z = z0)
        (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) (cf p.1.2) p.1.1)) p.2)).card : ℝ))) /
        ((2 : ℝ) ^ 128 - 1 * 2 ^ 64) <
      experPm x 1 ∅ (phiInv z0) (fun y π => aInv S z0 y π) -
        experPm x 1 {0} (phiInv z0) (fun y π => aInv S z0 y π) := by
  have hadv := inv_adv_ge x S z0
  have hch := inv_charge_le x S z0
  rw [card_blk, hS] at hadv hch
  push_cast at hadv hch
  have hden : (0 : ℝ) < 2 ^ 128 - 1 * 2 ^ 64 := by norm_num
  have h1 : (1 + exP (PCoins Blk 1 × (Blk → Equiv.Perm Blk)) (fun p => ((qkeys (fun z => z = z0)
        (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) (cf p.1.2) p.1.1)) p.2)).card : ℝ))) /
        ((2 : ℝ) ^ 128 - 1 * 2 ^ 64) ≤ (1 + 2 * 2 ^ 64 / 2 ^ 128) / (2 ^ 128 - 1 * 2 ^ 64) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have h2 : (1 + 2 * 2 ^ 64 / 2 ^ 128 : ℝ) / (2 ^ 128 - 1 * 2 ^ 64) <
      2 ^ 64 / 2 ^ 128 * (1 - 2 ^ 64 / 2 ^ 128) := by norm_num
  linarith

end Num

end VoleMole.ZK.IC
