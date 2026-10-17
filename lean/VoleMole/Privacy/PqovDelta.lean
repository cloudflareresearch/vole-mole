import VoleMole.Privacy.MoussakaPqov
import VoleMole.Protocols.UOVAssumptions

/-!
# The fraction `δ` of bad vinegars of pqov's signer

`Privacy/MoussakaPqov.lean` bounds Theorem 4(b′)'s abort term with pqov's signer by
`2·(δ₀²⁵⁵ + δ₁²⁵⁵)`, `δ = delta pk O` the fraction of vinegars `v` whose system `L_v` is singular.
The figure `δ ≤ 1/255` of the notes is the fraction of singular `45 × 45` matrices over GF(256);
it is not a bound for a fixed key: `L_v = Σ_i v_i S_i` (`Spec.Pqov.sysMat_eq_sum`) is linear in
`v ∈ GF(256)⁷⁴`, so for a fixed key it ranges over a subspace of dimension `≤ 74` of the
`2025`-dimensional space of matrices, and its law is not uniform (`S = 0` gives `δ = 1`;
`delta_zero_key`). It holds **on average over the key**, with `S` uniform:

* `pr_det_zero`, `pr_det_zero_le`: a uniform `45 × 45` matrix over GF(256) is singular with
  probability `σ = 1 − |GL₄₅(𝔽₂₅₆)|/256²⁰²⁵ ≤ 1/255` (`UOVAssumptions.singular_prob_bounds_256`).
* `pr_comp_addHom`: a surjective additive map pushes the uniform distribution forward to the
  uniform one. For `v ≠ 0`, `S ↦ Σ_i v_i S_i` is surjective, so `L_v` is uniform over uniform `S`.
* **`pr_singular_avg`**: over uniform `S` and `v`, `Pr[L_v singular] ≤ 1/255 + 256⁻⁷⁴`, i.e.
  `E_S[δ] ≤ 1/255 + 256⁻⁷⁴`.
* `pr_singular_all`, `pr_dependent_le`: for `m ≤ 74` vinegars, `E_S[δ^m] ≤ σ^m +
  256^m/(255·256⁷⁴)`: linearly independent vinegars give independent uniform systems (the map
  `S ↦ (L_{v_l})_l` is surjective), and `m` uniform vinegars are dependent with probability
  `≤ 256^m/(255·256⁷⁴)` (Mathlib's count of linearly independent families).
* The key family `keyO0 P1 P2` (any `P1` part, `P2` part `P2`, `P3 = 0`): pqov's key generation
  with the oil matrix `O = 0` (`P3 = Upper(Oᵀ P1 O + Oᵀ P2) = 0`). `P` vanishes on its oil space
  (`oilSpace_keyO0`, so pqov's signer is correct for it) and its `S` is `P2` itself
  (`sysCoef_keyO0`). For uniform `P2` (in pqov expanded from `pk_seed`, uniform for AES as a
  random function): **`avg_delta_keyO0`**, `E[δ] ≤ 1/255 + 256⁻⁷⁴`; `avg_delta_pow_keyO0`;
  **`avg_delta255_keyO0`**, `E[δ²⁵⁵] ≤ E[δ³⁷] ≤ 255⁻³⁷ + 1/(255·256³⁷) ≈ 2⁻²⁹⁵·⁸`.
* **`anonymityNC_pqov_keys`**, **`anonymityNCRO_pqov_keys`**: Theorem 4(b′) with pqov's signers
  for keys `keyO0` with independent uniform `P2` parts, averaged over the keys and the vinegar
  tables (the Moderator may depend on the keys): abort term `≤ 4·(255⁻³⁷ + 1/(255·256³⁷))`.

For pqov's real keys (any `O`, `P3` computed) see `Privacy/PqovKeys.lean`: `S = (P1 + P1ᵀ)·O + P2`
from the key layout (`Spec.Pqov.sysCoef_pqovKey`), uniform given `P1` and `O` because `P2` is, and
the same bounds and key-averaged theorems (`avg_delta255_pqovKey`, `anonymityNC_pqov_pqovKeys`,
`anonymityNCRO_pqov_pqovKeys`); `keyO0` is the case `O = 0` (`pqovKey_zero`). The distribution of
`P2` (AES-CTR of `pk_seed`) is the modelling step, not derived.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV

/-- `45 × 45` matrices over GF(256). -/
abbrev Mat45 := Matrix (Fin 45) (Fin 45) GF256

/-- The coefficients `S k i j` of the system (`sysCoef`). -/
abbrev Coef := Fin 45 → Fin 74 → Fin 45 → GF256

/-! ## Uniform pushforward -/

/-- **A surjective additive map sends the uniform distribution to the uniform one.** -/
lemma pr_comp_addHom {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (P : H → Prop) :
    pr G (fun g => P (f g)) = pr H P := by
  classical
  set c := #{g : G | f g = 0} with hc
  have hfib : ∀ h : H, #{g : G | f g = h} = c := fun h =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) (hf 0)
  have hc0 : 0 < c := Finset.card_pos.2 ⟨0, by simp⟩
  have hG : Fintype.card G = Fintype.card H * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := univ)
      (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
    rw [Finset.sum_congr rfl fun h _ => hfib h, sum_const, card_univ, smul_eq_mul]
  have hP : #{g : G | P (f g)} = #{h : H | P h} * c := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := univ.filter P)
      (fun g hg => by simpa using hg)]
    rw [Finset.sum_congr rfl fun h hh => ?_, sum_const, smul_eq_mul]
    rw [← hfib h]
    congr 1
    ext g
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact (mem_filter.1 hh).2
  rw [pr_def, pr_def, hP, hG]
  push_cast
  have : (0 : ℝ) < c := by exact_mod_cast hc0
  field_simp

/-! ## Singular matrices -/

/-- `Pr[P]` as a ratio of `Nat.card`s (generic, so that no `Finset.card` of a concrete predicate on
a huge type has to be compared by the kernel). -/
lemma pr_eq_natCard {α : Type*} [Fintype α] (P : α → Prop) :
    pr α P = (Nat.card {a // P a} : ℝ) / Fintype.card α := by
  classical
  rw [pr_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma pr_not {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) :
    pr α (fun a => ¬ P a) = 1 - pr α P := by
  classical
  have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) P
  rw [card_univ] at h
  rw [pr_def, pr_def, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  norm_cast
  rw [Nat.add_comm]
  convert h using 3

/-- The invertible matrices are the units. -/
noncomputable def unitsEquiv : (Mat45)ˣ ≃ {M : Mat45 // M.det ≠ 0} where
  toFun u := ⟨u, by
    rw [ne_eq, ← isUnit_iff_ne_zero.not_left, not_not]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit⟩
  invFun M := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 M.2)).unit
  left_inv u := by ext1; simp
  right_inv M := Subtype.ext (IsUnit.unit_spec
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 M.2)))

lemma card_mat45 : (Fintype.card Mat45 : ℝ) = (Fintype.card GF256 : ℝ) ^ (45 * 45) := by
  rw [show Fintype.card Mat45 = Fintype.card (Fin 45 → Fin 45 → GF256) from rfl,
    Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  push_cast
  rfl

/-- **A uniform `45 × 45` matrix over GF(256) is singular with probability
`1 − |GL₄₅(𝔽₂₅₆)| / 256²⁰²⁵`.** -/
theorem pr_det_zero :
    pr Mat45 (fun M => M.det = 0) =
      1 - (Nat.card (GL (Fin 45) GF256) : ℝ) / (Fintype.card GF256 : ℝ) ^ (45 * 45) := by
  have h := pr_not (α := Mat45) (fun M => M.det = 0)
  rw [pr_eq_natCard (fun M : Mat45 => ¬ M.det = 0), card_mat45] at h
  rw [show Nat.card (GL (Fin 45) GF256) = Nat.card {M : Mat45 // M.det ≠ 0} from
    Nat.card_congr unitsEquiv]
  linarith

/-- **`σ ≤ 1/255`** (and `≥ 1/256`). -/
theorem pr_det_zero_le : pr Mat45 (fun M => M.det = 0) ≤ 1 / 255 := by
  rw [pr_det_zero]
  exact (UOVAssumptions.singular_prob_bounds_256 GF256.card_eq).2

theorem pr_det_zero_ge : 1 / 256 ≤ pr Mat45 (fun M => M.det = 0) := by
  rw [pr_det_zero]
  exact (UOVAssumptions.singular_prob_bounds_256 GF256.card_eq).1

/-! ## `L_v` over uniform coefficients -/

/-- `S ↦ L_v = Σ_i v_i S_i`, additive. -/
noncomputable def lin (v : Vin) : Coef →+ Mat45 where
  toFun S := Matrix.of fun k j => ∑ i, v i * S k i j
  map_zero' := by ext k j; simp
  map_add' S S' := by
    ext k j
    simp only [Matrix.of_apply, Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- For `v ≠ 0`, `S ↦ L_v` is surjective. -/
lemma lin_surjective {v : Vin} (hv : v ≠ 0) : Function.Surjective (lin v) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv
  intro M
  refine ⟨fun k i j => if i = i₀ then (v i₀)⁻¹ * M k j else 0, ?_⟩
  ext k j
  simp only [lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ i₀]
  simp only [mem_univ, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ hi₀, one_mul]

lemma card_vin : (Fintype.card Vin : ℝ) = 256 ^ 74 := by
  rw [Fintype.card_fun, Fintype.card_fin, GF256.card_eq]
  norm_num

/-- **`E_S[δ] ≤ 1/255 + 256⁻⁷⁴`**: over uniform coefficients `S` and a uniform vinegar `v`, the
system `L_v = Σ_i v_i S_i` is singular with probability at most `1/255 + 256⁻⁷⁴` (`v = 0`, or
`v ≠ 0` and the then uniform `L_v` singular). -/
theorem pr_singular_avg :
    pr (Coef × Vin) (fun z => (Matrix.of fun k j => ∑ i, z.2 i * z.1 k i j).det = 0) ≤
      1 / 255 + 1 / 256 ^ 74 := by
  classical
  rw [← pr_equiv (Equiv.prodComm Vin Coef), pr_prod]
  have hV : (0 : ℝ) < Fintype.card Vin := by exact_mod_cast Fintype.card_pos
  have hσ := pr_det_zero_le
  have hσ0 := pr_nonneg (α := Mat45) (fun M => M.det = 0)
  have hterm : ∀ v : Vin, pr Coef (fun S => (Matrix.of fun k j => ∑ i, v i * S k i j).det = 0) ≤
      pr Mat45 (fun M => M.det = 0) + if v = 0 then 1 else 0 := by
    intro v
    by_cases hv : v = 0
    · have h1 := pr_le_one (α := Coef) (fun S => (Matrix.of fun k j => ∑ i, v i * S k i j).det = 0)
      simp only [hv, ↓reduceIte] at h1 ⊢
      linarith
    · simp only [hv, ↓reduceIte, add_zero]
      exact le_of_eq (pr_comp_addHom (lin v) (lin_surjective hv) (fun M => M.det = 0))
  rw [div_le_iff₀ hV]
  refine (Finset.sum_le_sum fun v _ => hterm v).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq' univ (0 : Vin)]
  simp only [mem_univ, ↓reduceIte]
  rw [card_vin]
  have : (1 : ℝ) / 256 ^ 74 * 256 ^ 74 = 1 := by field_simp
  nlinarith

/-- For a fixed key the bound fails: the key with `S = 0` (e.g. the zero key) has `δ = 1`. -/
theorem delta_zero_key (O : OilMat) : delta ⟨[], fun _ => 0⟩ O = 1 := by
  have h : ∀ v, (sysMat ⟨[], fun _ => 0⟩ O v).det = 0 := fun v => by
    have : sysMat ⟨[], fun _ => 0⟩ O v = 0 := by
      ext k j
      simp [sysMat, polar]
    rw [this, Matrix.det_zero]
  unfold delta
  rw [pr_congr fun v => iff_true_intro (h v)]
  simp [pr_const]

/-! ## The key family `keyO0` -/

section Keys

lemma triangle_74 : triangle 74 = 2775 := by decide

/-- **pqov's key with oil matrix `O = 0`**: the `P1` part `P1` (offsets `< 124875`), the `P2` part
`P2` (`P2 i j k` at `124875 + 2025 i + 45 j + k`), `P3 = 0` (offsets `≥ 274725`). -/
def keyO0 (P1 : ℕ → GF256) (P2 : Fin 74 → Fin 45 → Fin 45 → GF256) : UOVKey :=
  ⟨[], fun n => if n < 124875 then P1 n else
    if h : n < 274725 then P2 ⟨(n - 124875) / 2025, by omega⟩ ⟨(n - 124875) / 45 % 45, by omega⟩
      ⟨(n - 124875) % 45, by omega⟩ else 0⟩

variable (P1 : ℕ → GF256) (P2 : Fin 74 → Fin 45 → Fin 45 → GF256)

lemma keyO0_map_p3 {n : ℕ} (h : 274725 ≤ n) : (keyO0 P1 P2).map n = 0 := by
  simp only [keyO0, show ¬ n < 124875 by omega, show ¬ n < 274725 by omega, ↓reduceIte,
    ↓reduceDIte]

lemma keyO0_map_p2 (a : Fin 74) (t k : Fin 45) :
    (keyO0 P1 P2).map (124875 + a.val * 2025 + t.val * 45 + k.val) = P2 a t k := by
  have h1 : ¬ 124875 + a.val * 2025 + t.val * 45 + k.val < 124875 := by omega
  have h2 : 124875 + a.val * 2025 + t.val * 45 + k.val < 274725 := by omega
  have key : ∀ (a' : Fin 74) (t' k' : Fin 45), a'.val = a.val → t'.val = t.val → k'.val = k.val →
      P2 a' t' k' = P2 a t k := by
    intro a' t' k' e1 e2 e3
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  unfold keyO0
  dsimp only
  simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
  exact key _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)

/-- The P3 monomials (`74 ≤ i`) sit at offsets `≥ 274725` (after `P1`, `P2`). -/
lemma off_ge_of_oil {m : Monomial} (hm : m ∈ forEachMonomial 119 45) (hi : 74 ≤ m.i) :
    274725 ≤ m.off := by
  simp only [forEachMonomial, row, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_range', List.mem_map] at hm
  rcases hm with ⟨a, ha, ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩⟩ | ⟨a, ha, t, ht, rfl⟩
  · simp at hi ha; omega
  · simp at hi ha; omega
  · simp only [Nat.reduceSub, triangle_74] at *
    omega

/-- **`P` vanishes on the oil space of `keyO0`** (`O = 0`: the oil space is the last 45
coordinates, and every monomial in them is a `P3` monomial, whose coefficients are `0`). -/
theorem oilSpace_keyO0 : OilSpace (keyO0 P1 P2) 0 := by
  intro y
  funext k
  simp only [qmap, publicMap, Pi.zero_apply]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  by_cases hi : m.i < 74
  · have : (∑ j, y j • oilVec 0 j) m.i = 0 := by
      simp [Finset.sum_apply, oilVec, hi]
    rw [this, mul_zero, zero_mul]
  · rw [keyO0_map_p3 P1 P2 (by have := off_ge_of_oil hm (by omega); omega), zero_mul, zero_mul]

lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (f : ℕ → List α) (g : α → β) (L : List ℕ) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

lemma list_sum_range {β : Type*} [AddCommMonoid β] (n : ℕ) (g : ℕ → β) :
    ((List.range n).map g).sum = ∑ t ∈ range n, g t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma vinVec_unit (i : Fin 74) (n : ℕ) : vinVec (unitVin i) n = if n = i.val then 1 else 0 := by
  unfold vinVec unitVin
  by_cases h : n < 74
  · simp only [h, ↓reduceDIte]
    by_cases e : n = i.val
    · subst e; simp
    · simp only [e, ↓reduceIte]
      exact Pi.single_eq_of_ne (fun h' => e (by rw [← h']) ) _
  · have : n ≠ i.val := by omega
    simp [h, this]

lemma oilVec_zero (j : Fin 45) (n : ℕ) : oilVec 0 j n = if n = 74 + j.val then 1 else 0 := by
  unfold oilVec
  by_cases h : n < 74
  · have : n ≠ 74 + j.val := by omega
    simp [h, this]
  · simp [h]

section Sel
variable (c : ℕ → GF256) (i : Fin 74) (j k : Fin 45)

/-- The one monomial `x_i x_{74+j}` of `B(e_i, ō_j)` for `O = 0`. -/
def gsel (m : Monomial) : GF256 := if m.i = i.val ∧ m.j = 74 + j.val then c (m.off + k) else 0

lemma sum_row_zero (a j0 n p : ℕ) (h : ∀ t < n - j0, ¬ (a = i.val ∧ j0 + t = 74 + j.val)) :
    ((row 45 a j0 n p).map (gsel c i j k)).sum = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  simp only [row, List.map_map, List.mem_map, List.mem_range, Function.comp] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [gsel]
  simp [h t ht]

lemma sum_row_p2 (a p : ℕ) :
    ((row 45 a 74 119 p).map (gsel c i j k)).sum =
      if a = i.val then c (p + j.val * 45 + k) else 0 := by
  unfold row
  rw [List.map_map, list_sum_range]
  simp only [Function.comp, gsel, Nat.reduceSub, Nat.add_left_cancel_iff]
  by_cases ha : a = i.val
  · simp only [ha, true_and, ↓reduceIte]
    rw [Finset.sum_ite_eq' (range 45) j.val]
    simp [j.isLt]
  · simp [ha]

end Sel

/-- **The system coefficients of `keyO0` are its `P2` part**: `S k i j = P2 i j k`. -/
theorem sysCoef_keyO0 (k : Fin 45) (i : Fin 74) (j : Fin 45) :
    sysCoef (keyO0 P1 P2) 0 k i j = P2 i j k := by
  unfold sysCoef polar
  rw [List.map_congr_left (g := gsel (keyO0 P1 P2).map i j k) fun m hm => by
    obtain ⟨hij, -⟩ := mem_forEachMonomial hm
    have hi := i.isLt
    rw [vinVec_unit, vinVec_unit, oilVec_zero, oilVec_zero]
    have hz :
        (if m.i = 74 + j.val then (1 : GF256) else 0) * (if m.j = i.val then 1 else 0) = 0 := by
      by_cases h1 : m.i = 74 + j.val
      · have h2 : m.j ≠ i.val := by omega
        simp [h2]
      · simp [h1]
    rw [hz, add_zero]
    unfold gsel
    by_cases hA : m.i = i.val <;> by_cases hB : m.j = 74 + j.val <;> simp [hA, hB]]
  unfold forEachMonomial
  simp only [Nat.reduceSub, List.map_append, List.sum_append, list_sum_flatMap]
  rw [List.map_congr_left (g := fun a => if a = i.val then
      (keyO0 P1 P2).map (45 * triangle 74 + a * (45 * 45) + j.val * 45 + k) else 0) fun a ha => by
    rw [List.mem_range] at ha
    rw [sum_row_zero _ _ _ _ _ _ _ _ (fun t ht => by omega), sum_row_p2, zero_add]]
  rw [List.map_congr_left (l := List.range' 74 45) (g := fun _ => (0 : GF256)) fun a ha => by
    rw [List.mem_range'_1] at ha
    exact sum_row_zero _ _ _ _ _ _ _ _ (fun t ht => by omega)]
  rw [list_sum_range, Finset.sum_ite_eq' (range 74) i.val]
  simp only [mem_range, i.isLt, ↓reduceIte, List.map_const', List.sum_replicate, smul_zero,
    add_zero, triangle_74]
  rw [show 45 * 2775 + i.val * (45 * 45) + j.val * 45 + k.val =
    124875 + i.val * 2025 + j.val * 45 + k.val by ring]
  exact keyO0_map_p2 P1 P2 i j k

end Keys

/-! ## Higher moments: `m` vinegars at once -/

section Moments

lemma mulVec_surj_of_li {m : ℕ} (vs : Fin m → Vin) (h : LinearIndependent GF256 vs) :
    Function.Surjective (Matrix.of vs).mulVec := by
  have hr : (Matrix.of vs).rank = m := by
    have := LinearIndependent.rank_matrix (M := Matrix.of vs) h
    rwa [Fintype.card_fin] at this
  have htop : LinearMap.range (Matrix.of vs).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [← Matrix.rank, hr, Module.finrank_fin_fun])
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop y
  exact ⟨x, by rwa [Matrix.mulVecLin_apply] at hx⟩

/-- `S ↦ (L_{v_l})_l` for `m` vinegars. -/
noncomputable def linM {m : ℕ} (vs : Fin m → Vin) : Coef →+ (Fin m → Mat45) :=
  AddMonoidHom.pi fun l => lin (vs l)

lemma linM_surjective {m : ℕ} {vs : Fin m → Vin} (h : LinearIndependent GF256 vs) :
    Function.Surjective (linM vs) := by
  intro T
  have hs := mulVec_surj_of_li vs h
  choose s hs using fun kj : Fin 45 × Fin 45 => hs (fun l => T l kj.1 kj.2)
  refine ⟨fun k i j => s (k, j) i, ?_⟩
  funext l
  ext k j
  have := congrFun (hs (k, j)) l
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at this
  simp only [linM, AddMonoidHom.pi_apply, lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply]
  exact this

/-- Averages of `f ≤ a + [Q]`. -/
lemma avg_le_add_pr {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (a : ℝ) (Q : X → Prop)
    [DecidablePred Q] (h : ∀ x, f x ≤ a + if Q x then 1 else 0) :
    (∑ x, f x) / Fintype.card X ≤ a + pr X Q := by
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hX, pr_def, add_mul, div_mul_cancel₀ _ hX.ne']
  refine (Finset.sum_le_sum fun x _ => h x).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, Finset.sum_boole]
  ring

/-- **`m` vinegars at once**: over uniform `S` and `m` uniform vinegars, all `m` systems are
singular with probability `≤ σ^m + Pr[the vinegars are linearly dependent]`. -/
theorem pr_singular_all (m : ℕ) :
    pr (Coef × (Fin m → Vin)) (fun z => ∀ l, (lin (z.2 l) z.1).det = 0) ≤
      pr Mat45 (fun M => M.det = 0) ^ m +
        pr (Fin m → Vin) (fun vs => ¬ LinearIndependent GF256 vs) := by
  classical
  rw [← pr_equiv (Equiv.prodComm (Fin m → Vin) Coef), pr_prod]
  refine avg_le_add_pr _ _ _ fun vs => ?_
  by_cases hli : LinearIndependent GF256 vs
  · simp only [hli, not_true_eq_false, ↓reduceIte, add_zero]
    have h1 := pr_comp_addHom (linM vs) (linM_surjective hli) (fun T => ∀ l, (T l).det = 0)
    have h2 := pr_forall_fin m (fun M : Mat45 => M.det = 0)
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact le_of_eq (h1.trans h2)
  · simp only [hli, not_false_eq_true, ↓reduceIte]
    have := pr_le_one (α := Coef) (fun S => ∀ l, (lin (vs l) S).det = 0)
    have := pr_nonneg (α := Mat45) (fun M => M.det = 0)
    have : 0 ≤ pr Mat45 (fun M => M.det = 0) ^ m := by positivity
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    linarith


set_option maxRecDepth 20000 in
/-- **`m ≤ 74` uniform vinegars are linearly dependent with probability
`≤ 256^m / (255·256⁷⁴)`.** -/
theorem pr_dependent_le (m : ℕ) (hm : m ≤ 74) :
    pr (Fin m → Vin) (fun vs => ¬ LinearIndependent GF256 vs) ≤ 256 ^ m / (255 * 256 ^ 74) := by
  have hfr : Module.finrank GF256 Vin = 74 := Module.finrank_fin_fun GF256
  have hcard := card_linearIndependent (K := GF256) (V := Vin) (k := m) (by rw [hfr]; exact hm)
  rw [hfr, GF256.card_eq] at hcard
  rw [pr_not, pr_eq_natCard, hcard]
  have hV : (Fintype.card (Fin m → Vin) : ℝ) = ((256 : ℝ) ^ 74) ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, card_vin]
  rw [hV, Nat.cast_prod]
  have hq : (0 : ℝ) < 256 ^ 74 := by positivity
  have hprod : (∏ i : Fin m, ((256 ^ 74 - 256 ^ (i : ℕ) : ℕ) : ℝ)) / ((256 : ℝ) ^ 74) ^ m =
      ∏ i : Fin m, (1 - (256 : ℝ) ^ (i : ℕ) / 256 ^ 74) := by
    rw [show ((256 : ℝ) ^ 74) ^ m = ∏ _i : Fin m, (256 : ℝ) ^ 74 by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hle : 256 ^ (i : ℕ) ≤ 256 ^ 74 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, sub_div, div_self hq.ne']
  rw [hprod]
  have ha0 : ∀ i ∈ (univ : Finset (Fin m)), (0 : ℝ) ≤ 256 ^ (i : ℕ) / 256 ^ 74 :=
    fun i _ => by positivity
  have ha1 : ∀ i ∈ (univ : Finset (Fin m)), (256 : ℝ) ^ (i : ℕ) / 256 ^ 74 ≤ 1 := fun i _ => by
    rw [div_le_one hq]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hu := UOVAssumptions.one_sub_sum_le_prod univ
    (fun i : Fin m => (256 : ℝ) ^ (i : ℕ) / 256 ^ 74)
    ha0 ha1
  have hsum : ∑ i : Fin m, (256 : ℝ) ^ (i : ℕ) / 256 ^ 74 ≤ 256 ^ m / (255 * 256 ^ 74) := by
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i => (256 : ℝ) ^ i)]
    have hg := geom_sum_mul (256 : ℝ) m
    rw [div_le_div_iff₀ hq (by positivity)]
    nlinarith
  linarith

end Moments

/-! ## On average over the key -/

section Average

open VoleMole.ZK.Sim

/-- The `P2` parts of the keys `keyO0`. -/
abbrev P2Part := Fin 74 → Fin 45 → Fin 45 → GF256

/-- The `P2` part as the system coefficients. -/
def p2Equiv : P2Part ≃ Coef where
  toFun P2 k i j := P2 i j k
  invFun S i j k := S k i j
  left_inv _ := rfl
  right_inv _ := rfl

variable (P1 : ℕ → GF256)

lemma sysMat_keyO0 (P2 : P2Part) (v : Vin) : sysMat (keyO0 P1 P2) 0 v = lin v (p2Equiv P2) := by
  rw [sysMat_eq_sum]
  ext k j
  simp only [Matrix.of_apply, lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sysCoef_keyO0]
  rfl

/-- **`E_{P2}[δ] ≤ 1/255 + 256⁻⁷⁴`** for the keys `keyO0 P1 P2` with uniform `P2`. -/
theorem avg_delta_keyO0 :
    (∑ P2 : P2Part, delta (keyO0 P1 P2) 0) / Fintype.card P2Part ≤ 1 / 255 + 1 / 256 ^ 74 := by
  have e : pr (P2Part × Vin) (fun z => (lin z.2 (p2Equiv z.1)).det = 0) =
      pr (Coef × Vin) (fun z => (lin z.2 z.1).det = 0) :=
    pr_equiv ((p2Equiv).prodCongr (Equiv.refl Vin)) (fun z => (lin z.2 z.1).det = 0)
  rw [pr_prod] at e
  have hd : ∀ P2 : P2Part, delta (keyO0 P1 P2) 0 = pr Vin (fun v => (lin v (p2Equiv P2)).det = 0) :=
    fun P2 => pr_congr fun v => by rw [sysMat_keyO0]
  simp only [hd]
  rw [e]
  exact pr_singular_avg

/-- **`E_{P2}[δ^m] ≤ (1/255)^m + 256^m / (255·256⁷⁴)`** for `m ≤ 74`. -/
theorem avg_delta_pow_keyO0 (m : ℕ) (hm : m ≤ 74) :
    (∑ P2 : P2Part, delta (keyO0 P1 P2) 0 ^ m) / Fintype.card P2Part ≤
      (1 / 255) ^ m + 256 ^ m / (255 * 256 ^ 74) := by
  have e : pr (P2Part × (Fin m → Vin)) (fun z => ∀ l, (lin (z.2 l) (p2Equiv z.1)).det = 0) =
      pr (Coef × (Fin m → Vin)) (fun z => ∀ l, (lin (z.2 l) z.1).det = 0) :=
    pr_equiv ((p2Equiv).prodCongr (Equiv.refl (Fin m → Vin)))
      (fun z => ∀ l, (lin (z.2 l) z.1).det = 0)
  rw [pr_prod] at e
  have hd : ∀ P2 : P2Part, delta (keyO0 P1 P2) 0 ^ m =
      pr (Fin m → Vin) (fun vs => ∀ l, (lin (vs l) (p2Equiv P2)).det = 0) := fun P2 => by
    rw [pr_forall_fin m (fun v : Vin => (lin v (p2Equiv P2)).det = 0)]
    exact congrArg (· ^ m) (pr_congr fun v => by rw [sysMat_keyO0])
  simp only [hd]
  rw [e]
  refine (pr_singular_all m).trans ?_
  have hσ := pr_det_zero_le
  have hσ0 := pr_nonneg (α := Mat45) (fun M => M.det = 0)
  have h1 : pr Mat45 (fun M => M.det = 0) ^ m ≤ (1 / 255) ^ m := pow_le_pow_left₀ hσ0 hσ m
  have h2 := pr_dependent_le m hm
  linarith

/-- **pqov's abort probability on average over the key**: `E_{P2}[δ²⁵⁵] ≤ 255⁻³⁷ + 1/(255·256³⁷)`
(about `2⁻²⁹⁵·⁸`), from the 37th moment (`δ²⁵⁵ ≤ δ³⁷`). -/
theorem avg_delta255_keyO0 :
    (∑ P2 : P2Part, delta (keyO0 P1 P2) 0 ^ 255) / Fintype.card P2Part ≤
      (1 / 255) ^ 37 + 1 / (255 * 256 ^ 37) := by
  have hcard : (0 : ℝ) < Fintype.card P2Part := by exact_mod_cast Fintype.card_pos
  have hle : ∀ P2 : P2Part, delta (keyO0 P1 P2) 0 ^ 255 ≤ delta (keyO0 P1 P2) 0 ^ 37 := fun P2 =>
    pow_le_pow_of_le_one (pr_nonneg _) (pr_le_one _) (by norm_num)
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun P2 _ => hle P2) hcard.le).trans ?_
  refine (avg_delta_pow_keyO0 P1 37 (by norm_num)).trans (le_of_eq ?_)
  congr 1
  rw [show (256 : ℝ) ^ 74 = 256 ^ 37 * 256 ^ 37 by rw [← pow_add]]
  field_simp

/-- The marginal of one coordinate of a uniform `Bool → X`. -/
lemma avg_bool_arrow {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (c : Bool) :
    (∑ κ : Bool → X, f (κ c)) / Fintype.card (Bool → X) = (∑ x, f x) / Fintype.card X := by
  classical
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hr : (0 : ℝ) < Fintype.card ({b // b ≠ c} → X) := by exact_mod_cast Fintype.card_pos
  have hs : ∑ κ : Bool → X, f (κ c) = ∑ p : X × ({b // b ≠ c} → X), f p.1 :=
    (Fintype.sum_equiv (Equiv.funSplitAt c X).symm _ _ fun p => by
      simp [Equiv.funSplitAt, Equiv.piSplitAt]).symm
  rw [hs, Fintype.sum_prod_type, Fintype.card_congr (Equiv.funSplitAt c X), Fintype.card_prod]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  field_simp

/-- `OilSpace` and `δ` depend only on the key's map (not on its digest). -/
lemma oilSpace_of_map_eq {pk pk' : UOVKey} (h : pk.map = pk'.map) (O : OilMat)
    (hO : OilSpace pk' O) : OilSpace pk O := by
  intro y
  have := hO y
  simp only [qmap, h] at this ⊢
  exact this

lemma delta_of_map_eq {pk pk' : UOVKey} (h : pk.map = pk'.map) (O : OilMat) :
    delta pk O = delta pk' O := by
  have e : ∀ v, sysMat pk O v = sysMat pk' O v := fun v => by
    ext k j
    simp only [sysMat, polar, Matrix.of_apply, h]
  unfold delta
  exact pr_congr fun v => by rw [e]

/-- The abort bound of the key-averaged theorems: `255⁻³⁷ + 1/(255·256³⁷)`. -/
noncomputable def abortKeys : ℝ := (1 / 255) ^ 37 + 1 / (255 * 256 ^ 37)

lemma avg_delta255_keys (P1 : Bool → ℕ → GF256) (c : Bool) :
    (∑ κ : Bool → P2Part, delta (keyO0 (P1 c) (κ c)) 0 ^ 255) / Fintype.card (Bool → P2Part) ≤
      abortKeys := by
  rw [avg_bool_arrow (fun P2 => delta (keyO0 (P1 c) P2) 0 ^ 255) c]
  exact avg_delta255_keyO0 (P1 c)

/-- **Theorem 4(b′) with honestly generated pqov keys** (the family `keyO0`: `O = 0`, uniform
independent `P2` parts per Anchor, any `P1` parts) **and pqov's signers**: for every family of
Moderators indexed by the Anchors' keys (whose choices may depend on the keys), averaged over the
keys and the vinegar tables, `≤ 4εR + 4·(255⁻³⁷ + 1/(255·256³⁷))`, about `4εR + 2⁻²⁹³·⁸`. -/
theorem anonymityNC_pqov_keys (P1 : Bool → ℕ → GF256) (A : (Bool → P2Part) → AdversaryNC)
    (hpk : ∀ κ c, ((A κ).pk c).map = (keyO0 (P1 c) (κ c)).map)
    (idx : Spec.Moussaka.AnchorSet → UOVKey → ℕ)
    (PI : Spec.Moussaka.NIZK Spec.Moussaka.IssueInstance) (hidx : IdxSound idx) {CR : Type}
    [Fintype CR] [Nonempty CR]
    (simR : Spec.Moussaka.RedeemInstance → CR → Bytes)
    (PR : Spec.Moussaka.NIZK Spec.Moussaka.RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr ((Bool → P2Part) × (VTab Vin × TapeNC)) (fun z =>
        realGameNC (A z.1) idx PI (pqovRO (A z.1).pk (fun _ => 0) 255 z.2.1) PR false z.2.2) -
      pr ((Bool → P2Part) × (VTab Vin × TapeNC)) (fun z =>
        realGameNC (A z.1) idx PI (pqovRO (A z.1).pk (fun _ => 0) 255 z.2.1) PR true z.2.2)| ≤
      4 * εR + 2 * (abortKeys + abortKeys) := by
  have hO : ∀ κ c, OilSpace ((A κ).pk c) ((fun _ => (0 : OilMat)) c) := fun κ c =>
    oilSpace_of_map_eq (hpk κ c) 0 (oilSpace_keyO0 _ _)
  have hw (κ : Bool → P2Part) := anonymityNC_pqov (A κ) idx PI (fun _ => 0) (hO κ) hidx simR PR
    hεR hR
  refine abs_pr_avg_abort
    (fun κ (z : VTab Vin × TapeNC) =>
      realGameNC (A κ) idx PI (pqovRO (A κ).pk (fun _ => 0) 255 z.1) PR false z.2)
    (fun κ (z : VTab Vin × TapeNC) =>
      realGameNC (A κ) idx PI (pqovRO (A κ).pk (fun _ => 0) 255 z.1) PR true z.2)
    (4 * εR) (fun κ c => delta ((A κ).pk c) 0 ^ 255) (fun _ => abortKeys) hw fun c => ?_
  simp only [delta_of_map_eq (hpk _ c)]
  exact avg_delta255_keys P1 c

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model with honestly generated pqov keys
and pqov's signers** (the Lean prover and verifier on the shared tables, every type of cipher
rows), averaged over the keys `keyO0` and the vinegar tables:

    4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 4·q₃·2⁻¹²⁸
      + 4·(255⁻³⁷ + 1/(255·256³⁷)). -/
theorem anonymityNCRO_pqov_keys {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    (P1 : Bool → ℕ → GF256) (A : (Bool → P2Part) → AdversaryNCRO R)
    (hpk : ∀ κ c, ((A κ).pk c).map = (keyO0 (P1 c) (κ c)).map)
    (idx : Spec.Moussaka.AnchorSet → UOVKey → ℕ)
    (hidx : IdxSound idx) {q3 q5 qE : ℕ} (hA : ∀ κ, (A κ).Budget q3 q5 qE) :
    |pr ((Bool → P2Part) × (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R))) (fun z =>
        realGameNCRO (A z.1) idx leanPI leanVI (pqovRO (A z.1).pk (fun _ => 0) 255 z.2.1) leanPR
          false z.2.2) -
      pr ((Bool → P2Part) × (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R))) (fun z =>
        realGameNCRO (A z.1) idx leanPI leanVI (pqovRO (A z.1).pk (fun _ => 0) 255 z.2.1) leanPR
          true z.2.2)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) + 2 * (abortKeys + abortKeys) := by
  have hO : ∀ κ c, OilSpace ((A κ).pk c) ((fun _ => (0 : OilMat)) c) := fun κ c =>
    oilSpace_of_map_eq (hpk κ c) 0 (oilSpace_keyO0 _ _)
  have hw (κ : Bool → P2Part) := anonymityNCRO_pqov (A κ) idx (fun _ => 0) (hO κ) hidx (hA κ)
  generalize (2 : ℝ) ^ 1024 = M at hw ⊢
  refine abs_pr_avg_abort
    (fun κ (z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) =>
      realGameNCRO (A κ) idx leanPI leanVI (pqovRO (A κ).pk (fun _ => 0) 255 z.1) leanPR false z.2)
    (fun κ (z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) =>
      realGameNCRO (A κ) idx leanPI leanVI (pqovRO (A κ).pk (fun _ => 0) 255 z.1) leanPR true z.2)
    (4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / M) + 4 * (q3 / 2 ^ 128))
    (fun κ c => delta ((A κ).pk c) 0 ^ 255) (fun _ => abortKeys) hw fun c => ?_
  simp only [delta_of_map_eq (hpk _ c)]
  exact avg_delta255_keys P1 c

end Average

end VoleMole.Privacy.Moussaka
