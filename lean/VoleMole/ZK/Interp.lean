import VoleMole.ZK.QsIdeal
import VoleMole.ZK.BavcLemmas

/-!
# Newton interpolation is correct (`InterpOk`)

`Prover.qsProve` interpolates its `d + 1` samples with `Prover.interpolate` (Newton's divided
differences, then the Newton form expanded by Horner's rule). `ZK/QsIdeal.lean` took the
correctness of this code as the hypothesis `InterpOk d`; here it is proved for every `d` with
`d + 1 < 2⁶⁴` (the sample points `1, …, d + 1` are then distinct), so `InterpOk 2` (PomFRIT) and
`InterpOk 9` (Moussaka, Ratatouille) hold (`interpOk`).

* The code (`interpolate_eq`): `phase1` (the divided-difference table, in place) then `phase2`
  (Horner on the Newton form). In characteristic 2 the code's `+` is `−`.
* `dd x y a m`: the divided difference of the window `[a, a + m]`, by the code's recurrence;
  `phase1_get`: the table ends with `dd x y 0 i` at `i`.
* `newton x y a m = Σ_{t ≤ m} D(a, t) Π_{k<t} (X − x_{a+k})`, the Newton form of the window;
  `newton_interp`: it interpolates the window, by induction on `m` through Neville's identity
  (the combination `((X − x_a) N_{a+1,m} − (X − x_b) N_{a,m}) / (x_b − x_a)` interpolates
  `[a, b]` and has the same top coefficient as `N_{a,m+1}`, so their difference, of degree
  `≤ m`, vanishes at `m + 1` points).
* `polyOf_phase2`: Horner's rule builds the Newton form.
-/

open Finset Polynomial

namespace VoleMole.ZK.Interp

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

lemma two_eq_zero : (2 : GF128) = 0 := CharTwo.two_eq_zero

lemma add_self (a : GF128) : a + a = 0 := CharTwo.add_self_eq_zero a

lemma gfInv_eq (a : GF128) : gfInv a = a⁻¹ := gfId.map_gfInv GF128.card_eq a

/-! ## Divided differences and the Newton form -/

section Newton

variable (x y : ℕ → GF128)

/-- The divided differences, by the code's recurrence (`+` is `−` in characteristic 2):
`D(a, 0) = y_a`, `D(a, m + 1) = (D(a + 1, m) + D(a, m)) / (x_{a+m+1} + x_a)`. -/
noncomputable def dd : ℕ → ℕ → GF128
  | a, 0 => y a
  | a, m + 1 => (dd (a + 1) m + dd a m) * (x (a + m + 1) + x a)⁻¹

/-- `Π_{k<t} (X − x_{a+k})`. -/
noncomputable def omega (a t : ℕ) : GF128[X] := ∏ k ∈ range t, (X - C (x (a + k)))

/-- The Newton form of the window `[a, a + m]`. -/
noncomputable def newton (a m : ℕ) : GF128[X] :=
  ∑ t ∈ range (m + 1), C (dd x y a t) * omega x a t

lemma omega_monic (a t : ℕ) : (omega x a t).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma natDegree_omega (a t : ℕ) : (omega x a t).natDegree = t := by
  induction t with
  | zero => simp [omega]
  | succ t ih =>
    rw [omega, prod_range_succ, ← omega, (omega_monic x a t).natDegree_mul (monic_X_sub_C _), ih,
      natDegree_X_sub_C]

lemma omega_coeff_top (a t : ℕ) : (omega x a t).coeff t = 1 := by
  have := (omega_monic x a t).coeff_natDegree
  rwa [natDegree_omega] at this

lemma omega_eval_zero {a t k : ℕ} (hk : k < t) : (omega x a t).eval (x (a + k)) = 0 := by
  rw [omega, eval_prod]
  exact prod_eq_zero (mem_range.2 hk) (by simp)

lemma omega_zero (a : ℕ) : omega x a 0 = 1 := by simp [omega]

lemma omega_succ' (a t : ℕ) : omega x a (t + 1) = (X - C (x a)) * omega x (a + 1) t := by
  rw [omega, prod_range_succ', add_zero, mul_comm, omega]
  refine congrArg _ (prod_congr rfl fun k _ => ?_)
  rw [show a + (k + 1) = a + 1 + k by ring]

lemma newton_succ (a m : ℕ) :
    newton x y a (m + 1) = newton x y a m + C (dd x y a (m + 1)) * omega x a (m + 1) := by
  rw [newton, sum_range_succ]
  rfl

lemma newton_deg (a m : ℕ) :
    (newton x y a m).natDegree ≤ m ∧ (newton x y a m).coeff m = dd x y a m := by
  induction m with
  | zero => simp [newton, omega]
  | succ m ih =>
    rw [newton_succ]
    have h1 : (C (dd x y a (m + 1)) * omega x a (m + 1)).natDegree ≤ m + 1 :=
      (natDegree_C_mul_le _ _).trans (natDegree_omega x a (m + 1)).le
    refine ⟨(natDegree_add_le _ _).trans (max_le (ih.1.trans (Nat.le_succ m)) h1), ?_⟩
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (by omega), coeff_C_mul, omega_coeff_top]
    ring

lemma coeff_X_add_C_mul (c : GF128) (p : GF128[X]) (m : ℕ) :
    ((X + C c) * p).coeff (m + 1) = p.coeff m + c * p.coeff (m + 1) := by
  rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

/-- **The Newton form interpolates its window.** -/
theorem newton_interp (m : ℕ) : ∀ a, (∀ i j, i ≤ m → j ≤ m → x (a + i) = x (a + j) → i = j) →
    ∀ k ≤ m, (newton x y a m).eval (x (a + k)) = y (a + k) := by
  induction m with
  | zero =>
    intro a _ k hk
    obtain rfl : k = 0 := by omega
    simp [newton, omega, dd]
  | succ m ih =>
    intro a hinj k hk
    have I0 := ih a fun i j hi hj h => hinj i j (by omega) (by omega) h
    have I1 := ih (a + 1) fun i j hi hj h => by
      have := hinj (i + 1) (j + 1) (by omega) (by omega)
        (by rw [show a + (i + 1) = a + 1 + i by ring, show a + (j + 1) = a + 1 + j by ring]
            exact h)
      omega
    have hab : x (a + m + 1) + x a ≠ 0 := by
      intro h
      have h' : x (a + (m + 1)) = x (a + 0) := by
        rw [add_zero, ← add_assoc, ← sub_eq_zero, CharTwo.sub_eq_add, h]
      have := hinj (m + 1) 0 le_rfl (Nat.zero_le _) h'
      omega
    set D := (x (a + m + 1) + x a)⁻¹ with hD
    have hDm : D * (x (a + m + 1) + x a) = 1 := inv_mul_cancel₀ hab
    -- Neville's combination.
    set Q := C D * ((X + C (x a)) * newton x y (a + 1) m + (X + C (x (a + m + 1))) * newton x y a m)
      with hQ
    have hQe : ∀ k ≤ m + 1, Q.eval (x (a + k)) = y (a + k) := by
      intro k hk
      simp only [hQ, eval_mul, eval_C, eval_add, eval_X]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have e0 := I0 0 (Nat.zero_le _)
        rw [add_zero] at e0
        rw [add_zero, add_self, zero_mul, zero_add, e0, add_comm (x a), ← mul_assoc, hDm, one_mul]
      · by_cases hkm : k = m + 1
        · subst hkm
          rw [show a + (m + 1) = a + m + 1 by ring, add_self, zero_mul, add_zero,
            show a + m + 1 = a + 1 + m by ring, I1 m le_rfl, show a + 1 + m = a + m + 1 by ring,
            ← mul_assoc, hDm, one_mul]
        · have e1 := I1 (k - 1) (by omega)
          rw [show a + 1 + (k - 1) = a + k by omega] at e1
          rw [e1, I0 k (by omega)]
          linear_combination (D * x (a + k) * y (a + k)) * two_eq_zero + y (a + k) * hDm
    -- `Q` is the Newton form of `[a, a + m + 1]`.
    have hR : Q = newton x y a (m + 1) := by
      have hN0 := newton_deg x y a m
      have hN1 := newton_deg x y (a + 1) m
      have hN := newton_deg x y a (m + 1)
      have hXC : ∀ c : GF128, (X + C c).natDegree = 1 := fun c => natDegree_X_add_C c
      have hQd : Q.natDegree ≤ m + 1 := by
        refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
        · exact (natDegree_mul_le).trans (by rw [hXC]; omega)
        · exact (natDegree_mul_le).trans (by rw [hXC]; omega)
      have hQc : Q.coeff (m + 1) = dd x y a (m + 1) := by
        rw [hQ, coeff_C_mul, coeff_add, coeff_X_add_C_mul, coeff_X_add_C_mul,
          coeff_eq_zero_of_natDegree_lt (show (newton x y (a + 1) m).natDegree < m + 1 by omega),
          coeff_eq_zero_of_natDegree_lt (show (newton x y a m).natDegree < m + 1 by omega), hN0.2,
          hN1.2, dd, hD]
        ring
      have hdeg : (Q - newton x y a (m + 1)).natDegree < Fintype.card (Fin (m + 1)) := by
        rw [Fintype.card_fin, Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
        intro N hN'
        rw [coeff_sub]
        rcases Nat.lt_or_ge (m + 1) N with h | h
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
            sub_zero]
        · obtain rfl : N = m + 1 := by omega
          rw [hQc, hN.2, sub_self]
      have := eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Q - newton x y a (m + 1))
        (f := fun i : Fin (m + 1) => x (a + i))
        (fun i j h => Fin.ext (hinj i j (by omega) (by omega) h)) (fun i => by
          rw [eval_sub, hQe i (by omega), newton_succ, eval_add, eval_mul,
            omega_eval_zero x i.isLt, mul_zero, add_zero, I0 i (by omega), sub_self]) hdeg
      exact sub_eq_zero.1 this
    rw [← hR]
    exact hQe k hk

end Newton

/-! ## The code -/

/-- One update of the divided-difference table (round `j`, step `s`: index `i = n − 1 − s`). -/
def innerStep (xs : Array GF128) (j : ℕ) (dd : Array GF128) (s : ℕ) : Array GF128 :=
  dd.set! (xs.size - 1 - s) ((dd[xs.size - 1 - s]! + dd[xs.size - 1 - s - 1]!) *
    gfInv (xs[xs.size - 1 - s]! + xs[xs.size - 1 - s - j]!))

/-- Round `j` of the table. -/
def round (xs : Array GF128) (dd : Array GF128) (j : ℕ) : Array GF128 :=
  (List.range (xs.size - j)).foldl (innerStep xs j) dd

/-- The divided-difference table. -/
def phase1 (xs ys : Array GF128) : Array GF128 := (List.range' 1 (xs.size - 1)).foldl (round xs) ys

/-- One Horner step on the Newton form. -/
def hornerStep (xs dd : Array GF128) (p : Array GF128) (s : ℕ) : Array GF128 :=
  (Prover.mulLinear p xs[xs.size - 1 - s]!).set! 0
    ((Prover.mulLinear p xs[xs.size - 1 - s]!)[0]! + dd[xs.size - 1 - s]!)

/-- Horner's rule on the Newton form with coefficients `dd`. -/
def phase2 (xs dd : Array GF128) : Array GF128 :=
  (List.range' 1 (xs.size - 1)).foldl (hornerStep xs dd) #[dd[xs.size - 1]!]

lemma forIn_range'_foldl {β : Type} (a b : ℕ) (init : β) (g : ℕ → β → β) :
    forIn (m := Id) [a:b] init (fun i s => pure (ForInStep.yield (g i s))) =
      pure ((List.range' a (b - a)).foldl (fun s i => g i s) init) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel]
  rw [List.forIn_pure_yield_eq_foldl]

lemma interpolate_eq (xs ys : Array GF128) :
    Prover.interpolate xs ys = phase2 xs (phase1 xs ys) := by
  unfold Prover.interpolate
  simp only [Id.run, forIn_range'_foldl, pure_bind, Nat.sub_zero, ← List.range_eq_range']
  rfl

/-! ### The divided-difference table -/

section Table

variable (xs ys : Array GF128)

/-- The table after round `j`: `D(i − j, j)` at `i ≥ j`, the finished `D(0, i)` below. -/
noncomputable def tab (j i : ℕ) : GF128 :=
  if j ≤ i then dd (fun i => xs[i]!) (fun i => ys[i]!) (i - j) j
  else dd (fun i => xs[i]!) (fun i => ys[i]!) 0 i

lemma tab_zero (i : ℕ) : tab xs ys 0 i = ys[i]! := by simp [tab, dd]

/-- The new entry of round `j` at `i ≥ j`. -/
lemma tab_succ {j i : ℕ} (hj : 1 ≤ j) (hi : j ≤ i) :
    (tab xs ys (j - 1) i + tab xs ys (j - 1) (i - 1)) * gfInv (xs[i]! + xs[i - j]!) =
      tab xs ys j i := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [tab, Nat.add_sub_cancel, show j ≤ i by omega, show j ≤ i - 1 by omega, hi,
    ↓reduceIte, gfInv_eq]
  rw [dd, show i - (j + 1) + 1 = i - j by omega, show i - 1 - j = i - (j + 1) by omega,
    show i - (j + 1) + j + 1 = i by omega]

lemma tab_below {j i : ℕ} (hij : i < j) : tab xs ys (j - 1) i = tab xs ys j i := by
  simp only [tab, show ¬ j ≤ i by omega, ↓reduceIte]
  split_ifs with h
  · rw [show i - (j - 1) = 0 by omega, show j - 1 = i by omega]
  · rfl

/-- **Round `j`** turns the table of round `j − 1` into that of round `j`. -/
lemma round_spec {j : ℕ} (hj : 1 ≤ j) (hjn : j < xs.size) (a : Array GF128)
    (ha : a.size = xs.size) (hE : ∀ i < xs.size, a[i]! = tab xs ys (j - 1) i) :
    (round xs a j).size = xs.size ∧ ∀ i < xs.size, (round xs a j)[i]! = tab xs ys j i := by
  set n := xs.size
  have key : ∀ t ≤ n - j, ((List.range t).foldl (innerStep xs j) a).size = n ∧
      ∀ i < n, ((List.range t).foldl (innerStep xs j) a)[i]! =
        if n - t ≤ i then tab xs ys j i else tab xs ys (j - 1) i := by
    intro t
    induction t with
    | zero => intro _; exact ⟨ha, fun i hi => by simp [show ¬ n ≤ i by omega, hE i hi]⟩
    | succ t ih =>
      intro ht
      obtain ⟨hs, hg⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set b := (List.range t).foldl (innerStep xs j) a
      refine ⟨by rw [innerStep, size_set!, hs], fun i hi => ?_⟩
      rw [innerStep, getElem!_set!, hs]
      have hb0 := hg (n - 1 - t) (by omega)
      have hb1 := hg (n - 1 - t - 1) (by omega)
      rw [ite_eq_right (show ¬ n - t ≤ n - 1 - t by omega)] at hb0
      rw [ite_eq_right (show ¬ n - t ≤ n - 1 - t - 1 by omega)] at hb1
      by_cases hie : n - 1 - t = i
      · subst hie
        rw [ite_eq_left ⟨rfl, hi⟩, ite_eq_left (by omega), hb0, hb1]
        exact tab_succ xs ys hj (by omega)
      · rw [ite_eq_right (fun h => hie h.1), hg i hi]
        by_cases h1 : n - t ≤ i
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
  obtain ⟨hs, hg⟩ := key (n - j) le_rfl
  refine ⟨hs, fun i hi => ?_⟩
  show ((List.range (n - j)).foldl (innerStep xs j) a)[i]! = _
  rw [hg i hi]
  split_ifs with h
  · rfl
  · exact tab_below xs ys (by omega)

/-- **The table**: `phase1` ends with the divided differences `D(0, i)`. -/
lemma phase1_spec (hn : 0 < xs.size) (hys : ys.size = xs.size) :
    (phase1 xs ys).size = xs.size ∧
      ∀ i < xs.size, (phase1 xs ys)[i]! = dd (fun i => xs[i]!) (fun i => ys[i]!) 0 i := by
  have key : ∀ m ≤ xs.size - 1, ((List.range' 1 m).foldl (round xs) ys).size = xs.size ∧
      ∀ i < xs.size, ((List.range' 1 m).foldl (round xs) ys)[i]! = tab xs ys m i := by
    intro m
    induction m with
    | zero => intro _; exact ⟨hys, fun i _ => (tab_zero xs ys i).symm⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hg⟩ := ih (by omega)
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.add_comm 1 m]
      exact round_spec xs ys (j := m + 1) (by omega) (by omega) _ hs fun i hi => by
        rw [hg i hi, Nat.add_sub_cancel]
  obtain ⟨hs, hg⟩ := key (xs.size - 1) le_rfl
  refine ⟨hs, fun i hi => ?_⟩
  rw [phase1, hg i hi, tab]
  split_ifs with h
  · rw [show i - (xs.size - 1) = 0 by omega, show xs.size - 1 = i by omega]
  · rfl

end Table

/-! ### Horner's rule -/

lemma getElem!_ge (a : Array GF128) {k : ℕ} (hk : a.size ≤ k) : a[k]! = 0 := by
  rw [getElem!_neg a k (by omega)]; rfl

lemma polyOf_coeff (a : Array GF128) (k : ℕ) : (polyOf a).coeff k = a[k]! := by
  rw [polyOf, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq (range a.size) k]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_pos a k (mem_range.1 h)]
    simp [Array.getElem?_eq_getElem (mem_range.1 h)]
  · rw [getElem!_ge a (by simpa using h)]

lemma coeff_mul_X' (p : GF128[X]) (k : ℕ) :
    (p * X).coeff k = if k = 0 then 0 else p.coeff (k - 1) := by
  rcases k with _ | k
  · simp
  · simp [coeff_mul_X]

lemma mulLinear_size (a : Array GF128) (c : GF128) :
    (Prover.mulLinear a c).size = a.size + 1 := by simp [Prover.mulLinear]

lemma polyOf_mulLinear (a : Array GF128) (c : GF128) :
    polyOf (Prover.mulLinear a c) = polyOf a * (X + C c) := by
  ext k
  rw [polyOf_coeff, mul_add, coeff_add, coeff_mul_C, coeff_mul_X', polyOf_coeff, polyOf_coeff]
  by_cases hk : k < a.size + 1
  · rw [Prover.mulLinear, getElem!_range_map _ _ hk]
    by_cases h1 : k < a.size
    · by_cases h0 : k = 0
      · subst h0; simp [h1]
      · simp only [h1, ↓reduceIte, h0, Nat.pos_of_ne_zero h0]
        ring
    · rw [getElem!_ge a (show a.size ≤ k by omega)]
      by_cases h0 : k = 0
      · subst h0; simp
      · simp only [h1, ↓reduceIte, h0, Nat.pos_of_ne_zero h0]
        ring
  · rw [getElem!_ge _ (by rw [mulLinear_size]; omega), getElem!_ge a (show a.size ≤ k by omega),
      getElem!_ge a (show a.size ≤ k - 1 by omega)]
    simp

lemma polyOf_set_zero (a : Array GF128) (v : GF128) (ha : 0 < a.size) :
    polyOf (a.set! 0 (a[0]! + v)) = polyOf a + C v := by
  ext k
  rw [polyOf_coeff, coeff_add, polyOf_coeff, getElem!_set!, coeff_C]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ha]
  · simp [show k ≠ 0 by omega, show (0 : ℕ) ≠ k by omega]

lemma X_sub_C_eq (c : GF128) : (X - C c : GF128[X]) = X + C c := by
  rw [sub_eq_add_neg, ← C_neg, CharTwo.neg_eq]

/-- **Horner's rule builds the Newton form** with coefficients `D[i]`. -/
lemma phase2_spec (xs D : Array GF128) (hn : 0 < xs.size) :
    (phase2 xs D).size = xs.size ∧
      polyOf (phase2 xs D) = ∑ t ∈ range xs.size, C D[t]! * omega (fun i => xs[i]!) 0 t := by
  set n := xs.size
  set x : ℕ → GF128 := fun i => xs[i]!
  have key : ∀ u ≤ n - 1, ((List.range' 1 u).foldl (hornerStep xs D) #[D[n - 1]!]).size = u + 1 ∧
      polyOf ((List.range' 1 u).foldl (hornerStep xs D) #[D[n - 1]!]) =
        ∑ t ∈ range (u + 1), C D[n - 1 - u + t]! * omega x (n - 1 - u) t := by
    intro u
    induction u with
    | zero =>
      intro _
      refine ⟨rfl, ?_⟩
      ext k
      simp only [List.range'_zero, List.foldl_nil, polyOf_coeff, zero_add, range_one, sum_singleton,
        omega, range_zero, prod_empty, mul_one, coeff_C, Nat.sub_zero, add_zero]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rfl
      · rw [getElem!_ge _ (by simp; omega)]
        simp [show k ≠ 0 by omega]
    | succ u ih =>
      intro hu
      obtain ⟨hs, hp⟩ := ih (by omega)
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set p := (List.range' 1 u).foldl (hornerStep xs D) #[D[n - 1]!]
      have hi : n - 1 - (1 + u) = n - 1 - (u + 1) := by omega
      refine ⟨by rw [hornerStep, size_set!, mulLinear_size, hs], ?_⟩
      rw [hornerStep, polyOf_set_zero _ _ (by rw [mulLinear_size]; omega), polyOf_mulLinear, hp,
        hi]
      conv_rhs => rw [sum_range_succ']
      rw [omega_zero, add_zero, mul_one, add_left_inj, sum_mul]
      refine sum_congr rfl fun t _ => ?_
      rw [show n - 1 - (u + 1) + (t + 1) = n - 1 - u + t by omega, omega_succ', X_sub_C_eq,
        show n - 1 - (u + 1) + 1 = n - 1 - u by omega]
      simp only [x]
      ring
  obtain ⟨hs, hp⟩ := key (n - 1) le_rfl
  refine ⟨by rw [phase2, hs]; omega, ?_⟩
  rw [phase2, hp, Nat.sub_add_cancel hn, Nat.sub_self]
  simp only [zero_add]

/-! ## Correctness -/

/-- **Newton interpolation is correct**: for distinct points, the coefficients `interpolate`
returns are those of the Newton form, which interpolates the data. -/
theorem interpolate_correct (xs ys : Array GF128) (hn : 0 < xs.size) (hys : ys.size = xs.size) :
    (Prover.interpolate xs ys).size = xs.size ∧
      polyOf (Prover.interpolate xs ys) =
        newton (fun i => xs[i]!) (fun i => ys[i]!) 0 (xs.size - 1) := by
  obtain ⟨h1s, h1⟩ := phase1_spec xs ys hn hys
  obtain ⟨h2s, h2⟩ := phase2_spec xs (phase1 xs ys) hn
  refine ⟨by rw [interpolate_eq, h2s], ?_⟩
  rw [interpolate_eq, h2, newton, Nat.sub_add_cancel hn]
  refine sum_congr rfl fun t ht => ?_
  rw [h1 t (mem_range.1 ht)]

/-- **`InterpOk d`** for `d + 1 < 2⁶⁴`. -/
theorem interpOk (d : ℕ) (hd : d + 1 < 2 ^ 64) : InterpOk d := by
  intro P hP
  set xs := samplePts d
  set ys := xs.map P.eval
  have hxs : xs.size = d + 1 := by simp [xs, samplePts]
  have hys : ys.size = xs.size := by simp [ys]
  obtain ⟨hs, hpoly⟩ := interpolate_correct xs ys (by omega) hys
  have hx : ∀ i, i < d + 1 → xs[i]! = Prover.samplePt i := fun i hi => by
    simp only [xs, samplePts]; exact getElem!_range_map _ _ hi
  have hy : ∀ i, i < d + 1 → ys[i]! = P.eval (Prover.samplePt i) := fun i hi => by
    simp only [ys, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    rw [Array.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [← getElem!_pos xs i (by omega), hx i hi]
  -- The Newton form is `P`.
  have hN : newton (fun i => xs[i]!) (fun i => ys[i]!) 0 d = P := by
    have hinj : Function.Injective fun i : Fin (d + 1) => xs[(i : ℕ)]! := by
      intro i j h
      simp only [hx i i.isLt, hx j j.isLt] at h
      exact Fin.ext (samplePt_injOn (d + 1) hd (by simp; omega) (by simp; omega) h)
    refine eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun i => ?_) ?_
    · have hinj' : ∀ i j, i ≤ d → j ≤ d → xs[0 + i]! = xs[0 + j]! → i = j := by
        intro i j hi hj h
        have := hinj (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) (by simpa using h)
        exact congrArg Fin.val this
      have := newton_interp (fun i => xs[i]!) (fun i => ys[i]!) d 0 hinj' i (by omega)
      simp only [zero_add] at this
      rw [this, hy i i.isLt, hx i i.isLt]
    · rw [Fintype.card_fin]
      exact lt_of_le_of_lt (max_le (newton_deg _ _ 0 d).1 hP) (Nat.lt_succ_self d)
  rw [hxs, Nat.add_sub_cancel, hN] at hpoly
  apply Array.ext
  · rw [hs, hxs]; simp
  intro k h1 h2
  rw [← getElem!_pos _ k h1, ← polyOf_coeff, hpoly]
  simp [Array.getElem_map, Array.getElem_range]

theorem interpOk_two : InterpOk 2 := interpOk 2 (by norm_num)

theorem interpOk_nine : InterpOk 9 := interpOk 9 (by norm_num)

end VoleMole.ZK.Interp
