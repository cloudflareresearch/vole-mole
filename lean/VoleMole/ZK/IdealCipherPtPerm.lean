import VoleMole.ZK.IdealCipherPt
import VoleMole.ZK.IdealCipherPerm

/-!
# Puncturing a GGM tree at points with permutation rows, charged at points and at values

`IC.puncturePt_real` (`ZK/IdealCipherPt.lean`) charges a distinguisher of a GGM tree with
**function** rows only for the keys it reads at the points `P` where the tree reads its secret
rows. With **permutation** rows that charge is false (`inv_point_charge_fails`,
`ZK/InvPoint.lean`): an inverse query at a value the tree reveals is a guess of the secret key at
every key, yet it reads no point of `P` except under the secret key. Here is the hop that holds.

**The read model.** The table is `π : K → Equiv.Perm K`. A reader reads it at **forward points**
`(k, z)` (its value `π k z`); an inverse query `(k, y)` is the forward point `(k, π_k⁻¹ y)`
(`qInv_cons`). The charge of a set of reads `Q`, given a set `V` of values, is

    chV P V Q π = #{k | ∃ (k, z) ∈ Q, z ∈ P ∨ π k z ∈ V}          (`vkeys`),

the keys read at an input in `P` **or at a value in `V`**. For the tree, `V` is the set of the
values of the secret rows at their read points (`valsP`).

**The hop** (`hopPtPm`). Node `n`'s row is read by the tree at a finite set `Pn n` (its children's
inputs, and whatever the output reads). Its replacement is a uniform **function** `u` on `Pn n`
(the real rows elsewhere), as in `IC.hopPt`. Programming the table: the row `σ = π v` at the node's
value `v` becomes `σ' = progL (σ, u)`, the composition of the swaps `swap (σ p) (u p)` over
`p ∈ Pn n` (`stepPm`, an involution of `Perm K × (K → K)`, so programming is perfect,
`pr_progPm_eq`). If `u` has no collision on `Pn n`, `σ'` agrees with `u` there (`progL_on`), and
`σ'` agrees with `σ` at every input `z ∉ Pn n` with `σ z ∉ u(Pn n)` (`progL_off`). So the two
experiments differ only if

* another node has the value `v`, or the distinguisher reads `v` at an input in `Pn n` or at a
  value in `u(Pn n)` (`v` is uniform and independent of these, `pr_secretPm_mem_candsV`), or
* `u` has a collision on `Pn n` (`≤ C(|Pn n|, 2)/|K|`, `pr_not_injOn_le`).

The value condition is what an inverse query needs: `σ'⁻¹(u p) = p`, while `σ⁻¹(u p)` is
random.

* `hopPtPm`: `|before − after| ≤ (N + E_after[chV])/|K| + C(|Pn n|, 2)/|K|`.
* `puncturePtPm`: the hybrid over the secret nodes.
* **`puncturePtPm_real`**: the charges moved to the real experiment, for a consistent reader that
  reads at most `qm` charged keys (`s` secret nodes below `N`):

      |real − fully replaced| ≤ (s·(N + E_real[chV]) + Σ_m C(|Pn m|, 2)) / (|K| − s·qm),

  `E_real[chV]` charged at the real tree's values `valsP` (the secret rows at their read points:
  the secret nodes' children's keys and everything the output reads of them). The fully replaced
  experiment reads uniform **function** rows at the secret nodes (`experQ`), so the last step of
  the function-row proof applies for every permutation table.

The extension of the output by the values (`A` sees `valsP` as well) is what moves the charge:
the values are equal in the coupled experiments, so the hybrid bounds hold for events of them.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-! ## Programming a permutation at a list of points -/

section Prog

variable {K : Type} [DecidableEq K]

/-- **One programming step at `p`**: the permutation takes the answer's value at `p`, and the
answer takes the permutation's old value (an involution). -/
def stepPm (p : K) : Equiv.Perm K × (K → K) ≃ Equiv.Perm K × (K → K) where
  toFun a := (Equiv.swap (a.1 p) (a.2 p) * a.1, Function.update a.2 p (a.1 p))
  invFun a := (Equiv.swap (a.1 p) (a.2 p) * a.1, Function.update a.2 p (a.1 p))
  left_inv a := by
    obtain ⟨σ, u⟩ := a
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Function.update_self, Function.update_idem, Function.update_eq_self, Prod.mk.injEq, and_true]
    rw [Equiv.swap_comm, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  right_inv a := by
    obtain ⟨σ, u⟩ := a
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Function.update_self, Function.update_idem, Function.update_eq_self, Prod.mk.injEq, and_true]
    rw [Equiv.swap_comm, ← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- **Programming at the points of `l`**, in order. -/
def progL (l : List K) : Equiv.Perm K × (K → K) ≃ Equiv.Perm K × (K → K) :=
  l.foldr (fun p e => (stepPm p).trans e) (Equiv.refl _)

lemma progL_cons (p : K) (l : List K) (a : Equiv.Perm K × (K → K)) :
    progL (p :: l) a = progL l (stepPm p a) := rfl

/-- **Off the points and off their answers' values, the permutation is unchanged.** -/
theorem progL_off (l : List K) (σ : Equiv.Perm K) (u : K → K) (z : K) (hz : z ∉ l)
    (hv : σ z ∉ l.map u) : (progL l (σ, u)).1 z = σ z := by
  induction l generalizing σ u with
  | nil => rfl
  | cons q l ih =>
    rw [progL_cons]
    simp only [List.mem_cons, not_or, List.map_cons] at hz hv
    have hzq : σ z ≠ σ q := fun e => hz.1 (σ.injective e)
    have h1 : (Equiv.swap (σ q) (u q) * σ) z = σ z := by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      exact Equiv.swap_apply_of_ne_of_ne hzq hv.1
    show (progL l (Equiv.swap (σ q) (u q) * σ, Function.update u q (σ q))).1 z = σ z
    rw [ih _ _ hz.2 ?_, h1]
    rw [h1]
    intro hm
    obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
    by_cases hrq : r = q
    · subst hrq
      rw [Function.update_self] at e
      exact hzq e.symm
    · rw [Function.update_of_ne hrq] at e
      exact hv.2 (List.mem_map.2 ⟨r, hr, e⟩)

/-- **On the points, the permutation takes the answers' values**, if they are distinct. -/
theorem progL_on (l : List K) (hl : l.Nodup) (σ : Equiv.Perm K) (u : K → K)
    (hu : ∀ p ∈ l, ∀ q ∈ l, u p = u q → p = q) : ∀ p ∈ l, (progL l (σ, u)).1 p = u p := by
  induction l generalizing σ u with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons q l ih =>
    intro p hp
    rw [progL_cons]
    have hq : q ∉ l := (List.nodup_cons.1 hl).1
    have hu1 : ∀ r ∈ l, Function.update u q (σ q) r = u r := fun r hr =>
      Function.update_of_ne (fun e => hq (by rw [← e]; exact hr)) _ _
    rcases List.mem_cons.1 hp with rfl | hp
    · show (progL l (Equiv.swap (σ p) (u p) * σ, Function.update u p (σ p))).1 p = u p
      have h1 : (Equiv.swap (σ p) (u p) * σ) p = u p := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
      rw [progL_off l _ _ p hq ?_, h1]
      rw [h1]
      intro hm
      obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
      rw [hu1 r hr] at e
      have hrp : r = p := hu r (List.mem_cons_of_mem _ hr) p List.mem_cons_self e
      exact hq (hrp ▸ hr)
    · show (progL l (Equiv.swap (σ q) (u q) * σ, Function.update u q (σ q))).1 p = u p
      rw [ih (List.nodup_cons.1 hl).2 _ _ (fun r hr r' hr' e => by
        rw [hu1 r hr, hu1 r' hr'] at e
        exact hu r (List.mem_cons_of_mem _ hr) r' (List.mem_cons_of_mem _ hr') e) p hp, hu1 p hp]

variable [Fintype K]

/-- **The table `π` with the row at `v` programmed on the points `S` with the answer `u`.** -/
noncomputable def progPm (S : Finset K) (v : K) (u : K → K) (π : K → Equiv.Perm K) : K → Equiv.Perm K :=
  Function.update π v (progL S.toList (π v, u)).1

lemma progPm_ne (S : Finset K) {v k : K} (h : k ≠ v) (u : K → K) (π : K → Equiv.Perm K) :
    progPm S v u π k = π k := Function.update_of_ne h _ _

lemma progPm_self (S : Finset K) (v : K) (u : K → K) (π : K → Equiv.Perm K) :
    progPm S v u π v = (progL S.toList (π v, u)).1 := Function.update_self _ _ _

/-- The programmed row on the points: the answer, if it has no collision there. -/
lemma progPm_on (S : Finset K) (v : K) (u : K → K) (π : K → Equiv.Perm K) (hu : InjOnF u S)
    {z : K} (hz : z ∈ S) : progPm S v u π v z = u z := by
  rw [progPm_self]
  exact progL_on S.toList (nodup_toList S) _ u (fun p hp q hq e =>
    hu p (mem_toList.1 hp) q (mem_toList.1 hq) e) z (mem_toList.2 hz)

/-- The programmed row off the points and off the answer's values: the old row. -/
lemma progPm_off (S : Finset K) (v : K) (u : K → K) (π : K → Equiv.Perm K) {z : K} (hz : z ∉ S)
    (hv : π v z ∉ S.image u) : progPm S v u π v z = π v z := by
  rw [progPm_self]
  refine progL_off S.toList _ u z (fun h => hz (mem_toList.1 h)) fun h => hv ?_
  obtain ⟨r, hr, e⟩ := List.mem_map.1 h
  exact mem_image.2 ⟨r, mem_toList.1 hr, e⟩

/-- The programming as a bijection of the table and the answer. -/
noncomputable def progPmEquiv (S : Finset K) (v : K) :
    (K → Equiv.Perm K) × (Unit → K → K) ≃ (K → Equiv.Perm K) × (Unit → K → K) where
  toFun q := (Function.update q.1 v (progL S.toList (q.1 v, q.2 ())).1,
    fun _ => (progL S.toList (q.1 v, q.2 ())).2)
  invFun q := (Function.update q.1 v ((progL S.toList).symm (q.1 v, q.2 ())).1,
    fun _ => ((progL S.toList).symm (q.1 v, q.2 ())).2)
  left_inv q := by
    obtain ⟨π, u⟩ := q
    simp only [Function.update_self, Prod.mk.eta, Equiv.symm_apply_apply, Function.update_idem,
      Function.update_eq_self]
  right_inv q := by
    obtain ⟨π, u⟩ := q
    simp only [Function.update_self, Prod.mk.eta, Equiv.apply_symm_apply, Function.update_idem,
      Function.update_eq_self]

/-- **Programming a uniform permutation table at `v` on `S` with a uniform answer is perfect.** -/
theorem pr_progPm_eq [Nonempty K] {C : Type} [Fintype C] (S : Finset K) (v : C → K)
    (A : C → (K → Equiv.Perm K) → Prop) :
    pr (C × (K → Equiv.Perm K)) (fun p => A p.1 p.2) =
      pr (C × ((K → Equiv.Perm K) × (Unit → K → K)))
        (fun p => A p.1 (progPm S (v p.1) (p.2.2 ()) p.2.1)) := by
  rw [pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pr_prod_fst (β := Unit → K → K) (fun g => A c g)]
  exact (pr_equiv (progPmEquiv S (v c)) (fun q => A c q.1)).symm

end Prog

/-! ## A coordinate through a lens -/

section Lens

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

/-- **An event of a coordinate**: if `set` replaces the coordinate `f`, an event of `f` has the
probability of the event under the uniform law. -/
theorem pr_lens (f : α → β) (set : α → β → α) (hf : ∀ a b, f (set a b) = b)
    (hss : ∀ a b b', set (set a b) b' = set a b') (hsf : ∀ a, set a (f a) = a) (Q : β → Prop) :
    pr α (fun a => Q (f a)) = pr β Q := by
  classical
  obtain ⟨b0⟩ := (inferInstance : Nonempty β)
  obtain ⟨a0⟩ := (inferInstance : Nonempty α)
  let γ := {a : α // set a b0 = a}
  have : Nonempty γ := ⟨⟨set a0 b0, hss _ _ _⟩⟩
  let e : α ≃ β × γ :=
    { toFun := fun a => (f a, ⟨set a b0, hss _ _ _⟩)
      invFun := fun p => set p.2.1 p.1
      left_inv := fun a => by simp only [hss, hsf]
      right_inv := fun p => by
        obtain ⟨k, b, hb⟩ := p
        simp only [hf, Prod.mk.injEq, true_and]
        exact Subtype.ext (by simp only [hss]; exact hb) }
  rw [← pr_prod_fst (β := γ) Q, ← pr_equiv e]
  rfl

end Lens

/-! ## The experiment with permutation rows replaced at points -/

section HopQ

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {x : ℕ → K} {N : ℕ} {O : Type}
  {P : K → Prop} [DecidablePred P]

variable (N) in
/-- **The values of the secret rows at their read points.** -/
def valsP (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K) (ρ : ℕ → K → K) : Finset K :=
  ((range N).filter sec).biUnion fun m => (Pn m).image (ρ m)

variable (P) in
/-- **The keys charged**: read at an input in `P` or at a value in `V`. -/
def vkeys (V : Finset K) (S : Finset (K × K)) (π : K → Equiv.Perm K) : Finset K :=
  (S.filter fun kz => P kz.2 ∨ π kz.1 kz.2 ∈ V).image Prod.fst

lemma vkeys_mono {V V' : Finset K} (h : V ⊆ V') (S : Finset (K × K)) (π : K → Equiv.Perm K) :
    vkeys P V S π ⊆ vkeys P V' S π := by
  intro k hk
  simp only [vkeys, mem_image, mem_filter] at hk ⊢
  obtain ⟨kz, ⟨hm, hc⟩, e⟩ := hk
  exact ⟨kz, ⟨hm, hc.imp_right fun h' => h h'⟩, e⟩

/-- The charge of a consistent reader depends on the table only at its reads. -/
lemma vkeys_congr {Q : Finset (K × K)} {π π' : K → Equiv.Perm K} (V : Finset K)
    (h : ∀ kz ∈ Q, π kz.1 kz.2 = π' kz.1 kz.2) : vkeys P V Q π = vkeys P V Q π' := by
  unfold vkeys
  congr 1
  exact Finset.filter_congr fun kz hkz => by rw [h kz hkz]

variable (x N P) in
/-- **The experiment** with the secret nodes `rep` replaced on `P` by uniform function rows, the
table a uniform permutation per key; `A` sees `Φ` of the rows, the values of the secret rows at
their read points, and the table. -/
noncomputable def experQ (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (rep : Finset ℕ) (Φ : (ℕ → K → K) → O) (A : O → Finset K → (K → Equiv.Perm K) → Prop) : ℝ :=
  pr (Coins K K N × (K → Equiv.Perm K)) (fun p =>
    A (Φ (rowAtP x N P rep (cf p.2) p.1.2 p.1.1))
      (valsP N sec Pn (rowAtP x N P rep (cf p.2) p.1.2 p.1.1)) p.2)

/-- Node `n`'s row taken from the answer, and the old one moved to the answer (an involution). -/
def swapRowQ {n : ℕ} (hN : n < N) :
    Coins K K N × ((K → Equiv.Perm K) × (Unit → K → K)) ≃
      Coins K K N × ((K → Equiv.Perm K) × (Unit → K → K)) where
  toFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  invFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  left_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

omit [DecidableEq K] [Nonempty K] in
/-- An unread answer does not change a probability. -/
lemma pr_drop_ans {C T U : Type} [Fintype C] [Fintype T] [Fintype U] [Nonempty U]
    (F : C × T → Prop) : pr (C × (T × U)) (fun p => F (p.1, p.2.1)) = pr (C × T) F := by
  let e : (C × T) × U ≃ C × (T × U) := Equiv.prodAssoc C T U
  rw [← pr_equiv e]
  exact pr_prod_fst (β := U) F

/-! ### The rows under a table programmed at the secret value -/

/-- **Identical until the secret value is read**: with the table `G` equal to `E` off the secret
value `v` of node `n`, and equal to the answer `u` at `v` on the node's points `S` (which contain
its children's inputs), the experiment with `rep` under `G` has the rows of the experiment with `n`
also replaced by `u` under `E`, except node `n`'s row off `S`, unless another node below `N` has
the value `v`. -/
lemma rowAtP_progG {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (hPx : ∀ m, P (x m)) (S : Finset K)
    (hSP : ∀ z ∈ S, P z) (hch : ∀ c, c ≠ 0 → (c - 1) / 2 = n → x c ∈ S) (E G : K → K → K)
    (c : Coins K K N) (u : K → K)
    (hGE : ∀ k, k ≠ secretVal (x := x) n hN c → G k = E k)
    (hGv : ∀ z ∈ S, G (secretVal (x := x) n hN c) z = u z)
    (hgood : ∀ m < N, m ≠ n →
      keyAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m ≠
        secretVal (x := x) n hN c) :
    ∀ m < N, (m ≠ n → rowAtP x N P rep G c.2 c.1 m =
        rowAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m) ∧
      keyAtP x N P rep G c.2 c.1 m =
        keyAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m ∧
      (m = n → ∀ z ∈ S, rowAtP x N P rep G c.2 c.1 m z =
        rowAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m z) := by
  set v := secretVal (x := x) n hN c
  set R' := Function.update c.2 ⟨n, hN⟩ u
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hkey : keyAtP x N P rep G c.2 c.1 m = keyAtP x N P (insert n rep) E R' c.1 m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      · rw [keyAtP_pos (by omega), keyAtP_pos (by omega)]
        have ihp := ih ((m - 1) / 2) (by omega) (by omega)
        by_cases hq : (m - 1) / 2 = n
        · exact ihp.2.2 hq _ (hch m (by omega) hq)
        · rw [ihp.1 hq]
    have hv : keyAtP x N P (insert n rep) E R' c.1 n = v := by
      have h := keyAtP_secret (P := P) (rep := insert n rep) hN
        (fun h0 => Finset.mem_insert_of_mem (hpar h0)) hPx E (c.1, R')
      rw [h]
      exact secretVal_update hN c u
    refine ⟨fun hmn => ?_, hkey, fun hmn z hz => ?_⟩
    · have hne : keyAtP x N P (insert n rep) E R' c.1 m ≠ v := hgood m hm hmn
      have hG : G (keyAtP x N P (insert n rep) E R' c.1 m) =
          E (keyAtP x N P (insert n rep) E R' c.1 m) := hGE _ hne
      by_cases hmr : m ∈ rep
      · rw [rowAtP_of_mem hmr hm, rowAtP_of_mem (Finset.mem_insert_of_mem hmr) hm, hkey, hG]
        simp only [R']
        rw [Function.update_of_ne (fun h => hmn (congrArg Fin.val h))]
      · have hmi : m ∉ insert n rep := by simp [hmn, hmr]
        rw [rowAtP_of_not_mem hmr, rowAtP_of_not_mem hmi, hkey, hG]
    · subst hmn
      rw [rowAtP_of_not_mem hnr, rowAtP_of_mem (Finset.mem_insert_self _ _) hm, hkey, hv,
        hGv z hz, patchP_of_P (hSP z hz)]
      simp only [R', Function.update_self]

/-! ### The bad event -/

variable (x N P) in
/-- **The candidates for the secret value of node `n`** in the experiment with `ins` replaced: the
values of the other nodes below `N`, and the keys that `A` reads at an input of `Pn n` or at a
value of the node's replacement row on `Pn n`. -/
noncomputable def candsV (Pn : ℕ → Finset K) (ins : Finset ℕ) (n : ℕ) (hN : n < N)
    (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (p : Coins K K N × (K → Equiv.Perm K)) : Finset K :=
  ((range N).filter (· ≠ n)).image (fun m => keyAtP x N P ins (cf p.2) p.1.2 p.1.1 m) ∪
    ((Q (Φ (rowAtP x N P ins (cf p.2) p.1.2 p.1.1)) p.2).filter fun kz =>
      kz.2 ∈ Pn n ∨ p.2 kz.1 kz.2 ∈ (Pn n).image (p.1.2 ⟨n, hN⟩)).image Prod.fst

variable (x N P) in
/-- The read part of the candidates. -/
noncomputable def candsVQ (Pn : ℕ → Finset K) (ins : Finset ℕ) (n : ℕ) (hN : n < N)
    (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (p : Coins K K N × (K → Equiv.Perm K)) : Finset K :=
  ((Q (Φ (rowAtP x N P ins (cf p.2) p.1.2 p.1.1)) p.2).filter fun kz =>
      kz.2 ∈ Pn n ∨ p.2 kz.1 kz.2 ∈ (Pn n).image (p.1.2 ⟨n, hN⟩)).image Prod.fst

lemma candsV_card (Pn : ℕ → Finset K) (ins : Finset ℕ) (n : ℕ) (hN : n < N)
    (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (p : Coins K K N × (K → Equiv.Perm K)) :
    ((candsV x N P Pn ins n hN Φ Q p).card : ℝ) ≤ N + (candsVQ x N P Pn ins n hN Φ Q p).card := by
  have h : (candsV x N P Pn ins n hN Φ Q p).card ≤ N + (candsVQ x N P Pn ins n hN Φ Q p).card := by
    unfold candsV candsVQ
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_image_le.trans ((card_filter_le _ _).trans (card_range N).le)
  exact_mod_cast h

/-- **The read part of the candidates is charged**: its keys are read at an input in `P` or at a
value of the secret rows, if node `n` is secret and replaced. -/
lemma candsVQ_sub (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (hPn : ∀ m, ∀ z ∈ Pn m, P z) {ins : Finset ℕ} {n : ℕ} (hN : n < N) (hn : n ∈ ins)
    (hs : sec n) (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (p : Coins K K N × (K → Equiv.Perm K)) :
    candsVQ x N P Pn ins n hN Φ Q p ⊆ vkeys P (valsP N sec Pn (rowAtP x N P ins (cf p.2) p.1.2 p.1.1))
      (Q (Φ (rowAtP x N P ins (cf p.2) p.1.2 p.1.1)) p.2) p.2 := by
  intro k hk
  simp only [candsVQ, vkeys, mem_image, mem_filter] at hk ⊢
  obtain ⟨kz, ⟨hm, hc⟩, e⟩ := hk
  refine ⟨kz, ⟨hm, ?_⟩, e⟩
  rcases hc with hz | hv
  · exact Or.inl (hPn n _ hz)
  · refine Or.inr ?_
    obtain ⟨z, hz, ez⟩ := hv
    simp only [valsP, mem_biUnion, mem_filter, mem_range, mem_image]
    refine ⟨n, ⟨hN, hs⟩, z, hz, ?_⟩
    rw [rowAtP_of_mem hn hN, patchP_of_P (hPn n z hz), ez]

/-- **The secret value is guessed with probability `≤ (N + E[#candidates read]) / |K|`**, the
expectation in the experiment with `n` replaced. -/
lemma pr_secretPm_mem_candsV (Pn : ℕ → Finset K) {rep : Finset ℕ} {n : ℕ} (hN : n < N)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦn : ∀ ρ r, (∀ z, P z → r z = ρ n z) → Φ (Function.update ρ n r) = Φ ρ)
    (Q : O → (K → Equiv.Perm K) → Finset (K × K)) :
    pr (Coins K K N × (K → Equiv.Perm K)) (fun p => secretVal (x := x) n hN p.1 ∈
      candsV x N P Pn (insert n rep) n hN Φ Q p) ≤
      (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
        ((candsVQ x N P Pn (insert n rep) n hN Φ Q p).card : ℝ))) / Fintype.card K := by
  set ins := insert n rep
  have hin : n ∈ ins := Finset.mem_insert_self _ _
  have hexp : exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
      ((candsV x N P Pn ins n hN Φ Q p).card : ℝ)) / Fintype.card K ≤
      (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
        ((candsVQ x N P Pn ins n hN Φ Q p).card : ℝ))) / Fintype.card K := by
    rw [← exP_const_add]
    exact div_le_div_of_nonneg_right (exP_mono fun p => candsV_card Pn ins n hN Φ Q p)
      (Nat.cast_nonneg _)
  refine le_trans ?_ hexp
  by_cases h0 : n = 0
  · subst h0
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_exp
      (α := Coins K K N × (K → Equiv.Perm K)) (fun p => p.1.1) (fun p k => ((k, p.1.2), p.2))
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (candsV x N P Pn ins 0 hN Φ Q) fun p k => ?_)
    · simp only [secretVal, ↓reduceIte]
    · have hind := rowAtP_seed_indep (x := x) (P := P) hin hN hPx (cf p.2) p.1.2 k p.1.1
      have hrows : rowAtP x N P ins (cf p.2) p.1.2 k = Function.update
          (rowAtP x N P ins (cf p.2) p.1.2 p.1.1) 0 (rowAtP x N P ins (cf p.2) p.1.2 k 0) := by
        funext m
        by_cases hm : m = 0
        · subst hm; rw [Function.update_self]
        · rw [Function.update_of_ne hm, (hind.2 m hm).1]
      unfold candsV
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        exact (hind.2 m (Finset.mem_filter.1 hm).2).2
      · simp only
        rw [hrows, hΦn _ _ fun z hz => hind.1 z hz]
  · have hp : (n - 1) / 2 ∈ ins := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    have hpn : (n - 1) / 2 ≠ n := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    have hpfn : (⟨n, hN⟩ : Fin N) ≠ pf := fun e => hpn (congrArg Fin.val e).symm
    let st : Coins K K N × (K → Equiv.Perm K) → K → Coins K K N × (K → Equiv.Perm K) := fun p k =>
      ((p.1.1, Function.update p.1.2 pf (Function.update (p.1.2 pf) (x n) k)), p.2)
    have hf : ∀ p k, (st p k).1.2 pf (x n) = k := fun p k => by simp [st]
    have hss : ∀ p k k', st (st p k) k' = st p k' := fun p k k' => by simp [st]
    have hsf : ∀ p, st p (p.1.2 pf (x n)) = p := fun p => by simp [st]
    have hT : ∀ p k, candsV x N P Pn ins n hN Φ Q (st p k) = candsV x N P Pn ins n hN Φ Q p := by
      intro p k
      have hind := rowAtP_point_indep (x := x) (P := P) hin hN h0 hp (hsib h0) hPx (cf p.2) p.1.2
        p.1.1 k
      unfold candsV
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        exact (hind m).1 (Finset.mem_filter.1 hm).2
      · simp only [st]
        set ρ := rowAtP x N P ins (cf p.2) p.1.2 p.1.1
        set ρ' := rowAtP x N P ins (cf p.2) (Function.update p.1.2 pf
          (Function.update (p.1.2 pf) (x n) k)) p.1.1
        have hρ : ρ' = Function.update (Function.update ρ ((n - 1) / 2)
            (Function.update (ρ ((n - 1) / 2)) (x n) k)) n (ρ' n) := by
          funext m
          by_cases hmn : m = n
          · subst hmn; rw [Function.update_self]
          · rw [Function.update_of_ne hmn]
            by_cases hm : m = (n - 1) / 2
            · subst hm; rw [Function.update_self]; exact (hind _).2.2.1 rfl
            · rw [Function.update_of_ne hm]; exact (hind m).2.1 hm hmn
        rw [hρ, hΦn _ _ fun z hz => by
          rw [Function.update_of_ne hpn.symm]; exact (hind n).2.2.2 rfl z hz, hΦ h0,
          Function.update_of_ne hpfn]
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_exp
      (α := Coins K K N × (K → Equiv.Perm K)) (fun p => p.1.2 pf (x n)) st hf hss hsf
      (candsV x N P Pn ins n hN Φ Q) hT)
    simp only [secretVal, h0, ↓reduceIte]
    rfl

/-- A collision of the replacement row of node `i` on a set. -/
lemma pr_coll_le (S : Finset K) (i : Fin N) :
    pr (Coins K K N × (K → Equiv.Perm K)) (fun p => ¬ InjOnF (p.1.2 i) S) ≤
      (S.card.choose 2 : ℕ) / Fintype.card K := by
  rw [pr_lens (fun p : Coins K K N × (K → Equiv.Perm K) => p.1.2 i)
    (fun p r => ((p.1.1, Function.update p.1.2 i r), p.2)) (fun _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ => by simp) (fun a => ¬ InjOnF a S)]
  exact pr_not_injOn_le S

/-! ### One hop -/

/-- **One hop with permutation rows at points**: replacing node `n` (its parent replaced, or the
root) on `Pn n` by a uniform function costs

    (N + E[#keys read at an input in `Pn n` or at a value of the new row on `Pn n`]) / |K|
      + C(|Pn n|, 2) / |K|,

the expectation in the experiment after the hop. `Pn n` contains the inputs of `n`'s children
(`hch`) and every point at which `Φ` reads the secret rows (`hΦP`); `A` may also read the values of
the secret rows at their points. -/
theorem hopPtPm (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K) (rep : Finset ℕ)
    (n : ℕ) (hN : n < N) (hnr : n ∉ rep) (hsn : sec n)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (hPn : ∀ m, ∀ z ∈ Pn m, P z)
    (hch : ∀ c, c ≠ 0 → x c ∈ Pn ((c - 1) / 2)) (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z ∈ Pn m, ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → Finset K → (K → Equiv.Perm K) → Prop)
    (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (hQ : ∀ o V G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o V G ↔ A o V G')) :
    |experQ x N P sec Pn rep Φ A - experQ x N P sec Pn (insert n rep) Φ A| ≤
      (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
        ((candsVQ x N P Pn (insert n rep) n hN Φ Q p).card : ℝ))) / Fintype.card K +
        ((Pn n).card.choose 2 : ℕ) / Fintype.card K := by
  classical
  let v : Coins K K N → K := secretVal (x := x) n hN
  let ins := insert n rep
  let T := K → Equiv.Perm K
  have hΦn : ∀ ρ r, (∀ z, P z → r z = ρ n z) → Φ (Function.update ρ n r) = Φ ρ := fun ρ r hr =>
    hΦP _ _ (fun m _ _ z hz => by
      by_cases hmn : m = n
      · subst hmn; rw [Function.update_self, hr z (hPn m z hz)]
      · rw [Function.update_of_ne hmn]) fun m _ hs => by
      by_cases hmn : m = n
      · subst hmn; exact absurd hsn hs
      · rw [Function.update_of_ne hmn]
  -- programming is perfect
  have h1 : experQ x N P sec Pn rep Φ A =
      pr (Coins K K N × (T × (Unit → K → K))) (fun p =>
        A (Φ (rowAtP x N P rep (cf (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1)) p.1.2 p.1.1))
          (valsP N sec Pn (rowAtP x N P rep (cf (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1))
            p.1.2 p.1.1)) (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1)) :=
    pr_progPm_eq (Pn n) v (fun c g => A (Φ (rowAtP x N P rep (cf g) c.2 c.1))
      (valsP N sec Pn (rowAtP x N P rep (cf g) c.2 c.1)) g)
  -- the experiment with `n` replaced by the answer
  let B : Coins K K N × (T × (Unit → K → K)) → Prop := fun p =>
    A (Φ (rowAtP x N P ins (cf p.2.1) (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1))
      (valsP N sec Pn (rowAtP x N P ins (cf p.2.1) (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1))
      p.2.1
  have h2 : pr _ B = experQ x N P sec Pn ins Φ A := by
    have e := pr_equiv (swapRowQ (K := K) hN)
      (fun p => A (Φ (rowAtP x N P ins (cf p.2.1) p.1.2 p.1.1))
        (valsP N sec Pn (rowAtP x N P ins (cf p.2.1) p.1.2 p.1.1)) p.2.1)
    rw [pr_drop_ans (fun p : Coins K K N × T => A (Φ (rowAtP x N P ins (cf p.2) p.1.2 p.1.1))
      (valsP N sec Pn (rowAtP x N P ins (cf p.2) p.1.2 p.1.1)) p.2)] at e
    exact e
  -- the bad event
  let bad : Coins K K N × (T × (Unit → K → K)) → Prop := fun p =>
    v p.1 ∈ candsV x N P Pn ins n hN Φ Q ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1) ∨
      ¬ InjOnF (p.2.2 ()) (Pn n)
  have h3 : pr _ bad ≤ (N + exP (Coins K K N × T) (fun p =>
        ((candsVQ x N P Pn ins n hN Φ Q p).card : ℝ))) / Fintype.card K +
        ((Pn n).card.choose 2 : ℕ) / Fintype.card K := by
    let bad0 : Coins K K N × T → Prop := fun p =>
      v p.1 ∈ candsV x N P Pn ins n hN Φ Q p ∨ ¬ InjOnF (p.1.2 ⟨n, hN⟩) (Pn n)
    have e := pr_equiv (swapRowQ (K := K) hN) (fun p => bad0 (p.1, p.2.1))
    rw [pr_drop_ans bad0] at e
    have e2 : pr _ bad = pr (Coins K K N × (T × (Unit → K → K)))
        (fun a => (fun p : Coins K K N × (T × (Unit → K → K)) => bad0 (p.1, p.2.1))
          (swapRowQ hN a)) :=
      pr_congr fun a => by
        show _ ↔ bad0 ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), a.2.1)
        simp only [bad, bad0, Function.update_self]
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from
          secretVal_update hN a.1 _]
    rw [e2, e]
    refine (pr_or_le _ _).trans (add_le_add ?_ (pr_coll_le (Pn n) ⟨n, hN⟩))
    exact pr_secretPm_mem_candsV Pn hN hpar hsib hPx Φ hΦ hΦn Q
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAtP x N P rep (cf (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1))
      p.1.2 p.1.1)) (valsP N sec Pn (rowAtP x N P rep (cf (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1))
            p.1.2 p.1.1)) (progPm (Pn n) (v p.1) (p.2.2 ()) p.2.1)) ↔ B p) := by
    intro p hp
    simp only [bad, not_or, not_not] at hp
    obtain ⟨hc, hinj⟩ := hp
    set u := p.2.2 ()
    set π := p.2.1
    set G := progPm (Pn n) (v p.1) u π
    have hgood : ∀ m < N, m ≠ n → keyAtP x N P ins (cf π)
        (Function.update p.1.2 ⟨n, hN⟩ u) p.1.1 m ≠ secretVal (x := x) n hN p.1 :=
      fun m hm hmn e => hc (by
        unfold candsV
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨m, Finset.mem_filter.2
          ⟨Finset.mem_range.2 hm, hmn⟩, e⟩))
    have hrows := rowAtP_progG (P := P) hN hnr hpar hPx (Pn n) (hPn n)
      (fun c hc0 hcn => hcn ▸ hch c hc0) (cf π) (cf G) p.1 u
      (fun k hk => by simp only [cf, G]; rw [progPm_ne _ hk])
      (fun z hz => by simp only [cf, G]; exact progPm_on _ _ u π hinj hz) hgood
    set ρb := rowAtP x N P rep (cf G) p.1.2 p.1.1
    set ρa := rowAtP x N P ins (cf π) (Function.update p.1.2 ⟨n, hN⟩ u) p.1.1
    have hag : ∀ m < N, sec m → ∀ z ∈ Pn m, ρb m z = ρa m z := fun m hm _ z hz => by
      by_cases hmn : m = n
      · subst hmn; exact (hrows m hm).2.2 rfl z hz
      · rw [(hrows m hm).1 hmn]
    have hΦe : Φ ρb = Φ ρa := hΦP _ _ hag fun m hm hs => (hrows m hm).1 fun e => hs (e ▸ hsn)
    have hVe : valsP N sec Pn ρb = valsP N sec Pn ρa := by
      unfold valsP
      refine Finset.biUnion_congr rfl fun m hm => ?_
      have hm' := Finset.mem_filter.1 hm
      exact Finset.image_congr fun z hz => hag m (Finset.mem_range.1 hm'.1) hm'.2 z hz
    show A (Φ ρb) (valsP N sec Pn ρb) G ↔ A (Φ ρa) (valsP N sec Pn ρa) π
    rw [hΦe, hVe]
    refine (hQ _ _ _ _ fun kz hkz => ?_).symm
    by_cases hk : kz.1 = v p.1
    · have hnot : ¬ (kz.2 ∈ Pn n ∨ π kz.1 kz.2 ∈ (Pn n).image u) := fun h => hc (by
        unfold candsV
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨kz, Finset.mem_filter.2 ⟨?_, ?_⟩, hk⟩)
        · exact hkz
        · simp only [Function.update_self]; exact h)
      push Not at hnot
      rw [hk] at hnot ⊢
      exact (progPm_off (Pn n) (v p.1) u π hnot.1 hnot.2).symm
    · show (π kz.1) kz.2 = (progPm (Pn n) (v p.1) u π kz.1) kz.2
      rw [progPm_ne _ hk]
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-! ## The hybrid over the secret nodes -/

variable (x N P) in
/-- **The charge of the hop for node `j`**: `(N + E[chV])/|K| + C(|Pn j|, 2)/|K|`, the expectation
in the experiment with the secret nodes up to `j` replaced. -/
noncomputable def chgQ (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K)) (j : ℕ) : ℝ :=
  (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
    ((vkeys P (valsP N sec Pn (rowAtP x N P ((range (j + 1)).filter sec) (cf p.2) p.1.2 p.1.1))
      (Q (Φ (rowAtP x N P ((range (j + 1)).filter sec) (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ))) /
    Fintype.card K + ((Pn j).card.choose 2 : ℕ) / Fintype.card K

lemma chgQ_nonneg (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset (K × K)) (j : ℕ) :
    0 ≤ chgQ x N P sec Pn Φ Q j :=
  add_nonneg (div_nonneg (add_nonneg (Nat.cast_nonneg _) (exP_nonneg fun _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- **The hybrid over the secret nodes**: for an upward-closed set `sec` of nodes, replacing the
secret nodes below `j` on their points costs the sum of their hops' charges. -/
theorem puncturePtPm (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (hPn : ∀ m, ∀ z ∈ Pn m, P z)
    (hch : ∀ c, c ≠ 0 → x c ∈ Pn ((c - 1) / 2)) (Φ : (ℕ → K → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z ∈ Pn m, ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → Finset K → (K → Equiv.Perm K) → Prop)
    (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (hQ : ∀ o V G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o V G ↔ A o V G')) :
    ∀ j ≤ N, |experQ x N P sec Pn ∅ Φ A - experQ x N P sec Pn ((range j).filter sec) Φ A| ≤
      ∑ i ∈ (range j).filter sec, chgQ x N P sec Pn Φ Q i := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hs
    · have hnot : j ∉ (range j).filter sec := by simp
      have h := hopPtPm (P := P) sec Pn ((range j).filter sec) j (by omega) hnot hs (fun h0 =>
          Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hup j (by omega) hs h0⟩)
        (hsib j (by omega) hs) hPx hPn hch Φ (hΦ j (by omega) hs) hΦP A Q hQ
      have he : insert j ((range j).filter sec) = (range (j + 1)).filter sec := by
        rw [Finset.range_add_one, Finset.filter_insert]; simp only [hs, ↓reduceIte]
      have hc : (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
          ((candsVQ x N P Pn (insert j ((range j).filter sec)) j (by omega) Φ Q p).card : ℝ))) /
          Fintype.card K + ((Pn j).card.choose 2 : ℕ) / Fintype.card K ≤
          chgQ x N P sec Pn Φ Q j := by
        unfold chgQ
        refine add_le_add (div_le_div_of_nonneg_right (add_le_add le_rfl
          (exP_mono (α := Coins K K N × (K → Equiv.Perm K)) fun p => ?_))
          (Nat.cast_nonneg (α := ℝ) _)) le_rfl
        have := card_le_card (candsVQ_sub (x := x) (P := P) sec Pn hPn (N := N) (by omega)
          (Finset.mem_insert_self j ((range j).filter sec)) hs Φ Q p)
        rw [he] at this ⊢
        exact_mod_cast this
      rw [Finset.sum_insert hnot]
      have := abs_sub_le (experQ x N P sec Pn ∅ Φ A) (experQ x N P sec Pn ((range j).filter sec) Φ A)
        (experQ x N P sec Pn (insert j ((range j).filter sec)) Φ A)
      linarith
    · exact ih

/-- **The hybrid at points with permutation rows, charged in the real experiment.** For a
**consistent** reader `Q` (`hQc`) that reads at most `qm` charged keys (`hqm`), with
`s·qm < |K|` (`s` secret nodes below `N`):

    |real − fully replaced| ≤ (s·(N + E_real[chV]) + Σ_m C(|Pn m|, 2)) / (|K| − s·qm),

`E_real[chV]` the expected number of keys read at an input in `P` or at a value of the real secret
rows at their points (`valsP`), in the real experiment. The fully replaced experiment has uniform
**function** rows at the secret nodes. -/
theorem puncturePtPm_real (sec : ℕ → Prop) [DecidablePred sec] (Pn : ℕ → Finset K)
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (hPn : ∀ m, ∀ z ∈ Pn m, P z)
    (hch : ∀ c, c ≠ 0 → x c ∈ Pn ((c - 1) / 2)) (Φ : (ℕ → K → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z ∈ Pn m, ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → Equiv.Perm K) → Prop) (Q : O → (K → Equiv.Perm K) → Finset (K × K))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G'))
    (hQc : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → Q o G = Q o G')
    {qm : ℕ} (hqm : ∀ o V G, (vkeys P V (Q o G) G).card ≤ qm)
    (hsmall : ((range N).filter sec).card * (qm : ℝ) < Fintype.card K) :
    |pr (Coins K K N × (K → Equiv.Perm K)) (fun p => A (Φ (rowAt x N ∅ (cf p.2) p.1.2 p.1.1)) p.2) -
        pr (Coins K K N × (K → Equiv.Perm K))
          (fun p => A (Φ (rowAt x N ((range N).filter sec) (cf p.2) p.1.2 p.1.1)) p.2)| ≤
      (((range N).filter sec).card * (N + exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
        ((vkeys P (valsP N sec Pn (rowAt x N ∅ (cf p.2) p.1.2 p.1.1))
          (Q (Φ (rowAt x N ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ))) +
        ∑ m ∈ (range N).filter sec, ((Pn m).card.choose 2 : ℕ)) /
        (Fintype.card K - ((range N).filter sec).card * qm) := by
  set secN := (range N).filter sec
  set S := ∑ i ∈ secN, chgQ x N P sec Pn Φ Q i with hSdef
  set E0 := exP (Coins K K N × (K → Equiv.Perm K)) (fun p =>
    ((vkeys P (valsP N sec Pn (rowAt x N ∅ (cf p.2) p.1.2 p.1.1))
      (Q (Φ (rowAt x N ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ))
  set Cs : ℝ := ((∑ m ∈ secN, (Pn m).card.choose 2 : ℕ) : ℝ)
  set s := secN.card
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hpun := puncturePtPm (P := P) sec Pn hup hsib hPx hPn hch Φ hΦ hΦP
  -- the real experiment
  have hreal : ∀ (B : O → Finset K → (K → Equiv.Perm K) → Prop),
      experQ x N P sec Pn ∅ Φ B = pr (Coins K K N × (K → Equiv.Perm K)) (fun p =>
        B (Φ (rowAt x N ∅ (cf p.2) p.1.2 p.1.1)) (valsP N sec Pn (rowAt x N ∅ (cf p.2) p.1.2 p.1.1))
          p.2) := fun B =>
    pr_congr fun p => by rw [rowAtP_empty (P := P) (cf p.2) p.1.2 p.1.2 p.1.1]
  -- the level sets of the charge are read
  let Al : ℕ → O → Finset K → (K → Equiv.Perm K) → Prop := fun l o V G =>
    l < (vkeys P V (Q o G) G).card
  have hAl : ∀ l o V G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (Al l o V G ↔ Al l o V G') :=
    fun l o V G G' h => by
      simp only [Al]
      rw [← hQc o G G' h, vkeys_congr V h]
  -- each hop's charge is within `qm · S` of the real one
  have hE : ∀ i ∈ secN, chgQ x N P sec Pn Φ Q i ≤
      (N + E0 + qm * S) / Fintype.card K + ((Pn i).card.choose 2 : ℕ) / Fintype.card K := by
    intro i hi
    have hiN : i + 1 ≤ N := by have := Finset.mem_range.1 (Finset.mem_filter.1 hi).1; omega
    unfold chgQ
    refine add_le_add (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg (α := ℝ) _)) le_rfl
    have hlevels : ∀ l < qm, |pr (Coins K K N × (K → Equiv.Perm K)) (fun p => l <
          (vkeys P (valsP N sec Pn (rowAtP x N P ((range (i + 1)).filter sec) (cf p.2) p.1.2 p.1.1))
            (Q (Φ (rowAtP x N P ((range (i + 1)).filter sec) (cf p.2) p.1.2 p.1.1)) p.2) p.2).card) -
        pr (Coins K K N × (K → Equiv.Perm K)) (fun p =>
          l < (vkeys P (valsP N sec Pn (rowAt x N ∅ (cf p.2) p.1.2 p.1.1))
            (Q (Φ (rowAt x N ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card)| ≤ S := by
      intro l _
      have h := hpun (Al l) Q (hAl l) (i + 1) hiN
      rw [hreal] at h
      rw [abs_sub_comm]
      refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => chgQ_nonneg _ _ _ _ _)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, secN] at hj ⊢
      exact ⟨by omega, hj.2⟩
    have h := exP_sub_le_of_levels _ _ (fun p => hqm _ _ _) (fun p => hqm _ _ _) hlevels
    have := (le_abs_self _).trans h
    linarith
  have hS : S ≤ s * ((N + E0 + qm * S) / Fintype.card K) + Cs / Fintype.card K := by
    calc S ≤ ∑ i ∈ secN, ((N + E0 + qm * S) / Fintype.card K +
          ((Pn i).card.choose 2 : ℕ) / Fintype.card K) := Finset.sum_le_sum hE
      _ = s * ((N + E0 + qm * S) / Fintype.card K) + Cs / Fintype.card K := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
          simp only [Cs, s, Nat.cast_sum]
  have hden : 0 < (Fintype.card K : ℝ) - s * qm := by linarith
  have hS' : S ≤ (s * (N + E0) + Cs) / (Fintype.card K - s * qm) := by
    rw [le_div_iff₀ hden]
    have h2 : S * Fintype.card K ≤ s * (N + E0 + qm * S) + Cs := by
      have := mul_le_mul_of_nonneg_right hS hK.le
      rw [add_mul, mul_div_assoc', div_mul_cancel₀ _ hK.ne', div_mul_cancel₀ _ hK.ne'] at this
      exact this
    nlinarith
  -- the fully replaced experiment
  have hfin := hpun (fun o _ G => A o G) Q (fun o _ G G' h => hQ o G G' h) N le_rfl
  rw [hreal] at hfin
  have hfull : experQ x N P sec Pn secN Φ (fun o _ G => A o G) =
      pr (Coins K K N × (K → Equiv.Perm K))
        (fun p => A (Φ (rowAt x N secN (cf p.2) p.1.2 p.1.1)) p.2) := by
    refine pr_congr fun p => ?_
    have hag := rowAtP_full_agree (P := P) (x := x) (N := N) sec hPx (cf p.2) p.1.2 p.1.1
    rw [hΦP _ _ (fun m hm hs z hz => (hag m hm).2 hs z (hPn m z hz))
      (fun m hm hs => ((hag m hm).1 hs).1)]
  rw [hfull] at hfin
  exact hfin.trans hS'

end HopQ

end VoleMole.ZK.IC
