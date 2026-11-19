import VoleMole.Privacy.Basic

/-!
# Lazy sampling of an adaptive reader's view

An adversary `S` that reads a random table `t` adaptively (its query set `Q t` and its output
`S t` depend on `t` only through `t` on `Q t`) learns `t` on `Q t` and nothing else: given its
output, the table is uniform off its queries. **`pr_resample`**: for every experiment `F` of the
output and the table,

    Pr_t[F(S t, t)] = Pr_{t, t'}[F(S t, mix (Q t) t t')],

`mix r t t'` the table that is `t` on `r` and `t'` elsewhere. The proof is the involution
`(t, t') ↦ (mix (Q t) t t', mix (Q t) t' t)` of the uniform pair: the first component agrees with
`t` on `Q t`, so it has the same queries and the same output (the consistency of an adaptive
reader).

This is how a statement chosen by a table-reading adversary is fed to a zero-knowledge theorem
for a fixed statement (`ZK/AdaptRO.lean`): with the outer `t` fixed, the statement is fixed, and
the tables are the uniform `t'` patched at the adversary's queries.
-/

namespace VoleMole.Privacy

section Resample

variable {T R C X : Type*} [Fintype T] [Nonempty T] [Fintype C]

/-- **Lazy sampling of an adaptive reader's view.** `mix r a b` is `a` on the read set `r` and `b`
elsewhere (`Ag r a a'`: `a` and `a'` agree on `r`); `S` reads `Q t` consistently (`hS`: a table that
agrees with `t` on `Q t` has the same reads and the same output). Then running `F` on `S`'s output
and the table is running it on `S`'s output and a fresh table patched with `S`'s view. -/
theorem pr_resample (mix : R → T → T → T) (Ag : R → T → T → Prop)
    (hag : ∀ r a b, Ag r a (mix r a b))
    (hinv : ∀ r a b, mix r (mix r a b) (mix r b a) = a)
    (S : T → X) (Q : T → R) (hS : ∀ t t', Ag (Q t) t t' → Q t' = Q t ∧ S t' = S t)
    (F : C → X → T → Prop) :
    pr (C × T) (fun z => F z.1 (S z.2) z.2) =
      pr ((C × T) × T) (fun z => F z.1.1 (S z.1.2) (mix (Q z.1.2) z.1.2 z.2)) := by
  let φ : T × T → T × T := fun ab => (mix (Q ab.1) ab.1 ab.2, mix (Q ab.1) ab.2 ab.1)
  have hφ : ∀ ab, φ (φ ab) = ab := by
    rintro ⟨a, b⟩
    have hQ : Q (mix (Q a) a b) = Q a := (hS a _ (hag _ a b)).1
    simp only [φ, hQ, hinv]
  let e : T × T ≃ T × T := ⟨φ, φ, hφ, hφ⟩
  let E : (C × T) × T ≃ C × (T × T) := Equiv.prodAssoc C T T
  have h1 : pr (C × T) (fun z => F z.1 (S z.2) z.2) =
      pr (C × (T × T)) (fun w => F w.1 (S w.2.1) w.2.1) := by
    rw [← pr_prod_fst (β := T) (fun z : C × T => F z.1 (S z.2) z.2), ← pr_equiv E.symm]
    rfl
  have h2 : pr (C × (T × T)) (fun w => F w.1 (S w.2.1) w.2.1) =
      pr (C × (T × T)) (fun w => F w.1 (S (e w.2).1) (e w.2).1) :=
    (pr_equiv (Equiv.prodCongr (Equiv.refl C) e) (fun w => F w.1 (S w.2.1) w.2.1)).symm
  have h3 : pr (C × (T × T)) (fun w => F w.1 (S (e w.2).1) (e w.2).1) =
      pr (C × (T × T)) (fun w => F w.1 (S w.2.1) (mix (Q w.2.1) w.2.1 w.2.2)) := by
    refine pr_congr fun w => ?_
    show F w.1 (S (mix (Q w.2.1) w.2.1 w.2.2)) (mix (Q w.2.1) w.2.1 w.2.2) ↔ _
    rw [(hS w.2.1 _ (hag _ w.2.1 w.2.2)).2]
  rw [h1, h2, h3, ← pr_equiv E]
  rfl

/-- **A bound for every outer table is a bound** (`pr_resample`, then the outer table fixed). -/
theorem pr_resample_le (mix : R → T → T → T) (Ag : R → T → T → Prop)
    (hag : ∀ r a b, Ag r a (mix r a b))
    (hinv : ∀ r a b, mix r (mix r a b) (mix r b a) = a)
    (S : T → X) (Q : T → R) (hS : ∀ t t', Ag (Q t) t t' → Q t' = Q t ∧ S t' = S t)
    (F : C → X → T → Prop) {ε : ℝ}
    (h : ∀ a, pr (C × T) (fun z => F z.1 (S a) (mix (Q a) a z.2)) ≤ ε) :
    pr (C × T) (fun z => F z.1 (S z.2) z.2) ≤ ε := by
  rw [pr_resample mix Ag hag hinv S Q hS F]
  let e : T × (C × T) ≃ (C × T) × T :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, pr_prod]
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hT]
  calc ∑ a, pr (C × T) (fun b => F (e (a, b)).1.1 (S (e (a, b)).1.2)
        (mix (Q (e (a, b)).1.2) (e (a, b)).1.2 (e (a, b)).2))
      ≤ ∑ _a : T, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card T := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **A closeness bound for every outer table is a bound** (`pr_resample` on both sides). -/
theorem abs_pr_resample_le {C' : Type*} [Fintype C'] (mix : R → T → T → T)
    (Ag : R → T → T → Prop) (hag : ∀ r a b, Ag r a (mix r a b))
    (hinv : ∀ r a b, mix r (mix r a b) (mix r b a) = a)
    (S : T → X) (Q : T → R) (hS : ∀ t t', Ag (Q t) t t' → Q t' = Q t ∧ S t' = S t)
    (F : C → X → T → Prop) (F' : C' → X → T → Prop) {ε : ℝ}
    (h : ∀ a, |pr (C × T) (fun z => F z.1 (S a) (mix (Q a) a z.2)) -
      pr (C' × T) (fun z => F' z.1 (S a) (mix (Q a) a z.2))| ≤ ε) :
    |pr (C × T) (fun z => F z.1 (S z.2) z.2) - pr (C' × T) (fun z => F' z.1 (S z.2) z.2)| ≤ ε := by
  rw [pr_resample mix Ag hag hinv S Q hS F, pr_resample (C := C') mix Ag hag hinv S Q hS F']
  let e : T × (C × T) ≃ (C × T) × T :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' : T × (C' × T) ≃ (C' × T) × T :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, ← pr_equiv e']
  exact abs_pr_prod_sub_le _ _ fun a => h a

end Resample

end VoleMole.Privacy
