import VoleMole.ROM.SimPerm

/-!
# One normalization for two parameter sets (permutation model)

The normalized prover `normP p π P` of `ROM/PermModel.lean` queries `H₄(iv_pre ‖ μ ‖ 4)` before
every `H₂¹` query, with `iv_pre` parsed from the `H₂¹` input at the parameters `p` (`ivIn p`). The
two relations of a protocol have different parameters (issuance and redemption or spend), so
`normP p_I π P` and `normP p_R π P` have different hash logs, and the joint charging of
`ROM/SimJoint.lean`, which needs **one** hash log for both relations' provers, does not apply to
them.

**The joint normalization** (`normJ`): `normP p_I π (addIV p_R P)`, where `addIV p_R P` is `P` with
the `H₄` query of the `iv` at the parameters `p_R` added before every `H₂¹` query (a prover of
the permutation model, independent of `π`). Its log has, before every `H₂¹` input `x`, both
`H₄(ivIn p_R x)` and `H₄(ivIn p_I x)`, so N1 holds at both parameter sets (`IvBefore`,
`ivBefore_normP`, `ivBefore_normP_addIV`); its records are those of `normP` (it **is** `normP p_I π`
of a fixed prover), so the record congruences of `ROM/PermModel.lean` and every per-table lemma
apply unchanged; it costs one more `H₄` query per `H₂¹` query (`isKindQueryBoundP_addIV`), which
the bounds do not charge.

The permutation model's failure bounds use the normalization's parameters `p_N` in two roles: the
records (any `p_N`) and N1 (the statement's parameters `p`). Here they are separated:

* `addIV`, `addIV_map`, `normJ_map`, `normJ_bind`, query bounds `isKindQueryBoundP_addIV`,
  `isQueryBoundP_right_addIV`, `isQueryBoundP_left_addIV`.
* `IvBefore p L` (N1 at `p` for a log), `ivBefore_normP`, `ivBefore_normP_addIV`.
* `prEvent_perm_postP_le_iv`: Post at `p` for `normP p_N` (any `p`, `p_N`), `≤ q_E·4608·q₂₁·p²`.
* `keysPre_of_not_postP_iv`: outside Post at `p`, `KeysPre` for a statement with parameters `p`,
  for `normP p_N π P` with N1 at `p`.
* `prEvent_jointP_postP_le_iv`, `prEvent_jointP_deadOpen_le_iv`, `keysPre_iv`, `sum_fail_leP_iv`:
  the adaptive failure bounds (`ROM/PermAdapt.lean`, `ROM/SimPerm.lean`) with the normalization's
  parameters `p_N` and the statements' `p` separate; the bounds are the same (`failEpsP`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Adding the `iv` queries of other parameters -/

section AddIV

variable {α : Type}

/-- **`P` with an `H₄` query of the `iv` at the parameters `p` before every `H₂¹` query** (N1 at
`p`, as in `normP`, without touching the cipher queries). -/
def addIV (p : Params) (P : OracleComp specP α) : OracleComp specP α :=
  OracleComp.construct (C := fun _ => OracleComp specP α)
    (fun a => pure a)
    (fun t _ rec => match t, rec with
      | .inl d, rec => if d.1 = .h21 then
          liftM (specP.query (.inl (.h4, ivIn p d.2))) >>= fun _ =>
            liftM (specP.query (.inl d)) >>= rec
        else liftM (specP.query (.inl d)) >>= rec
      | .inr c, rec => liftM (specP.query (.inr c)) >>= rec)
    P

variable (p : Params)

@[simp] lemma addIV_pure (a : α) : addIV p (pure a : OracleComp specP α) = pure a := rfl

lemma addIV_inl (d : Dom) (k : specP.Range (.inl d) → OracleComp specP α) :
    addIV p (liftM (specP.query (.inl d)) >>= k) = if d.1 = .h21 then
      liftM (specP.query (.inl (.h4, ivIn p d.2))) >>= fun _ =>
        liftM (specP.query (.inl d)) >>= fun u => addIV p (k u)
    else liftM (specP.query (.inl d)) >>= fun u => addIV p (k u) := rfl

lemma addIV_inr (c : PCell) (k : specP.Range (.inr c) → OracleComp specP α) :
    addIV p (liftM (specP.query (.inr c)) >>= k) =
      liftM (specP.query (.inr c)) >>= fun u => addIV p (k u) := rfl

/-- **Adding the `iv` queries commutes with a projection of the output.** -/
theorem addIV_map {γ : Type} (f : γ → α) (G : OracleComp specP γ) :
    addIV p (f <$> G) = f <$> addIV p G := by
  induction G using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | c
    · rw [map_bind, addIV_inl, addIV_inl]
      split_ifs
      · simp only [map_bind]
        exact congrArg _ (funext fun _ => congrArg _ (funext fun u => ih u))
      · simp only [map_bind]
        exact congrArg _ (funext fun u => ih u)
    · rw [map_bind, addIV_inr, addIV_inr]
      simp only [map_bind]
      exact congrArg _ (funext fun u => ih u)

/-- `P` with one more `H₄` query per `H₂¹` query. -/
theorem isKindQueryBoundP_addIV {P : OracleComp specP α} {q : Kind → ℕ}
    (hq : IsKindQueryBoundP P q) : IsKindQueryBoundP (addIV p P) (addH4 q) := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rcases t with ⟨kd, xd⟩ | c
    · rw [addIV_inl]
      simp only at h0 hk
      split_ifs with hd
      · simp only at hd
        subst hd
        rw [IsKindQueryBoundP, isQueryBound_query_bind_iff]
        refine ⟨?_, fun _ => ?_⟩
        · show 0 < addH4 q .h4
          simp only [addH4, Function.update_self]
          omega
        rw [isQueryBound_query_bind_iff]
        refine ⟨?_, fun u => ?_⟩
        · show 0 < Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21
          rw [Function.update_of_ne (by decide), addH4_of_ne q (by decide)]
          exact h0
        have hb : Function.update (Function.update (addH4 q) .h4 (addH4 q .h4 - 1)) .h21
            (Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21 - 1) =
            addH4 (Function.update q .h21 (q .h21 - 1)) := by
          funext k'
          by_cases h1 : k' = .h21
          · subst h1
            simp [addH4]
          · by_cases h2 : k' = .h4
            · subst h2
              simp only [addH4, Function.update_self, Function.update_of_ne h1,
                Function.update_of_ne (show Kind.h21 ≠ .h4 by decide)]
              omega
            · simp [addH4, Function.update_of_ne h1, Function.update_of_ne h2]
        show IsKindQueryBoundP (addIV p (k u))
          (Function.update (Function.update (addH4 q) .h4 (addH4 q .h4 - 1)) .h21
            (Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21 - 1))
        rw [hb]
        exact ih u (hk u)
      · simp only at hd
        rw [IsKindQueryBoundP, isQueryBound_query_bind_iff]
        refine ⟨?_, fun u => ?_⟩
        · show 0 < addH4 q kd
          by_cases h4 : kd = .h4
          · subst h4
            simp only [addH4, Function.update_self]
            omega
          · rw [addH4_of_ne q h4]; exact h0
        have hb : Function.update (addH4 q) kd (addH4 q kd - 1) =
            addH4 (Function.update q kd (q kd - 1)) := by
          funext k'
          by_cases h1 : k' = kd
          · subst h1
            by_cases h4 : k' = .h4
            · subst h4
              simp only [addH4, Function.update_self,
                Function.update_of_ne (show Kind.h21 ≠ .h4 by decide)]
              omega
            · simp [addH4, Function.update_of_ne h4]
          · by_cases h2 : k' = .h4
            · subst h2
              simp only [addH4, Function.update_self, Function.update_of_ne h1,
                Function.update_of_ne (Ne.symm hd)]
            · simp [addH4, Function.update_of_ne h1, Function.update_of_ne h2]
        show IsKindQueryBoundP (addIV p (k u)) (Function.update (addH4 q) kd (addH4 q kd - 1))
        rw [hb]
        exact ih u (hk u)
    · rw [addIV_inr, IsKindQueryBoundP, isQueryBound_query_bind_iff]
      exact ⟨trivial, fun u => ih u (hk u)⟩

/-- `P`'s cipher queries. -/
theorem isQueryBoundP_right_addIV {P : OracleComp specP α} {n : ℕ}
    (hn : IsQueryBoundP P (fun t => t.isRight = true) n) :
    IsQueryBoundP (addIV p P) (fun t => t.isRight = true) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with d | c
    · rw [addIV_inl]
      simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false] at hn
      split_ifs
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        intro _
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun u => ih u (hn.2 u)
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun u => ih u (hn.2 u)
    · simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true] at hn
      rw [addIV_inr, isQueryBoundP_query_bind_iff]
      simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true]
      exact ⟨hn.1, fun u => ih u (hn.2 u)⟩

/-- `P`'s hash queries and one `H₄` query per `H₂¹` query. -/
theorem isQueryBoundP_left_addIV {P : OracleComp specP α} {n : ℕ} {q : Kind → ℕ}
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (hq : IsKindQueryBoundP P q) :
    IsQueryBoundP (addIV p P) (fun t => t.isLeft = true) (n + q .h21) := by
  induction P using OracleComp.inductionOn generalizing n q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [IsKindQueryBoundP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rcases t with d | c
    · rw [addIV_inl]
      simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true] at hn
      obtain ⟨hn0, hn⟩ := hn
      simp only at h0 hk
      split_ifs with hd
      · rw [hd] at h0
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun _ => ?_⟩
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [hd, Function.update_self] at this
        convert this using 1
        omega
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [Function.update_of_ne (Ne.symm hd)] at this
        convert this using 1
        omega
    · simp only [Sum.isLeft_inr, Bool.false_eq_true, ite_false] at hn
      rw [addIV_inr, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
        true_and]
      exact fun u => ih u (hn.2 u) (hk u)

end AddIV

/-! ## The joint normalization -/

/-- **The joint normalization** for the parameter sets `pI` (normalization) and `pR` (added `iv`
queries): `normP pI π (addIV pR P)`. -/
abbrev normJ {α : Type} (pI pR : Params) (π : PTable) (P : OracleComp specP α) :
    OracleComp specIC α :=
  normP pI π (addIV pR P)

theorem normJ_map {γ α : Type} (pI pR : Params) (π : PTable) (f : γ → α)
    (G : OracleComp specP γ) : normJ pI pR π (f <$> G) = f <$> normJ pI pR π G := by
  rw [normJ, addIV_map, normP_map]

/-- **Projections of one run stay prefix runs after the joint normalization.** -/
theorem prefixRuns_normJ_map {ι' ι β γ : Type} (pI pR : Params) (π : PTable)
    (G : OracleComp specP γ) (proj : ι' → γ → ByteArray × (ι × β)) (j₀ : ι') (J : Finset ι') :
    PrefixRuns π.fwd (normJ pI pR π (proj j₀ <$> G)) (fun j => normJ pI pR π (proj j <$> G)) J :=
  by simpa only [normJ_map] using prefixRuns_map π.fwd (normJ pI pR π G) proj j₀ J

/-- **Two projections of one run have one hash log after the joint normalization.** -/
theorem tableQueryLog_runE_normJ_map {γ α α' : Type} (pI pR : Params) (π : PTable)
    (G : OracleComp specP γ) (f : γ → α) (f' : γ → α') (g : Table) :
    tableQueryLog (runE π.fwd (normJ pI pR π (f <$> G))) g =
      tableQueryLog (runE π.fwd (normJ pI pR π (f' <$> G))) g := by
  rw [normJ_map, normJ_map, tableQueryLog_runE_map, tableQueryLog_runE_map]

/-- **Normalization commutes with binds.** -/
theorem normP_bind {α β : Type} (p : Params) (π : PTable) (X : OracleComp specP α)
    (f : α → OracleComp specP β) :
    normP p π (X >>= f) = normP p π X >>= fun a => normP p π (f a) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl, normP_inl]
      split_ifs
      · simp only [bind_assoc]
        exact congrArg _ (funext fun _ => congrArg _ (funext fun u => ih u))
      · simp only [bind_assoc]
        exact congrArg _ (funext fun u => ih u)
    · cases b
      · rw [normP_inv, normP_inv]
        simp only [bind_assoc]
        exact congrArg _ (funext fun _ => ih _)
      · rw [normP_fwd, normP_fwd]
        simp only [bind_assoc]
        exact congrArg _ (funext fun u => ih u)

/-- **Adding the `iv` queries commutes with binds.** -/
theorem addIV_bind {α β : Type} (p : Params) (X : OracleComp specP α)
    (f : α → OracleComp specP β) :
    addIV p (X >>= f) = addIV p X >>= fun a => addIV p (f a) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with d | c
    · rw [addIV_inl, addIV_inl]
      split_ifs
      · simp only [bind_assoc]
        exact congrArg _ (funext fun _ => congrArg _ (funext fun u => ih u))
      · simp only [bind_assoc]
        exact congrArg _ (funext fun u => ih u)
    · rw [addIV_inr, addIV_inr]
      simp only [bind_assoc]
      exact congrArg _ (funext fun u => ih u)

theorem normJ_bind {α β : Type} (pI pR : Params) (π : PTable) (X : OracleComp specP α)
    (f : α → OracleComp specP β) :
    normJ pI pR π (X >>= f) = normJ pI pR π X >>= fun a => normJ pI pR π (f a) := by
  rw [normJ, addIV_bind, normP_bind]

/-! ## N1 at given parameters -/

/-- **N1 at the parameters `p`** for a joint log: every `H₂¹` input `x` is preceded by the `H₄`
query of its `iv` at `p`. -/
def IvBefore (p : Params) (L : QueryLog specIC) : Prop :=
  ∀ (pre post : QueryLog specIC) (x : ByteArray) (u : Ans (.h21, x)),
    L = pre ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: post →
      (.inl (.h4, ivIn p x) : DomIC) ∈ pre.map Sigma.fst

theorem ivBefore_normP {α : Type} (p : Params) (π : PTable) (P : OracleComp specP α) (h : Table) :
    IvBefore p (jP p h π P) := fun pre post x u hJ => normP_h4_mem p π P h pre post x u hJ

/-- **N1 at the added parameters**: `normP pN π (addIV p P)` queries `H₄(ivIn p x)` before every
`H₂¹` input `x`. -/
theorem ivBefore_normP_addIV {α : Type} (pN p : Params) (π : PTable) (P : OracleComp specP α)
    (h : Table) : IvBefore p (jP pN h π (addIV p P)) := by
  intro pre post x u hJ
  induction P using OracleComp.inductionOn generalizing pre with
  | pure a => simp [jP] at hJ
  | query_bind t k ih =>
    simp only [jP] at ih hJ
    rcases t with d | ⟨b, c⟩
    · rw [addIV_inl] at hJ
      split_ifs at hJ with hd
      · rw [normP_inl, ite_eq_right_of_eq_false _ _ (eq_false (show Kind.h4 ≠ Kind.h21 by decide)),
          tableQueryLog_query_bind, normP_inl, ite_eq_left_of_eq_true _ _ (eq_true hd),
          tableQueryLog_query_bind, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rcases pre with _ | ⟨b', pre⟩
        · rw [List.cons_append, List.nil_append, List.cons.injEq, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.2.1
          simp at this
        rcases pre with _ | ⟨c', pre⟩
        · rw [List.cons_append, List.cons_append, List.nil_append, List.cons.injEq,
            List.cons.injEq, List.cons.injEq] at hJ
          obtain ⟨rfl, -, he, -⟩ := hJ
          have hd' := congrArg Sigma.fst he
          simp only [Sum.inl.injEq] at hd'
          subst hd'
          simp
        rw [List.cons_append, List.cons_append, List.cons_append, List.cons.injEq,
          List.cons.injEq, List.cons.injEq] at hJ
        obtain ⟨-, -, -, hJ⟩ := hJ
        have := ih (h d) pre hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr this))
      · rw [normP_inl, ite_eq_right_of_eq_false _ _ (eq_false hd), tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨he, -⟩ := hJ
          have hd' := congrArg Sigma.fst he
          simp only [Sum.inl.injEq] at hd'
          subst hd'
          exact absurd rfl hd
        rw [List.cons_append, List.cons.injEq] at hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih (h d) pre hJ.2)
    · rw [addIV_inr] at hJ
      cases b
      · rw [normP_inv, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rw [List.cons_append, List.cons.injEq] at hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih _ pre hJ.2)
      · rw [normP_fwd, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rw [List.cons_append, List.cons.injEq] at hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih _ pre hJ.2)

/-! ## Post at the statement's parameters, for any normalization -/

/-- **Post at the parameters `p` for the normalization at `pN`**: `≤ q_E·4608·q₂₁·p²`, at every
hash table (`prEvent_perm_postP_le` with the two parameter sets separate). -/
theorem prEvent_perm_postP_le_iv {α : Type} (pN p : Params) (h : Table) (P : OracleComp specP α)
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jP pN h π P)] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  classical
  let TT : QueryLog specIC → Blk → PTable → Finset (Blk × Blk × Blk × Blk) :=
    fun pre _ _ => halfT p pre
  let Ev : ℕ → PTable → Prop := fun n π => ∃ pre e post κ w, jP pN h π P = pre ++ e :: post ∧
    (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧ π κ j.1 = j.2.2.1 ∧ π κ j.2.1 = j.2.2.2
  have hstep : ∀ n < qE, Pr{let π ← $ᵗ PTable}[Ev n π] ≤
      ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
    intro n hn
    refine (prEvent_perm_prefix_le pN h P n TT (fun _ _ _ _ _ => rfl)
      (fun j => j.1) (fun j => j.2.1) (fun j => j.2.2.1) (fun j => j.2.2.2)
      (fun pre κ σ j hj => mem_halfT_ne hj) (4608 * q .h21) (fun σ κ => ?_)).trans ?_
    · refine (card_halfT_le p _).trans (Nat.mul_le_mul_left _ ?_)
      refine (length_kindIns_le_of_sublist (hashLog_sublist (beforeCipher_sublist n _))).trans ?_
      have := length_kindIns_hashLog_le _ (isKindQueryBound_normP pN σ hq) (join h σ.fwd) .h21
      rwa [addH4_of_ne q (by decide)] at this
    · gcongr
      exact (inv_two_le_pE n).trans (pow_le_pow_left₀ zero_le (pE_mono (by omega)) 2)
  have hcover : ∀ π : PTable, PostP p π.fwd (jP pN h π P) → ∃ n ∈ range qE, Ev n π := by
    rintro π ⟨pre, e, post, κ, w, hJ, he, j, hj, h1, h2, h3, h4⟩
    have hlen : (cipherLog pre).length < qE := by
      have := length_cipherLog_le _ (isQueryBoundP_right_normP pN π hqE) (join h π.fwd)
      have hJ' : tableQueryLog (normP pN π P) (join h π.fwd) = pre ++ e :: post := hJ
      obtain ⟨t, u⟩ := e
      simp only at he
      subst he
      rw [hJ'] at this
      have hcl : cipherLog (pre ++ ⟨.inr (κ, w), u⟩ :: post) =
          cipherLog pre ++ ⟨(κ, w), u⟩ :: cipherLog post := by
        simp [cipherLog, List.filterMap_append]
      rw [hcl, List.length_append, List.length_cons] at this
      omega
    exact ⟨_, mem_range.2 hlen, pre, e, post, κ, w, hJ, rfl, he, j, hj, h1, h2, h3, h4⟩
  calc Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jP pN h π P)]
      ≤ Pr{let π ← $ᵗ PTable}[∃ n ∈ range qE, Ev n π] := prEvent_mono _ _ _ hcover
    _ ≤ ∑ n ∈ range qE, Pr{let π ← $ᵗ PTable}[Ev n π] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _n ∈ range qE, ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
        sum_le_sum fun n hn => hstep n (mem_range.1 hn)
    _ = qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-! ## Without Post, the committed keys are found before the chain -/

section Keys

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specP (ByteArray × β))

/-- **Outside `PostP p`, the keys committed at the `H₂¹` inputs are found before them**
(`keysPre_of_not_postP_gen` for the normalization at `pN` with N1 at the statement's parameters
`p`). -/
theorem keysPre_of_not_postP_iv (pN p : Params) (hp : st.params = p) (π : PTable) (g : Table)
    (hN1 : IvBefore p (jP pN g π P))
    (hpost : ¬PostP p π.fwd (jOf g (normP pN π P) π.fwd)) :
    KeysPre st π.fwd (jOf g (normP pN π P) π.fwd) (gLog T st (normP pN π P) π.fwd g) g := by
  intro x hxmu i hi j hj a hcom _
  set J := jOf g (normP pN π P) π.fwd
  set E := π.fwd
  set iv := ivX st x g
  by_cases hx : (.inl (.h21, x) : DomIC) ∈ J.map Sigma.fst
  swap
  · rw [logBefore_eq_of_not_mem hx]
  obtain ⟨u, rest, hJ⟩ := exists_split_of_mem hx
  set Jx := logBefore (.inl (.h21, x)) J
  have hcl : cipherLog J = cipherLog Jx ++ cipherLog (⟨.inl (.h21, x), u⟩ :: rest) := by
    rw [hJ, cipherLog_append]
  rw [extractKey_eq, extractKey_eq, hcl, List.find?_append]
  cases hA : (cipherLog Jx).find? (keyPred E iv i a) with
  | some q => rfl
  | none =>
    simp only [Option.none_or, Option.map_none]
    cases hB : (cipherLog (⟨.inl (.h21, x), u⟩ :: rest)).find? (keyPred E iv i a) with
    | none => rfl
    | some q₀ =>
      exfalso
      apply hpost
      obtain ⟨hpB, B₁, B₂, hB₁, hnB⟩ := List.find?_eq_some_iff_append.1 hB
      change cipherLog rest = _ at hB₁
      obtain ⟨R₁, R₂, hR, hcR⟩ := exists_split_cipherLog hB₁
      have hnA : ∀ q ∈ cipherLog Jx, keyPred E iv i a q = false := fun q hq => by
        have := List.find?_eq_none.1 hA q hq
        simpa using this
      set pre := Jx ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: R₁
      have hcpre : cipherLog pre = cipherLog Jx ++ cipherLog R₁ := by
        rw [cipherLog_append]; rfl
      have hpre : ∀ q ∈ cipherLog pre, keyPred E iv i a q = false := by
        intro q hq
        rw [hcpre, List.mem_append] at hq
        rcases hq with hq | hq
        · exact hnA q hq
        · rw [hcR] at hq
          have := hnB q hq
          simpa using this
      have hJ' : J = pre ++ (⟨.inr q₀.1, q₀.2⟩ : (t : DomIC) × AnsIC t) :: R₂ := by
        rw [hJ, hR]
        simp only [pre, List.append_assoc, List.cons_append]
      obtain ⟨⟨κ, w⟩, v⟩ := q₀
      have hp0 := hpB
      simp only [keyPred, decide_eq_true_eq] at hp0
      obtain ⟨-, hcomK⟩ := hp0
      have hfresh : ∀ w₀, (w₀ = lp iv i 0 ∨ w₀ = lp iv i 1) →
          (.inr (κ, w₀) : DomIC) ∉ pre.map Sigma.fst := by
        intro w₀ hw₀ hmem
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 (mem_cipherLog.2 hmem)
        have := hpre q hq
        simp only [keyPred, decide_eq_false_iff_not, not_and] at this
        rw [hq1] at this
        exact this hw₀ hcomK
      have hans : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩ :=
        tableQueryLog_answer (normP pN π P) (join g E)
      have hpreJ : ∀ e ∈ pre, e ∈ J := fun e he => by
        rw [hJ']; exact List.mem_append_left _ he
      have hG : ∀ e ∈ hashEnt pre, e = ⟨e.1, g e.1⟩ :=
        hashEnt_answer fun e he => hans e (hpreJ e he)
      -- The `iv` of `x` at the statement's parameters is recorded before `x` (N1 at `p`).
      have h4 : ((.h4, ivIn p x) : Dom) ∈ (hashEnt pre).map Sigma.fst := by
        rw [map_fst_hashEnt]
        refine mem_hashLog.2 ?_
        have hJ0 : jP pN g π P =
            Jx ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: rest := hJ
        have := hN1 Jx rest x u hJ0
        exact List.map_subset _ (List.subset_append_left _ _) this
      have hiv : ivAt p (hashEnt pre) x = some iv := by
        rw [ivAt_eq hG h4]
        show some (g (.h4, (xIvPre p x ++ x.extract 0 32).push 4)).ba = some (ivX st x g)
        rw [hxmu, ← hp]
        rfl
      have hxpre : (.inl (.h21, x) : DomIC) ∈ pre.map Sigma.fst := by
        simp [pre]
      have hcom' : comPre (logBefore (.h21, x) (hashEnt pre)) x i j = some a := by
        have e1 := logBefore_gLog_eq T st (normP pN π P) E g hx
        have e2 : logBefore ((.h21, x) : Dom) (hashEnt J) =
            logBefore ((.h21, x) : Dom) (hashEnt pre) := by
          rw [hJ', hashEnt_append]
          refine logBefore_append_of_mem _ ?_
          rw [map_fst_hashEnt]
          exact mem_hashLog.2 hxpre
        rw [← e2, ← e1]
        exact hcom
      have hsplit : split32 a = (E (κ, lp iv i 0), E (κ, lp iv i 1)) := by
        rw [← hcomK, split32_ba]
      refine ⟨pre, _, R₂, κ, w, hJ', rfl, (lp iv i 0, lp iv i 1, (split32 a).1, (split32 a).2),
        ?_, hfresh _ (Or.inl rfl), hfresh _ (Or.inr rfl), by rw [hsplit], by rw [hsplit]⟩
      unfold halfT
      rw [List.mem_toFinset, List.mem_flatMap]
      refine ⟨x, mem_kindIns (mem_hashLog.2 hxpre), ?_⟩
      rw [hiv]
      simp only
      refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2
        ⟨j, List.mem_range.2 hj, ?_⟩⟩
      rw [hcom']
      exact List.mem_cons_self

end Keys

/-! ## The failure events, adaptively, with the two parameter sets separate -/

section Fails

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (pN p : Params)
  (P : OracleComp specP (ByteArray × (ι × β)))

/-- **Post at `p`, adaptively, for the normalization at `pN`**: `≤ q_E·4608·q₂₁·p²`. -/
theorem prEvent_jointP_postP_le_iv (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP pN π P) π.fwd)).run' ∅}[PostPOut p π.fwd r] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  have h := prEvent_jointP_le_add (fun π => gameA T stF (normP pN π P) π.fwd)
    (fun π r => PostPOut p π.fwd r) (fun _ _ => False)
    (qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostPOut, evalWithAnswerFn_gameA, gameIC_aux]
      exact prEvent_perm_postP_le_iv pN p g P qE hqE q hq
  rwa [prEvent_jointP_false, add_zero] at h

/-- **`ε_open`, adaptively, for the normalization at `pN`** (statements with parameters `p`):
`≤ openHashEps q + q₁·p'²`. -/
theorem prEvent_jointP_deadOpen_le_iv (hparams : ∀ s, (stF s).params = p) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP pN π P) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] ≤
      openHashEps q + q .h1 * pE (qE + 4607) ^ 2 := by
  let m : PTable → ProbComp (Out ((ι × β) × QueryLog specIC)) := fun π =>
    (simulateQ randomOracle (gameA T stF (normP pN π P) π.fwd)).run' ∅
  let A : PTable → Out ((ι × β) × QueryLog specIC) → Prop := fun π r =>
    r.2.2.accept = true ∧
      @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r
  have hA : ∀ π, Pr{let r ← m π}[A π r] ≤ openHashEps q := fun π => by
    have hqW := isKindQueryBound_normP pN π hq
    rw [← openHashEps_addH4]
    refine (prEvent_mono _ _ (fun r => (r.2.2.accept = true ∧
        @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
          ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2) ∨
        (r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2))
        fun r h => (em (((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2)).elim
          (fun hz => Or.inl ⟨h.1, h.2, hz⟩) fun hz => Or.inr ⟨h.1, hz⟩).trans
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_leafUnqueried_z_le_A T stF (normP pN π P) p hparams (addH4 q) hqW π.fwd)
        (prEvent_zUnqueried_le_A T stF (normP pN π P) π.fwd)))
  have h1 : Pr{let π ← $ᵗ PTable; let r ← m π}[A π r] ≤ openHashEps q :=
    prEvent_avgP_le m A _ hA
  have h2 : Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r ∧ ¬A π r] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
    have h := prEvent_jointP_le_add (fun π => gameA T stF (normP pN π P) π.fwd)
      (fun π r => deadOpenA stF π.fwd r ∧ ¬A π r) (fun _ _ => False)
      (q .h1 * pE (qE + 4607) ^ 2) fun g =>
        ((prEvent_mono _ _ _ fun π h => by
          simp only [A, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at h
          exact deadQueried_of_deadOpen T _ (normP pN π P) g π.fwd h.1
            fun hL => h.2 ⟨h.1.1, hL⟩).trans
          (prEvent_perm_deadQueried_le_g g pN (fun π => stF (sA g (normP pN π P) π.fwd)) P
            (fun σ π hO => by simp only [sA, hO]) qE hqE q hq)).trans le_self_add
    rwa [prEvent_jointP_false, add_zero] at h
  calc Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r]
      ≤ Pr{let π ← $ᵗ PTable; let r ← m π}[A π r ∨ (deadOpenA stF π.fwd r ∧ ¬A π r)] :=
        prEvent_jointP_mono m _ _ fun π r h => (em (A π r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_jointP_or_le m _ _).trans (add_le_add h1 h2)

/-- Outside Post at `p`, the keys committed at the `H₂¹` inputs are found before them, at every
statement of the family (parameters `p`), for the normalization at `pN` with N1 at `p`. -/
theorem keysPre_iv {s : ι} (hp : (stF s).params = p) (π : PTable) (g : Table)
    (hN1 : IvBefore p (jP pN g π P))
    (h : ¬PostPOut p π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF s) (normP pN π P) π.fwd))) :
    KeysPre (stF s) π.fwd (jOf g (normP pN π P) π.fwd) (gLog T (stF s) (normP pN π P) π.fwd g)
      g := by
  refine keysPre_of_not_postP_iv T (stF s) P pN p hp π g hN1 ?_
  unfold PostPOut at h
  rwa [gameIC_aux] at h

end Fails

/-- **The per-output failure terms for the normalization at `pN`** (statements with parameters
`p`): as `sum_fail_leP`. -/
theorem sum_fail_leP_iv {ι' ι β : Type} (T : CrtTables) (stF : ι → Statement) (pN p : Params)
    (hparams : ∀ s, (stF s).params = p) (P : ι' → OracleComp specP (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : ∀ j ∈ J, IsKindQueryBoundP (P j) q) :
    ∑ j ∈ J, (Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP pN π (P j)) π.fwd)).run' ∅}[bindFailA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP pN π (P j)) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP pN π (P j)) π.fwd)).run' ∅}[PostPOut p π.fwd r]) ≤
      J.card * failEpsP q qE := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
  have hdo := prEvent_jointP_deadOpen_le_iv T stF pN p (P j) hparams qE (hqE j hj) q (hq j hj)
  unfold failEpsP
  gcongr
  · exact (prEvent_jointP_bindFail_le_A T stF pN (P j) qE (hqE j hj)).trans (add_le_add le_rfl hdo)
  · exact prEvent_jointP_postP_le_iv T stF pN p (P j) qE (hqE j hj) q (hq j hj)

/-- The failure terms do not count `H₄` queries. -/
lemma failEpsP_addH4 (q : Kind → ℕ) (qE : ℕ) : failEpsP (addH4 q) qE = failEpsP q qE := by
  simp only [failEpsP, openHashEps_addH4, addH4_of_ne q (show Kind.h1 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide)]

end VoleMole.ROM.IC
