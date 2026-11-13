import VoleMole.ROM.SimExtract

/-!
# Simultaneous extraction across two relations: one charge per query of the run

`ROM/SimExtract.lean` charges the queries of a protocol run once **per relation**: Moussaka's
issuance and redemption proofs (Ratatouille's issuance and spend requests) come from one run, but
each relation's simultaneous bound pays `Σ_k q_k·ε_k` for all of the run's queries. Here a query
of the run is charged **once in all**, at the larger of the two relations' per-query charges.

The bad event of a query is read off the statement committed at the query (`stmtAt`). The two
relations' statements are separated by their DSTs, so the `H₂⁰` preimage that commits the
statement at a query decodes in at most one family (`stmtAt_eq_bind`, `stmtAt_sep`). For a
fixed background table the query is therefore charged by one relation only, and on average over
the background, with weights `p_I + p_R ≤ 1`, the charge is `p_I·ε_I + p_R·ε_R ≤ ε_I ⊔ ε_R`.

* `prEvent_le_shared_suffix₂` (generic): `ROM/SimUnion.lean`'s shared-run union bound with two
  families of outputs, each with its own continuation charge.
* `prEvent_cell_le_mul`, `prEvent_three_le_of_first_mul`, `prEvent_three_le_of_second_mul`: the
  single-cell and two-cell resampling bounds, weighted by an event of the background.
* `prEvent_combBadA_h22_le_mul`: `ROM/AdaptComb.lean`'s two-cell `H₂²` bound, weighted by the
  probability that a statement of the combined family is committed at the query.
* `jointBad`, `jointEps`, **`prEvent_jointBad_le`**: the joint bad event of a query of the run
  (an issue-type relation's bad chain query at a committed statement of its family, or a bad
  query of a combined relation), and its per-query charge
  `(ε_I ⊔ ε_R) + [k = H₂²]·n·2⁻⁴⁴⁸ + hits + statement hits`.
* **`prEvent_sim_joint_le_E`** (per cipher table), **`prEvent_sim_joint_le`** (joint experiment),
  `sim_joint_sum_le`: the two relations' outputs together,

      Σ_k q_k·jointEps k + |J_I|·Σ_k r_k·ε_I,k + |J_R|·Σ_k r_k·ε_R,k
        + (|J_I| + |J_R|)·failEps,

  against `Σ_k q_k·(ε_I,k + ε_R,k) + …` from adding the two relations' simultaneous bounds.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

variable {D : Type} {R : D → Type} {α : Type}

section Lazy

variable [DecidableEq D] [∀ d, Nonempty (R d)] [∀ d, SampleableType (R d)]

/-- **The shared-run union bound with two families of outputs** (`prEvent_le_shared_suffix`
with outputs `j ∈ J₁` and `j ∈ J₂` of different types). The shared run's queries are charged
once with `errA`, each family's continuations with their own charge. -/
theorem prEvent_le_shared_suffix₂ {ι₁ ι₂ κ₁ κ₂ γ γ₁ δ₁ γ₂ δ₂ β₁ β₂ : Type} (S : Finset D)
    [SampleableType ((d : S) → R d.val)]
    (oa : OracleComp (ofFn R) α) (event : α → Prop) (hSo : AllQueriesSatisfy oa (· ∈ S))
    (A : OracleComp (ofFn R) γ) (hSA : AllQueriesSatisfy A (· ∈ S)) (errA : D → ℝ≥0∞)
    (BA : ℝ≥0∞) (hBA : WorstCaseCostBound A ⟨errA⟩ BA) (n₀ : ℕ) (hn₀ : IsTotalQueryBound A n₀)
    (badA : D → (∀ d, R d) → Prop)
    (J₁ : Finset ι₁) (A₁ : ι₁ → OracleComp (ofFn R) γ₁) (K₁ : ι₁ → γ₁ → OracleComp (ofFn R) δ₁)
    (hSK₁ : ∀ j ∈ J₁, AllQueriesSatisfy (A₁ j >>= K₁ j) (· ∈ S)) (err₁ : D → ℝ≥0∞)
    (BK₁ : ℝ≥0∞) (hBK₁ : ∀ j a, WorstCaseCostBound (K₁ j a) ⟨err₁⟩ BK₁) (nA₁ nK₁ : ℕ)
    (hnA₁ : ∀ j ∈ J₁, IsTotalQueryBound (A₁ j) nA₁) (hnK₁ : ∀ j a, IsTotalQueryBound (K₁ j a) nK₁)
    (bad₁ : ι₁ → D → (∀ d, R d) → Prop)
    (J₂ : Finset ι₂) (A₂ : ι₂ → OracleComp (ofFn R) γ₂) (K₂ : ι₂ → γ₂ → OracleComp (ofFn R) δ₂)
    (hSK₂ : ∀ j ∈ J₂, AllQueriesSatisfy (A₂ j >>= K₂ j) (· ∈ S)) (err₂ : D → ℝ≥0∞)
    (BK₂ : ℝ≥0∞) (hBK₂ : ∀ j a, WorstCaseCostBound (K₂ j a) ⟨err₂⟩ BK₂) (nA₂ nK₂ : ℕ)
    (hnA₂ : ∀ j ∈ J₂, IsTotalQueryBound (A₂ j) nA₂) (hnK₂ : ∀ j a, IsTotalQueryBound (K₂ j a) nK₂)
    (bad₂ : ι₂ → D → (∀ d, R d) → Prop)
    (I₁ : Finset κ₁) (ob₁ : κ₁ → OracleComp (ofFn R) β₁) (Q₁ : κ₁ → β₁ → Prop)
    (hSI₁ : ∀ i ∈ I₁, AllQueriesSatisfy (ob₁ i) (· ∈ S))
    (I₂ : Finset κ₂) (ob₂ : κ₂ → OracleComp (ofFn R) β₂) (Q₂ : κ₂ → β₂ → Prop)
    (hSI₂ : ∀ i ∈ I₂, AllQueriesSatisfy (ob₂ i) (· ∈ S))
    (N : ℕ) (hN₀ : n₀ ≤ N) (hN₁ : nA₁ + nK₁ ≤ N) (hN₂ : nA₂ + nK₂ ≤ N)
    (hbadA : ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[badA t.val (extendTable S (completeTable c g))] ≤
        errA t.val)
    (hbad₁ : ∀ j ∈ J₁, ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[bad₁ j t.val (extendTable S (completeTable c g))] ≤
        err₁ t.val)
    (hbad₂ : ∀ j ∈ J₂, ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[bad₂ j t.val (extendTable S (completeTable c g))] ≤
        err₂ t.val)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      (∃ e ∈ tableQueryLog A g, badA e.1 g) ∨
      (∃ j ∈ J₁, ∃ e ∈ tableQueryLog (K₁ j (evalWithAnswerFn (QueryImpl.ofFn g) (A₁ j))) g,
        e.1 ∉ (tableQueryLog (A₁ j) g).map Sigma.fst ∧ bad₁ j e.1 g) ∨
      (∃ j ∈ J₂, ∃ e ∈ tableQueryLog (K₂ j (evalWithAnswerFn (QueryImpl.ofFn g) (A₂ j))) g,
        e.1 ∉ (tableQueryLog (A₂ j) g).map Sigma.fst ∧ bad₂ j e.1 g) ∨
      (∃ i ∈ I₁, Q₁ i (evalWithAnswerFn (QueryImpl.ofFn g) (ob₁ i))) ∨
      (∃ i ∈ I₂, Q₂ i (evalWithAnswerFn (QueryImpl.ofFn g) (ob₂ i)))) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      BA + ∑ _j ∈ J₁, BK₁ + ∑ _j ∈ J₂, BK₂ +
        ∑ i ∈ I₁, Pr{let r ← (simulateQ randomOracle (ob₁ i)).run' ∅}[Q₁ i r] +
        ∑ i ∈ I₂, Pr{let r ← (simulateQ randomOracle (ob₂ i)).run' ∅}[Q₂ i r] := by
  classical
  let mG := $ᵗ ((d : S) → R d.val)
  have hempty : ∀ G : (d : S) → R d.val, tabC S ∅ G = extendTable S G := fun G => by
    simp only [tabC, completeTable_empty]
  have hcnone : ∀ d, CNone S (∅ : (ofFn fun d : S => R d.val).QueryCache) d := fun _ _ => rfl
  rw [prEvent_eq_extendTable' S oa hSo]
  rw [Finset.sum_congr rfl fun i hi => prEvent_eq_extendTable' S (ob₁ i) (hSI₁ i hi) (Q₁ i)]
  rw [Finset.sum_congr rfl fun i hi => prEvent_eq_extendTable' S (ob₂ i) (hSI₂ i hi) (Q₂ i)]
  let X₀ : ((d : S) → R d.val) → Prop := fun G =>
    SuffixBad S (pure () : OracleComp (ofFn R) Unit) (fun _ => A) badA ∅ (tabC S ∅ G)
  let X₁ : ι₁ → ((d : S) → R d.val) → Prop := fun j G =>
    SuffixBad S (A₁ j) (K₁ j) (bad₁ j) ∅ (tabC S ∅ G)
  let X₂ : ι₂ → ((d : S) → R d.val) → Prop := fun j G =>
    SuffixBad S (A₂ j) (K₂ j) (bad₂ j) ∅ (tabC S ∅ G)
  let X₃ : κ₁ → ((d : S) → R d.val) → Prop := fun i G =>
    Q₁ i (evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) (ob₁ i))
  let X₄ : κ₂ → ((d : S) → R d.val) → Prop := fun i G =>
    Q₂ i (evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) (ob₂ i))
  refine (prEvent_mono mG _ (fun G => X₀ G ∨ ((∃ j ∈ J₁, X₁ j G) ∨ ((∃ j ∈ J₂, X₂ j G) ∨
    ((∃ i ∈ I₁, X₃ i G) ∨ (∃ i ∈ I₂, X₄ i G))))) fun G hG => ?_).trans ?_
  · rcases htrace _ hG with ⟨e, he, hb⟩ | ⟨j, hj, e, he, hn, hb⟩ | ⟨j, hj, e, he, hn, hb⟩ |
      ⟨i, hi, hq⟩ | ⟨i, hi, hq⟩
    · left
      simp only [X₀, SuffixBad, tableQueryLog_pure, List.map_nil,
        List.not_mem_nil, not_false_eq_true, true_and, hempty]
      exact ⟨e, he, hcnone _, hb⟩
    · right; left
      refine ⟨j, hj, ?_⟩
      simp only [X₁, SuffixBad, hempty]
      exact ⟨e, he, hcnone _, hn, hb⟩
    · right; right; left
      refine ⟨j, hj, ?_⟩
      simp only [X₂, SuffixBad, hempty]
      exact ⟨e, he, hcnone _, hn, hb⟩
    · right; right; right; left
      exact ⟨i, hi, hq⟩
    · right; right; right; right
      exact ⟨i, hi, hq⟩
  rw [add_assoc, add_assoc, add_assoc]
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ ((prEvent_or_le _ _ _).trans
      (add_le_add ?_ ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_exists_finset_le I₁ mG X₃) (prEvent_exists_finset_le I₂ mG X₄))))))))
  · exact prEvent_suffixBad_le S (pure ()) (fun _ => A) (by simpa using hSA) errA BA
      (fun _ => hBA) 0 n₀ trivial (fun _ => hn₀) N badA hbadA ∅ 0
      (by rw [card_cachedKeys_empty]) (by omega)
  · refine (prEvent_exists_finset_le J₁ mG X₁).trans (Finset.sum_le_sum fun j hj => ?_)
    exact prEvent_suffixBad_le S (A₁ j) (K₁ j) (hSK₁ j hj) err₁ BK₁ (hBK₁ j) nA₁ nK₁ (hnA₁ j hj)
      (hnK₁ j) N (bad₁ j) (hbad₁ j hj) ∅ 0 (by rw [card_cachedKeys_empty]) (by omega)
  · refine (prEvent_exists_finset_le J₂ mG X₂).trans (Finset.sum_le_sum fun j hj => ?_)
    exact prEvent_suffixBad_le S (A₂ j) (K₂ j) (hSK₂ j hj) err₂ BK₂ (hBK₂ j) nA₂ nK₂ (hnA₂ j hj)
      (hnK₂ j) N (bad₂ j) (hbad₂ j hj) ∅ 0 (by rw [card_cachedKeys_empty]) (by omega)

/-- **The single-cell resampling bound, weighted by an event of the background**: if the event
`ev` has probability `≤ ε` when the uncached cell `t` alone is resampled at a background where
`w` holds, and is impossible where `w` fails, then over the uncached cells it has probability
`≤ Pr[w]·ε`. -/
theorem prEvent_cell_le_mul (S : Finset D) [SampleableType ((d : S) → R d.val)]
    (c : (ofFn fun d : S => R d.val).QueryCache) (t : S) (hc : c t = none)
    (ev w : (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (h₁ : ∀ G, w G → Pr{let u ← $ᵗ (R t.val)}[ev (Function.update G t.val u)] ≤ ε)
    (h₂ : ∀ G u, ¬w G → ¬ev (Function.update G t.val u)) :
    Pr{let g ← $ᵗ ((d : S) → R d.val)}[ev (extendTable S (completeTable c g))] ≤
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[w (extendTable S (completeTable c g))] * ε := by
  let : ∀ d : S, MeasurableSpace (R d.val) := fun _ => ⊤
  let : MeasurableSpace ((d : S) → R d.val) := ⊤
  rw [prEvent_uniformTable_update t]
  simp_rw [← completeTable_update_of_none c _ hc, extendTable_update]
  let : MeasurableSpace Prop := ⊤
  have hswap := evalDist_bind_bind_swap_of_countable ($ᵗ (R t.val)) ($ᵗ ((d : S) → R d.val))
    (fun u g => pure (ev (Function.update (extendTable S (completeTable c g)) t.val u)))
  have h' := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq id
  simp only [prEvent_norm, id_eq] at h'
  rw [h']
  have key := prEvent_bind_le_prEvent_mul_of_forall_le ($ᵗ ((d : S) → R d.val))
    (fun g => (fun u => ev (Function.update (extendTable S (completeTable c g)) t.val u)) <$>
      ($ᵗ (R t.val))) (fun g => w (extendTable S (completeTable c g))) id
    (fun g hw => by simpa only [prEvent_norm, id_eq] using h₁ _ hw)
    (fun g hw => by
      have hf : ∀ u, ev (Function.update (extendTable S (completeTable c g)) t.val u) = False :=
        fun u => eq_false (h₂ _ u hw)
      simp [hf])
  simpa only [prEvent_norm, id_eq] using key

end Lazy

/-! ## Three independent draws, weighted -/

section Three

variable {U V G : Type} [SampleableType U] [SampleableType V] [SampleableType G]

/-- The three draws reordered, the last first. -/
theorem prEvent_three_eq_last_first (P : U → V → G → Prop) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] =
      Pr{let g ← $ᵗ G; let x ← (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v))}[P x.1 x.2 g] := by
  have e : Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] =
      Pr{let x ← (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v)); let g ← $ᵗ G}[P x.1 x.2 g] := by
    simp only [prEvent_norm]
  rw [e, prEvent_bind_map_swap]

/-- **A bound over the first draw, weighted by an event of the third.** -/
theorem prEvent_three_le_of_first_mul (P : U → V → G → Prop) (w : G → Prop) {ε : ℝ≥0∞}
    (h₁ : ∀ v g, w g → Pr{let u ← $ᵗ U}[P u v g] ≤ ε) (h₂ : ∀ u v g, ¬w g → ¬P u v g) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] ≤ Pr{let g ← $ᵗ G}[w g] * ε := by
  rw [prEvent_three_eq_last_first]
  have key := prEvent_bind_le_prEvent_mul_of_forall_le ($ᵗ G)
    (fun g => (fun x => P x.1 x.2 g) <$> (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v))) w id
    (ε := ε) (fun g hw => ?_) (fun g hw => ?_)
  · simpa only [prEvent_norm, id_eq] using key
  · have e : Pr{let y ← (fun x : U × V => P x.1 x.2 g) <$> (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v))}[
        id y] = Pr{let u ← $ᵗ U; let v ← $ᵗ V}[P u v g] := by simp only [prEvent_norm, id_eq]
    rw [e, prEvent_bind_map_swap]
    have := prEvent_bind_le_of_forall_le ($ᵗ V) (fun v => (fun u => P u v g) <$> ($ᵗ U)) id
      (fun v => by simpa using h₁ v g hw)
    simpa only [prEvent_norm, id_eq, id_map'] using this
  · have hf : ∀ u v, P u v g = False := fun u v => eq_false (h₂ u v g hw)
    simp [hf]

/-- **A bound over the second draw, weighted by an event of the third.** -/
theorem prEvent_three_le_of_second_mul (P : V → G → Prop) (w : G → Prop) {ε : ℝ≥0∞}
    (h₁ : ∀ g, w g → Pr{let v ← $ᵗ V}[P v g] ≤ ε) (h₂ : ∀ v g, ¬w g → ¬P v g) :
    Pr{let _u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P v g] ≤ Pr{let g ← $ᵗ G}[w g] * ε := by
  rw [prEvent_three_eq_last_first (fun _ v g => P v g)]
  have key := prEvent_bind_le_prEvent_mul_of_forall_le ($ᵗ G)
    (fun g => (fun x => P x.2 g) <$> (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v))) w id
    (ε := ε) (fun g hw => ?_) (fun g hw => ?_)
  · simpa only [prEvent_norm, id_eq] using key
  · have e : Pr{let y ← (fun x : U × V => P x.2 g) <$> (do let u ← $ᵗ U; let v ← $ᵗ V; pure (u, v))}[
        id y] = Pr{let _u ← $ᵗ U; let v ← $ᵗ V}[P v g] := by simp only [prEvent_norm, id_eq]
    rw [e]
    have := prEvent_bind_le_of_forall_le ($ᵗ U) (fun _ => (fun v => P v g) <$> ($ᵗ V)) id
      (fun _ => by simpa using h₁ g hw)
    simpa only [prEvent_norm, id_eq, id_map'] using this
  · have hf : ∀ v, P v g = False := fun v => eq_false (h₂ v g hw)
    simp [hf]

end Three

/-- **Disjoint weights**: `p·a + p'·b ≤ a ⊔ b` when `p + p' ≤ 1`. -/
lemma mul_add_mul_le_max {p p' a b : ℝ≥0∞} (h : p + p' ≤ 1) : p * a + p' * b ≤ a ⊔ b :=
  calc p * a + p' * b ≤ p * (a ⊔ b) + p' * (a ⊔ b) := by gcongr <;> simp
    _ = (p + p') * (a ⊔ b) := (add_mul _ _ _).symm
    _ ≤ 1 * (a ⊔ b) := by gcongr
    _ = a ⊔ b := one_mul _

/-- **Two disjoint events of one draw have total probability at most one.** -/
lemma prEvent_add_le_one_of_disjoint {β : Type} (mx : ProbComp β) (p p' : β → Prop)
    (h : ∀ x, p x → p' x → False) : Pr{let x ← mx}[p x] + Pr{let x ← mx}[p' x] ≤ 1 := by
  calc Pr{let x ← mx}[p x] + Pr{let x ← mx}[p' x] ≤
        Pr{let x ← mx}[p x] + Pr{let x ← mx}[¬p x] :=
        add_le_add le_rfl (prEvent_mono _ _ _ fun x hx hp => h x hp hx)
    _ = Pr{let _ ← mx}[True] := prEvent_add_prEvent_not_eq_prEvent_true _ _
    _ ≤ 1 := prEvent_le_one _

end VoleMole.ROM

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The statement committed at a query, in two families -/

section Sep

/-- **The statement committed at a query is one decoded `H₂⁰` preimage**, whatever the decoder:
`stmtAt dec L t = o.bind dec` for an `o` that does not depend on `dec`. -/
theorem stmtAt_eq_bind (L : QueryLog spec) (t : Dom) :
    ∃ o : Option ByteArray, ∀ {κ : Type} (dec : ByteArray → Option κ),
      stmtAt dec L t = o.bind dec := by
  obtain ⟨k, x⟩ := t
  cases k
  case h21 => exact ⟨_, fun dec => rfl⟩
  case h22 =>
    cases h : firstIn .h21 (fun _ => true) (yChal1 x) (logBefore (.h22, x) L) with
    | none => exact ⟨none, fun dec => by simp only [stmtAt, sY, h, Option.bind_none]⟩
    | some x' => exact ⟨firstIn .mu (fun _ => true) (xMu x') (logBefore (.h21, x')
        (logBefore (.h22, x) L)), fun dec => by simp only [stmtAt, sY, h, sX]⟩
  case h23 =>
    cases h : firstIn .h22 (fun _ => true) (zChal2 x) (logBefore (.h23, x) L) with
    | none => exact ⟨none, fun dec => by simp only [stmtAt, sZ, h, Option.bind_none]⟩
    | some y =>
      cases h' : firstIn .h21 (fun _ => true) (yChal1 y) (logBefore (.h22, y)
          (logBefore (.h23, x) L)) with
      | none => exact ⟨none, fun dec => by simp only [stmtAt, sZ, h, sY, h', Option.bind_none]⟩
      | some x' => exact ⟨firstIn .mu (fun _ => true) (xMu x') (logBefore (.h21, x')
          (logBefore (.h22, y) (logBefore (.h23, x) L))),
          fun dec => by simp only [stmtAt, sZ, h, sY, h', sX]⟩
  all_goals exact ⟨none, fun dec => rfl⟩

/-- **Separated decoders commit at most one family's statement at a query.** -/
theorem stmtAt_sep {κ κ' : Type} (dec : ByteArray → Option κ) (dec' : ByteArray → Option κ')
    (hsep : ∀ x, (dec x).isSome → (dec' x).isSome → False) (L : QueryLog spec) (t : Dom)
    (h : (stmtAt dec L t).isSome) (h' : (stmtAt dec' L t).isSome) : False := by
  obtain ⟨o, ho⟩ := stmtAt_eq_bind L t
  rw [ho] at h h'
  cases o with
  | none => simp at h
  | some x => exact hsep x h h'

end Sep

/-! ## The combined relations' bad event, weighted by the committed statement -/

section CombW

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) {M : ℕ}
  (sysL : ι → (Fin M → GF128) → System GF128) (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray)

/-- No statement committed at `t`: no bad query of a combined relation there. -/
lemma not_combBadA_of_none (N : ℕ) (t : Dom) (G : Table)
    (h : ¬(stmtAt dec (gLogA T stF P E G) t).isSome) (u : Ans t) :
    ¬combBadA T stF dec P E sysL witL dst N t (Function.update G t u) := by
  rintro ⟨s, hs, -⟩
  unfold gLogA at hs h
  rw [stmtAt_update] at hs
  simp [hs] at h

set_option exponentiation.threshold 500 in
/-- **The `H₂²` bound at the committed statement, weighted** (`prEvent_combBadA_h22_le`): the
two-cell part `ε_QS(n') + ε_c` is paid only where a statement of the family is committed at `y`.
-/
theorem prEvent_combBadA_h22_le_mul (N : ℕ) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey M dst u ∈ K)
    {y : ByteArray} (hy : ((.h22, y) : Dom) ∈ K) (c : (ofFn fun d : K => Ans d.val).QueryCache)
    (hc : c ⟨_, hy⟩ = none) {n : ℕ} (hcard : (cachedKeys c).card < n) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      combBadA T stF dec P E sysL witL dst N (.h22, y) (extendTable K (completeTable c g))] ≤
      (n : ℝ≥0∞) / 2 ^ 448 +
        Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[(stmtAt dec (gLogA T stF P E
          (extendTable K (completeTable c g))) (.h22, y)).isSome] *
        (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  let t : K := ⟨_, hy⟩
  let p : Ans t.val → K := fun u => ⟨combKey M dst u, hK u⟩
  have hp : Function.Injective p := fun u u' h =>
    combKey_injective M dst (congrArg Subtype.val h)
  refine (prEvent_completeTable_le_two_cells c t p
    (fun G => combBadA T stF dec P E sysL witL dst N (.h22, y) (extendTable K G))).trans ?_
  refine add_le_add ?_ ?_
  · refine (prEvent_isSome_le c p hp).trans ?_
    have hcardU : Fintype.card (Ans t.val) = 2 ^ 448 := card_bytes 56
    rw [hcardU, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard.le) _
  · let X : ((d : K) → Ans d.val) → Table := fun g => extendTable K (completeTable c g)
    let σ : ((d : K) → Ans d.val) → Option ι := fun g =>
      stmtAt dec (gLogA T stF P E (X g)) (.h22, y)
    let CA := combDataA T stF P E sysL witL dst
    change Pr{let u ← $ᵗ (Prob.Bytes 56); let v ← $ᵗ (Prob.Bytes (16 * M)); let g ← $ᵗ ((d : K) → Ans d.val)}[
          c (p u) = none ∧ combBadA T stF dec P E sysL witL dst N (.h22, y)
          (extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)))] ≤
      Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[(σ g).isSome] * _
    refine (prEvent_three_mono (Q := fun u v g =>
      (∃ s, σ g = some s ∧ (¬((CA s).sysOf y (X g) (combDec v)).Holds
          ((CA s).wC T chal3Blocks y (X g)) ∧
        Seed.zkHash ((CA s).sysOf y (X g) (combDec v)).length (gfOfBytes u.ba 0)
          (gfOfBytes u.ba 16) (gfOfBytes u.ba 32) ⟨W128.word u.ba 48, 0⟩
          (valVec ((CA s).sysOf y (X g) (combDec v)) ((CA s).wC T chal3Blocks y (X g))) = 0)) ∨
      (∃ s, σ g = some s ∧ (((CA s).sysOf y (X g) (combDec v)).Holds
          ((CA s).wC T chal3Blocks y (X g)) ∧
        ¬(CA s).witOf y (X g) ((CA s).wC T chal3Blocks y (X g))))) ?_).trans ?_
    · intro u v g h
      obtain ⟨hcu, s, hσ, hb⟩ := h
      have hq := combBad_h22_update (CA s) K (combDataA_committed T stF P E sysL witL dst s) T
        chal3Blocks N hK hy c hc u v hcu g hb
      have hσ' : σ g = some s := by
        have hX' : extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)) =
            Function.update (Function.update (X g) (combKey M dst u) v) (.h22, y) u :=
          extend_two_updates dst K c hy hc hK u v hcu g
        rw [hX'] at hσ hb
        exact stmtAt_two_updates T stF dec P E sysL witL dst N (X g) u v hσ hb
      rcases hq with hq | hq
      · exact Or.inl ⟨s, hσ', hq⟩
      · exact Or.inr ⟨s, hσ', hq⟩
    rw [mul_add]
    refine (prEvent_three_or_le _ _).trans (add_le_add ?_ ?_)
    · refine prEvent_three_le_of_first_mul _ (fun g => (σ g).isSome) (fun v g hw => ?_)
        (fun u v g hw h => ?_)
      · obtain ⟨s, hσ⟩ := Option.isSome_iff_exists.1 hw
        simp only [hσ, Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        exact (prU_qs_bad_le _ _).trans_eq (by rw [show ((CA s).sysOf y (X g) (combDec v)).length
          = n' from hn' s _])
      · obtain ⟨s, hσ, -⟩ := h
        simp [hσ] at hw
    · refine prEvent_three_le_of_second_mul (fun v g => ∃ s, σ g = some s ∧
        (((CA s).sysOf y (X g) (combDec v)).Holds ((CA s).wC T chal3Blocks y (X g)) ∧
          ¬(CA s).witOf y (X g) ((CA s).wC T chal3Blocks y (X g)))) (fun g => (σ g).isSome)
        (fun g hw => ?_) (fun v g hw h => ?_)
      · obtain ⟨s, hσ⟩ := Option.isSome_iff_exists.1 hw
        simp only [hσ, Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        have := hεc s ((CA s).wC T chal3Blocks y (X g))
        rwa [prU_map_equiv (combEquiv M)] at this
      · obtain ⟨s, hσ, -⟩ := h
        simp [hσ] at hw

end CombW

/-! ## The joint bad event of a query of the run -/

section JointBad

variable {ιI βI ιR βR : Type} (T : CrtTables) (stI : ιI → Statement)
  (decI : ByteArray → Option ιI) (sysI : ιI → System GF128)
  (PI : OracleComp specIC (ByteArray × (ιI × βI))) (stR : ιR → Statement)
  (decR : ByteArray → Option ιR) (PR : OracleComp specIC (ByteArray × (ιR × βR))) (E : CTable)
  {M : ℕ} (sysL : ιR → (Fin M → GF128) → System GF128) (witL : ιR → (ℕ → GF128) → Prop)
  (dst : ByteArray)

/-- **The joint bad event of a query** for an issue-type relation (`stI`, `chainBadA`) and a
combined relation (`stR`, `combAdaptBad`) whose provers `PI`, `PR` share one run: a bad chain
query of the first at a statement of its family committed at the query (read off the second's
log, which agrees with the first's before a query of the run), or a bad query of the second (a bad
query at its committed statement, a hit, a statement hit). -/
def jointBad (N : ℕ) (t : Dom) (g : Table) : Prop :=
  (chainBadA T stI decI sysI PI E N t g ∧ (stmtAt decI (gLogA T stR PR E g) t).isSome) ∨
    combAdaptBad T stR decR PR E sysL witL dst N t g

/-- **The joint per-query charge**: the larger of the two relations' chain charges (at `H₂²` the
combined relation's `ε_QS(n') + ε_c`, plus `ntot·2⁻⁴⁴⁸` for its combination cell), the hits
(with the combination targets) and the statement hits. -/
noncomputable def jointEps (stI₀ stR₀ : Statement) (n n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ)
    (nn : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  ((chainEps stI₀ chal3Blocks n N k ⊔
      (if k = .h22 then ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc
        else chainEps stR₀ chal3Blocks 0 N k)) +
    (if k = .h22 then (ntot : ℝ≥0∞) / 2 ^ 448 else 0)) +
  (hitEps nn (combCount (some (M, dst)) nn) k + stmtEps nn k)

lemma jointEps_eq_zero (stI₀ stR₀ : Statement) (n n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ)
    (nn : Kind → ℕ) : ∀ k ∉ adaptKinds, jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k = 0 := by
  intro k hk
  cases k <;> simp_all [adaptKinds, jointEps, chainEps, hitEps, stmtEps]

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **The per-query bound of the joint bad event**, over the uncached cells of a cache with fewer
than `ntot` keys. The two families' decoders are separated (`hsep`: no `H₂⁰` input decodes in
both), so for a fixed background at most one family's statement is committed at the query; the
chain charges are weighted by the probabilities `p_I`, `p_R` of that, `p_I + p_R ≤ 1`. -/
theorem prEvent_jointBad_le (hT : liftInvOk T = true) (stI₀ : Statement)
    (hparamsI : ∀ s, (stI s).params = stI₀.params) {n : ℕ} (hn : ∀ s, (sysI s).length = n)
    (stR₀ : Statement) (hparamsR : ∀ s, (stR s).params = stR₀.params) {n' : ℕ}
    (hn' : ∀ s l, (sysL s l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (hsep : ∀ x, (decI x).isSome → (decR x).isSome → False)
    (N : ℕ) (q : Kind → ℕ) (hq : IsKindQueryBoundIC PR q)
    (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey M dst u ∈ K)
    (ntot : ℕ) (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[jointBad T stI decI sysI PI stR decR PR E sysL witL dst
        N t.val (extendTable K (completeTable c g))] ≤
      jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N (q + extractorQueries + verifierQueries)
        t.val.1 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  have hq'' := isKindQueryBound_gameA T stR PR E hq
  let X : ((d : K) → Ans d.val) → Table := fun g => extendTable K (completeTable c g)
  let wI : Table → Prop := fun G => (stmtAt decI (gLogA T stR PR E G) t.val).isSome
  let wR : Table → Prop := fun G => (stmtAt decR (gLogA T stR PR E G) t.val).isSome
  have hdis : Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wI (X g)] +
      Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wR (X g)] ≤ 1 :=
    prEvent_add_le_one_of_disjoint _ _ _ fun g h h' => stmtAt_sep decI decR hsep _ _ h h'
  let A : Table → Prop := fun G => chainBadA T stI decI sysI PI E N t.val G ∧ wI G
  let B : Table → Prop := fun G => combBadA T stR decR PR E sysL witL dst N t.val G
  have hA : Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[A (X g)] ≤
      Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wI (X g)] * chainEps stI₀ chal3Blocks n N t.val.1 :=
    prEvent_cell_le_mul K c t hc A wI _
      (fun G _ => (prEvent_mono _ _ _ fun _ h => h.1).trans
        (prEvent_chainBadA_le T stI decI sysI PI E hT stI₀ hparamsI hn N t.val G))
      (fun G u hw h => hw (by
        have h2 := h.2
        simp only [wI, gLogA] at h2 ⊢
        rwa [stmtAt_update] at h2))
  unfold jointBad combAdaptBad jointEps
  refine (prEvent_mono _ _ (fun g => (A (X g) ∨ B (X g)) ∨
    (chainHitL (some (M, dst)) (tableQueryLog (gameA T stR PR E)) t.val (X g) ∨
      stmtHit (tableQueryLog (gameA T stR PR E)) t.val (X g))) fun g h => ?_).trans ?_
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine (prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)))
  · obtain ⟨⟨k, x⟩, hx⟩ := t
    by_cases hk : k = .h22
    · subst hk
      have hB := prEvent_combBadA_h22_le_mul T stR decR PR E sysL witL dst N hn' hεc K hK hx c hc
        hcard
      simp only [ite_true]
      calc _ ≤ Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wI (X g)] *
              chainEps stI₀ chal3Blocks n N .h22 +
            ((ntot : ℝ≥0∞) / 2 ^ 448 + Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wR (X g)] *
              (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc)) := add_le_add hA hB
        _ = (Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wI (X g)] *
              chainEps stI₀ chal3Blocks n N .h22 +
            Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wR (X g)] *
              (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc)) +
            (ntot : ℝ≥0∞) / 2 ^ 448 := by ring
        _ ≤ _ := add_le_add (mul_add_mul_le_max hdis) le_rfl
    · have hB : Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[B (X g)] ≤
          Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[wR (X g)] * chainEps stR₀ chal3Blocks 0 N k :=
        prEvent_cell_le_mul K c ⟨(k, x), hx⟩ hc B wR _
          (fun G _ => prEvent_combBadA_cell_le T stR decR PR E sysL witL dst hT stR₀ hparamsR N
            (k, x) hk G)
          (fun G u hw => not_combBadA_of_none T stR decR PR E sysL witL dst N (k, x) G hw u)
      simp only [hk, ite_false, add_zero]
      exact (add_le_add hA hB).trans (mul_add_mul_le_max hdis)
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => chainHitL (some (M, dst)) (tableQueryLog (gameA T stR PR E)) t.val
        (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_chainHitL_le _ (gameA T stR PR E) _ hq'' _ _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => stmtHit (tableQueryLog (gameA T stR PR E)) t.val (extendTable K G)) _
      fun G => ?_
    simp only [extendTable_update]
    exact prEvent_stmtHit_le (gameA T stR PR E) _ hq'' _ _

/-- The hit targets without combination are among those with it. -/
lemma mem_hitTargets_of_none {b : ByteArray} {pre : QueryLog spec} {k : Kind}
    (cb : Option (ℕ × ByteArray)) (h : b ∈ hitTargets none pre k) : b ∈ hitTargets cb pre k := by
  cases k with
  | h22 =>
    simp only [hitTargets, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · simp [combTargets] at h
  | _ =>
    simp only [hitTargets] at h ⊢
    exact h

/-- **At a query of the shared run, the two relations' games have the same log before it.** -/
lemma logBefore_gLogA_joint (g : Table) {t : Dom}
    (hsame : tableQueryLog (runE E PI) g = tableQueryLog (runE E PR) g)
    (ht : t ∈ (tableQueryLog (runE E PR) g).map Sigma.fst) :
    logBefore t (gLogA T stI PI E g) = logBefore t (gLogA T stR PR E g) := by
  unfold gLogA
  rw [tableQueryLog_gameA_eq, tableQueryLog_gameA_eq, logBefore_append_of_mem _ (hsame ▸ ht),
    logBefore_append_of_mem _ ht, hsame]

set_option maxRecDepth 4000 in
/-- **A bad query of the issue-type relation in the shared run is a joint bad query** (its hits
are hits with the combination targets too). -/
theorem jointBad_of_adaptBad (N : ℕ) (g : Table) {t : Dom}
    (hsame : tableQueryLog (runE E PI) g = tableQueryLog (runE E PR) g)
    (ht : t ∈ (tableQueryLog (runE E PR) g).map Sigma.fst)
    (h : adaptBad T stI decI sysI PI E N none t g) :
    jointBad T stI decI sysI PI stR decR PR E sysL witL dst N t g := by
  have hL := logBefore_gLogA_joint T stI PI stR PR E g hsame ht
  have hL' : logBefore t (tableQueryLog (gameA T stI PI E) g) =
      logBefore t (tableQueryLog (gameA T stR PR E) g) := hL
  rcases h with ⟨s, hs, hb⟩ | h | h
  · refine Or.inl ⟨⟨s, hs, hb⟩, ?_⟩
    rw [← stmtAt_congr decI hL]
    have hs' : stmtAt decI (gLogA T stI PI E g) t = some s := hs
    simp [hs']
  · refine Or.inr (Or.inr (Or.inl ?_))
    unfold chainHitL at h ⊢
    rw [← hL']
    exact mem_hitTargets_of_none _ h
  · refine Or.inr (Or.inr (Or.inr ?_))
    unfold stmtHit at h ⊢
    rw [← hL']
    exact h

end JointBad

end VoleMole.ROM.IC
