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

/-! ## The two relations together, per cipher table -/

section SimJointE

variable {ιI' ιR' α ιI βI ιR βR : Type} (T : CrtTables) (stI : ιI → Statement)
  (decI : ByteArray → Option ιI) (stR : ιR → Statement) (decR : ByteArray → Option ιR)
  (E : CTable)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for an issue-type and a combined relation together, per cipher
table.** Provers `PI j` (`j ∈ J_I`) of the first relation and `PR j` (`j ∈ J_R`) of the second,
whose runs are prefixes of reference runs `PI₀`, `PR₀` with the same hash log (`hsame`: one run of
the protocol, read as a prover of either relation), all within the budgets `q` and `nG`; the
relations' statements are separated (`hsep`: no `H₂⁰` input decodes in both families). If an
event implies at every table that some output of either relation is accepted at its statement and
not extracted, then

    Pr[event] ≤ Σ_k q_k·jointEps_k + Σ_{j ∈ J_I} Σ_k r_k·ε_I,k + Σ_{j ∈ J_R} Σ_k r_k·ε_R,k
      + Σ_{j ∈ J_I} Pr[fail_I,j] + Σ_{j ∈ J_R} Pr[fail_R,j],

each query of the run charged once (`jointEps`, about the larger of the two relations' charges),
each output's continuation at its relation's charge (`adaptEps`, `combAdaptEps`). Adding
`prEvent_sim_le_E` and `prEvent_sim_comb_le_E` charges each query of the run twice. -/
theorem prEvent_sim_joint_le_E (hT : liftInvOk T = true)
    (sysI : ιI → System GF128) (stI₀ : Statement) (hparamsI : ∀ s, (stI s).params = stI₀.params)
    (hdelI : ∀ s, (stI s).delayed = false) (hcombI : ∀ s, (stI s).comb = none)
    (hdecI : ∀ s, decI (muIn (stI s)) = some s) {n : ℕ} (hn : ∀ s, (sysI s).length = n)
    {M : ℕ} (sysL : ιR → (Fin M → GF128) → System GF128) (witL : ιR → (ℕ → GF128) → Prop)
    (dst : ByteArray) (stR₀ : Statement) (hparamsR : ∀ s, (stR s).params = stR₀.params)
    (hdelR : ∀ s, (stR s).delayed = false) (hcombR : ∀ s, (stR s).comb = some (M, dst))
    (hdecR : ∀ s, decR (muIn (stR s)) = some s) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (hsep : ∀ x, (decI x).isSome → (decR x).isSome → False) (N : ℕ)
    (WitI : ιI → ByteArray → (ℕ → GF128) → Prop)
    (hvalsI : ∀ s c1 lb w, (stI s).values c1 lb w = (sysI s).values w)
    (hdetI : ∀ s, @ChainDet (icPrg E.cipher) T (stI s) (sysI s) N (WitI s))
    (WitR : ιR → ByteArray → (ℕ → GF128) → Prop)
    (hvalsR : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stR s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdetR : ∀ s, @CombDet (icPrg E.cipher) M T (stR s) (sysL s) (witL s) N (WitR s))
    (PI₀ : OracleComp specIC (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (ιR × βR)))
    (cfI : Out ((ιI × βI) × QueryLog specIC) → Prop)
    (hcfI : ∀ j s g, ¬cfI (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stI s) (PI j) E)) →
      KeysPre (stI s) E (jOf g (PI j) E) (gLog T (stI s) (PI j) E g) g)
    (cfR : Out ((ιR × βR) × QueryLog specIC) → Prop)
    (hcfR : ∀ j s g, ¬cfR (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stR s) (PR j) E)) →
      KeysPre (stR s) E (jOf g (PR j) E) (gLog T (stR s) (PR j) E g) g)
    (JI : Finset ιI') (JR : Finset ιR') (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundIC (PI j) q) (hqR₀ : IsKindQueryBoundIC PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundIC (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : PrefixRuns E PI₀ PI JI) (hpreR : PrefixRuns E PR₀ PR JR)
    (hsame : ∀ g, tableQueryLog (runE E PI₀) g = tableQueryLog (runE E PR₀) g)
    (oa : OracleComp spec α) (event : α → Prop)
    (htr : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stI (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stI (stOut r)) (WitI (stOut r)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stR (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stR (stOut r)) (WitR (stOut r)) r)) :
    let nn := q + extractorQueries + verifierQueries
    let ntot := nG + 2 + verifierTotal
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
      ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
      ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k +
      ∑ j ∈ JI, Pr{let r ← (simulateQ randomOracle (gameA T stI (PI j) E)).run' ∅}[
        bindFailA stI E r ∨ deadOpenA stI E r ∨ cfI r] +
      ∑ j ∈ JR, Pr{let r ← (simulateQ randomOracle (gameA T stR (PR j) E)).run' ∅}[
        bindFailA stR E r ∨ deadOpenA stR E r ∨ cfR r] := by
  classical
  intro nn ntot
  let εJ := jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn
  let εI := adaptEps stI₀ n N none nn
  let εR := combAdaptEps (M := M) dst stR₀ n' εc ntot N nn
  let S := simKeys T stI E PI₀ PI oa JI ∪ simKeys T stR E PR₀ PR oa JR ∪
    Finset.univ.image (combKey M dst)
  have hKS : ∀ u, combKey M dst u ∈ S := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hsubI : ∀ d, d ∈ simKeys T stI E PI₀ PI oa JI → d ∈ S := fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hsubR : ∀ d, d ∈ simKeys T stR E PR₀ PR oa JR → d ∈ S := fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_right _ h)
  let : SampleableType ((d : S) → Ans d.val) := SampleableType.piOfFintype _
  have hbadI : ∀ Q : OracleComp specIC (ByteArray × (ιI × βI)), IsKindQueryBoundIC Q q →
      ∀ (c : (ofFn fun d : S => Ans d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < ntot →
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
        adaptBad T stI decI sysI Q E N none t.val (extendTable S (completeTable c g))] ≤
        εI t.val.1 := fun Q hQ c t hc _ =>
    cached_of_cell S (adaptBad T stI decI sysI Q E N none) (fun t => εI t.1)
      (fun t g => prEvent_adaptBad_le T stI decI sysI Q E hT stI₀ hparamsI hn N none q hQ t g) c t hc
  have hbadR : ∀ Q : OracleComp specIC (ByteArray × (ιR × βR)), IsKindQueryBoundIC Q q →
      ∀ (c : (ofFn fun d : S => Ans d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < ntot →
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[combAdaptBad T stR decR Q E sysL witL dst N
        t.val (extendTable S (completeTable c g))] ≤ εR t.val.1 := fun Q hQ c t hc hcard =>
    prEvent_combAdaptBad_le T stR decR Q E sysL witL dst hT stR₀ hparamsR hn' hεc N q hQ S hKS ntot
      c t hc hcard
  have hbadJ : ∀ (c : (ofFn fun d : S => Ans d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < ntot →
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[jointBad T stI decI sysI PI₀ stR decR PR₀ E sysL witL
        dst N t.val (extendTable S (completeTable c g))] ≤ εJ t.val.1 := fun c t hc hcard =>
    prEvent_jointBad_le T stI decI sysI PI₀ stR decR PR₀ E sysL witL dst hT stI₀ hparamsI hn stR₀
      hparamsR hn' hεc hsep N q hqR₀ S hKS ntot c t hc hcard
  refine prEvent_le_shared_suffix₂ S oa event ((simKeys_oa T stI E PI₀ PI oa JI).mono hsubI)
    (runE E PR₀) ((simKeys_run T stR E PR₀ PR oa JR).mono hsubR) (fun t => εJ t.1) _
    (worstCaseCostBound_of_kindQueryBound _ adaptKinds εJ
      (jointEps_eq_zero dst stI₀ stR₀ n n' εc ntot N nn) q (isKindQueryBound_runE E hqR₀)) nG
    (isTotalQueryBound_runE E hnGR₀)
    (jointBad T stI decI sysI PI₀ stR decR PR₀ E sysL witL dst N)
    JI (fun j => runE E (PI j)) (fun _ => gameK T stI E id) (fun j hj => ?_) (fun t => εI t.1) _
    (fun _ a => worstCaseCostBound_of_kindQueryBound _ adaptKinds εI
      (adaptEps_eq_zero stI₀ n N none nn) _ (isKindQueryBound_gameK T stI E id a))
    nG (2 + verifierTotal) (fun j hj => isTotalQueryBound_runE E (hnGI j hj))
    (fun _ a => isTotalQueryBound_gameK T stI E id a)
    (fun j => adaptBad T stI decI sysI (PI j) E N none)
    JR (fun j => runE E (PR j)) (fun _ => gameK T stR E id) (fun j hj => ?_) (fun t => εR t.1) _
    (fun _ a => worstCaseCostBound_of_kindQueryBound _ adaptKinds εR
      (combAdaptEps_eq_zero dst stR₀ n' εc ntot N nn) _ (isKindQueryBound_gameK T stR E id a))
    nG (2 + verifierTotal) (fun j hj => isTotalQueryBound_runE E (hnGR j hj))
    (fun _ a => isTotalQueryBound_gameK T stR E id a)
    (fun j => combAdaptBad T stR decR (PR j) E sysL witL dst N)
    JI (fun j => gameA T stI (PI j) E) (fun _ r => bindFailA stI E r ∨ deadOpenA stI E r ∨ cfI r)
    (fun j hj => (simKeys_game T stI E PI₀ PI oa JI j hj).mono hsubI)
    JR (fun j => gameA T stR (PR j) E) (fun _ r => bindFailA stR E r ∨ deadOpenA stR E r ∨ cfR r)
    (fun j hj => (simKeys_game T stR E PR₀ PR oa JR j hj).mono hsubR)
    ntot (by omega) (by omega) (by omega) hbadJ (fun j hj => hbadI (PI j) (hqI j hj))
    (fun j hj => hbadR (PR j) (hqR j hj)) fun g hev => ?_
  · rw [← gameA_eq_bind]
    exact (simKeys_game T stI E PI₀ PI oa JI j hj).mono hsubI
  · rw [← gameA_eq_bind]
    exact (simKeys_game T stR E PR₀ PR oa JR j hj).mono hsubR
  rcases htr g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
  · -- an output of the issue-type relation
    by_cases hf : bindFailA stI E (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stI (PI j) E)) ∨ deadOpenA stI E (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stI (PI j) E)) ∨ cfI (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stI (PI j) E))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, hf⟩)))
    simp only [not_or] at hf
    obtain ⟨e, he, hb⟩ := adaptBad_trace T stI decI sysI (PI j) E hT hdelI none hcombI hdecI N WitI
      hvalsI hdetI cfI (hcfI j) g ⟨⟨hacc, hnex⟩, hf.1, hf.2.1, hf.2.2⟩
    rw [tableQueryLog_gameA_eq] at he
    by_cases hm : e.1 ∈ (tableQueryLog (runE E (PI j)) g).map Sigma.fst
    · obtain ⟨⟨Y, hY⟩, hJ⟩ := hpreI j hj g
      have hm₀ : e.1 ∈ (tableQueryLog (runE E PI₀) g).map Sigma.fst := by
        rw [hY, List.map_append]; exact List.mem_append_left _ hm
      have hmR : e.1 ∈ (tableQueryLog (runE E PR₀) g).map Sigma.fst := hsame g ▸ hm₀
      obtain ⟨e', he', heq⟩ := List.mem_map.1 hmR
      refine Or.inl ⟨e', he', ?_⟩
      rw [heq]
      exact jointBad_of_adaptBad T stI decI sysI PI₀ stR decR PR₀ E sysL witL dst N g (hsame g) hmR
        ((adaptBad_prefix_congr T stI decI E sysI (PI j) PI₀ N none g e.1 hm ⟨Y, hY⟩ hJ).1 hb)
    · refine Or.inr (Or.inl ⟨j, hj, e, ?_, hm, hb⟩)
      exact (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h)
  · -- an output of the combined relation
    by_cases hf : bindFailA stR E (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stR (PR j) E)) ∨ deadOpenA stR E (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stR (PR j) E)) ∨ cfR (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stR (PR j) E))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, hf⟩)))
    simp only [not_or] at hf
    obtain ⟨e, he, hb⟩ := combAdaptBad_trace T stR decR (PR j) E sysL witL dst hT hdelR hcombR
      hdecR N WitR hvalsR hdetR cfR (hcfR j) g ⟨⟨hacc, hnex⟩, hf.1, hf.2.1, hf.2.2⟩
    rw [tableQueryLog_gameA_eq] at he
    by_cases hm : e.1 ∈ (tableQueryLog (runE E (PR j)) g).map Sigma.fst
    · obtain ⟨⟨Y, hY⟩, hJ⟩ := hpreR j hj g
      have hm₀ : e.1 ∈ (tableQueryLog (runE E PR₀) g).map Sigma.fst := by
        rw [hY, List.map_append]; exact List.mem_append_left _ hm
      obtain ⟨e', he', heq⟩ := List.mem_map.1 hm₀
      refine Or.inl ⟨e', he', ?_⟩
      rw [heq]
      exact Or.inr ((combAdaptBad_prefix_congr T stR decR E sysL witL dst (PR j) PR₀ N g e.1 hm
        ⟨Y, hY⟩ hJ).1 hb)
    · refine Or.inr (Or.inr (Or.inl ⟨j, hj, e, ?_, hm, hb⟩))
      exact (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h)

end SimJointE

/-! ## The joint experiment -/

section SimJoint

variable {ιI' ιR' α ιI βI ιR βR : Type}

/-- **Averaging a per-cipher-table bound with two families of per-output failure terms.** -/
theorem prEvent_avg_le_sum3₂ {C X Y Y' : Type} (mE : ProbComp C) (m : C → ProbComp X) (ev : C → X → Prop)
    (c : ℝ≥0∞) (J : Finset ιI') (m' : ιI' → C → ProbComp Y) (Q₁ Q₂ Q₃ : C → Y → Prop)
    (J' : Finset ιR') (m'' : ιR' → C → ProbComp Y') (Q₁' Q₂' Q₃' : C → Y' → Prop)
    (h : ∀ E, Pr{let r ← m E}[ev E r] ≤
      c + ∑ j ∈ J, Pr{let r ← m' j E}[Q₁ E r ∨ Q₂ E r ∨ Q₃ E r] +
        ∑ j ∈ J', Pr{let r ← m'' j E}[Q₁' E r ∨ Q₂' E r ∨ Q₃' E r]) :
    Pr{let E ← mE; let r ← m E}[ev E r] ≤
      c + ∑ j ∈ J, (Pr{let E ← mE; let r ← m' j E}[Q₁ E r] +
        Pr{let E ← mE; let r ← m' j E}[Q₂ E r] +
        Pr{let E ← mE; let r ← m' j E}[Q₃ E r]) +
      ∑ j ∈ J', (Pr{let E ← mE; let r ← m'' j E}[Q₁' E r] +
        Pr{let E ← mE; let r ← m'' j E}[Q₂' E r] +
        Pr{let E ← mE; let r ← m'' j E}[Q₃' E r]) := by
  let : MeasurableSpace C := ⊤
  have h3 : ∀ {Z : Type} (mz : ProbComp Z) (P₁ P₂ P₃ : Z → Prop),
      Pr{let r ← mz}[P₁ r ∨ P₂ r ∨ P₃ r] ≤
        Pr{let r ← mz}[P₁ r] + Pr{let r ← mz}[P₂ r] + Pr{let r ← mz}[P₃ r] :=
    fun mz _ _ _ => (prEvent_or_le _ _ _).trans (by
      rw [add_assoc]; exact add_le_add le_rfl (prEvent_or_le _ _ _))
  rw [prEvent_bind_of_discrete]
  simp only [prEvent_bind_of_discrete]
  calc ∫⁻ E, Pr{let r ← m E}[ev E r] ∂𝒟[mE]
      ≤ ∫⁻ E, (c + ∑ j ∈ J, (Pr{let r ← m' j E}[Q₁ E r] + Pr{let r ← m' j E}[Q₂ E r] +
          Pr{let r ← m' j E}[Q₃ E r]) + ∑ j ∈ J', (Pr{let r ← m'' j E}[Q₁' E r] +
          Pr{let r ← m'' j E}[Q₂' E r] + Pr{let r ← m'' j E}[Q₃' E r])) ∂𝒟[mE] :=
        MeasureTheory.lintegral_mono fun E => (h E).trans
          (add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun j _ => h3 _ _ _ _))
            (Finset.sum_le_sum fun j _ => h3 _ _ _ _))
    _ = c * 𝒟[mE] Set.univ + ∑ j ∈ J, (∫⁻ E, Pr{let r ← m' j E}[Q₁ E r] ∂𝒟[mE] +
          ∫⁻ E, Pr{let r ← m' j E}[Q₂ E r] ∂𝒟[mE] +
          ∫⁻ E, Pr{let r ← m' j E}[Q₃ E r] ∂𝒟[mE]) +
        ∑ j ∈ J', (∫⁻ E, Pr{let r ← m'' j E}[Q₁' E r] ∂𝒟[mE] +
          ∫⁻ E, Pr{let r ← m'' j E}[Q₂' E r] ∂𝒟[mE] +
          ∫⁻ E, Pr{let r ← m'' j E}[Q₃' E r] ∂𝒟[mE]) := by
        rw [MeasureTheory.lintegral_add_right _ (Finset.measurable_sum _ fun _ _ =>
            measurable_from_top),
          MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top,
          MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top]
        rw [add_assoc, add_assoc]
        refine congrArg _ (congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
          (Finset.sum_congr rfl fun j _ => ?_))
        · rw [MeasureTheory.lintegral_add_left measurable_from_top,
            MeasureTheory.lintegral_add_left measurable_from_top]
        · rw [MeasureTheory.lintegral_add_left measurable_from_top,
            MeasureTheory.lintegral_add_left measurable_from_top]
    _ ≤ _ := add_le_add (add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
          le_rfl) le_rfl


set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for an issue-type and a combined relation together, in the joint
experiment**: `prEvent_sim_joint_le_E` averaged over the cipher table, with `cf` = Post and each
output's failure terms bounded by `failEps`. -/
theorem prEvent_sim_joint_le (T : CrtTables) (hT : liftInvOk T = true)
    (stI : ιI → Statement) (decI : ByteArray → Option ιI)
    (sysI : ιI → System GF128) (stI₀ : Statement) (hparamsI : ∀ s, (stI s).params = stI₀.params)
    (hdelI : ∀ s, (stI s).delayed = false) (hcombI : ∀ s, (stI s).comb = none)
    (hdecI : ∀ s, decI (muIn (stI s)) = some s) {n : ℕ} (hn : ∀ s, (sysI s).length = n)
    (stR : ιR → Statement) (decR : ByteArray → Option ιR)
    {M : ℕ} (sysL : ιR → (Fin M → GF128) → System GF128) (witL : ιR → (ℕ → GF128) → Prop)
    (dst : ByteArray) (stR₀ : Statement) (hparamsR : ∀ s, (stR s).params = stR₀.params)
    (hdelR : ∀ s, (stR s).delayed = false) (hcombR : ∀ s, (stR s).comb = some (M, dst))
    (hdecR : ∀ s, decR (muIn (stR s)) = some s) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (hsep : ∀ x, (decI x).isSome → (decR x).isSome → False) (N : ℕ)
    (WitI : ιI → ByteArray → (ℕ → GF128) → Prop)
    (hvalsI : ∀ s c1 lb w, (stI s).values c1 lb w = (sysI s).values w)
    (hdetI : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stI s) (sysI s) N (WitI s))
    (WitR : ιR → ByteArray → (ℕ → GF128) → Prop)
    (hvalsR : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stR s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdetR : ∀ (E : CTable) s, @CombDet (icPrg E.cipher) M T (stR s) (sysL s) (witL s) N (WitR s))
    (PI₀ : OracleComp specIC (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (ιR × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundIC (PI j) q) (hqR₀ : IsKindQueryBoundIC PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundIC (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ E, PrefixRuns E PI₀ PI JI) (hpreR : ∀ E, PrefixRuns E PR₀ PR JR)
    (hsame : ∀ E g, tableQueryLog (runE E PI₀) g = tableQueryLog (runE E PR₀) g)
    (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stI (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stI (stOut r)) (WitI (stOut r)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stR (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stR (stOut r)) (WitR (stOut r)) r)) :
    let nn := q + extractorQueries + verifierQueries
    let ntot := nG + 2 + verifierTotal
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
      ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
      ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k +
      JI.card * failEps q qE + JR.card * failEps q qE := by
  intro nn ntot
  refine (prEvent_avg_le_sum3₂ ($ᵗ CTable) _ _ (∑ k ∈ adaptKinds, (q k : ℝ≥0∞) *
      jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
    ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
      ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
    ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
      combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k) JI (fun j E => (simulateQ randomOracle
    (gameA T stI (PI j) E)).run' ∅) (fun E r => bindFailA stI E r)
    (fun E r => deadOpenA stI E r) (fun E r => PostOut E r) JR (fun j E => (simulateQ randomOracle
    (gameA T stR (PR j) E)).run' ∅) (fun E r => bindFailA stR E r)
    (fun E r => deadOpenA stR E r) (fun E r => PostOut E r) fun E =>
      prEvent_sim_joint_le_E T stI decI stR decR E hT sysI stI₀ hparamsI hdelI hcombI hdecI
      hn sysL witL dst stR₀ hparamsR hdelR hcombR hdecR hn' hεc hsep N WitI hvalsI (hdetI E) WitR
      hvalsR (hdetR E) PI₀ PI PR₀ PR (fun r => PostOut E r)
      (fun j s g h => keysPre_of_not_postOut T (stI s) (PI j) E g h) (fun r => PostOut E r)
      (fun j s g h => keysPre_of_not_postOut T (stR s) (PR j) E g h) JI JR q hqI hqR₀ hqR nG hnGI
      hnGR₀ hnGR (hpreI E) (hpreR E) (hsame E) (oa E) (event E) (htr E)).trans ?_
  rw [add_assoc _ (∑ j ∈ JI, _) (∑ j ∈ JR, _), add_assoc _ ((JI.card : ℝ≥0∞) * _)]
  exact add_le_add le_rfl (add_le_add (sum_fail_le T stI stI₀.params hparamsI PI JI qE hqEI q hqI)
    (sum_fail_le T stR stR₀.params hparamsR PR JR qE hqER q hqR))

/-! ## The terms -/

/-- A per-query charge dominating the two relations' and the joint one: `κ` at `H₂¹`,
`ε₂ + ntot·2⁻⁴⁴⁸` at `H₂²`, `N·2⁻¹²⁸` at `H₂³`, the hits with the combination targets and the
statement hits. -/
noncomputable def jointMaxEps {M : ℕ} (dst : ByteArray) (κ ε₂ : ℝ≥0∞) (ntot N : ℕ)
    (nn : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  (if k = .h21 then κ else if k = .h22 then ε₂ + (ntot : ℝ≥0∞) / 2 ^ 448
    else if k = .h23 then (N : ℝ≥0∞) / 2 ^ 128 else 0) +
  (hitEps nn (combCount (some (M, dst)) nn) k + stmtEps nn k)

set_option exponentiation.threshold 1100 in
/-- **The joint charge, summed**: with `κ` bounding both relations' `ε_KOS` and `ε₂` both
relations' `H₂²` charges, the run's queries are charged once and each of the `m_I + m_R` outputs'
continuations once:

    (q₂₁ + m)·κ + (q₂₂ + m)·(ε₂ + ntot·2⁻⁴⁴⁸) + (q₂₃ + m)·N·2⁻¹²⁸ + chainHitEpsCombSim q M m
      + stmtBindEpsSim q m,   m = m_I + m_R. -/
theorem sim_joint_sum_le (stI₀ stR₀ : Statement) (n n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) {M : ℕ}
    (dst : ByteArray) (q : Kind → ℕ) (JI : Finset ιI') (JR : Finset ιR') (κ ε₂ : ℝ≥0∞)
    (hκI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ κ)
    (hκR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ κ)
    (h₂I : ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) ≤ ε₂)
    (h₂R : ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc ≤ ε₂) :
    let nn := q + extractorQueries + verifierQueries
    ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
      ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
      ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k ≤
      (q .h21 + (JI.card + JR.card)) * κ +
        (q .h22 + (JI.card + JR.card)) * (ε₂ + (ntot : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((N : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q M (JI.card + JR.card) + stmtBindEpsSim q (JI.card + JR.card) := by
  intro nn
  let Est := jointMaxEps (M := M) dst κ ε₂ ntot N nn
  have hhit : hitEps nn (combCount none nn) .h22 ≤ hitEps nn (combCount (some (M, dst)) nn) .h22 := by
    simp only [hitEps, combCount]
    gcongr
    omega
  have hJ : ∀ k, jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k ≤ Est k := by
    intro k
    cases k
    case h21 =>
      simp only [jointEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true, add_zero]
      gcongr
      exact sup_le hκI hκR
    case h22 =>
      simp only [jointEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
      exact sup_le h₂I h₂R
    case h23 =>
      simp only [jointEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true, add_zero,
        sup_idem, le_refl]
    all_goals simp [jointEps, Est, jointMaxEps, chainEps]
  have hI : ∀ k, adaptEps stI₀ n N none nn k ≤ Est k := by
    intro k
    cases k
    case h21 =>
      simp only [adaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
      · simp only [hitEps]; rfl
    case h22 =>
      simp only [adaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
      · exact h₂I.trans le_self_add
    case h23 =>
      simp only [adaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
      simp only [hitEps]; rfl
    all_goals simp [adaptEps, Est, jointMaxEps, chainEps, hitEps]
  have hR : ∀ k, combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k ≤ Est k := by
    intro k
    cases k
    case h21 =>
      simp only [combAdaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
    case h22 =>
      simp only [combAdaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true]
      gcongr
    case h23 =>
      simp only [combAdaptEps, Est, jointMaxEps, chainEps, reduceCtorEq, ite_false, ite_true,
        le_refl]
    all_goals simp [combAdaptEps, Est, jointMaxEps, chainEps]
  calc _ ≤ ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * Est k +
        ∑ _j ∈ JI, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * Est k +
        ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * Est k := by
        refine add_le_add (add_le_add (Finset.sum_le_sum fun k _ => ?_)
          (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun k _ => ?_))
          (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun k _ => ?_)
        · gcongr; exact hJ k
        · gcongr; exact hI k
        · gcongr; exact hR k
    _ = _ := by
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      simp only [adaptKinds, nn, Est, jointMaxEps]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [hitEps, stmtEps, combCount, chainHitEpsCombSim, chainHitEpsSim,
        stmtBindEpsSim, Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self,
        false_or, or_false, ↓reduceIte, add_zero, zero_add, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
      ring

end SimJoint

end VoleMole.ROM.IC
