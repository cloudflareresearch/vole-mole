import VoleMole.ROM.PermBind

/-!
# The permutation game, binding and `ε_open` (permutation model)

* **The game** `gameP T st P π`: the normalized prover `normP st.params π P` (forward-and-inverse
  queries of `P` recorded as forward records, N1's `H₄` queries) with the straight-line extractor
  of `ROM/CipherGame.lean` (it reads the records and the forward table `π.fwd`), then the verifier
  with the ideal-cipher PRG of `π.fwd`; the experiment draws `π` uniformly, then runs the game
  against the lazy hash oracle. Per permutation table this is `gameIC` for a forward prover, so
  every per-table lemma of `ROM/Cipher*.lean` applies; only the bounds averaged over the cipher are
  redone.
* **The bridge** `prEvent_jointP_le_add`: `prEvent_joint_le_add` with the permutation table.
* **Binding** (`prEvent_jointP_bindFail_le`): `Pr[bindFail] ≤ 2·q_E²·p² + Pr[DeadOpenOut]`,
  `p = 1/(2¹²⁸ − q_E)`, from `binds_or_coll_or_dead` (deterministic, at each table) and
  `prEvent_perm_coll_le`.
* **An opened dead leaf whose leaf hash `P` queried** (`prEvent_perm_deadQueried_le`): two fresh
  values of the dead key, protected inputs its records and the `2·2303` GGM points (the verifier's
  tree must not change), `≤ q₁·p'²` with `p' = 1/(2¹²⁸ − q_E − 4607)`.
* **`ε_open`** (`prEvent_jointP_deadOpen_le`): `≤ openHashEps q + q₁·p'²`.
-/

open Finset OracleComp OracleSpec
open MeasureTheory
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The joint experiment over permutation tables -/

section Eager

variable {X : Type}

lemma exists_allQueriesSatisfyP (m : PTable → OracleComp spec X) :
    ∃ S : Finset Dom, ∀ π, AllQueriesSatisfy (m π) (· ∈ S) := by
  have hfin : (⋃ π, (possibleQueryKeys (m π) : Set Dom)).Finite :=
    Set.finite_iUnion fun π => (possibleQueryKeys (m π)).finite_toSet
  refine ⟨hfin.toFinset, fun π => (allQueriesSatisfy_possibleQueryKeys (m π)).mono fun d hd => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_iUnion]
  exact ⟨π, hd⟩

/-- **The bridge for permutation tables** (`prEvent_joint_le_add`). -/
theorem prEvent_jointP_le_add (m : PTable → OracleComp spec X) (ev ev' : PTable → X → Prop)
    (c : ℝ≥0∞)
    (h : ∀ g : Table, Pr{let π ← $ᵗ PTable}[ev π (evalWithAnswerFn (QueryImpl.ofFn g) (m π))] ≤
      c + Pr{let π ← $ᵗ PTable}[ev' π (evalWithAnswerFn (QueryImpl.ofFn g) (m π))]) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ≤
      c + Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev' π r] := by
  classical
  obtain ⟨S, hS⟩ := exists_allQueriesSatisfyP m
  let _ : ∀ d : S, Fintype (Ans d.val) := fun _ => inferInstance
  let _ : SampleableType ((d : S) → Ans d.val) := SampleableType.ofFintype _
  let : MeasurableSpace PTable := ⊤
  let : MeasurableSpace ((d : S) → Ans d.val) := ⊤
  have hjoint : ∀ p : PTable → X → Prop,
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[p π r] =
        ∫⁻ g, Pr{let π ← $ᵗ PTable}[
          p π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := by
    intro p
    calc Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[p π r]
        = ∫⁻ π, Pr{let r ← (simulateQ randomOracle (m π)).run' ∅}[p π r] ∂𝒟[$ᵗ PTable] :=
          prEvent_bind_of_discrete _ _
      _ = ∫⁻ π, Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
            p π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))] ∂𝒟[$ᵗ PTable] :=
          lintegral_congr fun π => prEvent_randomOracle_eq_eager (m π) S (hS π) (p π)
      _ = Pr{let π ← $ᵗ PTable; let g ← $ᵗ ((d : S) → Ans d.val)}[
            p π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))] :=
          (prEvent_bind_of_discrete _ _).symm
      _ = Pr{let g ← $ᵗ ((d : S) → Ans d.val); let π ← $ᵗ PTable}[
            p π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))] :=
          prEvent_bind_map_swap _ _ _
      _ = _ := prEvent_bind_of_discrete _ _
  rw [hjoint ev, hjoint ev']
  calc ∫⁻ g, Pr{let π ← $ᵗ PTable}[
          ev π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)]
      ≤ ∫⁻ g, (c + Pr{let π ← $ᵗ PTable}[
          ev' π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))])
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := lintegral_mono fun g => h (extendTable S g)
    _ = c * 𝒟[$ᵗ ((d : S) → Ans d.val)] Set.univ + ∫⁻ g, Pr{let π ← $ᵗ PTable}[
          ev' π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl

/-- Averaging over the permutation table, three error terms. -/
theorem prEvent_avgP_le_add3 (m : PTable → ProbComp X) (ev e₁ e₂ e₃ : PTable → X → Prop)
    (c : ℝ≥0∞) (h : ∀ π, Pr{let r ← m π}[ev π r] ≤
      c + Pr{let r ← m π}[e₁ π r] + Pr{let r ← m π}[e₂ π r] + Pr{let r ← m π}[e₃ π r]) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[ev π r] ≤
      c + Pr{let π ← $ᵗ PTable; let r ← m π}[e₁ π r] +
        Pr{let π ← $ᵗ PTable; let r ← m π}[e₂ π r] +
        Pr{let π ← $ᵗ PTable; let r ← m π}[e₃ π r] := by
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete, prEvent_bind_of_discrete,
    prEvent_bind_of_discrete]
  calc ∫⁻ π, Pr{let r ← m π}[ev π r] ∂𝒟[$ᵗ PTable]
      ≤ ∫⁻ π, (c + Pr{let r ← m π}[e₁ π r] + Pr{let r ← m π}[e₂ π r] + Pr{let r ← m π}[e₃ π r])
          ∂𝒟[$ᵗ PTable] := lintegral_mono h
    _ = ∫⁻ π, (c + Pr{let r ← m π}[e₁ π r] + Pr{let r ← m π}[e₂ π r]) ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m π}[e₃ π r] ∂𝒟[$ᵗ PTable] := lintegral_add_left measurable_from_top _
    _ = ∫⁻ π, (c + Pr{let r ← m π}[e₁ π r]) ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m π}[e₂ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m π}[e₃ π r] ∂𝒟[$ᵗ PTable] := by
        rw [lintegral_add_left measurable_from_top _]
    _ = c * 𝒟[$ᵗ PTable] Set.univ + ∫⁻ π, Pr{let r ← m π}[e₁ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m π}[e₂ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m π}[e₃ π r] ∂𝒟[$ᵗ PTable] := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := add_le_add (add_le_add (add_le_add
        (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl) le_rfl) le_rfl

/-- Averaging a per-table bound over the permutation table. -/
theorem prEvent_avgP_le (m : PTable → ProbComp X) (ev : PTable → X → Prop) (c : ℝ≥0∞)
    (h : ∀ π, Pr{let r ← m π}[ev π r] ≤ c) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[ev π r] ≤ c := by
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete]
  calc ∫⁻ π, Pr{let r ← m π}[ev π r] ∂𝒟[$ᵗ PTable] ≤ ∫⁻ _π, c ∂𝒟[$ᵗ PTable] := lintegral_mono h
    _ = c * 𝒟[$ᵗ PTable] Set.univ := lintegral_const _
    _ ≤ c := mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

lemma prEvent_jointP_mono (m : PTable → ProbComp X) (p p' : PTable → X → Prop)
    (h : ∀ π r, p π r → p' π r) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[p π r] ≤ Pr{let π ← $ᵗ PTable; let r ← m π}[p' π r] := by
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact lintegral_mono fun π => prEvent_mono _ _ _ (h π)

lemma prEvent_jointP_or_le (m : PTable → ProbComp X) (p p' : PTable → X → Prop) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[p π r ∨ p' π r] ≤
      Pr{let π ← $ᵗ PTable; let r ← m π}[p π r] + Pr{let π ← $ᵗ PTable; let r ← m π}[p' π r] := by
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  calc ∫⁻ π, Pr{let r ← m π}[p π r ∨ p' π r] ∂𝒟[$ᵗ PTable]
      ≤ ∫⁻ π, (Pr{let r ← m π}[p π r] + Pr{let r ← m π}[p' π r]) ∂𝒟[$ᵗ PTable] :=
        lintegral_mono fun π => prEvent_or_le _ _ _
    _ = _ := lintegral_add_left measurable_from_top _

lemma prEvent_jointP_false (m : PTable → ProbComp X) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[(fun _ _ => False : PTable → X → Prop) π r] = 0 := by
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete]
  simp

end Eager

/-! ## The game -/

section Game

variable {β : Type}

/-- **The soundness game in the permutation model**: the normalized prover (forward and inverse
queries recorded, N1) with the straight-line extractor, then the verifier, at the permutation
table `π` (whose forward table the extractor and the verifier read). -/
def gameP (T : CrtTables) (st : Statement) (P : OracleComp specP (ByteArray × β)) (π : PTable) :
    OracleComp spec (Out (β × QueryLog specIC)) :=
  gameIC T st (normP st.params π P) π.fwd

/-- **Binding fails only by a collision or an opened dead leaf** (deterministic, at any tables and
for any forward prover; the pointwise step of `pr_bindFail_le_table`). -/
theorem bindFail_imp_ic (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
    (h : Table) (E : CTable)
    (hb : @bindFail (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E))) :
    freshBadC (runH h P) ∅ E collBad ∨
      DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E)) := by
  let _ : HasPrg := icPrg E.cipher
  obtain ⟨hacc, hnb⟩ := hb
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC] at hacc hnb ⊢
  set π := (evalWithAnswerFn (QueryImpl.ofFn (join h E)) P).1
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, -⟩ := verify_iv_chal1 _ T st π hacc hr
  rcases binds_or_coll_or_dead (runH h P) E (ivOf (Hashes.ofTable h) ⟨st.params, π⟩
      (st.mu1 (Hashes.ofTable h))) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) with hB | hC | hD
  · exact absurd (fun leaves' hr' => hB leaves' (hiv ▸ hr')) hnb
  · exact Or.inl hC
  · refine Or.inr ⟨hacc, ?_⟩
    show DeadOpen (cipherLog (tableQueryLog P (join h E))) E _ _ _
    rw [cipherLog_tableQueryLog, hiv]
    exact hD

/-- **Binding in the permutation model**: `Pr[bindFail] ≤ 2·q_E²·p² + Pr[DeadOpenOut]`, jointly. -/
theorem prEvent_jointP_bindFail_le (T : CrtTables) (st : Statement)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
        @bindFail (icPrg π.fwd.cipher) _ st r] ≤
      2 * qE ^ 2 * pE qE ^ 2 +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
          DeadOpenOut st π.fwd r] := by
  refine prEvent_jointP_le_add (gameP T st P) (fun π r => @bindFail (icPrg π.fwd.cipher) _ st r)
    (fun π r => DeadOpenOut st π.fwd r) _ fun g => ?_
  refine (prEvent_mono _ _ (fun π => freshBadC (runH g (normP st.params π P)) ∅ π.fwd collBad ∨
    DeadOpenOut st π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameP T st P π)))
    fun π hb => bindFail_imp_ic T st _ g π.fwd hb).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  exact prEvent_perm_coll_le st.params g P qE hqE

end Game

/-! ## A dead leaf whose leaf hash the prover queried -/

section Dead

variable {β : Type} (g : Table) (st : Statement) (P : OracleComp specP (ByteArray × β))

/-- The GGM points of `iv`: the blocks the verifier's tree derivation evaluates (tweaks `< L − 1`,
counters `0`, `1`). (Irreducible: a membership must not be evaluated.) -/
@[irreducible] def ggmPts (iv : ByteArray) : Finset Blk :=
  ((range (BAVC.numLeaves - 1)) ×ˢ (range 2)).image fun nc => gp iv nc.1 nc.2

lemma card_ggmPts_le (iv : ByteArray) : #(ggmPts iv) ≤ 4606 := by
  unfold ggmPts
  refine card_image_le.trans ?_
  rw [card_product, card_range, card_range]
  have hL : BAVC.numLeaves = 2304 := rfl
  rw [hL]

lemma gp_mem_ggmPts (iv : ByteArray) {n c : ℕ} (hn : n < BAVC.numLeaves - 1) (hc : c < 2) :
    gp iv n c ∈ ggmPts iv := by
  unfold ggmPts
  rw [mem_image]
  exact ⟨(n, c), by rw [mem_product, mem_range, mem_range]; exact ⟨hn, hc⟩, rfl⟩

-- The linter would evaluate the membership in the explicit range product.
set_option linter.constructorNameAsVariable false in
lemma mem_ggmPts {iv : ByteArray} {x : Blk} (h : x ∈ ggmPts iv) :
    ∃ n < BAVC.numLeaves - 1, ∃ c < 2, gp iv n c = x := by
  unfold ggmPts at h
  rw [mem_image] at h
  obtain ⟨⟨n, c⟩, hnc, he⟩ := h
  rw [mem_product, mem_range, mem_range] at hnc
  exact ⟨n, hnc.1, c, hnc.2, he⟩

/-- The normalized prover at `π`. -/
abbrev Wn (π : PTable) : OracleComp specIC (ByteArray × β) := normP st.params π P

end Dead

section DeadG

variable {β : Type} (g : Table) (p : Params) (stf : PTable → Statement)
  (P : OracleComp specP (ByteArray × β))

/-- The protected inputs of the dead key: its records and the GGM points. (Irreducible.) -/
@[irreducible] noncomputable def deadXg (σ : PTable) : Finset Blk :=
  keyIns (deadKey g (stf σ) (normP p σ P) σ.fwd) (jOf g (normP p σ P) σ.fwd) ∪
    ggmPts (ivE g (stf σ) (normP p σ P) σ.fwd)

lemma mem_deadXg {σ : PTable} {x : Blk} : x ∈ deadXg g p stf P σ ↔
    x ∈ keyIns (deadKey g (stf σ) (normP p σ P) σ.fwd) (jOf g (normP p σ P) σ.fwd) ∨
      x ∈ ggmPts (ivE g (stf σ) (normP p σ P) σ.fwd) := by
  unfold deadXg
  rw [mem_union]

lemma card_deadXg_le (σ : PTable) : #(deadXg g p stf P σ) ≤
    #(keyIns (deadKey g (stf σ) (normP p σ P) σ.fwd) (jOf g (normP p σ P) σ.fwd)) + 4606 := by
  unfold deadXg
  exact (card_union_le _ _).trans (add_le_add le_rfl (card_ggmPts_le _))

/-- **Changing the dead key's permutation off its protected inputs changes nothing else.** -/
theorem deadQueried_perm_inv_g
    (hstf : ∀ σ π : PTable, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (normP p π P) =
      evalWithAnswerFn (QueryImpl.ofFn (join g σ.fwd)) (normP p σ P) → stf π = stf σ)
    {σ π : PTable} (hE : ∃ p', DeadAt g (stf σ) (normP p σ P) σ.fwd p')
    (hoff : ∀ κ, κ ≠ deadKey g (stf σ) (normP p σ P) σ.fwd → π κ = σ κ)
    (hX : ∀ x ∈ deadXg g p stf P σ, π (deadKey g (stf σ) (normP p σ P) σ.fwd) x =
      σ (deadKey g (stf σ) (normP p σ P) σ.fwd) x) :
    deadKey g (stf π) (normP p π P) π.fwd = deadKey g (stf σ) (normP p σ P) σ.fwd ∧
      dc g (stf π) (normP p π P) π.fwd 0 = dc g (stf σ) (normP p σ P) σ.fwd 0 ∧
      dc g (stf π) (normP p π P) π.fwd 1 = dc g (stf σ) (normP p σ P) σ.fwd 1 ∧
      deadTargets g (stf π) (normP p π P) π.fwd = deadTargets g (stf σ) (normP p σ P) σ.fwd := by
  obtain ⟨hi, -, -, -⟩ := deadAt_deadPt g (stf σ) (normP p σ P) hE
  set k := deadKey g (stf σ) (normP p σ P) σ.fwd
  obtain ⟨hJ, hO⟩ := normP_congr p P g σ π fun c v hc => by
    rw [← answer_of_mem_jP p hc]
    by_cases hk : c.1 = k
    · have hx : c.2 ∈ deadXg g p stf P σ := by
        refine (mem_deadXg g p stf P).2 (Or.inl (mem_keyIns.2 ?_))
        rw [show (deadKey g (stf σ) (normP p σ P) σ.fwd, c.2) = c from Prod.ext hk.symm rfl]
        exact List.mem_map.2 ⟨_, hc, rfl⟩
      have := hX c.2 hx
      rw [← hk] at this
      exact this
    · rw [hoff c.1 hk]
  have hπ : πOf g (normP p π P) π.fwd = πOf g (normP p σ P) σ.fwd := congrArg Prod.fst hO
  have hJ' : jOf g (normP p π P) π.fwd = jOf g (normP p σ P) σ.fwd := hJ
  have hs : stf π = stf σ := hstf σ π hO
  rw [hs]
  have hiv : ivE g (stf σ) (normP p π P) π.fwd = ivE g (stf σ) (normP p σ P) σ.fwd := by
    simp only [ivE, hπ]
  have hrt : rtOf g (stf σ) (normP p π P) π.fwd = rtOf g (stf σ) (normP p σ P) σ.fwd := by
    unfold rtOf
    rw [hiv, hπ]
    refine recTree_ic_congr_cells fun k' n hn c hc => ?_
    show π k' _ = σ k' _
    by_cases hk : k' = k
    · subst hk
      exact hX _ ((mem_deadXg g p stf P).2 (Or.inr (gp_mem_ggmPts _ hn hc)))
    · rw [hoff k' hk]
  have hdead : DeadAt g (stf σ) (normP p π P) π.fwd = DeadAt g (stf σ) (normP p σ P) σ.fwd := by
    funext p'
    simp only [DeadAt, hπ, hJ', hiv, hrt]
  have hpt : deadPt g (stf σ) (normP p π P) π.fwd = deadPt g (stf σ) (normP p σ P) σ.fwd := by
    simp only [deadPt, hdead]
  have hkey : deadKey g (stf σ) (normP p π P) π.fwd = k := by simp only [k, deadKey, hrt, hpt]
  refine ⟨hkey, ?_, ?_, ?_⟩
  · simp only [dc, hkey, hiv, hpt, k]
  · simp only [dc, hkey, hiv, hpt, k]
  · simp only [deadTargets, hJ', hpt]

/-- **A dead leaf whose leaf hash `P` queried, in the permutation model**: `≤ q₁·p'²` with
`p' = 1/(2¹²⁸ − q_E − 4607)`, at every hash table, for a statement `stf π` that only depends on the
normalized prover's output. -/
theorem prEvent_perm_deadQueried_le_g
    (hstf : ∀ σ π : PTable, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (normP p π P) =
      evalWithAnswerFn (QueryImpl.ofFn (join g σ.fwd)) (normP p σ P) → stf π = stf σ) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable}[DeadQueried g (stf π) (normP p π P) π.fwd] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
  classical
  let kk : PTable → Blk := fun σ => deadKey g (stf σ) (normP p σ P) σ.fwd
  let TT : PTable → Finset (Blk × Blk × Blk × Blk) := fun σ =>
    (deadTargets g (stf σ) (normP p σ P) σ.fwd).image fun t =>
      ((dc g (stf σ) (normP p σ P) σ.fwd 0).2, (dc g (stf σ) (normP p σ P) σ.fwd 1).2, t.1, t.2)
  let ev : Blk × Blk × Blk × Blk → PTable → Prop := fun j σ =>
    DeadQueried g (stf σ) (normP p σ P) σ.fwd ∧ j ∈ TT σ ∧ σ (kk σ) j.1 = j.2.2.1 ∧
      σ (kk σ) j.2.1 = j.2.2.2
  have hmemT : ∀ σ j, j ∈ TT σ → j.1 = (dc g (stf σ) (normP p σ P) σ.fwd 0).2 ∧
      j.2.1 = (dc g (stf σ) (normP p σ P) σ.fwd 1).2 := by
    intro σ j hj
    obtain ⟨t, -, rfl⟩ := mem_image.1 hj
    exact ⟨rfl, rfl⟩
  refine (prEvent_mono _ _ (fun π => ∃ j, ev j π) ?_).trans
    ((prEvent_perm_two_le ev kk (deadXg g p stf P) TT (fun j => j.1) (fun j => j.2.1)
      (fun j => j.2.2.1) (fun j => j.2.2.2) (q .h1) (qE + 4606) ?_ ?_ ?_ ?_).trans ?_)
  · intro π hD
    have hm := deadQueried_mem g (stf π) (normP p π P) hD
    refine ⟨((dc g (stf π) (normP p π P) π.fwd 0).2, (dc g (stf π) (normP p π P) π.fwd 1).2,
      π.fwd (dc g (stf π) (normP p π P) π.fwd 0), π.fwd (dc g (stf π) (normP p π P) π.fwd 1)), hD,
      mem_image.2 ⟨_, hm, rfl⟩, rfl, rfl⟩
  · rintro j σ ⟨hD, hj, h1, h2⟩
    obtain ⟨hj1, hj2⟩ := hmemT σ j hj
    obtain ⟨hi, -, -, hnc⟩ := deadAt_deadPt g (stf σ) (normP p σ P) hD.2
    refine ⟨hj, ?_, ?_, ?_, h1, h2⟩
    · rw [hj1, hj2, dc_snd, dc_snd]
      exact lp_ne _ _
    · rw [hj1, dc_snd]
      intro hx
      rcases (mem_deadXg g p stf P).1 hx with hx | hx
      · rw [mem_keyIns, ← mem_cipherLog] at hx
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
        exact hnc ⟨e, he, Or.inl he1⟩
      · obtain ⟨n, hn, c, -, he⟩ := mem_ggmPts hx
        exact lp_ne_gp _ 0 c hi hn he.symm
    · rw [hj2, dc_snd]
      intro hx
      rcases (mem_deadXg g p stf P).1 hx with hx | hx
      · rw [mem_keyIns, ← mem_cipherLog] at hx
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
        exact hnc ⟨e, he, Or.inr he1⟩
      · obtain ⟨n, hn, c, -, he⟩ := mem_ggmPts hx
        exact lp_ne_gp _ 1 c hi hn he.symm
  · rintro j σ ⟨hD, -⟩ π hoff hX
    obtain ⟨hk, h0, h1, hT⟩ := deadQueried_perm_inv_g g p stf P hstf hD.2 hoff hX
    refine ⟨hk, ?_⟩
    simp only [TT, h0, h1, hT]
  · intro σ
    refine (card_deadXg_le g p stf P σ).trans (add_le_add ((card_keyIns_le _ _).trans ?_) le_rfl)
    exact length_cipherLog_le _ (isQueryBoundP_right_normP p σ hqE) _
  · intro σ
    refine card_image_le.trans ((List.toFinset_card_le _).trans ?_)
    rw [List.length_map]
    have := length_kindIns_hashLog_le _ (isKindQueryBound_normP p σ hq) (join g σ.fwd) .h1
    rwa [addH4_of_ne q (by decide)] at this
  · gcongr
    exact inv_two_le_pE _

end DeadG

section Dead2

variable {β : Type} (g : Table) (st : Statement) (P : OracleComp specP (ByteArray × β))

/-- **A dead leaf whose leaf hash `P` queried, in the permutation model** (fixed statement):
`≤ q₁·p'²`, `p' = 1/(2¹²⁸ − q_E − 4607)`, at every hash table. -/
theorem prEvent_perm_deadQueried_le (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable}[DeadQueried g st (Wn st P π) π.fwd] ≤
      q .h1 * pE (qE + 4607) ^ 2 :=
  prEvent_perm_deadQueried_le_g g st.params (fun _ => st) P (fun _ _ _ => rfl) qE hqE q hq

/-! ## `ε_open` -/

lemma openHashEps_addH4 (q : Kind → ℕ) : openHashEps (addH4 q) = openHashEps q := by
  simp [openHashEps, ladderEps, addH4]

/-- **`ε_open` in the permutation model**: an accepted proof opens a dead leaf with probability at
most `openHashEps q + q₁·p'²`, `p' = 1/(2¹²⁸ − q_E − 4607)`. -/
theorem prEvent_jointP_deadOpen_le (T : CrtTables) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
        DeadOpenOut st π.fwd r] ≤ openHashEps q + q .h1 * pE (qE + 4607) ^ 2 := by
  let m : PTable → ProbComp (Out (β × QueryLog specIC)) := fun π =>
    (simulateQ randomOracle (gameP T st P π)).run' ∅
  let A : PTable → Out (β × QueryLog specIC) → Prop := fun π r =>
    r.2.2.accept = true ∧ @LeafUnqueried (icPrg π.fwd.cipher) _ st (hashLog r.2.1.aux.2) r
  have h1 : Pr{let π ← $ᵗ PTable; let r ← m π}[A π r] ≤ openHashEps q := by
    refine prEvent_avgP_le m A _ fun π => ?_
    have := prEvent_leafUnqueried_ic_le T st (Wn st P π) (addH4 q)
      (isKindQueryBound_normP st.params π hq) π.fwd
    rwa [openHashEps_addH4] at this
  have h2 : Pr{let π ← $ᵗ PTable; let r ← m π}[DeadOpenOut st π.fwd r ∧ ¬A π r] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
    have h := prEvent_jointP_le_add (gameP T st P) (fun π r => DeadOpenOut st π.fwd r ∧ ¬A π r)
      (fun _ _ => False) (q .h1 * pE (qE + 4607) ^ 2) fun g' =>
        ((prEvent_mono _ _ _ fun π h => deadQueried_of_deadOpen T st (Wn st P π) g' π.fwd h.1
          fun hL => h.2 ⟨h.1.1, hL⟩).trans
          (prEvent_perm_deadQueried_le g' st P qE hqE q hq)).trans le_self_add
    rwa [prEvent_jointP_false, add_zero] at h
  calc Pr{let π ← $ᵗ PTable; let r ← m π}[DeadOpenOut st π.fwd r]
      ≤ Pr{let π ← $ᵗ PTable; let r ← m π}[A π r ∨ (DeadOpenOut st π.fwd r ∧ ¬A π r)] :=
        prEvent_jointP_mono m _ _ fun π r h => (em (A π r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_jointP_or_le m _ _).trans (add_le_add h1 h2)

end Dead2

end VoleMole.ROM.IC
