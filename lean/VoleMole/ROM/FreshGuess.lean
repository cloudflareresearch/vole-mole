import VoleMole.ROM.CipherGame
import VoleMole.ROM.Queried

/-!
# A fresh answer guessed (counting over the eager table)

VCVio's union bound (`prEvent_exists_bad_query_le`) charges a bad answer to **every** query of
the computation. When the event names one particular query, e.g. the verifier's last query
`H₂³(z)`, and that query is fresh (no earlier query of `z`) and its answer must hit a set of at
most `K` values fixed by everything else, the right bound is `K / |answers|`, not
`(number of queries) · K / |answers|`. That is proved here by counting.

* `finOf p`: the finite set of the elements with a property (irreducible, so that the elaborator
  never evaluates a membership in a set of tables).
* **`card_finOf_mul_le`** (abstract class counting): `up g i w` sets the cells `i` of `g` to `w`,
  `rd g i` reads them. If every event element `g` has valid cells `t g`, its value there in a set
  `T g` of at most `K` targets, and its class `{up g (t g) w}` keeps the cells and the targets, then
  `#{ev} · |W| ≤ K · |Ω|`. The classes of different cells are disjoint and each has `|W|`
  elements of which at most `K` are in the event. (Abstract, so that no cardinality of a
  `2¹²⁸`-element type enters an arithmetic step, which the kernel would evaluate.)
* **`prEvent_fresh_guess_le`**: for a computation against the lazy random oracle, if the event
  implies that a cell `t g` of a fixed kind `k₀` is queried, that `t` does not change when the
  table is updated at `t g`, and that at most `K` answers there keep the event, then
  `Pr[event] ≤ K / 2^{8·outLen k₀}` (the lazy oracle as a uniform table on a finite set of keys,
  `prEvent_randomOracle_eq_eager`, then the class counting with the cell `t` as the index).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

open VoleMole.Prob

/-- The finite set of the elements with a property. Irreducible: the elaborator must not evaluate
a membership in a set of `2²⁵⁶`-cell tables. -/
@[irreducible] noncomputable def finOf {α : Type} [Fintype α] (p : α → Prop) : Finset α := by
  classical exact univ.filter p

lemma mem_finOf {α : Type} [Fintype α] {p : α → Prop} {x : α} : x ∈ finOf p ↔ p x := by
  unfold finOf
  simp

lemma finOf_eq {α : Type} [Fintype α] (p : α → Prop) :
    finOf p = @Finset.filter _ p (Classical.decPred p) univ := by
  unfold finOf
  rfl

/-- **The class counting** (abstract): `up g i w` sets the cells `i` of `g` to `w` and `rd g i`
reads them. If every event table `g` has its cells `t g` valid, its value there in `T g` (at most
`K` targets), and its whole class `{up g (t g) w}` keeps the cells and the targets, then the event
tables are at most a `K / |W|` fraction. (Kept abstract so that no cardinality of a concrete
`2²⁵⁶`-element type ever enters an arithmetic step.) -/
theorem card_finOf_mul_le {Ω I W : Type} [Fintype Ω] [Fintype I] [Fintype W] [DecidableEq Ω]
    [DecidableEq I] (up : Ω → I → W → Ω) (rd : Ω → I → W) (valid : I → Prop)
    (h_up_up : ∀ g i w w', up (up g i w) i w' = up g i w') (h_up_rd : ∀ g i, up g i (rd g i) = g)
    (h_rd_up : ∀ g i w, valid i → rd (up g i w) i = w)
    (ev : Ω → Prop) (t : Ω → I) (T : Ω → Finset W) (K : ℕ) (hvalid : ∀ g, ev g → valid (t g))
    (hinv : ∀ g, ev g → ∀ w, t (up g (t g) w) = t g ∧ T (up g (t g) w) = T g)
    (hK : ∀ g, ev g → (T g).card ≤ K) (hev : ∀ g, ev g → rd g (t g) ∈ T g) :
    #(finOf ev) * Fintype.card W ≤ K * Fintype.card Ω := by
  let PB : I → Ω → Prop := fun i g => ∃ w, ev (up g i w) ∧ t (up g i w) = i
  let B : I → Finset Ω := fun i => finOf (PB i)
  let F : I → Finset Ω := fun i => finOf fun g => ev g ∧ t g = i
  -- The classes of different cells are disjoint.
  have hB : ∀ i g, g ∈ B i → t g = i := by
    intro i g hg
    obtain ⟨w, hw, hwt⟩ := mem_finOf.1 hg
    have := (hinv _ hw (rd g i)).1
    rw [hwt, h_up_up, h_up_rd] at this
    exact this
  have hdisj : ((univ : Finset I) : Set I).PairwiseDisjoint B := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun g hi hj => hij ?_
    exact (hB i g hi).symm.trans (hB j g hj)
  have hsumB : ∑ i, #(B i) ≤ Fintype.card Ω := by
    rw [← card_biUnion hdisj]
    exact card_le_univ _
  -- One class: at most `K` event tables per `|W|` tables.
  have hone : ∀ i, #(F i) * Fintype.card W ≤ K * #(B i) := by
    intro i
    rcases em (valid i) with hi | hi
    swap
    · have : F i = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.2 fun g hg => ?_
        obtain ⟨hg, htg⟩ := mem_finOf.1 hg
        exact hi (htg ▸ hvalid g hg)
      rw [this, card_empty, zero_mul]
      exact Nat.zero_le _
    let PX : Ω × W → Prop := fun p => ev (up p.1 i p.2) ∧ t (up p.1 i p.2) = i
    let X : Finset (Ω × W) := finOf PX
    have hFX : #(F i) * Fintype.card W = #X := by
      rw [← card_univ, ← card_product]
      refine (card_nbij' (fun p => (up p.1 i p.2, rd p.1 i)) (fun p => (up p.1 i p.2, rd p.1 i))
        ?_ ?_ ?_ ?_).symm
      · rintro ⟨g, w⟩ hp
        have hp := (mem_finOf (p := PX)).1 (mem_coe.1 hp)
        exact mem_coe.2 (mem_product.2 ⟨mem_finOf.2 hp, by simp only [mem_univ]⟩)
      · rintro ⟨g, w⟩ hp
        have hp := mem_finOf.1 (mem_product.1 (mem_coe.1 hp)).1
        refine mem_coe.2 ((mem_finOf (p := PX)).2 ?_)
        show ev (up (up g i w) i (rd g i)) ∧ t (up (up g i w) i (rd g i)) = i
        rw [h_up_up, h_up_rd]
        exact hp
      · rintro ⟨g, w⟩ -
        simp only [h_rd_up _ _ _ hi, h_up_up, h_up_rd]
      · rintro ⟨g, w⟩ -
        simp only [h_rd_up _ _ _ hi, h_up_up, h_up_rd]
    rw [hFX, card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ)
      (fun _ _ => mem_coe.2 (by simp only [mem_univ]))]
    calc ∑ g, #(X.filter fun p => p.1 = g) ≤ ∑ g, if g ∈ B i then K else 0 := by
          refine sum_le_sum fun g _ => ?_
          split_ifs with hg
          · obtain ⟨w₀, hw₀, hw₀t⟩ := mem_finOf.1 hg
            set g₀ := up g i w₀
            refine (card_le_card_of_injOn Prod.snd (fun p hp => ?_) ?_).trans (hK g₀ hw₀)
            · obtain ⟨hpX, hpg⟩ := mem_filter.1 (mem_coe.1 hp)
              obtain ⟨hev', ht'⟩ := (mem_finOf (p := PX)).1 hpX
              have hT := (hinv g₀ hw₀ p.2).2
              rw [hw₀t] at hT
              simp only [g₀, h_up_up] at hT
              have := hev _ hev'
              rw [ht', h_rd_up _ _ _ hi, hpg, hT] at this
              exact mem_coe.2 this
            · rintro ⟨g₁, w₁⟩ h₁ ⟨g₂, w₂⟩ h₂ he
              have e1 := (mem_filter.1 (mem_coe.1 h₁)).2
              have e2 := (mem_filter.1 (mem_coe.1 h₂)).2
              exact Prod.ext (e1.trans e2.symm) he
          · refine Nat.le_zero.2 (card_eq_zero.2 (Finset.eq_empty_iff_forall_notMem.2
              fun p hp => ?_))
            obtain ⟨hpX, hpg⟩ := mem_filter.1 hp
            subst hpg
            exact hg (mem_finOf.2 ⟨p.2, (mem_finOf (p := PX)).1 hpX⟩)
      _ = K * #(B i) := by
          rw [sum_ite_mem, univ_inter, sum_const, smul_eq_mul, mul_comm]
  -- Summing over the cells.
  have hS : finOf ev = (univ : Finset I).biUnion F := by
    ext g
    rw [mem_finOf, mem_biUnion]
    exact ⟨fun h => ⟨t g, by simp only [mem_univ], mem_finOf.2 ⟨h, rfl⟩⟩,
      fun ⟨_, _, h⟩ => (mem_finOf.1 h).1⟩
  have hFdisj : ((univ : Finset I) : Set I).PairwiseDisjoint F := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun g hi hj => hij ?_
    exact (mem_finOf.1 hi).2.symm.trans (mem_finOf.1 hj).2
  rw [hS, card_biUnion hFdisj, sum_mul]
  calc ∑ i, #(F i) * Fintype.card W ≤ ∑ i, K * #(B i) := sum_le_sum fun i _ => hone i
    _ = K * ∑ i, #(B i) := (mul_sum _ _ _).symm
    _ ≤ K * Fintype.card Ω := Nat.mul_le_mul_left _ hsumB

/-- Every logged query satisfies a predicate that all possible queries satisfy. -/
lemma allQueriesSatisfy_tableQueryLog {D α : Type} {R : D → Type} {oa : OracleComp (ofFn R) α}
    {P : D → Prop} (h : AllQueriesSatisfy oa P) (f : ∀ d, R d) :
    ∀ e ∈ tableQueryLog oa f, P e.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    intro e he
    rw [tableQueryLog_query_bind, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact ih (f t) (h.2 _) e he

section Guess

variable {α : Type}

lemma ans_eq {d : Dom} {k₀ : Kind} (h : d.1 = k₀) : Bytes k₀.outLen = Ans d := by
  rw [← h]

/-- Setting the cell `i` (if of kind `k₀`) of a restricted table to `w`. -/
def upK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) :
    Option S → Bytes k₀.outLen → (d : S) → Ans d.val
  | none, _ => g
  | some d, w => if h : d.val.1 = k₀ then Function.update g d (cast (ans_eq h) w) else g

/-- Reading the cell `i` (if of kind `k₀`). -/
def rdK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) : Option S → Bytes k₀.outLen
  | none => 0
  | some d => if h : d.val.1 = k₀ then cast (ans_eq h).symm (g d) else 0

lemma upK_upK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) (i : Option S)
    (w w' : Bytes k₀.outLen) : upK S k₀ (upK S k₀ g i w) i w' = upK S k₀ g i w' := by
  cases i with
  | none => rfl
  | some d =>
    simp only [upK]
    split_ifs with h
    · exact Function.update_idem _ _ _
    · rfl

lemma upK_rdK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) (i : Option S) :
    upK S k₀ g i (rdK S k₀ g i) = g := by
  cases i with
  | none => rfl
  | some d =>
    simp only [upK, rdK]
    split_ifs with h
    · rw [cast_cast, cast_eq]
      exact Function.update_eq_self _ _
    · rfl

lemma rdK_upK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) (d : S) (h : d.val.1 = k₀)
    (w : Bytes k₀.outLen) : rdK S k₀ (upK S k₀ g (some d) w) (some d) = w := by
  simp only [upK, rdK, h, dite_true, Function.update_self, cast_cast, cast_eq]

lemma extendTable_upK (S : Finset Dom) (k₀ : Kind) (g : (d : S) → Ans d.val) (d : S)
    (h : d.val.1 = k₀) (w : Bytes k₀.outLen) :
    extendTable S (upK S k₀ g (some d) w) =
      Function.update (extendTable S g) d.val (cast (ans_eq h) w) := by
  simp only [upK, h, dite_true]
  exact extendTable_update S g d _

/-- **A fresh answer guessed**: if the event implies that the cell `t g` (of kind `k₀`) is
queried, that `t` is unchanged by updating the table at `t g`, and that at most `K` answers there
keep the event, then the event has probability at most `K / 2^{8·outLen k₀}`. -/
theorem prEvent_fresh_guess_le (oa : OracleComp spec α) (ev : α → Prop) (t : Table → Dom)
    (k₀ : Kind) (K : ℕ) (hk : ∀ g, (t g).1 = k₀)
    (hlog : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      t g ∈ (tableQueryLog oa g).map Sigma.fst)
    (ht : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) oa) → ∀ u,
      t (Function.update g (t g) u) = t g)
    (hK : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ Tg : Finset (Ans (t g)), Tg.card ≤ K ∧
        ∀ u, ev (evalWithAnswerFn (QueryImpl.ofFn (Function.update g (t g) u)) oa) → u ∈ Tg) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[ev r] ≤
      K * (2 ^ (8 * k₀.outLen) : ℝ≥0∞)⁻¹ := by
  classical
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  let _ : SampleableType ((d : S) → Ans d.val) := SampleableType.ofFintype _
  rw [IC.prEvent_randomOracle_eq_eager oa S hS ev]
  let Ω := (d : S) → Ans d.val
  let ev' : Ω → Prop := fun g => ev (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) oa)
  let tt : Dom → Option S := fun x => if h : x ∈ S then some ⟨x, h⟩ else none
  let t' : Ω → Option S := fun g => tt (t (extendTable S g))
  let T' : Ω → Finset (Bytes k₀.outLen) := fun g => finOf fun w => ev' (upK S k₀ g (t' g) w)
  -- The cell of an event table is a queried cell, so in `S`.
  have hmemS : ∀ g, ev' g → t (extendTable S g) ∈ S := fun g hg => by
    obtain ⟨e, he, hee⟩ := List.mem_map.1 (hlog _ hg)
    exact hee ▸ allQueriesSatisfy_tableQueryLog hS _ e he
  have ht' : ∀ g (hg : ev' g), t' g = some ⟨_, hmemS g hg⟩ := fun g hg =>
    dite_eq_left_of_eq_true (eq_true (hmemS g hg))
  -- Updating at the cell changes neither the cell nor the class.
  have hext : ∀ g (hg : ev' g) w, extendTable S (upK S k₀ g (t' g) w) =
      Function.update (extendTable S g) (t (extendTable S g)) (cast (ans_eq (hk _)) w) :=
    fun g hg w => by rw [ht' g hg, extendTable_upK S k₀ g _ (hk _) w]
  have hcell : ∀ g (hg : ev' g) w, t' (upK S k₀ g (t' g) w) = t' g := fun g hg w => by
    have e1 : t (extendTable S (upK S k₀ g (t' g) w)) = t (extendTable S g) := by
      rw [hext g hg w]; exact ht _ hg _
    exact congrArg tt e1
  have hnat := card_finOf_mul_le (Ω := Ω) (I := Option S) (W := Bytes k₀.outLen) (upK S k₀)
    (rdK S k₀) (fun i => ∃ d, i = some d ∧ d.val.1 = k₀) (upK_upK S k₀) (upK_rdK S k₀)
    (fun g i w ⟨d, hd, h⟩ => by subst hd; exact rdK_upK S k₀ g d h w) ev' t' T' K
    (fun g hg => ⟨_, ht' g hg, hk _⟩)
    (fun g hg w => ⟨hcell g hg w, by
      simp only [T']
      rw [hcell g hg w]
      congr 1
      funext w'
      rw [upK_upK]⟩)
    (fun g hg => by
      obtain ⟨Tg, hcard, hmemT⟩ := hK _ hg
      refine (card_le_card_of_injOn (fun w => cast (ans_eq (hk _)) w) (fun w hw => ?_)
        (fun w₁ _ w₂ _ he => (cast_inj _).1 he)).trans hcard
      have hw' := mem_finOf.1 (mem_coe.1 hw)
      simp only [ev'] at hw'
      rw [hext g hg w] at hw'
      exact mem_coe.2 (hmemT _ hw'))
    (fun g hg => mem_finOf.2 (by simp only [upK_rdK]; exact hg))
  have hM : Fintype.card (Bytes k₀.outLen) = 2 ^ (8 * k₀.outLen) := card_bytes _
  have hev' : Pr{let g ← $ᵗ Ω}[ev' g] = (#(finOf ev') : ℝ≥0∞) / Fintype.card Ω := by
    rw [@SampleableType.prEvent_uniformSample _ _ _ ev' (Classical.decPred ev'), finOf_eq]
  show Pr{let g ← $ᵗ Ω}[ev' g] ≤ _
  rw [hev']
  have hN0 : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNt : (Fintype.card Ω : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hN0 hNt]
  have h2 : (2 ^ (8 * k₀.outLen) : ℝ≥0∞) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2t : (2 ^ (8 * k₀.outLen) : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hcast : (#(finOf ev') : ℝ≥0∞) * 2 ^ (8 * k₀.outLen) ≤ K * Fintype.card Ω := by
    have := (Nat.cast_le (α := ℝ≥0∞)).2 hnat
    rw [Nat.cast_mul, Nat.cast_mul, hM, Nat.cast_pow, Nat.cast_ofNat] at this
    exact this
  calc (#(finOf ev') : ℝ≥0∞) = #(finOf ev') * 2 ^ (8 * k₀.outLen) * (2 ^ (8 * k₀.outLen))⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2 h2t, mul_one]
    _ ≤ K * Fintype.card Ω * (2 ^ (8 * k₀.outLen))⁻¹ := mul_le_mul_of_nonneg_right hcast (by simp)
    _ = K * (2 ^ (8 * k₀.outLen))⁻¹ * Fintype.card Ω := by ring

end Guess

/-! ## The verifier's `H₂³` query, fresh -/

section Z

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [HasPrg] {β : Type}

omit [HasPrg] in
lemma hash_ofTable_update_h23 (g : Table) (z : ByteArray) (u : Ans (.h23, z)) {k : Kind}
    (hk : k ≠ .h23) :
    (Hashes.ofTable (Function.update g (.h23, z) u)).hash k = (Hashes.ofTable g).hash k := by
  funext x
  simp only [Hashes.ofTable_hash]
  rw [Function.update_of_ne (fun h => hk (congrArg Prod.fst h))]

/-- **The verifier's chain does not read the `H₂³` table.** -/
lemma runChain_ofTable_update_h23 (g : Table) (z : ByteArray) (u : Ans (.h23, z)) (T : CrtTables)
    (st : Statement) (proof : ByteArray) (leaves : BAVC.Leaves) (keys : ℕ → ℕ → ByteArray) :
    runChain (Hashes.ofTable (Function.update g (.h23, z) u)) T st proof leaves keys =
      runChain (Hashes.ofTable g) T st proof leaves keys := by
  have hc : ∀ M, (Hashes.ofTable (Function.update g (.h23, z) u)).hash (.comb M) =
      (Hashes.ofTable g).hash (.comb M) := fun M => hash_ofTable_update_h23 g z u (by simp)
  simp only [runChain, ivOf, Statement.mu1, mu, chal1, BAVC.check, crtReconstruct,
    crtReconstructAt, gateHashes, chal2, Statement.muDelayed, Statement.combBytes,
    hash_ofTable_update_h23 g z u (show Kind.h4 ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.mu ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.muDelayed ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.h1 ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.h21 ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.h5 ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.h22 ≠ .h23 by decide), hc]

omit [HasPrg] in
lemma ivOf_ofTable_update_h23 (g : Table) (z : ByteArray) (u : Ans (.h23, z)) (st : Statement)
    (pf : Proof) :
    ivOf (Hashes.ofTable (Function.update g (.h23, z) u)) pf
        (st.mu1 (Hashes.ofTable (Function.update g (.h23, z) u))) =
      ivOf (Hashes.ofTable g) pf (st.mu1 (Hashes.ofTable g)) := by
  simp only [ivOf, Statement.mu1, mu,
    hash_ofTable_update_h23 g z u (show Kind.h4 ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.mu ≠ .h23 by decide),
    hash_ofTable_update_h23 g z u (show Kind.muDelayed ≠ .h23 by decide)]

/-- **The verifier's `H₂³` input, unqueried by the prover, gives acceptance with probability at
most `2⁻¹²⁸`**: a single fresh answer must be the proof's `Δ` (the prover's output does not read
that cell, `hfix`, and the verifier's chain up to it reads no `H₂³` cell). -/
theorem prEvent_accept_zUnqueried_le (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) (qs : β → List Dom)
    (hfix : ∀ (g : Table) (d : Dom) (u : Ans d), d.1 ∈ ladderKinds →
      d ∉ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux →
      evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) oa =
        evalWithAnswerFn (QueryImpl.ofFn g) oa) :
    Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[
        r.2.2.accept = true ∧ ((.h23, zOut st r) : Dom) ∉ qs r.2.1.aux] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  let π : Table → ByteArray := fun g => (evalWithAnswerFn (QueryImpl.ofFn g) oa).1
  let lv : Table → BAVC.Leaves := fun g =>
    (BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, π g⟩ (st.mu1 (Hashes.ofTable g)))
      (Proof.opening ⟨st.params, π g⟩) (Proof.delta ⟨st.params, π g⟩)).getD ⟨.empty, .empty⟩
  let zz : Table → ByteArray := fun g =>
    runZ st (runChain (Hashes.ofTable g) T st (π g) (lv g) fun _ _ => ByteArray.empty)
  let ev : Out β → Prop := fun r => r.2.2.accept = true ∧ ((.h23, zOut st r) : Dom) ∉ qs r.2.1.aux
  -- On an event table: the accepted proof's leaves, and the verifier's `H₂³` input.
  have hfacts : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) →
      BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, π g⟩ (st.mu1 (Hashes.ofTable g)))
        (Proof.opening ⟨st.params, π g⟩) (Proof.delta ⟨st.params, π g⟩) = some (lv g) ∧
      (verify (Hashes.ofTable g) T st (π g)).accept = true ∧
      ((.h23, zz g) : Dom) ∉ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux := by
    intro g hg
    obtain ⟨hacc, hz⟩ := hg
    rw [evalWithAnswerFn_game] at hacc hz
    obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st (π g)).1 hacc
    have hlv : lv g = leaves := by simp only [lv, hr, Option.getD_some]
    refine ⟨hlv ▸ hr, hacc, ?_⟩
    rw [zOut_eq_runZ _ T st (π g) _ hacc hr (fun _ _ => ByteArray.empty)] at hz
    simpa only [zz, hlv] using hz
  have hfix' : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) → ∀ u,
      evalWithAnswerFn (QueryImpl.ofFn (Function.update g (.h23, zz g) u)) oa =
        evalWithAnswerFn (QueryImpl.ofFn g) oa :=
    fun g hg u => hfix g _ u (by simp [ladderKinds]) (hfacts g hg).2.2
  have hlv' : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) → ∀ u,
      π (Function.update g (.h23, zz g) u) = π g ∧ lv (Function.update g (.h23, zz g) u) = lv g :=
    fun g hg u => by
      have hπ : π (Function.update g (.h23, zz g) u) = π g := by
        simp only [π, hfix' g hg u]
      refine ⟨hπ, ?_⟩
      simp only [lv, hπ, ivOf_ofTable_update_h23]
  have hzz : ∀ g, ev (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) → ∀ u,
      zz (Function.update g (.h23, zz g) u) = zz g := fun g hg u => by
    obtain ⟨hπ, hl⟩ := hlv' g hg u
    simp only [zz, hπ, hl, runChain_ofTable_update_h23]
  have h := prEvent_fresh_guess_le (game T st oa) ev (fun g => (.h23, zz g)) .h23 1
    (fun _ => rfl)
    (fun g hg => by
      obtain ⟨hr, hacc, -⟩ := hfacts g hg
      exact inLog_game (inLog_verifyQ g T st (π g) hacc hr (fun _ _ => ByteArray.empty)).2.2)
    (fun g hg u => by
      show ((.h23, zz (Function.update g (.h23, zz g) u)) : Dom) = (.h23, zz g)
      rw [hzz g hg u])
    (fun g hg => by
      refine ⟨finOf fun u : Bytes 16 => u.ba = Proof.delta ⟨st.params, π g⟩,
        Finset.card_le_one.2 fun a ha b hb =>
          Bytes.ba_injective ((mem_finOf.1 ha).trans (mem_finOf.1 hb).symm), fun u hu => ?_⟩
      refine mem_finOf.2 ?_
      obtain ⟨hacc', -⟩ := hu
      rw [evalWithAnswerFn_game] at hacc'
      obtain ⟨hπ, hl⟩ := hlv' g hg u
      obtain ⟨-, leaves', hr', -, h3⟩ :=
        (accept_iff _ T st (π (Function.update g (.h23, zz g) u))).1 hacc'
      have hlv'' : lv (Function.update g (.h23, zz g) u) = leaves' := by
        simp only [lv, hr', Option.getD_some]
      have hz' := hzz g hg u
      simp only [zz, hlv''] at hz'
      have h3' : (Function.update g (.h23, zz g) u
          (.h23, runZ st (runChain (Hashes.ofTable (Function.update g (.h23, zz g) u)) T st
            (π (Function.update g (.h23, zz g) u)) leaves' fun _ _ => ByteArray.empty))).ba =
          Proof.delta ⟨st.params, π (Function.update g (.h23, zz g) u)⟩ := h3
      rw [hz', Function.update_self, hπ] at h3'
      exact h3')
  refine h.trans (le_of_eq ?_)
  norm_num [Kind.outLen]

end Z

end VoleMole.ROM
