import VoleMole.Theft.PlainOracle

/-!
# The theft tables as a uniform table on finitely many points, and the lazy random oracle

`ROM/`'s extraction bounds are for the lazy random oracle on `Dom = Kind × ByteArray` and a
uniform cipher table `E : CTable`. The theft games draw finite tables instead: two `H₃` slices,
`H₂³` on the grinding points (`Tab2G`), `H₅` on 37-byte inputs (`Tab5F`), function rows for the
cipher (`Blk → Blk → Blk`) and the extra table (`XTab L M`: `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₂¹`,
`H₂²`, `H_comb` on inputs of at most `L` bytes), with SHAKE answering every other input
(`ansP`, `Theft/PlainOracle.lean`). Here the two are related (`docs/security/ratatouille.md` §5,
item 4 (a)):

* `TK p L`, `tpt`: the **table points**, the keys of `Dom` the tables answer (`tpt_injective`);
  `TPts p L M` their finite set.
* `tabEquiv`: the slices and the tables are a table on the table points and a cipher table
  (a bijection, so the uniform draws correspond). `tabP_tpt`, `cellP_tabEquiv`: the answers of
  `ansP` at the table points are the table's, its cells the cipher table's.
* **`normT`**: an oracle computation over `specIC` with every hash query off the table points
  answered by SHAKE locally (`blk k.outLen (shake128 x)`); cipher queries are passed through.
  `runT_normT`: run on `ansP` it is the computation; it queries only table points
  (`allQueriesSatisfy_normT`), within the same query bounds (`qBud_normT`), and its run has the same
  cipher queries with the same answers (`cipherQs_normT`).
* **`pr_tables_eq_ro`**: for computations `oa E` against the hash oracles that query only table
  points, an event's probability on the tables (uniform slices and tables, SHAKE elsewhere) is its
  probability in `ROM/`'s experiment (uniform `E`, then the lazy random oracle):
  `prEvent_randomOracle_eq_eager` on the table points, the two draws joined
  (`prEvent_uniform_bind_eq`), and `tabEquiv`.

The cipher rows here are random functions (`CipherRow.fn`), as `ROM/`'s `CTable`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The table points -/

section Points

variable (p : Params) (L M : ℕ)

/-- **The indices of the table points**: a slice key, a grinding point, an `H₅` input, and an input
of at most `L` bytes for each of the seven extra hashes. -/
abbrev TK := (Bool × Bytes 16) ⊕ K2 p ⊕ Bytes 37 ⊕ KL L ⊕ KL L ⊕ KL L ⊕ KL L ⊕ KL L ⊕ KL L ⊕ KL L

/-- **The table points**: `H₃` at the slices' inputs, `H₂³` at the grinding points, `H₅` at the
37-byte inputs, the extra hashes at the inputs of at most `L` bytes. -/
def tpt : TK p L → Dom
  | .inl a => (.h3, encSl a)
  | .inr (.inl a) => (.h23, enc2 p a)
  | .inr (.inr (.inl a)) => (.h5, enc5 a)
  | .inr (.inr (.inr (.inl a))) => (.h1, encL a)
  | .inr (.inr (.inr (.inr (.inl a)))) => (.mu, encL a)
  | .inr (.inr (.inr (.inr (.inr (.inl a))))) => (.muDelayed, encL a)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))) => (.h4, encL a)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))) => (.h21, encL a)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))) => (.h22, encL a)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))) => (.comb M, encL a)

lemma enc5_injective : Function.Injective enc5 := fun _ _ h => ba_injective h

set_option maxHeartbeats 1000000 in
lemma tpt_injective : Function.Injective (tpt p L M) := by
  intro a b h
  rcases a with a | a | a | a | a | a | a | a | a | a <;>
    rcases b with b | b | b | b | b | b | b | b | b | b <;>
    simp only [tpt, Prod.mk.injEq, reduceCtorEq, false_and, true_and] at h ⊢
  · rw [encSl_injective h]
  · rw [enc2_injective (p := p) h]
  · rw [enc5_injective h]
  all_goals rw [encL_injective h]

set_option maxRecDepth 10000 in
/-- **The finite set of the table points.** -/
@[irreducible] noncomputable def TPts : Finset Dom := Finset.univ.image (tpt p L M)

set_option maxRecDepth 10000 in
lemma tpt_mem (k : TK p L) : tpt p L M k ∈ TPts p L M := by
  unfold TPts
  exact Finset.mem_image_of_mem _ (Finset.mem_univ k)

set_option maxRecDepth 10000 in
lemma mem_TPts {d : Dom} : d ∈ TPts p L M ↔ ∃ k, tpt p L M k = d := by
  simp [TPts]

set_option maxRecDepth 10000 in
/-- The table points as a type. -/
noncomputable def tptEquiv : TK p L ≃ TPts p L M :=
  Equiv.ofBijective (fun k => ⟨tpt p L M k, tpt_mem p L M k⟩)
    ⟨fun a b h => tpt_injective p L M (congrArg Subtype.val h), fun d => by
      obtain ⟨k, hk⟩ := (mem_TPts p L M).1 d.2
      exact ⟨k, Subtype.ext hk⟩⟩

set_option maxRecDepth 10000 in
@[simp] lemma tptEquiv_val (k : TK p L) : (tptEquiv p L M k).val = tpt p L M k := rfl

end Points

/-! ## The values at the table points -/

section Values

variable {L M : ℕ}

lemma hbX_muDelayed (x : XTab L M) (k : KL L) :
    (hbX x).hash .muDelayed (encL k) = ba (x.2.2.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .muDelayed (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h22) .muDelayed (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h21) .muDelayed (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h4) .muDelayed (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .muDelayed encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl)))))

lemma hbX_h4 (x : XTab L M) (k : KL L) :
    (hbX x).hash .h4 (encL k) = ba (x.2.2.2.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h22) .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h21) .h4 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h4 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl))))

lemma hbX_comb (x : XTab L M) (k : KL L) :
    (hbX x).hash (.comb M) (encL k) = ba (x.2.2.2.2.2.2 k) :=
  (Hashes.withTable_enc _ (.comb M) encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl)

variable {R : Type} [CipherRow R] {p : Params}

omit [CipherRow R] in
open Classical in
lemma recP_h3_enc (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (a : Bool × Bytes 16) :
    (recP g₁ g₂ t).hash .h3 (encSl a) = ba (slT g₁ g₂ a) := by
  rw [recP_h3, dite_eq_left_of_eq_true (eq_true ⟨a, rfl⟩)]
  have h : (⟨a, rfl⟩ : ∃ a', encSl a' = encSl a).choose = a :=
    encSl_injective (⟨a, rfl⟩ : ∃ a', encSl a' = encSl a).choose_spec
  rw [h]

omit [CipherRow R] in
open Classical in
lemma recP_h23_enc (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (a : K2 p) :
    (recP g₁ g₂ t).hash .h23 (enc2 p a) = ba (t.1 a) := by
  rw [recP_h23, dite_eq_left_of_eq_true (eq_true ⟨a, rfl⟩)]
  have h : (⟨a, rfl⟩ : ∃ a', enc2 p a' = enc2 p a).choose = a :=
    enc2_injective (p := p) (⟨a, rfl⟩ : ∃ a', enc2 p a' = enc2 p a).choose_spec
  rw [h]

omit [CipherRow R] in
open Classical in
lemma recP_h5_enc (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (a : Bytes 37) :
    (recP g₁ g₂ t).hash .h5 (enc5 a) = ba (t.2.1.1 a) := by
  rw [recP_h5, dite_eq_left_of_eq_true (eq_true ⟨a, rfl⟩)]
  have h : (⟨a, rfl⟩ : ∃ a', enc5 a' = enc5 a).choose = a :=
    enc5_injective (⟨a, rfl⟩ : ∃ a', enc5 a' = enc5 a).choose_spec
  rw [h]

/-- The answer at a table point, as a table. -/
def tabOf (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) : (k : TK p L) → Ans (tpt p L M k)
  | .inl a => slT g₁ g₂ a
  | .inr (.inl a) => t.1 a
  | .inr (.inr (.inl a)) => t.2.1.1 a
  | .inr (.inr (.inr (.inl a))) => t.2.2.1 a
  | .inr (.inr (.inr (.inr (.inl a)))) => t.2.2.2.1 a
  | .inr (.inr (.inr (.inr (.inr (.inl a))))) => t.2.2.2.2.1 a
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))) => t.2.2.2.2.2.1 a
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))) => t.2.2.2.2.2.2.1 a
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))) => t.2.2.2.2.2.2.2.1 a
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))) => t.2.2.2.2.2.2.2.2 a

omit [CipherRow R] in
/-- **The answers of `ansP` at the table points are the tables'.** -/
lemma tabP_tpt (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (k : TK p L) :
    tabP g₁ g₂ t (tpt p L M k) = tabOf g₁ g₂ t k := by
  rcases k with a | a | a | a | a | a | a | a | a | a
  · exact (congrArg _ (recP_h3_enc g₁ g₂ t a)).trans (blk_ba _)
  · exact (congrArg _ (recP_h23_enc g₁ g₂ t a)).trans (blk_ba _)
  · exact (congrArg _ (recP_h5_enc g₁ g₂ t a)).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_h1 _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_mu _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_muDelayed _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_h4 _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_h21 _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by decide) (by decide) (by decide) _).trans
      (hbX_h22 _ a))).trans (blk_ba _)
  · exact (congrArg _ ((recP_other g₁ g₂ t (by simp) (by simp) (by simp) _).trans
      (hbX_comb _ a))).trans (blk_ba _)

end Values

/-! ## The slices and the tables as one table on the table points and a cipher table -/

section Equiv

variable {p : Params} {L M : ℕ}

/-- **The slices and the tables are a table on the table points and a cipher table** (function
rows are the cipher's rows). -/
def tabEquiv : (Tab3 × Tab3) × ShX (Blk → Blk) p (XTab L M) ≃
    ((k : TK p L) → Ans (tpt p L M k)) × CTable where
  toFun z := (tabOf z.1.1 z.1.2 z.2, cellP z.2)
  invFun y := ((fun k => y.1 (.inl (false, k)), fun k => y.1 (.inl (true, k))),
    (fun a => y.1 (.inr (.inl a)), ((fun a => y.1 (.inr (.inr (.inl a))), fun b z => y.2 (b, z)),
      (fun a => y.1 (.inr (.inr (.inr (.inl a)))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inl a))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inl a)))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))))))))
  left_inv z := rfl
  right_inv y := by
    refine Prod.ext (funext fun k => ?_) rfl
    rcases k with ⟨b, a⟩ | a | a | a | a | a | a | a | a | a
    · cases b <;> rfl
    all_goals rfl

@[simp] lemma tabEquiv_fst (z : (Tab3 × Tab3) × ShX (Blk → Blk) p (XTab L M)) :
    (tabEquiv z).1 = tabOf z.1.1 z.1.2 z.2 := rfl

@[simp] lemma tabEquiv_snd (z : (Tab3 × Tab3) × ShX (Blk → Blk) p (XTab L M)) :
    (tabEquiv z).2 = cellP z.2 := rfl

set_option maxRecDepth 10000 in
/-- A table on the table points, indexed by the points themselves. -/
noncomputable def ptsEquiv (p : Params) (L M : ℕ) :
    ((k : TK p L) → Ans (tpt p L M k)) ≃ ((d : TPts p L M) → Ans d.val) :=
  Equiv.piCongrLeft (fun d : TPts p L M => Ans d.val) (tptEquiv p L M)

set_option maxRecDepth 10000 in
lemma ptsEquiv_tpt (g : (k : TK p L) → Ans (tpt p L M k)) (k : TK p L) :
    ptsEquiv p L M g (tptEquiv p L M k) = g k :=
  Equiv.piCongrLeft_apply_apply (fun d : TPts p L M => Ans d.val) (tptEquiv p L M) g k

end Equiv

/-! ## Runs that query only some keys -/

section Congr

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- **A run reads only the keys its computation may query.** -/
lemma runT_congr_of_allQueries (oa : OracleComp spec α) (P : ι → Prop)
    (h : AllQueriesSatisfy oa P) (f f' : (k : ι) → spec k) (hf : ∀ d, P d → f d = f' d) :
    runT f oa = runT f' oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff t k P).1 h
    show runT f (k (f t)) = runT f' (k (f' t))
    rw [hf t ht]
    exact ih (f' t) (hk _)

end Congr

/-! ## Two uniform draws, and the lazy oracle as a uniform table -/

section Joint

variable {X : Type}

/-- **Two uniform draws in sequence are a uniform pair.** -/
lemma prEvent_uniform_bind_eq {A B : Type} [SampleableType A] [SampleableType B] [Fintype A]
    [Fintype B] [Nonempty A] [Nonempty B] (P : A → B → Prop) :
    Pr{let a ← $ᵗ A; let b ← $ᵗ B}[P a b] = Prob.prU (A × B) fun z => P z.1 z.2 := by
  rw [← prEvent_uniformSample_eq_prU, SampleableType.uniformSample_prod_eq_bind]
  congr 1
  simp [map_bind]

set_option maxRecDepth 100000 in
/-- **The joint experiment as a uniform cipher table and a uniform table on `S`**, for computations
that query only keys of `S`. -/
theorem prEvent_joint_eq_prU (S : Finset Dom) (m : CTable → OracleComp spec X)
    (hS : ∀ E, AllQueriesSatisfy (m E) (· ∈ S)) (ev : CTable → X → Prop)
    [SampleableType ((d : S) → Ans d.val)] :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] =
      Prob.prU (CTable × ((d : S) → Ans d.val)) fun z =>
        ev z.1 (evalWithAnswerFn (QueryImpl.ofFn (extendTable S z.2)) (m z.1)) := by
  have h := prEvent_uniform_bind_eq (A := CTable) (B := (d : S) → Ans d.val) fun E g =>
    ev E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))
  rw [← h]
  let : MeasurableSpace CTable := ⊤
  calc Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r]
      = ∫⁻ E, Pr{let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] ∂𝒟[$ᵗ CTable] :=
        prEvent_bind_of_discrete _ _
    _ = ∫⁻ E, Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
          ev E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))] ∂𝒟[$ᵗ CTable] :=
        MeasureTheory.lintegral_congr fun E => prEvent_randomOracle_eq_eager (m E) S (hS E) (ev E)
    _ = _ := (prEvent_bind_of_discrete _ _).symm

end Joint

/-! ## The tables and the lazy random oracle -/

section Bridge

variable {p : Params} {L M : ℕ} {X : Type}

set_option maxRecDepth 10000 in
/-- **The tables are the lazy random oracle on the table points.** For computations `m E` against
the hash oracles that query only table points, an event's probability on uniform slices and
tables (`tabP`, SHAKE elsewhere; the cipher table of the function rows, `cellP`) is its
probability in `ROM/`'s experiment: a uniform cipher table, then the lazy random oracle. -/
theorem pr_tables_eq_ro (m : CTable → OracleComp spec X)
    (hm : ∀ E, AllQueriesSatisfy (m E) (· ∈ TPts p L M)) (ev : CTable → X → Prop) :
    pr ((Tab3 × Tab3) × ShX (Blk → Blk) p (XTab L M)) (fun z =>
        ev (cellP z.2) (runT (tabP z.1.1 z.1.2 z.2) (m (cellP z.2)))) =
      (Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r]).toReal := by
  classical
  let : SampleableType ((d : TPts p L M) → Ans d.val) := SampleableType.ofFintype _
  rw [prEvent_joint_eq_prU _ m hm ev, pr_eq_toReal_prU]
  congr 1
  let e : (Tab3 × Tab3) × ShX (Blk → Blk) p (XTab L M) ≃
      CTable × ((d : TPts p L M) → Ans d.val) :=
    tabEquiv.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (ptsEquiv p L M)))
  rw [Prob.prU_map_equiv e]
  refine Prob.prU_congr fun z => ?_
  show _ ↔ ev (cellP z.2) (evalWithAnswerFn (QueryImpl.ofFn (extendTable (TPts p L M)
    (ptsEquiv p L M (tabOf z.1.1 z.1.2 z.2)))) (m (cellP z.2)))
  rw [← runT_eq_eval]
  refine iff_of_eq (congrArg _ (runT_congr_of_allQueries _ _ (hm _) _ _ fun d hd => ?_))
  obtain ⟨k, rfl⟩ := (mem_TPts p L M).1 hd
  rw [tabP_tpt]
  have h := extendTable_subtype (TPts p L M) (ptsEquiv p L M (tabOf z.1.1 z.1.2 z.2))
    (tptEquiv p L M k)
  rw [ptsEquiv_tpt] at h
  exact h.symm

end Bridge

/-! ## SHAKE off the table points -/

section Shake

variable {p : Params} {L M : ℕ}

lemma withTable_off (Hs : Hashes) (k : Kind) {K : Type} (enc : K → ByteArray)
    (G : K → Bytes k.outLen) {k' : Kind} {b : ByteArray} (h : ∀ a, ¬ (k' = k ∧ enc a = b)) :
    (Hs.withTable k enc G).hash k' b = Hs.hash k' b := by
  classical
  unfold Hashes.withTable
  dsimp only
  split_ifs with h1 h2
  · exact absurd ⟨h1, h2.choose_spec⟩ (h h2.choose)
  · rw [h1]
  · rfl

variable {R : Type} [CipherRow R]

omit [CipherRow R] in
/-- **Off the table points the record is SHAKE.** -/
lemma recP_off (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) {d : Dom} (hd : d ∉ TPts p L M) :
    (recP g₁ g₂ t).hash d.1 d.2 = Hashes.shake.hash d.1 d.2 := by
  obtain ⟨k, b⟩ := d
  have hn : ∀ i, tpt p L M i ≠ (k, b) := fun i hi => hd (hi ▸ tpt_mem p L M i)
  exact (withTable_off _ .h3 encSl _ fun a ⟨h1, h2⟩ => hn (.inl a) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .h5 enc5 _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inl a))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .h23 (enc2 p) _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inl a)) (by subst h1 h2; rfl)).trans
    ((withTable_off _ (.comb M) encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a))))))))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .h22 encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .h21 encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .h4 encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .muDelayed encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inr (.inl a)))))) (by subst h1 h2; rfl)).trans
    ((withTable_off _ .mu encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inr (.inl a))))) (by subst h1 h2; rfl)).trans
    (withTable_off _ .h1 encL _ fun a ⟨h1, h2⟩ =>
      hn (.inr (.inr (.inr (.inl a)))) (by subst h1 h2; rfl))))))))))

/-- **The SHAKE answer** of a hash query, as `ROM/`'s answer type. -/
def shakeAns (d : Dom) : Ans d := blk d.1.outLen (Hashes.shake.hash d.1 d.2)

omit [CipherRow R] in
lemma tabP_off (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) {d : Dom} (hd : d ∉ TPts p L M) :
    tabP g₁ g₂ t d = shakeAns d :=
  congrArg _ (recP_off g₁ g₂ t hd)

end Shake

/-! ## The normalization: SHAKE answered locally off the table points -/

section Norm

variable (p : Params) (L M : ℕ) {α : Type}

/-- **The normalized computation**: a hash query at a table point and every cipher query are
made; a hash query off the table points is answered locally by SHAKE (`shakeAns`). -/
noncomputable def normT : OracleComp specIC α → OracleComp specIC α
  | .pure x => pure x
  | .queryBind (.inl d) k => if d ∈ TPts p L M then
      liftM (specIC.query (.inl d)) >>= fun u => normT (k u) else normT (k (shakeAns d))
  | .queryBind (.inr c) k => liftM (specIC.query (.inr c)) >>= fun u => normT (k u)

/-- The queries the normalized computation makes: hash queries at table points, cells. -/
def OnT : DomIC → Prop
  | .inl d => d ∈ TPts p L M
  | .inr _ => True

noncomputable instance : DecidablePred (OnT p L M) := Classical.decPred _

variable {p L M}

/-- **The normalized run**: on answers that are SHAKE off the table points, the run is the
computation's, and its queries are the computation's at table points and cells. -/
theorem normT_run (f : (d : DomIC) → AnsIC d) (hf : ∀ d, d ∉ TPts p L M → f (.inl d) = shakeAns d)
    (oa : OracleComp specIC α) :
    runT f (normT p L M oa) = runT f oa ∧
      qlog f (normT p L M oa) = (qlog f oa).filter fun d => decide (OnT p L M d) := by
  induction oa with
  | pure x => exact ⟨rfl, rfl⟩
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · have e : normT p L M (.queryBind (.inl d) k) =
            liftM (specIC.query (.inl d)) >>= fun u => normT p L M (k u) := by
          simp only [normT, hd, ite_true]
        rw [e]
        refine ⟨(ih (f (.inl d))).1, ?_⟩
        show (Sum.inl d) :: qlog f (normT p L M (k (f (.inl d)))) = _
        rw [(ih _).2]
        show _ = List.filter _ ((Sum.inl d) :: qlog f (k (f (.inl d))))
        exact (List.filter_cons_of_pos (p := fun d => decide (OnT p L M d))
          (decide_eq_true (show OnT p L M (.inl d) from hd))).symm
      · have e : normT p L M (.queryBind (.inl d) k) = normT p L M (k (shakeAns d)) := by
          simp only [normT, hd, ite_false]
        rw [e]
        have hf' : f (.inl d) = shakeAns d := hf d hd
        refine ⟨?_, ?_⟩
        · show runT f (normT p L M (k (shakeAns d))) = runT f (k (f (.inl d)))
          rw [hf']
          exact (ih _).1
        · show qlog f (normT p L M (k (shakeAns d))) =
            List.filter _ ((Sum.inl d) :: qlog f (k (f (.inl d))))
          rw [List.filter_cons_of_neg (p := fun d => decide (OnT p L M d))
            (by rw [decide_eq_true_eq]; exact hd), hf']
          exact (ih _).2
    · refine ⟨(ih (f (.inr c))).1, ?_⟩
      show (Sum.inr c) :: qlog f (normT p L M (k (f (.inr c)))) = _
      rw [(ih _).2]
      show _ = List.filter _ ((Sum.inr c) :: qlog f (k (f (.inr c))))
      exact (List.filter_cons_of_pos (p := fun d => decide (OnT p L M d))
        (decide_eq_true (show OnT p L M (.inr c) from trivial))).symm

/-- **The normalized computation queries only table points and cells.** -/
theorem allQueriesSatisfy_normT (oa : OracleComp specIC α) :
    AllQueriesSatisfy (normT p L M oa) (OnT p L M) := by
  induction oa with
  | pure x => exact allQueriesSatisfy_pure _ _
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · have e : normT p L M (.queryBind (.inl d) k) =
            liftM (specIC.query (.inl d)) >>= fun u => normT p L M (k u) := by
          simp only [normT, hd, ite_true]
        rw [e]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨hd, fun u => ih u⟩
      · have e : normT p L M (.queryBind (.inl d) k) = normT p L M (k (shakeAns d)) := by
          simp only [normT, hd, ite_false]
        rw [e]
        exact ih _
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun u => ih u⟩

/-- **The normalized computation keeps every query bound of a class.** -/
theorem isQueryBoundP_normT {P : DomIC → Prop} [DecidablePred P] {oa : OracleComp specIC α}
    {n : ℕ} (h : IsQueryBoundP oa P n) : IsQueryBoundP (normT p L M oa) P n := by
  induction oa generalizing n with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff P t k n).1 h
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · have e : normT p L M (.queryBind (.inl d) k) =
            liftM (specIC.query (.inl d)) >>= fun u => normT p L M (k u) := by
          simp only [normT, hd, ite_true]
        rw [e]
        exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · have e : normT p L M (.queryBind (.inl d) k) = normT p L M (k (shakeAns d)) := by
          simp only [normT, hd, ite_false]
        rw [e]
        exact ih _ ((h'.2 _).mono (by split <;> omega))
    · exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- **The normalized computation keeps the per-kind hash bounds.** -/
theorem isKindQueryBoundIC_normT {oa : OracleComp specIC α} {q : Kind → ℕ}
    (h : IsKindQueryBoundIC oa q) : IsKindQueryBoundIC (normT p L M oa) q := by
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · have e : normT p L M (.queryBind (.inl d) k) =
            liftM (specIC.query (.inl d)) >>= fun u => normT p L M (k u) := by
          simp only [normT, hd, ite_true]
        rw [e]
        exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · have e : normT p L M (.queryBind (.inl d) k) = normT p L M (k (shakeAns d)) := by
          simp only [normT, hd, ite_false]
        rw [e]
        refine ih _ ((show IsKindQueryBoundIC (k (shakeAns d)) (Function.update q d.1 (q d.1 - 1))
          from h'.2 _).mono fun k' => ?_)
        by_cases hk : k' = d.1
        · subst hk; simp
        · simp [Function.update_of_ne hk]
    · exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- The normalized computation keeps the query budget. -/
theorem qBud_normT {oa : OracleComp specIC α} {q : Kind → ℕ} {qE : ℕ} (h : QBud q qE oa) :
    QBud q qE (normT p L M oa) :=
  ⟨isKindQueryBoundIC_normT h.1, isQueryBoundP_normT h.2⟩

variable {R : Type} [CipherRow R]

/-- **On the tables, the normalized run is the computation's**, with the queries at table points
and the cells. -/
theorem normT_ansP (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (oa : OracleComp specIC α) :
    runT (ansP g₁ g₂ t) (normT p L M oa) = runT (ansP g₁ g₂ t) oa ∧
      qlog (ansP g₁ g₂ t) (normT p L M oa) =
        (qlog (ansP g₁ g₂ t) oa).filter fun d => decide (OnT p L M d) :=
  normT_run _ (fun _ hd => tabP_off g₁ g₂ t hd) oa

end Norm

end VoleMole.Theft
