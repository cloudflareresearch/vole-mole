import VoleMole.ZK.ReadsRO

/-!
# One shared `H₃`: the proofs' slices as columns of one table

The privacy games (`Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`,
`Privacy/PomFRITRO.lean` and their table-reading versions) give every proof its own independent
`H₃` slice (`Tab3`: `H₃` at the proof's seed inputs `wPrefix ‖ μ₁ ‖ ρ ‖ 3`). In the scheme all
proofs hash with one `H₃` (SHAKE), and a proof's slice is the restriction of that one oracle to
its **prefix** `wPrefix ‖ μ₁`. This file models the one oracle and the slices it determines.

* **Prefixes** (`Pre`): byte strings of fewer than `1024` bytes (`preKey`; the prefixes of all five
  relations are below `900` bytes). Since `ρ` has a fixed length (`16` bytes), `(x, ρ) ↦ x ‖ ρ ‖ 3`
  is injective on `Pre × Bytes 16`: `H₃` on these seed inputs is a uniform table indexed by the
  prefix and `ρ`.
* **`H₃` in the shared tables.** The shared tables of the games are `ShG R p = H₂³ × H₅ × (Blk → R)`
  with the cipher's rows in `R`. Here each row also carries `H₃`'s column at that `ρ`
  (`RowH R = R × (Pre → Bytes 32)`, `Blk = Bytes 16 = ρ`'s type): row `j` is the cipher's row `j`
  and `H₃(x ‖ j ‖ 3)` for every prefix `x`. The proof with prefix `k` has the slice `h3At s k`
  (`ρ ↦ H₃(k ‖ ρ ‖ 3)`). Reading `H₃` at one input costs one row read, like a cipher query.
  `CipherRow (RowH R)` reads a row as its cipher part, so the prover, the verifier and the
  simulator see the cipher as before.
* **Zero knowledge with one shared `H₃`.** `ZKRow.rowH`: the prover with its own slice and the
  shared tables `ShG (RowH R) p` (the `H₃` columns are extra uniform data for it) has `ZKRow R`'s
  error. **`ZeroKnowledgeRO.shared`**: a prover that reads its slice off the shared tables at its
  prefix (`h3At s (key x w)`), the slice argument of the game unused, is `ZeroKnowledgeRO` against
  every distinguisher with budget `(q₃, q₅, q_E)` with the error of the slice prover at
  `(q_E, q₅, q_E)`: the distinguisher reads the proof's slice only through rows. The proof
  re-samples the prover's column (`pr_setK`: overwriting a column of a uniform table with an
  independent uniform slice keeps it uniform), after which the real proof reads an independent
  slice; nothing needs the prefixes of different proofs to differ: another proof with the same
  prefix reads this slice, as part of the distinguisher, at its own `ρ` (one row).
* **Collision terms.** `pr_h3At_slice`: an event of a proof that reads its slice off the shared
  tables (and is otherwise blind to the `H₃` columns) has the probability of the same event with
  an independent slice. The games' programming-collision terms `δ` move to the shared model
  unchanged.
* **What the prover reads.** `prove_h3_congr`: the executable prover reads `H₃` at its seed input
  only, for every witness (`realROb_g3_congr'`, without the zero-knowledge hypotheses of
  `realRO_g3_congr`); `rd5_h3At`, `rdE_h3At`: a reader of its slice at one key, run on the slice
  of the shared tables, reads one row more.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

/-! ## The prover reads `H₃` only at its seed input -/

section ProverH3

variable [HasPrg] {Hs Hs' : Hashes}

/-- Step 1 after `H₃` does not read `H₃`. -/
lemma voleGenAt_agreeOff_h3 (h : Hs.AgreeOff .h3 Hs') (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre binder1 : ByteArray) :
    voleGenAt Hs T p mu1 wPrefix seed ivPre binder1 =
      voleGenAt Hs' T p mu1 wPrefix seed ivPre binder1 := by
  simp only [voleGenAt, h .h4 (by decide), h .h1 (by decide), h .h5 (by decide),
    h.chal1 (by decide)]

omit [HasPrg] in
/-- **Step 2 does not read `H₃`.** -/
lemma proveCommit_agreeOff_h3 (h : Hs.AgreeOff .h3 Hs') (st : Statement) (suf : ByteArray)
    (P : Prover.Pending) : Prover.proveCommit Hs st suf P = Prover.proveCommit Hs' st suf P := by
  have e4 : Prover.grindStep Hs = Prover.grindStep Hs' := by
    funext s pre ctr
    simp only [Prover.grindStep, h .h23 (by decide)]
  simp only [Prover.proveCommit, h.chal2 (by decide), h.muDelayed (by decide) st,
    h.combBytes (fun _ => nofun) st, e4]

/-- **The prover reads `H₃` only at its seed input** `wPrefix ‖ μ₁ ‖ ρ ‖ 3`, for every witness:
two records that agree off `H₃` and at that input give the same proof. -/
theorem prove_h3_congr (h : Hs.AgreeOff .h3 Hs') (T : CrtTables) (st : Statement)
    (w rho : ByteArray) (pb : ℕ)
    (hx : Hs.hash .h3 ((w.extract 0 pb ++ st.mu1 Hs ++ rho).push 3) =
      Hs'.hash .h3 ((w.extract 0 pb ++ st.mu1 Hs ++ rho).push 3)) :
    Prover.prove Hs T st w rho pb = Prover.prove Hs' T st w rho pb := by
  have hm := h.mu1 (by decide) (by decide) st
  unfold Prover.prove
  rw [voleGen_eq_voleGenAt, voleGen_eq_voleGenAt, ← hm, hx, voleGenAt_agreeOff_h3 h,
    proveCommit_agreeOff_h3 h]

omit [HasPrg] in
/-- With `H₃` a table on the seed inputs, two slices that agree at the keys of an input answer it
alike. -/
lemma withTable_h3_congr (X : Hashes) (mu1 wPrefix : ByteArray) {G G' : Tab3} {x : ByteArray}
    (h : ∀ a, seedInput mu1 wPrefix a = x → G a = G' a) :
    (X.withTable .h3 (seedInput mu1 wPrefix) G).hash .h3 x =
      (X.withTable .h3 (seedInput mu1 wPrefix) G').hash .h3 x := by
  simp only [Hashes.withTable, ite_true]
  split_ifs with hx
  · rw [h _ hx.choose_spec]
  · rfl

end ProverH3

section RealH3

variable {R : Type} [CipherRow R] {p : Params} {Hb : Hashes} {st : Statement} {w : ByteArray}

/-- `recHp` with two slices: the records agree off `H₃`. -/
lemma recHp_agreeOff_h3 (G3 G3' : Tab3) (G2 : Tab2G p) (G5 : Tab5F) :
    (recHp p Hb st w G3 G2 G5).AgreeOff .h3 (recHp p Hb st w G3' G2 G5) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recHp, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h23 : k = .h23
  · subst h23; simp only [recHp, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recHp, Hashes.withTable, h5, h23, hk, ite_false]

/-- **The real prover reads its slice only at its randomness**, for every witness: two slices that
agree at `blk 16 rho` give the same proof. -/
theorem realROb_g3_congr' (rho : ByteArray) {G3 G3' : Tab3} (s : ShG R p)
    (h : G3 (blk 16 rho) = G3' (blk 16 rho)) :
    realROb p Hb st w rho G3 s = realROb p Hb st w rho G3' s := by
  unfold realROb
  refine @prove_h3_congr (icPrg (rowFn s.2.2)) _ _ (recHp_agreeOff_h3 G3 G3' s.1 s.2.1) _ _ _ _ _ ?_
  rw [recHp_h3, recHp_h3, recHp_mu1]
  refine withTable_h3_congr _ _ _ fun a ha => ?_
  have h1 : ba a = rho := (ByteArray.append_right_inj _).1 (push_injective 3 ha)
  have h2 : a = blk 16 rho := by rw [← h1, blk_ba]
  rw [h2]
  exact h

end RealH3

/-! ## Prefixes and the rows with `H₃`'s columns -/

/-- The prefix lengths of the model. -/
abbrev preMax : ℕ := 1024

/-- **A prefix**: a byte string of fewer than `preMax` bytes. -/
abbrev Pre := Σ n : Fin preMax, Bytes n

/-- The prefix of a byte string (the empty prefix if it has `preMax` bytes or more). Irreducible:
nothing unfolds it (a prefix is compared as a key, never computed). -/
irreducible_def preKey (b : ByteArray) : Pre :=
  if h : b.size < preMax then ⟨⟨b.size, h⟩, fun i => b.get! i⟩ else ⟨⟨0, by decide⟩, Fin.elim0⟩

/-- **`H₃`'s column at one `ρ`**: `H₃(x ‖ ρ ‖ 3)` for every prefix `x`. -/
abbrev H3Row := Pre → Bytes 32

/-- **A row of the shared tables with `H₃`**: the cipher's row and `H₃`'s column at the same
16-byte block. -/
abbrev RowH (R : Type) := R × H3Row

/-- The prover, the verifier and the simulator read a row as its cipher part. -/
instance CipherRow.rowH {R : Type} [CipherRow R] : CipherRow (RowH R) := ⟨fun r => CipherRow.row r.1⟩

section Columns

variable {R : Type} {p : Params}

/-- **The slice at prefix `k`** of the shared tables: `ρ ↦ H₃(k ‖ ρ ‖ 3)`. -/
def h3At (s : ShG (RowH R) p) (k : Pre) : Tab3 := fun j => (s.2.2 j).2 k

/-- The shared tables with the slice at prefix `k` overwritten by `g`. -/
def setK (s : ShG (RowH R) p) (k : Pre) (g : Tab3) : ShG (RowH R) p :=
  (s.1, s.2.1, fun j => ((s.2.2 j).1, Function.update (s.2.2 j).2 k (g j)))

@[simp] lemma h3At_setK (s : ShG (RowH R) p) (k : Pre) (g : Tab3) : h3At (setK s k g) k = g := by
  funext j
  simp [h3At, setK]

lemma h3At_setK_ne (s : ShG (RowH R) p) {k k' : Pre} (h : k' ≠ k) (g : Tab3) :
    h3At (setK s k g) k' = h3At s k' := by
  funext j
  simp [h3At, setK, Function.update_of_ne h]

@[simp] lemma setK_setK (s : ShG (RowH R) p) (k : Pre) (g g' : Tab3) :
    setK (setK s k g) k g' = setK s k g' := by
  simp [setK]

@[simp] lemma setK_h3At (s : ShG (RowH R) p) (k : Pre) : setK s k (h3At s k) = s := by
  obtain ⟨a, b, c⟩ := s
  simp only [setK, h3At, Function.update_eq_self]

/-- Exchange the slice at `k` with an independent slice. -/
def swapK (k : Pre) (a : Tab3 × ShG (RowH R) p) : Tab3 × ShG (RowH R) p :=
  (h3At a.2 k, setK a.2 k a.1)

lemma swapK_involutive (k : Pre) : Function.Involutive (swapK (R := R) (p := p) k) := by
  intro a
  simp only [swapK, h3At_setK, setK_setK, setK_h3At]

variable [Fintype R]

/-- **Overwriting a column with an independent uniform slice keeps the tables uniform.** -/
theorem pr_setK (k : Pre) (F : ShG (RowH R) p → Prop) :
    pr (Tab3 × ShG (RowH R) p) (fun a => F (setK a.2 k a.1)) = pr (ShG (RowH R) p) F := by
  have e := pr_equiv (swapK_involutive (R := R) (p := p) k).toPerm (fun a => F a.2)
  have e' : pr (Tab3 × ShG (RowH R) p) (fun a => F a.2) = pr (ShG (RowH R) p) F := pr_prod_snd F
  rw [← e'] at *
  exact e

/-- `pr_setK` with an extra coordinate that may choose the prefix. -/
theorem pr_prod_setK {A : Type*} [Fintype A] (k : A → Pre) (Φ : A → ShG (RowH R) p → Prop) :
    pr (A × (Tab3 × ShG (RowH R) p)) (fun z => Φ z.1 (setK z.2.2 (k z.1) z.2.1)) =
      pr (A × ShG (RowH R) p) (fun z => Φ z.1 z.2) := by
  rw [pr_prod, pr_prod]
  exact congrArg (· / (Fintype.card A : ℝ))
    (Finset.sum_congr rfl fun a _ => pr_setK (k a) (Φ a))

/-- **An event of a proof that reads its slice off the shared tables** (and is otherwise blind to
the `H₃` columns) **has the probability of the same event with an independent slice.** The slice
coordinate `g` of the left-hand tape is unused. -/
theorem pr_h3At_slice {Γ ρT : Type*} [Fintype Γ] [Fintype ρT] (κ : Γ → Pre)
    (C : Γ → ρT → Tab3 → ShG (RowH R) p → Prop)
    (hC : ∀ γ r G s k g, C γ r G (setK s k g) ↔ C γ r G s) :
    pr (Γ × ((ρT × Tab3) × ShG (RowH R) p)) (fun z => C z.1 z.2.1.1 (h3At z.2.2 (κ z.1)) z.2.2) =
      pr (Γ × ((ρT × Tab3) × ShG (RowH R) p)) (fun z => C z.1 z.2.1.1 z.2.1.2 z.2.2) := by
  let Φ : (Γ × ρT) → ShG (RowH R) p → Prop := fun a s => C a.1 a.2 (h3At s (κ a.1)) s
  have hR : pr (Γ × ((ρT × Tab3) × ShG (RowH R) p)) (fun z => C z.1 z.2.1.1 z.2.1.2 z.2.2) =
      pr ((Γ × ρT) × (Tab3 × ShG (RowH R) p)) (fun z =>
        Φ z.1 (setK z.2.2 (κ z.1.1) z.2.1)) := by
    let e : (Γ × ρT) × (Tab3 × ShG (RowH R) p) ≃ Γ × ((ρT × Tab3) × ShG (RowH R) p) :=
      { toFun := fun z => (z.1.1, ((z.1.2, z.2.1), z.2.2))
        invFun := fun z => ((z.1, z.2.1.1), (z.2.1.2, z.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_congr fun z => ?_
    simp only [Φ, e, Equiv.coe_fn_mk, h3At_setK]
    exact (hC _ _ _ _ _ _).symm
  have hL : pr (Γ × ((ρT × Tab3) × ShG (RowH R) p)) (fun z =>
      C z.1 z.2.1.1 (h3At z.2.2 (κ z.1)) z.2.2) =
      pr ((Γ × ρT) × ShG (RowH R) p) (fun z => Φ z.1 z.2) := by
    let e : Tab3 × ((Γ × ρT) × ShG (RowH R) p) ≃ Γ × ((ρT × Tab3) × ShG (RowH R) p) :=
      { toFun := fun z => (z.2.1.1, ((z.2.1.2, z.1), z.2.2))
        invFun := fun z => (z.2.1.2, ((z.1, z.2.1.1), z.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    exact pr_prod_snd (fun z : (Γ × ρT) × ShG (RowH R) p => Φ z.1 z.2)
  rw [hR, hL, pr_prod_setK (fun a : Γ × ρT => κ a.1) Φ]

end Columns

/-! ## The prover and the simulator's programming do not read the `H₃` columns -/

section Blind

variable {R : Type} [CipherRow R] {p : Params} (Hb : Hashes) (st : Statement) (w : ByteArray)

@[simp] lemma realROb_setK (rho : ByteArray) (G3 : Tab3) (s : ShG (RowH R) p) (k : Pre) (g : Tab3) :
    realROb p Hb st w rho G3 (setK s k g) = realROb p Hb st w rho G3 s := rfl

@[simp] lemma progRO_setK (c : SimCoins p) (s : ShG (RowH R) p) (k : Pre) (g : Tab3) :
    progRO p Hb st c (setK s k g) = setK (progRO p Hb st c s) k g := rfl

@[simp] lemma h3At_progRO (c : SimCoins p) (s : ShG (RowH R) p) (k : Pre) :
    h3At (progRO p Hb st c s) k = h3At s k := rfl

end Blind

/-! ## What a reader of the slice at one key reads of the shared tables -/

section Reads

variable {R : Type} {p : Params} {X : Sort*}

/-- A reader of its slice and the shared tables, run on the slice at prefix `k`, reads `H₅` as
before. -/
lemma rd5_h3At {f : Tab3 → ShG (RowH R) p → X} {q : ℕ} (hf : ∀ G, Rd5 (f G) q) (k : Pre) :
    Rd5 (fun s => f (h3At s k) s) q := by
  choose Q hQc hQ using hf
  exact ⟨fun s => Q (h3At s k) s, fun s => hQc _ s, fun s G5 h => hQ (h3At s k) s G5 h⟩

/-- **A reader of its slice at the key `j` only**, run on the slice at prefix `k` of the shared
tables, reads one row more: row `j`. -/
lemma rdE_h3At {f : Tab3 → ShG (RowH R) p → X} {q : ℕ} (j : Blk)
    (h3 : ∀ G G' s, G j = G' j → f G s = f G' s) (hf : ∀ G, RdE (f G) q) (k : Pre) :
    RdE (fun s => f (h3At s k) s) (q + 1) := by
  choose Q hQc hQ using hf
  refine ⟨fun s => insert j (Q (h3At s k) s), fun s => (card_insert_le _ _).trans
    (Nat.add_le_add_right (hQc _ s) 1), fun s E h => ?_⟩
  have hj : h3At (s.1, s.2.1, E) k j = h3At s k j := by
    simp only [h3At]
    rw [h j (mem_insert_self _ _)]
  show f (h3At (s.1, s.2.1, E) k) (s.1, s.2.1, E) = f (h3At s k) s
  rw [h3 _ _ _ hj]
  exact hQ (h3At s k) s E fun x hx => h x (mem_insert_of_mem hx)

end Reads

section SetKSimp

variable {R : Type} {p : Params}

@[simp] lemma setK_fst (s : ShG (RowH R) p) (k : Pre) (g : Tab3) : (setK s k g).1 = s.1 := rfl

@[simp] lemma setK_snd_fst (s : ShG (RowH R) p) (k : Pre) (g : Tab3) : (setK s k g).2.1 = s.2.1 := rfl

@[simp] lemma rowFn_setK [CipherRow R] (s : ShG (RowH R) p) (k : Pre) (g : Tab3) :
    rowFn (setK s k g).2.2 = rowFn s.2.2 := rfl

end SetKSimp

/-! ## A reader of the shared tables, with one column overwritten -/

section SetKReads

variable {R : Type} {p : Params} {X : Sort*}

/-- A reader of the shared tables, run with the column at `k` overwritten by `G`, reads `G` at
the rows it reads. -/
lemma rd3_setK {f : ShG (RowH R) p → X} {q : ℕ} (hf : RdE f q) (s : ShG (RowH R) p) (k : Pre) :
    Rd3 (fun G => f (setK s k G)) q := by
  obtain ⟨Q, hQc, hQ⟩ := hf
  refine ⟨fun G => Q (setK s k G), fun G => hQc _, fun G G' h => ?_⟩
  exact hQ (setK s k G) (setK s k G').2.2 fun j hj => by
    simp only [setK]
    rw [h j hj]

lemma rd5_setK {f : ShG (RowH R) p → X} {q : ℕ} (hf : Rd5 f q) (k : Pre) (G : Tab3) :
    Rd5 (fun s => f (setK s k G)) q := by
  obtain ⟨Q, hQc, hQ⟩ := hf
  exact ⟨fun s => Q (setK s k G), fun s => hQc _, fun s G5 h => hQ (setK s k G) G5 h⟩

lemma rdE_setK {f : ShG (RowH R) p → X} {q : ℕ} (hf : RdE f q) (k : Pre) (G : Tab3) :
    RdE (fun s => f (setK s k G)) q := by
  obtain ⟨Q, hQc, hQ⟩ := hf
  refine ⟨fun s => Q (setK s k G), fun s => hQc _, fun s E h => ?_⟩
  exact hQ (setK s k G) (setK (s.1, s.2.1, E) k G).2.2 fun j hj => by
    simp only [setK]
    rw [h j hj]

end SetKReads

/-! ## Zero knowledge with the `H₃` columns in the rows -/

section RowH

variable {R : Type} [Fintype R] [CipherRow R] {p : Params}

/-- The shared tables as the tables with plain rows and the `H₃` columns. -/
def splitH : ShG (RowH R) p ≃ (Blk → H3Row) × ShG R p where
  toFun s := (fun j => (s.2.2 j).2, (s.1, s.2.1, fun j => (s.2.2 j).1))
  invFun a := (a.2.1, a.2.2.1, fun j => (a.2.2.2 j, a.1 j))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Plain tables with `H₃` columns added. -/
abbrev combH (s : ShG R p) (H : Blk → H3Row) : ShG (RowH R) p := splitH.symm (H, s)

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

lemma realRO_combH (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params) (H : Blk → H3Row) :
    realRO st.params Hb st w ρ G3 (combH s H) = realRO st.params Hb st w ρ G3 s := rfl

lemma progRO_combH (c : SimCoins st.params) (s : ShG R st.params) (H : Blk → H3Row) :
    progRO st.params Hb st c (combH s H) = combH (progRO st.params Hb st c s) H := rfl

variable {Hb st w}

/-- A budget on the tables with `H₃` columns is one on the plain tables, the columns fixed. -/
lemma Budget.withH {O : Type*} {q3 q5 qE : ℕ} {D : O → Tab3 → ShG (RowH R) p → Prop}
    (hD : Budget p q3 q5 qE D) (H : Blk → H3Row) :
    Budget p q3 q5 qE (fun o G s => D o G (combH s H)) where
  h3 o s := hD.h3 o (combH s H)
  h5 o G := by
    obtain ⟨Q, hQc, hQ⟩ := hD.h5 o G
    exact ⟨fun s => Q (combH s H), fun s => hQc _, fun s G5 h => hQ (combH s H) G5 h⟩
  hE o G := by
    obtain ⟨Q, hQc, hQ⟩ := hD.hE o G
    refine ⟨fun s => Q (combH s H), fun s => hQc _, fun s E h => ?_⟩
    exact hQ (combH s H) (fun j => (E j, H j)) fun j hj => by
      simp only [combH, splitH, Equiv.coe_fn_symm_mk]
      rw [h j hj]

variable [ZKRow R]

/-- **Zero knowledge with the `H₃` columns in the rows**: `ZKRow R`'s theorem for the tables
`ShG (RowH R) p` (the columns are uniform data the proof does not read; averaged over them). -/
noncomputable instance ZKRow.rowH : ZKRow (RowH R) where
  εz := ZKRow.εz R
  εz_mono := ZKRow.εz_mono (R := R)
  εz_nonneg := ZKRow.εz_nonneg (R := R)
  zk Hb st w _ hlr hzk hHb hp q3 q5 qE D hD := by
    let e1 : (Blk → H3Row) × ((Bytes 16 × Tab3) × ShG R st.params) ≃
        (Bytes 16 × Tab3) × ShG (RowH R) st.params :=
      { toFun := fun b => (b.2.1, combH b.2.2 b.1)
        invFun := fun a => ((splitH a.2).1, (a.1, (splitH a.2).2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e2 : (Blk → H3Row) × ((SimCoins st.params × Tab3) × ShG R st.params) ≃
        (SimCoins st.params × Tab3) × ShG (RowH R) st.params :=
      { toFun := fun b => (b.2.1, combH b.2.2 b.1)
        invFun := fun a => ((splitH a.2).1, (a.1, (splitH a.2).2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e1, ← pr_equiv e2]
    refine abs_pr_prod_sub_le _ _ fun H => ?_
    exact ZKRow.zk (R := R) Hb st w hlr hzk hHb hp (fun o G s => D o G (combH s H)) (hD.withH H)

@[simp] lemma ZKRow.εz_rowH : ZKRow.εz (RowH R) = ZKRow.εz R := rfl

end RowH

/-! ## Zero knowledge for a prover that reads its slice off the shared tables -/

section Shared

variable {R : Type} [Fintype R] {p : Params}

/-- **The distinguisher of the slice prover** built from one of the shared prover: the slice `G`
written into the column at `k`, the game's own (unused) slice argument fixed to `g`. -/
def dCol {O : Type*} (D : O → Tab3 → ShG (RowH R) p → Prop) (k : Pre) (g : Tab3) :
    O → Tab3 → ShG (RowH R) p → Prop :=
  fun o G s => D o g (setK s k G)

/-- `dCol`'s budget: the distinguisher's reads of the rows, now also reads of the slice. -/
lemma Budget.dCol {O : Type*} {q3 q5 qE : ℕ} {D : O → Tab3 → ShG (RowH R) p → Prop}
    (hD : Budget p q3 q5 qE D) (k : Pre) (g : Tab3) : Budget p qE q5 qE (dCol D k g) where
  h3 o s := by
    obtain ⟨Q, hQc, hQ⟩ := hD.hE o g
    refine ⟨fun G => Q (setK s k G), fun G => hQc _, fun G G' h => ?_⟩
    exact hQ (setK s k G) (setK s k G').2.2 fun j hj => by
      simp only [setK]
      rw [h j hj]
  h5 o G := by
    obtain ⟨Q, hQc, hQ⟩ := hD.h5 o g
    exact ⟨fun s => Q (setK s k G), fun s => hQc _, fun s G5 h => hQ (setK s k G) G5 h⟩
  hE o G := by
    obtain ⟨Q, hQc, hQ⟩ := hD.hE o g
    refine ⟨fun s => Q (setK s k G), fun s => hQc _, fun s E h => ?_⟩
    exact hQ (setK s k G) (setK (s.1, s.2.1, E) k G).2.2 fun j hj => by
      simp only [setK]
      rw [h j hj]

/-- **Zero knowledge with one shared `H₃`.** If the slice prover `P` (which does not read the
`H₃` columns, `hP`) is `ZeroKnowledgeRO` at every budget, with a simulator whose programming does
not touch them (`hprog`), then the prover that reads its slice off the shared tables at its
prefix `key x w` is `ZeroKnowledgeRO` against the distinguishers with budget `(q₃, q₅, q_E)`
(their slice argument unused by the prover) with the error at `(q_E, q₅, q_E)`. No hypothesis on
the prefixes: a distinguisher (another proof of the game, the adversary) that reads the same
prefix reads this proof's slice through rows, which the error accounts for. -/
theorem ZeroKnowledgeRO.shared {I W C O ρT : Type*} [Fintype C] [Fintype ρT]
    {Rl : I → W → Prop} {P : I → W → ρT → Tab3 → ShG (RowH R) p → O} {sim : I → C → O}
    {prog : I → C → ShG (RowH R) p → ShG (RowH R) p} {ε : ℕ → ℕ → ℕ → ℝ} (key : I → W → Pre)
    (hP : ∀ x w r G s k g, P x w r G (setK s k g) = P x w r G s)
    (hprog : ∀ x c s k g, prog x c (setK s k g) = setK (prog x c s) k g)
    (h : ∀ a b c, ZeroKnowledgeRO Rl P sim prog (Budget p a b c) (ε a b c)) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO Rl (fun x w r _g s => P x w r (h3At s (key x w)) s) sim prog
      (Budget p q3 q5 qE) (ε qE q5 qE) := by
  intro x w hxw D hD
  set k := key x w
  have e1 : pr ((ρT × Tab3) × ShG (RowH R) p) (fun a =>
      D (P x w a.1.1 (h3At a.2 k) a.2) a.1.2 a.2) =
      pr (Tab3 × ((ρT × Tab3) × ShG (RowH R) p)) (fun b =>
        dCol D k b.1 (P x w b.2.1.1 b.2.1.2 b.2.2) b.2.1.2 b.2.2) := by
    let e : Tab3 × ((ρT × Tab3) × ShG (RowH R) p) ≃ (ρT × Tab3) × (Tab3 × ShG (RowH R) p) :=
      { toFun := fun b => ((b.2.1.1, b.1), (b.2.1.2, b.2.2))
        invFun := fun a => (a.1.2, ((a.1.1, a.2.1), a.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e.symm, ← pr_prod_setK (fun _ => k)
      (fun (a : ρT × Tab3) s => D (P x w a.1 (h3At s k) s) a.2 s)]
    refine pr_congr fun b => ?_
    simp only [dCol, e, Equiv.coe_fn_symm_mk, h3At_setK, hP]
  have e2 : pr ((C × Tab3) × ShG (RowH R) p) (fun a => D (sim x a.1.1) a.1.2 (prog x a.1.1 a.2)) =
      pr (Tab3 × ((C × Tab3) × ShG (RowH R) p)) (fun b =>
        dCol D k b.1 (sim x b.2.1.1) b.2.1.2 (prog x b.2.1.1 b.2.2)) := by
    let e : Tab3 × ((C × Tab3) × ShG (RowH R) p) ≃ (C × Tab3) × (Tab3 × ShG (RowH R) p) :=
      { toFun := fun b => ((b.2.1.1, b.1), (b.2.1.2, b.2.2))
        invFun := fun a => (a.1.2, ((a.1.1, a.2.1), a.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e.symm, ← pr_prod_setK (fun _ => k)
      (fun (a : C × Tab3) s => D (sim x a.1) a.2 (prog x a.1 s))]
    refine pr_congr fun b => ?_
    simp only [dCol, e, Equiv.coe_fn_symm_mk, hprog]
  rw [e1, e2]
  exact abs_pr_prod_sub_le _ _ fun g => h qE q5 qE x w hxw (dCol D k g) (hD.dCol k g)

end Shared

end VoleMole.ZK.Sim
