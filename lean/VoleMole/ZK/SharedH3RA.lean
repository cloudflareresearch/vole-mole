import VoleMole.ZK.AdaptRO
import VoleMole.ZK.SharedH3

/-!
# One shared `H₃` with statements chosen from the tables

`ZK/SharedH3.lean` moves zero knowledge to one shared `H₃` for a statement fixed before the tables
are drawn: the proof's column is re-sampled at a key known in advance. With a statement chosen by a
reader of the tables (`Privacy/AdaptiveRO.lean`'s `ZeroKnowledgeROA`), the prefix, hence the
column, is known only after the reader ran, and the reader may have read that column first: an
adversary that reads `H₃` at a future proof's prefix before choosing the statement. Here:

* **`swapOff k U`**: exchange an independent slice with the column at `k`, off the rows `U`. For a
  reader `S` with read sets `Q` (`SReads`, no slice reads), `t ↦ swapOff (k (S t)) (Q t) t` is a
  measure-preserving involution that keeps `S`'s output: the reader's rows are kept, and so are its
  reads. After it, the proof's column agrees with the independent slice at every row the reader did
  not read; the real proof reads its column only at its fresh `ρ`, which is a read row with
  probability `≤ s_E·2⁻¹²⁸`.
* **`ZeroKnowledgeROA.shared`**: a prover that reads its slice off the shared tables at the prefix of
  its statement, against readers that do not read the (game's own, unused) slice and
  distinguishers that do not either (`SReads p · 0 s₂ s₅ s_E`, `Budget p 0 q₅ q_E`), is
  `ZeroKnowledgeROA` with the slice prover's error at `(q_E, q₅, q_E)` plus `s_E·2⁻¹²⁸`. This is the
  only place a "future prefix" read costs anything: the birthday-type event that the fresh `ρ` is
  one of the reader's rows.
* **`pr_h3At_sliceA`**: the same for a collision event of such a proof (`s_E·2⁻¹²⁸`).
* **`ZKPRow.rowH`**: `zk_roP` (the patched theorem behind `zk_adaptive`) for the tables with
  `H₃`'s columns in the rows.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

/-! ## The `H₃` columns of the rows -/

section Cols

variable {R : Type} {p : Params}

/-- The shared tables with all `H₃` columns replaced by `E`. -/
def withH (s : ShG (RowH R) p) (E : Blk → H3Row) : ShG (RowH R) p :=
  (s.1, s.2.1, fun j => ((s.2.2 j).1, E j))

/-- The `H₃` columns of the shared tables. -/
def hcols (s : ShG (RowH R) p) : Blk → H3Row := fun j => (s.2.2 j).2

@[simp] lemma withH_hcols (s : ShG (RowH R) p) : withH s (hcols s) = s := rfl

@[simp] lemma hcols_withH (s : ShG (RowH R) p) (E : Blk → H3Row) : hcols (withH s E) = E := rfl

@[simp] lemma withH_withH (s : ShG (RowH R) p) (E E' : Blk → H3Row) :
    withH (withH s E) E' = withH s E' := rfl

/-- **Exchange the slice with the column at `k`, off the rows `U`.** -/
def swapOff (k : Pre) (U : Finset Blk) (a : Tab3 × ShG (RowH R) p) : Tab3 × ShG (RowH R) p :=
  (fun j => if j ∈ U then a.1 j else (a.2.2.2 j).2 k,
    withH a.2 fun j => if j ∈ U then (a.2.2.2 j).2 else Function.update (a.2.2.2 j).2 k (a.1 j))

lemma swapOff_swapOff (k : Pre) (U : Finset Blk) (a : Tab3 × ShG (RowH R) p) :
    swapOff k U (swapOff k U a) = a := by
  obtain ⟨g, s1, s2, s3⟩ := a
  simp only [swapOff, withH, Prod.mk.injEq]
  refine ⟨funext fun j => ?_, trivial, trivial, funext fun j => ?_⟩
  · by_cases hj : j ∈ U <;> simp [hj]
  · by_cases hj : j ∈ U <;> simp [hj]

lemma swapOff_fst (k : Pre) (U : Finset Blk) (a : Tab3 × ShG (RowH R) p) :
    (swapOff k U a).2.1 = a.2.1 := rfl

lemma swapOff_rows_of_mem (k : Pre) {U : Finset Blk} (a : Tab3 × ShG (RowH R) p) {j : Blk}
    (hj : j ∈ U) : (swapOff k U a).2.2.2 j = a.2.2.2 j := by
  simp [swapOff, withH, hj]

lemma h3At_swapOff_of_not_mem (k : Pre) {U : Finset Blk} (a : Tab3 × ShG (RowH R) p) {j : Blk}
    (hj : j ∉ U) : h3At (swapOff k U a).2 k j = a.1 j := by
  simp [swapOff, withH, h3At, hj]

/-- The shared tables after `swapOff` differ only in their `H₃` columns. -/
lemma swapOff_snd (k : Pre) (U : Finset Blk) (a : Tab3 × ShG (RowH R) p) :
    (swapOff k U a).2 = withH a.2 (hcols (swapOff k U a).2) := rfl

/-- **A map that only reprograms the plain part commutes with `swapOff`.** -/
lemma swapOff_map {L : ShG (RowH R) p → ShG (RowH R) p}
    (hL : ∀ s E, L (withH s E) = withH (L s) E) (k : Pre) (U : Finset Blk) (g : Tab3)
    (s : ShG (RowH R) p) : swapOff k U (g, L s) = ((swapOff k U (g, s)).1, L (swapOff k U (g, s)).2) := by
  have hc : hcols (L s) = hcols s := by
    have := congrArg hcols (hL s (hcols s))
    simpa using this
  have hc' : ∀ j, ((L s).2.2 j).2 = (s.2.2 j).2 := fun j => congrFun hc j
  simp only [swapOff, hc']
  refine Prod.ext rfl ?_
  dsimp only
  rw [hL]

end Cols

section ColsBlind

variable {R : Type} [CipherRow R] {p : Params} (Hb : Hashes) (st : Statement) (w : ByteArray)

@[simp] lemma realROb_withH (rho : ByteArray) (G3 : Tab3) (s : ShG (RowH R) p) (E : Blk → H3Row) :
    realROb p Hb st w rho G3 (withH s E) = realROb p Hb st w rho G3 s := rfl

@[simp] lemma progRO_withH (c : SimCoins p) (s : ShG (RowH R) p) (E : Blk → H3Row) :
    progRO p Hb st c (withH s E) = withH (progRO p Hb st c s) E := rfl

@[simp] lemma h3At_withH (s : ShG (RowH R) p) (E : Blk → H3Row) (k : Pre) :
    h3At (withH s E) k = fun j => E j k := rfl

end ColsBlind

/-! ## A uniform `ρ` hits a read row rarely -/

lemma pr_mem_rows_le {T : Type*} [Fintype T] [Nonempty T] (U : T → Finset Blk) {n : ℕ} (hU : ∀ t, (U t).card ≤ n) :
    pr (Bytes 16 × T) (fun z => z.1 ∈ U z.2) ≤ n / 2 ^ 128 := by
  refine pr_le_of_snd fun t => ?_
  have h1 : pr (Bytes 16) (fun ρ => ρ ∈ U t) ≤ ((U t).card : ℝ) / 2 ^ 128 := by
    have := pr_mem_le (α := Bytes 16) id Function.injective_id (U t)
    rw [card_bytes16] at this
    exact this.trans (le_of_eq (by norm_num))
  have : ((U t).card : ℝ) ≤ n := by exact_mod_cast hU t
  exact h1.trans (by gcongr)

/-! ## The involution of a reader -/

section Reader

variable {R : Type} [Fintype R] {p : Params} {X : Type*}

/-- A reader that does not read the slice reads no slice keys. -/
lemma sReads_slice_empty {Q : Tb (RowH R) p → RS p} {s2 s5 sE : ℕ}
    (hc : ∀ t, (Q t).1.card ≤ 0 ∧ (Q t).2.1.card ≤ s2 ∧ (Q t).2.2.1.card ≤ s5 ∧ (Q t).2.2.2.card ≤ sE)
    (t : Tb (RowH R) p) : (Q t).1 = ∅ :=
  Finset.card_eq_zero.1 (Nat.le_zero.1 (hc t).1)

/-- **`swapOff` at a reader's rows keeps the reader's reads.** -/
lemma agT_swapOff {Q : Tb (RowH R) p → RS p} (hQ1 : ∀ t, (Q t).1 = ∅) (k : Pre) (t : Tb (RowH R) p) :
    AgT (Q t) t (swapOff k (Q t).2.2.2 t) := by
  refine ⟨fun j hj => ?_, fun j _ => rfl, fun j _ => rfl, fun j hj => ?_⟩
  · rw [hQ1 t] at hj
    exact absurd hj (Finset.notMem_empty _)
  · exact (swapOff_rows_of_mem k t hj).symm

end Reader

/-! ## Zero knowledge with a statement chosen from the tables, one shared `H₃` -/

section Shared

variable {R : Type} [Fintype R] [Nonempty R] {p : Params}

/-- `Rd3 · 0`: the function does not depend on the slice. -/
lemma rd3_zero {X : Sort*} {f : Tab3 → X} (h : Rd3 f 0) (g g' : Tab3) : f g' = f g := by
  obtain ⟨Q, hQc, hQ⟩ := h
  exact hQ g g' fun k hk => absurd (Finset.card_eq_zero.1 (Nat.le_zero.1 (hQc g)) ▸ hk)
    (Finset.notMem_empty _)

/-- The budget of the slice prover's distinguisher built from a slice-blind one. -/
lemma Budget.offSwap {O : Type*} {q5 qE : ℕ} {D : O → Tab3 → ShG (RowH R) p → Prop}
    (hD : Budget p 0 q5 qE D) (k : Pre) (U : Finset Blk) :
    Budget p qE q5 qE (fun o g s => D o g (swapOff k U (g, s)).2) where
  h3 o s := by
    obtain ⟨Q, hQc, hQ⟩ := hD.hE o default
    refine ⟨fun g => Q (swapOff k U (g, s)).2, fun g => hQc _, fun g g' h => ?_⟩
    have e1 : ∀ g'' (S : ShG (RowH R) p), D o g'' S = D o default S := fun g'' _ =>
      rd3_zero (hD.h3 o _) default g''
    beta_reduce
    rw [e1 g, e1 g']
    exact hQ (swapOff k U (g, s)).2 (swapOff k U (g', s)).2.2.2 fun j hj => by
      simp only [swapOff, Sim.withH]
      rw [h j hj]
  h5 o g := by
    obtain ⟨Q, hQc, hQ⟩ := hD.h5 o g
    exact ⟨fun s => Q (swapOff k U (g, s)).2, fun s => hQc _, fun s G5 h =>
      hQ (swapOff k U (g, s)).2 G5 h⟩
  hE o g := by
    obtain ⟨Q, hQc, hQ⟩ := hD.hE o g
    refine ⟨fun s => Q (swapOff k U (g, s)).2, fun s => hQc _, fun s E h => ?_⟩
    exact hQ (swapOff k U (g, s)).2 (swapOff k U (g, (s.1, s.2.1, E))).2.2.2 fun j hj => by
      simp only [swapOff, Sim.withH]
      rw [h j hj]

/-- **Zero knowledge for a statement chosen from the tables, with one shared `H₃`.** The slice
prover `P` does not read the `H₃` columns (`hP`) and reads its slice only at its randomness
(`hP3`, for witnesses in the relation); the simulator's programming does not touch the columns
(`hprog`). Then the prover that reads its slice off the shared tables at the prefix `key x w` of the
chosen statement is `ZeroKnowledgeROA` against slice-blind readers and distinguishers, with the
slice prover's error at `(q_E, q₅, q_E)` plus `s_E·2⁻¹²⁸` (the fresh `ρ` is one of the reader's rows:
the only event where a read of the future prefix matters). -/
theorem ZeroKnowledgeROA.shared {I W C O : Type*} [Fintype C]
    {Rl : I → W → Prop} {P : I → W → Bytes 16 → Tab3 → ShG (RowH R) p → O} {sim : I → C → O}
    {prog : I → C → ShG (RowH R) p → ShG (RowH R) p} {ε : ℝ} (key : I → W → Pre)
    {s2 s5 sE q5 qE : ℕ}
    (hP : ∀ x w r G s E, P x w r G (withH s E) = P x w r G s)
    (hP3 : ∀ x w, Rl x w → ∀ r G G' s, G r = G' r → P x w r G s = P x w r G' s)
    (hprog : ∀ x c s E, prog x c (withH s E) = withH (prog x c s) E)
    (h : ZeroKnowledgeROA Rl P sim prog (fun _ Sx => SReads p Sx 0 s2 s5 sE) (Budget p qE q5 qE) ε) :
    ZeroKnowledgeROA Rl (fun x w r _g s => P x w r (h3At s (key x w)) s) sim prog
      (fun _ Sx => SReads p Sx 0 s2 s5 sE) (Budget p 0 q5 qE) (ε + sE / 2 ^ 128) := by
  intro X Sx stw hS hR dummy D hD
  obtain ⟨Q, hQ, hc⟩ := hS
  have hbad : pr (Bytes 16 × Tb (RowH R) p) (fun z => z.1 ∈ (Q z.2).2.2.2) ≤ sE / 2 ^ 128 :=
    pr_mem_rows_le (T := Tb (RowH R) p) (fun t => (Q t).2.2.2) fun t => (hc t).2.2.2
  have hQ1 := sReads_slice_empty hc
  let kx : X → Pre := fun x => (stw x).elim (preKey .empty) fun iw => key iw.1 iw.2
  let ψ : Tb (RowH R) p → Tb (RowH R) p := fun t => swapOff (kx (Sx t)) (Q t).2.2.2 t
  have hinv : ∀ t, Q (ψ t) = Q t ∧ Sx (ψ t) = Sx t := fun t => hQ t (ψ t) (agT_swapOff hQ1 _ t)
  have hψψ : Function.Involutive ψ := fun t => by
    show swapOff (kx (Sx (ψ t))) (Q (ψ t)).2.2.2 (ψ t) = t
    rw [(hinv t).1, (hinv t).2]
    exact swapOff_swapOff _ _ t
  -- The slice-blind distinguisher.
  have hfree : ∀ x o g g' s, D x o g' s ↔ D x o g s := fun x o g g' s =>
    Iff.of_eq (rd3_zero ((hD x).h3 o s) g g')
  -- The slice prover's reader and distinguisher.
  let Sx' : Tb (RowH R) p → X × RS p := fun t => (Sx t, Q t)
  let stw' : X × RS p → Option (I × W) := fun x' => stw x'.1
  let D' : X × RS p → O → Tab3 → ShG (RowH R) p → Prop := fun x' o g s =>
    D x'.1 o g (swapOff (kx x'.1) x'.2.2.2.2 (g, s)).2
  have hS' : SReads p Sx' 0 s2 s5 sE :=
    ⟨Q, fun t t' ht => ⟨(hQ t t' ht).1, by simp only [Sx', (hQ t t' ht).1, (hQ t t' ht).2]⟩, hc⟩
  have hD' : ∀ x', Budget p qE q5 qE (D' x') := fun x' => (hD x'.1).offSwap _ _
  have hkey := h (X × RS p) Sx' stw' hS' (fun x' i w h' => hR x'.1 i w h') dummy D' hD'
  -- The real side: equal to the slice prover's off `ρ ∈ U`.
  have eR : pr (Bytes 16 × Tb (RowH R) p) (fun z => D (Sx z.2)
      (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy (Sx z.2) z.1 z.2.1 z.2.2)
        z.2.1 z.2.2) =
      pr (Bytes 16 × Tb (RowH R) p) (fun z => D (Sx z.2)
        (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy (Sx z.2) z.1 (ψ z.2).1
          (ψ z.2).2) (ψ z.2).1 (ψ z.2).2) := by
    refine (pr_equiv (Equiv.prodCongr (Equiv.refl (Bytes 16)) hψψ.toPerm) _).symm.trans
      (pr_congr fun z => ?_)
    show D (Sx (ψ z.2)) (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy
        (Sx (ψ z.2)) z.1 (ψ z.2).1 (ψ z.2).2) (ψ z.2).1 (ψ z.2).2 ↔ _
    rw [(hinv z.2).2]
  have hRl : |pr (Bytes 16 × Tb (RowH R) p) (fun z => D (Sx z.2)
      (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy (Sx z.2) z.1 (ψ z.2).1
        (ψ z.2).2) (ψ z.2).1 (ψ z.2).2) -
      pr (Bytes 16 × Tb (RowH R) p) (fun z => D' (Sx' z.2)
        (outReal stw' P dummy (Sx' z.2) z.1 z.2.1 z.2.2) z.2.1 z.2.2)| ≤ sE / 2 ^ 128 := by
    refine le_trans (abs_pr_sub_le_of_agree _ _ (fun z => z.1 ∈ (Q z.2).2.2.2) ?_) ?_
    swap
    · exact hbad
    intro z hz
    obtain ⟨ρ, t⟩ := z
    have hz' : ρ ∉ (Q t).2.2.2 := hz
    show D (Sx t) (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy (Sx t) ρ
        (ψ t).1 (ψ t).2) (ψ t).1 (ψ t).2 ↔
      D (Sx t) (outReal stw P dummy (Sx t) ρ t.1 t.2) t.1 (ψ t).2
    refine (hfree _ _ t.1 (ψ t).1 _).trans ?_
    rcases hst : stw (Sx t) with _ | ⟨i, w⟩
    · simp only [outReal, hst, Option.elim]
    · simp only [outReal, hst, Option.elim]
      have hk : kx (Sx t) = key i w := by simp only [kx, hst, Option.elim]
      have h1 : h3At (ψ t).2 (key i w) ρ = t.1 ρ := by
        show h3At (swapOff (kx (Sx t)) (Q t).2.2.2 t).2 (key i w) ρ = t.1 ρ
        rw [hk]
        exact h3At_swapOff_of_not_mem _ t hz'
      rw [hP3 i w (hR _ i w hst) ρ _ _ _ h1, swapOff_snd, hP]
  -- The simulated side: equal.
  have hSm : pr (C × Tb (RowH R) p) (fun z => D' (Sx' z.2) (outSim stw' sim dummy (Sx' z.2) z.1)
        z.2.1 (progSim stw' prog (Sx' z.2) z.1 z.2.2)) =
      pr (C × Tb (RowH R) p) (fun z => D (Sx z.2) (outSim stw sim dummy (Sx z.2) z.1) z.2.1
        (progSim stw prog (Sx z.2) z.1 z.2.2)) := by
    refine (pr_equiv (Equiv.prodCongr (Equiv.refl C) hψψ.toPerm) _).symm.trans
      (pr_congr fun z => ?_)
    obtain ⟨c, t⟩ := z
    have hL : ∀ s E, progSim stw prog (Sx t) c (withH s E) =
        withH (progSim stw prog (Sx t) c s) E := fun s E => by
      unfold progSim
      rcases stw (Sx t) with _ | iw
      · rfl
      · exact hprog _ _ _ _
    show D (Sx (ψ t)) (outSim stw sim dummy (Sx (ψ t)) c) (ψ t).1
        (swapOff (kx (Sx (ψ t))) (Q (ψ t)).2.2.2 ((ψ t).1, progSim stw prog (Sx (ψ t)) c (ψ t).2)).2 ↔
      D (Sx t) (outSim stw sim dummy (Sx t) c) t.1 (progSim stw prog (Sx t) c t.2)
    rw [(hinv t).1, (hinv t).2]
    have e := swapOff_map hL (kx (Sx t)) (Q t).2.2.2 t.1 t.2
    have e' : ((ψ t).1, progSim stw prog (Sx t) c (ψ t).2) = swapOff (kx (Sx t)) (Q t).2.2.2
        (t.1, progSim stw prog (Sx t) c t.2) := e.symm
    rw [e', swapOff_swapOff]
    exact hfree _ _ _ _ _
  rw [eR]
  have := abs_sub_le (pr (Bytes 16 × Tb (RowH R) p) (fun z => D (Sx z.2)
      (outReal stw (fun x w r _g s => P x w r (h3At s (key x w)) s) dummy (Sx z.2) z.1 (ψ z.2).1
        (ψ z.2).2) (ψ z.2).1 (ψ z.2).2))
    (pr (Bytes 16 × Tb (RowH R) p) (fun z => D' (Sx' z.2)
        (outReal stw' P dummy (Sx' z.2) z.1 z.2.1 z.2.2) z.2.1 z.2.2))
    (pr (C × Tb (RowH R) p) (fun z => D (Sx z.2) (outSim stw sim dummy (Sx z.2) z.1) z.2.1
        (progSim stw prog (Sx z.2) z.1 z.2.2)))
  rw [← hSm] at this ⊢
  linarith

/-- **A collision event of a proof that reads its slice off the shared tables at the prefix of a
statement chosen from the tables** has, up to `s_E·2⁻¹²⁸`, the probability of the same event with an
independent slice. The event reads the slice only at `ρ` (`hC3`) and not the `H₃` columns
(`hC`); the reader does not read the slice. -/
theorem pr_h3At_sliceA {Γ X : Type*} [Fintype Γ] [Nonempty Γ] (Sx : Γ → Tb (RowH R) p → X) {s2 s5 sE : ℕ}
    (hS : ∀ γ, SReads p (Sx γ) 0 s2 s5 sE) (κ : Γ → X → Pre)
    (C : Γ → X → Bytes 16 → Tab3 → ShG (RowH R) p → Prop)
    (hC3 : ∀ γ x ρ G G' s, G ρ = G' ρ → (C γ x ρ G s ↔ C γ x ρ G' s))
    (hC : ∀ γ x ρ G s E, C γ x ρ G (withH s E) ↔ C γ x ρ G s) :
    |pr (Γ × (Bytes 16 × Tb (RowH R) p)) (fun z =>
        C z.1 (Sx z.1 z.2.2) z.2.1 (h3At z.2.2.2 (κ z.1 (Sx z.1 z.2.2))) z.2.2.2) -
      pr (Γ × (Bytes 16 × Tb (RowH R) p)) (fun z =>
        C z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2)| ≤ sE / 2 ^ 128 := by
  refine abs_pr_prod_sub_le _ _ fun γ => ?_
  obtain ⟨Q, hQ, hc⟩ := hS γ
  have hQ1 := sReads_slice_empty hc
  let ψ : Tb (RowH R) p → Tb (RowH R) p := fun t => swapOff (κ γ (Sx γ t)) (Q t).2.2.2 t
  have hinv : ∀ t, Q (ψ t) = Q t ∧ Sx γ (ψ t) = Sx γ t := fun t => hQ t (ψ t) (agT_swapOff hQ1 _ t)
  have hψψ : Function.Involutive ψ := fun t => by
    show swapOff (κ γ (Sx γ (ψ t))) (Q (ψ t)).2.2.2 (ψ t) = t
    rw [(hinv t).1, (hinv t).2]
    exact swapOff_swapOff _ _ t
  refine le_of_eq_of_le (congrArg (fun a => |a - _|)
    (pr_equiv (Equiv.prodCongr (Equiv.refl (Bytes 16)) hψψ.toPerm) _).symm) ?_
  have hbad : pr (Bytes 16 × Tb (RowH R) p) (fun z => z.1 ∈ (Q z.2).2.2.2) ≤ sE / 2 ^ 128 :=
    pr_mem_rows_le (T := Tb (RowH R) p) (fun t => (Q t).2.2.2) fun t => (hc t).2.2.2
  refine le_trans (abs_pr_sub_le_of_agree _ _ (fun z => z.1 ∈ (Q z.2).2.2.2) ?_) ?_
  swap
  · exact hbad
  intro z hz
  obtain ⟨ρ, t⟩ := z
  have hz' : ρ ∉ (Q t).2.2.2 := hz
  show C γ (Sx γ (ψ t)) ρ (h3At (ψ t).2 (κ γ (Sx γ (ψ t)))) (ψ t).2 ↔ C γ (Sx γ t) ρ t.1 t.2
  rw [(hinv t).2]
  have h1 : h3At (ψ t).2 (κ γ (Sx γ t)) ρ = t.1 ρ := h3At_swapOff_of_not_mem _ t hz'
  rw [hC3 γ _ ρ _ _ _ h1, swapOff_snd, hC]

end Shared

/-! ## The patched theorem with the `H₃` columns in the rows -/

section RowH

variable {R : Type} [Fintype R] [CipherRow R] {p : Params}

lemma patch5E_combH (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → RowH R)
    (s : ShG R p) (H : Blk → H3Row) :
    patch5E P5 W5 PE WE (combH s H) =
      combH (patch5E P5 W5 PE (fun j => (WE j).1) s) (IC.patchT PE (fun j => (WE j).2) H) := by
  simp only [patch5E, combH, splitH, Equiv.coe_fn_symm_mk, Prod.mk.injEq, true_and]
  funext j
  by_cases hj : j ∈ PE <;> simp [IC.patchT, hj]

variable [ZKPRow R]

/-- **`zk_roP` with the `H₃` columns in the rows**: `ZKPRow R`'s theorem, the columns (patched with
the rows) fixed. -/
noncomputable instance ZKPRow.rowH : ZKPRow (RowH R) where
  εP := ZKPRow.εP R
  εP_nonneg := ZKPRow.εP_nonneg (R := R)
  εP_mono := ZKPRow.εP_mono (R := R)
  zkP Hb st w _ hlr hzk hHb hp q3 q5 qE D hD P5 W5 PE WE := by
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
    have key := ZKPRow.zkP (R := R) Hb st w hlr hzk hHb hp
      (fun o G s => D o G (combH s (IC.patchT PE (fun j => (WE j).2) H)))
      (hD.withH (IC.patchT PE (fun j => (WE j).2) H)) P5 W5 PE (fun j => (WE j).1)
    refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_))) key
    · show D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE (combH a.2 H))) a.1.2
          (patch5E P5 W5 PE WE (combH a.2 H)) ↔ _
      rw [patch5E_combH, realRO_combH]
    · show D (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE (combH a.2 H))) ↔ _
      rw [patch5E_combH, progRO_combH]

@[simp] lemma ZKPRow.εP_rowH : ZKPRow.εP (RowH R) = ZKPRow.εP R := rfl

@[simp] lemma εAdG_rowH : εAdG (RowH R) = εAdG R := rfl

end RowH

end VoleMole.ZK.Sim
