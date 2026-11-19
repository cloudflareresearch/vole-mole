import VoleMole.ZK.ReadsROExp

/-!
# Consistent point readers of the tables, and how they compose

`zk_ro_exp` (`ZK/ReadsROExp.lean`) needs the distinguisher as a consistent point reader of its
view (`PtReads`, `Cons`). The distinguishers of the many-proof games are compositions: later real
proofs, the earlier simulators' programmings, the adversary, a verifier, an extractor. Here a
reader is stated on the **tables** (`TRd`: a function `F g s` of one `H₃` slice `g` and the shared
tables `s`, its `H₃` keys, `H₅` keys and cipher points as functions of `(g, s)`, consistent:
tables that agree with `s` at the reads, with the same `H₂³`, give the same value and the same
reads). `H₂³` is read freely, as in `PtReads`.

* `TRd.const`, `TRd.map`, `TRd.congr`: constants, functions of a read value, equal functions.
* **`TRd.bind`**: `f (m g s) g s` reads what `m` reads and what `f` reads at `m`'s value.
* **`TRd.prog`**: `F g (L s)`, `L` a programming of `H₂³` (it keeps `H₅` and the cipher) whose new
  `H₂³` table is read by a point reader: the reads of both.
* **`TRd.toPt`**: a family of table readers, one per output, is a consistent `PtReads`
  (`TRd.toPt_cons`) that reads the distinguisher (`TRd.toPt_reads`).
* `TRd.Bnd`: worst-case budgets (keys), with the union bounds `TRd.bnd_bind`, `TRd.bnd_prog`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.ZK VoleMole.Privacy

variable {p : Params} {X Y : Type*}

/-- **Tables that agree with `s` at the reads `(Q5, QE)`**, with the same `H₂³`. -/
def TAgree (Q5 : Finset (Bytes 37)) (QE : Finset (Blk × Blk)) (s s' : Sh p) : Prop :=
  s'.1 = s.1 ∧ (∀ k ∈ Q5, s.2.1 k = s'.2.1 k) ∧ ∀ kz ∈ QE, s.2.2 kz.1 kz.2 = s'.2.2 kz.1 kz.2

lemma TAgree.mono {Q5 Q5' : Finset (Bytes 37)} {QE QE' : Finset (Blk × Blk)} {s s' : Sh p}
    (h : TAgree Q5' QE' s s') (h5 : Q5 ⊆ Q5') (hE : QE ⊆ QE') : TAgree Q5 QE s s' :=
  ⟨h.1, fun k hk => h.2.1 k (h5 hk), fun kz hkz => h.2.2 kz (hE hkz)⟩

lemma TAgree.refl (Q5 : Finset (Bytes 37)) (QE : Finset (Blk × Blk)) (s : Sh p) :
    TAgree Q5 QE s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **A consistent point reader of a function of one slice and the shared tables.** -/
structure TRd (F : Tab3 → Sh p → X) where
  /-- The `H₃` keys read (of the slice `g`). -/
  Q3 : Tab3 → Sh p → Finset (Bytes 16)
  /-- The `H₅` keys read. -/
  Q5 : Tab3 → Sh p → Finset (Bytes 37)
  /-- The cipher points `(key, input)` read. -/
  QE : Tab3 → Sh p → Finset (Blk × Blk)
  /-- Consistency: agreement at the reads gives the same value and the same reads. -/
  cons : ∀ g s g' s', (∀ k ∈ Q3 g s, g k = g' k) → TAgree (Q5 g s) (QE g s) s s' →
    F g' s' = F g s ∧ Q3 g' s' = Q3 g s ∧ Q5 g' s' = Q5 g s ∧ QE g' s' = QE g s

namespace TRd

/-- A constant reads nothing. -/
def const (x : X) : TRd (p := p) (fun _ _ => x) where
  Q3 _ _ := ∅
  Q5 _ _ := ∅
  QE _ _ := ∅
  cons _ _ _ _ _ _ := ⟨rfl, rfl, rfl, rfl⟩

/-- A function of a read value reads what it reads. -/
def map {F : Tab3 → Sh p → X} (R : TRd F) (f : X → Y) : TRd (fun g s => f (F g s)) where
  Q3 := R.Q3
  Q5 := R.Q5
  QE := R.QE
  cons g s g' s' h3 h := by
    obtain ⟨e, e3, e5, eE⟩ := R.cons g s g' s' h3 h
    exact ⟨by rw [e], e3, e5, eE⟩

/-- An equal function reads what it reads. -/
def congr {F F' : Tab3 → Sh p → X} (R : TRd F) (h : ∀ g s, F' g s = F g s) : TRd F' where
  Q3 := R.Q3
  Q5 := R.Q5
  QE := R.QE
  cons g s g' s' h3 hA := by
    obtain ⟨e, e3, e5, eE⟩ := R.cons g s g' s' h3 hA
    exact ⟨by rw [h, h, e], e3, e5, eE⟩

/-- **Sequencing**: `f (m g s) g s` reads what `m` reads and what `f` reads at `m`'s value. -/
def bind {m : Tab3 → Sh p → Y} {f : Y → Tab3 → Sh p → X} (Rm : TRd m) (Rf : ∀ y, TRd (f y)) :
    TRd (fun g s => f (m g s) g s) where
  Q3 g s := Rm.Q3 g s ∪ (Rf (m g s)).Q3 g s
  Q5 g s := Rm.Q5 g s ∪ (Rf (m g s)).Q5 g s
  QE g s := Rm.QE g s ∪ (Rf (m g s)).QE g s
  cons g s g' s' h3 hA := by
    obtain ⟨em, e3, e5, eE⟩ := Rm.cons g s g' s' (fun k hk => h3 k (mem_union_left _ hk))
      (hA.mono subset_union_left subset_union_left)
    obtain ⟨ef, f3, f5, fE⟩ := (Rf (m g s)).cons g s g' s'
      (fun k hk => h3 k (mem_union_right _ hk)) (hA.mono subset_union_right subset_union_right)
    refine ⟨by rw [em, ef], ?_, ?_, ?_⟩
    · show Rm.Q3 g' s' ∪ (Rf (m g' s')).Q3 g' s' = _; rw [e3, em, f3]
    · show Rm.Q5 g' s' ∪ (Rf (m g' s')).Q5 g' s' = _; rw [e5, em, f5]
    · show Rm.QE g' s' ∪ (Rf (m g' s')).QE g' s' = _; rw [eE, em, fE]

/-- **A programming of `H₂³`** (it keeps `H₅` and the cipher) whose new `H₂³` table is read by
`RL`, followed by `F`: the reads of both. -/
def prog {F : Tab3 → Sh p → X} {L : Sh p → Sh p} (hL : ∀ s, (L s).2 = s.2)
    (RL : TRd (fun _ s => (L s).1)) (RF : TRd F) : TRd (fun g s => F g (L s)) where
  Q3 g s := RL.Q3 g s ∪ RF.Q3 g (L s)
  Q5 g s := RL.Q5 g s ∪ RF.Q5 g (L s)
  QE g s := RL.QE g s ∪ RF.QE g (L s)
  cons g s g' s' h3 hA := by
    obtain ⟨eL, e3, e5, eE⟩ := RL.cons g s g' s' (fun k hk => h3 k (mem_union_left _ hk))
      (hA.mono subset_union_left subset_union_left)
    have hLs : L s' = ((L s).1, s'.2) := by
      rw [← eL]; exact Prod.ext rfl (hL s')
    have hA' : TAgree (RF.Q5 g (L s)) (RF.QE g (L s)) (L s) (L s') := by
      refine ⟨by rw [hLs], fun k hk => ?_, fun kz hkz => ?_⟩
      · rw [hLs, hL s]; exact hA.2.1 k (mem_union_right _ hk)
      · rw [hLs, hL s]; exact hA.2.2 kz (mem_union_right _ hkz)
    obtain ⟨eF, f3, f5, fE⟩ := RF.cons g (L s) g' (L s')
      (fun k hk => h3 k (mem_union_right _ hk)) hA'
    exact ⟨eF, by rw [e3, f3], by rw [e5, f5], by rw [eE, fE]⟩

/-! ## Budgets -/

/-- **Worst-case budgets** of a table reader (keys). -/
structure Bnd {F : Tab3 → Sh p → X} (R : TRd F) (q3 q5 qE : ℕ) : Prop where
  h3 : ∀ g s, (R.Q3 g s).card ≤ q3
  h5 : ∀ g s, (R.Q5 g s).card ≤ q5
  hE : ∀ g s, ((R.QE g s).image Prod.fst).card ≤ qE

lemma bnd_const (x : X) : (const (p := p) x).Bnd 0 0 0 :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

lemma Bnd.mono {F : Tab3 → Sh p → X} {R : TRd F} {q3 q5 qE q3' q5' qE' : ℕ} (h : R.Bnd q3 q5 qE)
    (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') : R.Bnd q3' q5' qE' :=
  ⟨fun g s => (h.h3 g s).trans h3, fun g s => (h.h5 g s).trans h5, fun g s => (h.hE g s).trans hE⟩

lemma bnd_map {F : Tab3 → Sh p → X} {R : TRd F} (f : X → Y) {q3 q5 qE : ℕ} (h : R.Bnd q3 q5 qE) :
    (R.map f).Bnd q3 q5 qE := ⟨h.h3, h.h5, h.hE⟩

lemma bnd_congr {F F' : Tab3 → Sh p → X} {R : TRd F} (hF : ∀ g s, F' g s = F g s) {q3 q5 qE : ℕ}
    (h : R.Bnd q3 q5 qE) : (R.congr hF).Bnd q3 q5 qE := ⟨h.h3, h.h5, h.hE⟩

lemma card_image_union_le (A B : Finset (Blk × Blk)) :
    ((A ∪ B).image Prod.fst).card ≤ (A.image Prod.fst).card + (B.image Prod.fst).card := by
  classical
  rw [image_union]; exact card_union_le _ _

lemma bnd_bind {m : Tab3 → Sh p → Y} {f : Y → Tab3 → Sh p → X} {Rm : TRd m}
    {Rf : ∀ y, TRd (f y)} {a3 a5 aE b3 b5 bE : ℕ} (hm : Rm.Bnd a3 a5 aE)
    (hf : ∀ y, (Rf y).Bnd b3 b5 bE) : (bind Rm Rf).Bnd (a3 + b3) (a5 + b5) (aE + bE) :=
  ⟨fun g s => (card_union_le _ _).trans (add_le_add (hm.h3 g s) ((hf _).h3 g s)),
    fun g s => (card_union_le _ _).trans (add_le_add (hm.h5 g s) ((hf _).h5 g s)),
    fun g s => (card_image_union_le _ _).trans (add_le_add (hm.hE g s) ((hf _).hE g s))⟩

lemma bnd_prog {F : Tab3 → Sh p → X} {L : Sh p → Sh p} {hL : ∀ s, (L s).2 = s.2}
    {RL : TRd (fun _ s => (L s).1)} {RF : TRd F} {a3 a5 aE b3 b5 bE : ℕ} (hRL : RL.Bnd a3 a5 aE)
    (hRF : RF.Bnd b3 b5 bE) : (prog hL RL RF).Bnd (a3 + b3) (a5 + b5) (aE + bE) :=
  ⟨fun g s => (card_union_le _ _).trans (add_le_add (hRL.h3 g s) (hRF.h3 g _)),
    fun g s => (card_union_le _ _).trans (add_le_add (hRL.h5 g s) (hRF.h5 g _)),
    fun g s => (card_image_union_le _ _).trans (add_le_add (hRL.hE g s) (hRF.hE g _))⟩

/-! ## A family of table readers is a reader of the view -/

/-- The tables of a view. -/
def shV (v : VwIC p) : Sh p := (v.2.2.1, v.2.2.2.1, v.2.2.2.2)

/-- **The point reader of the view** given by a table reader per output. -/
def toPt {D : Except String ByteArray → Tab3 → Sh p → X} (R : ∀ o, TRd (D o)) : PtReads p where
  Q3 v := (R v.1).Q3 v.2.1 (shV v)
  Q5 v := (R v.1).Q5 v.2.1 (shV v)
  QE v := (R v.1).QE v.2.1 (shV v)

lemma agree_toPt {D : Except String ByteArray → Tab3 → Sh p → X} (R : ∀ o, TRd (D o))
    {v : VwIC p} {G3 : Tab3} {G5 : Tab5F} {E : Cipher} (h : (toPt R).Agree v G3 G5 E) :
    (∀ k ∈ (R v.1).Q3 v.2.1 (shV v), v.2.1 k = G3 k) ∧
      TAgree ((R v.1).Q5 v.2.1 (shV v)) ((R v.1).QE v.2.1 (shV v)) (shV v)
        (shV (PtReads.withT v G3 G5 E)) :=
  ⟨h.1, rfl, h.2.1, h.2.2⟩

/-- **The view reader of a family of consistent table readers is consistent.** -/
theorem toPt_cons {D : Except String ByteArray → Tab3 → Sh p → X} (R : ∀ o, TRd (D o)) :
    (toPt R).Cons := by
  intro v G3 G5 E h
  obtain ⟨h3, hA⟩ := agree_toPt R h
  obtain ⟨-, e3, e5, eE⟩ := (R v.1).cons v.2.1 (shV v) G3 (shV (PtReads.withT v G3 G5 E)) h3 hA
  exact ⟨e3, e5, eE⟩

/-- **The view reader reads the distinguisher.** -/
theorem toPt_reads (D : Except String ByteArray → Tab3 → Sh p → Prop) (R : ∀ o, TRd (D o)) :
    (toPt R).Reads (fun v => D v.1 v.2.1 (v.2.2.1, v.2.2.2.1, v.2.2.2.2)) := by
  intro v G3 G5 E h
  obtain ⟨h3, hA⟩ := agree_toPt R h
  obtain ⟨e, -, -, -⟩ := (R v.1).cons v.2.1 (shV v) G3 (shV (PtReads.withT v G3 G5 E)) h3 hA
  show D v.1 G3 (shV (PtReads.withT v G3 G5 E)) ↔ D v.1 v.2.1 (shV v)
  rw [e]

/-- **Budgets of the view reader.** -/
theorem toPt_bnd {D : Except String ByteArray → Tab3 → Sh p → X} (R : ∀ o, TRd (D o))
    {q3 q5 qE : ℕ} (h : ∀ o, (R o).Bnd q3 q5 qE) : (toPt R).Bnd q3 q5 qE :=
  ⟨fun v => (h v.1).h3 _ _, fun v => (h v.1).h5 _ _, fun v => (h v.1).hE _ _⟩

end TRd

end VoleMole.ZK.Sim
