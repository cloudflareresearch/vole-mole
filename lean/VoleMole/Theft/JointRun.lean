import VoleMole.Theft.JointVer
import VoleMole.Theft.PlainSlicesN

/-!
# Game readers at points: the adversary's oracle run, and how game readers compose

`real_sim_leN_lean` (`Theft/JointLean.lean`) and `real_sim_leN_leanG` (`Theft/JointLeanSum.lean`)
bound the event of a game of proofs for every event a **consistent game reader** (`GRd`) reads.
The theft games' event is read by the adversary's last stage, the verifier and the extractor. The
adversary's last stage is the run on the `N` slices and the tables of an oracle computation over
`ROM/`'s `specIC` (`AdmLN`, answers `ansPN`). Its reads are its queries, which are points:

* **`ansPN_agree`**: two slice families and tables that agree at a query's slice key, `H₅` key
  or cipher cell (with the same `H₂³` and extra table) give the same answer;
* **`runT_agree`**: so a run reads the slices at its slice queries, `H₅` at its `H₅` queries and
  the cipher at its **cells** (`runQ3`, `runQ5`, `runQE`), consistently;
* **`runGRd`**: the run of a computation chosen from the history, as a consistent game reader
  (`runGRd_cons`), that reads every event of the run's output, `H₂³` and the extra table
  (`runGRd_reads`), within the run's query budget (`runGRd_bnd`);
* **`GRd.seq`**: a consistent reader, then a consistent reader chosen by a value it reads: the
  union of the reads, consistent (`GRd.seq_cons`), and it reads what the second reads
  (`GRd.seq_reads`); `GRd.ofTRd`: a table point reader (the verifier `verPtRd`) of the shared
  tables, at a value chosen from the view, as a game reader that reads no slice.
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The answers at points -/

section Ans

variable {p : Params} {L M N : ℕ}

/-- The cipher cell of a query. -/
def decC : DomIC → Option (Blk × Blk)
  | .inl _ => none
  | .inr c => some c

lemma decC_right {d : DomIC} {kz : Blk × Blk} (h : decC d = some kz) : d.isRight = true := by
  rcases d with d | c
  · simp [decC] at h
  · rfl

open Classical in
/-- **The answers agree at a query** whose slice key, `H₅` key and cell the slices and tables
agree at (with the same `H₂³` and extra table). -/
theorem ansPN_agree (gs gs' : Fin N → Tab3) (t t' : ShX (Blk → Blk) p (XTab L M))
    (h2 : t'.1 = t.1) (hx : t'.2.2 = t.2.2) (d : DomIC)
    (h3 : ∀ j k, dec3N j d = some k → gs j k = gs' j k)
    (h5 : ∀ k, dec5 d = some k → t.2.1.1 k = t'.2.1.1 k)
    (hE : ∀ kz, decC d = some kz → t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2) :
    ansPN gs t d = ansPN gs' t' d := by
  obtain ⟨G2, ⟨G5, E⟩, x⟩ := t
  obtain ⟨G2', ⟨G5', E'⟩, x'⟩ := t'
  simp only at h2 hx
  subst h2 hx
  rcases d with ⟨k, b⟩ | c
  · by_cases hs : SlPt N (k, b)
    · rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
      unfold slAns
      by_cases h : ∃ jk : Fin N × Bytes 16, encSlN jk = (k, b).2
      · rw [dite_eq_left h, dite_eq_left h]
        have hk : k = .h3 := hs.1
        rw [h3 h.choose.1 h.choose.2 (by simp only [dec3N, hk, ite_true, dite_eq_left h])]
      · rw [dite_eq_right h, dite_eq_right h]
    · rw [ansPN_notSl _ _ hs zT zT, ansPN_notSl _ _ hs zT zT]
      show blk _ ((recP zT zT _).hash k b) = blk _ ((recP zT zT _).hash k b)
      by_cases hk5 : k = .h5
      · subst hk5
        rw [recP_h5, recP_h5]
        by_cases h : ∃ a, enc5 a = b
        · rw [dite_eq_left h, dite_eq_left h]
          rw [h5 h.choose (by simp only [dec5, ite_true, dite_eq_left h])]
        · rw [dite_eq_right h, dite_eq_right h]
      · by_cases hk3 : k = .h3
        · subst hk3; rw [recP_h3, recP_h3]
        · by_cases hk23 : k = .h23
          · subst hk23; rw [recP_h23, recP_h23]
          · rw [recP_other _ _ _ hk3 hk5 hk23, recP_other _ _ _ hk3 hk5 hk23]
  · exact hE c rfl

/-! ## The reads of a run -/

variable {α : Type}

/-- The keys of slice `j` a run reads. -/
noncomputable def runQ3 (oa : OracleComp specIC α) (gs : Fin N → Tab3)
    (t : ShX (Blk → Blk) p (XTab L M)) (j : Fin N) : Finset (Bytes 16) :=
  ((qlog (ansPN gs t) oa).filterMap (dec3N j)).toFinset

/-- The `H₅` keys a run reads. -/
noncomputable def runQ5 (oa : OracleComp specIC α) (gs : Fin N → Tab3)
    (t : ShX (Blk → Blk) p (XTab L M)) : Finset (Bytes 37) :=
  ((qlog (ansPN gs t) oa).filterMap dec5).toFinset

/-- The cipher cells a run reads. -/
noncomputable def runQE (oa : OracleComp specIC α) (gs : Fin N → Tab3)
    (t : ShX (Blk → Blk) p (XTab L M)) : Finset (Blk × Blk) :=
  ((qlog (ansPN gs t) oa).filterMap decC).toFinset

/-- **A run reads at its queries, consistently.** -/
theorem runT_agree (oa : OracleComp specIC α) (gs gs' : Fin N → Tab3)
    (t t' : ShX (Blk → Blk) p (XTab L M)) (h2 : t'.1 = t.1) (hx : t'.2.2 = t.2.2)
    (h3 : ∀ j, ∀ k ∈ runQ3 oa gs t j, gs j k = gs' j k)
    (h5 : ∀ k ∈ runQ5 oa gs t, t.2.1.1 k = t'.2.1.1 k)
    (hE : ∀ kz ∈ runQE oa gs t, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2) :
    qlog (ansPN gs' t') oa = qlog (ansPN gs t) oa ∧ runT (ansPN gs' t') oa = runT (ansPN gs t) oa :=
  runT_congr oa _ _ fun d hd => ansPN_agree gs gs' t t' h2 hx d
    (fun j k hk => h3 j k (mem_dec hd hk)) (fun k hk => h5 k (mem_dec hd hk))
    (fun kz hkz => hE kz (mem_dec hd hkz))

end Ans

/-! ## Game readers -/

section GRdOps

variable {Ω O : Type*} {p : Params} {X : Type} {N : ℕ}

namespace GRd

/-- **A reader, then a reader chosen by a value the first reads**: the union of the reads. -/
noncomputable def seq {Y : Type*} (R₁ : GRd Ω O p X N)
    (f : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Y) (R₂ : Y → GRd Ω O p X N) :
    GRd Ω O p X N where
  Q3 ω l gs t j := R₁.Q3 ω l gs t j ∪ (R₂ (f (ω, l, gs, t))).Q3 ω l gs t j
  Q5 ω l gs t := R₁.Q5 ω l gs t ∪ (R₂ (f (ω, l, gs, t))).Q5 ω l gs t
  QE ω l gs t := R₁.QE ω l gs t ∪ (R₂ (f (ω, l, gs, t))).QE ω l gs t

variable {Y : Type*} {R₁ : GRd Ω O p X N}
  {f : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Y} {R₂ : Y → GRd Ω O p X N}

lemma seq_agree {ω l gs t gs' t'} (h : (seq R₁ f R₂).Agree ω l gs t gs' t') :
    R₁.Agree ω l gs t gs' t' ∧ (R₂ (f (ω, l, gs, t))).Agree ω l gs t gs' t' :=
  ⟨⟨h.1, h.2.1, fun j k hk => h.2.2.1 j k (mem_union_left _ hk),
      fun k hk => h.2.2.2.1 k (mem_union_left _ hk), fun kz hkz => h.2.2.2.2 kz (mem_union_left _ hkz)⟩,
    ⟨h.1, h.2.1, fun j k hk => h.2.2.1 j k (mem_union_right _ hk),
      fun k hk => h.2.2.2.1 k (mem_union_right _ hk),
      fun kz hkz => h.2.2.2.2 kz (mem_union_right _ hkz)⟩⟩

/-- **The sequence of consistent readers is consistent**, if the first reads the value. -/
theorem seq_cons (h₁ : R₁.Cons) (hf : ∀ ω l gs t gs' t', R₁.Agree ω l gs t gs' t' →
    f (ω, l, gs', t') = f (ω, l, gs, t)) (h₂ : ∀ y, (R₂ y).Cons) : (seq R₁ f R₂).Cons := by
  intro ω l gs t gs' t' h
  obtain ⟨a1, a2⟩ := seq_agree h
  obtain ⟨e3, e5, eE⟩ := h₁ ω l gs t gs' t' a1
  obtain ⟨f3, f5, fE⟩ := h₂ _ ω l gs t gs' t' a2
  have ef := hf ω l gs t gs' t' a1
  refine ⟨?_, ?_, ?_⟩
  · funext j
    show R₁.Q3 ω l gs' t' j ∪ (R₂ (f (ω, l, gs', t'))).Q3 ω l gs' t' j = _
    rw [ef, e3, f3]; rfl
  · show R₁.Q5 ω l gs' t' ∪ (R₂ (f (ω, l, gs', t'))).Q5 ω l gs' t' = _
    rw [ef, e5, f5]; rfl
  · show R₁.QE ω l gs' t' ∪ (R₂ (f (ω, l, gs', t'))).QE ω l gs' t' = _
    rw [ef, eE, fE]; rfl

/-- **The sequence reads what the second reader reads at the value.** -/
theorem seq_reads (hf : ∀ ω l gs t gs' t', R₁.Agree ω l gs t gs' t' →
    f (ω, l, gs', t') = f (ω, l, gs, t))
    (F : Y → Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop)
    (hF : ∀ y, (R₂ y).Reads (F y)) :
    (seq R₁ f R₂).Reads (fun v => F (f v) v) := by
  intro ω l gs t gs' t' h
  obtain ⟨a1, a2⟩ := seq_agree h
  show F (f (ω, l, gs', t')) (ω, l, gs', t') ↔ F (f (ω, l, gs, t)) (ω, l, gs, t)
  rw [hf ω l gs t gs' t' a1]
  exact hF _ ω l gs t gs' t' a2

/-- The sequence reads what the first reader reads. -/
theorem seq_reads_fst (F : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop)
    (hF : R₁.Reads F) : (seq R₁ f R₂).Reads F := fun ω l gs t gs' t' h =>
  hF ω l gs t gs' t' (seq_agree h).1

/-- **Budgets of a sequence**: the sums. -/
theorem seq_bnd {a3 a5 aE b3 b5 bE : ℕ} (h₁ : R₁.Bnd a3 a5 aE) (h₂ : ∀ y, (R₂ y).Bnd b3 b5 bE) :
    (seq R₁ f R₂).Bnd (a3 + b3) (a5 + b5) (aE + bE) :=
  ⟨fun _ _ _ _ _ => (card_union_le _ _).trans (add_le_add (h₁.h3 _ _ _ _ _) ((h₂ _).h3 _ _ _ _ _)),
    fun _ _ _ _ => (card_union_le _ _).trans (add_le_add (h₁.h5 _ _ _ _) ((h₂ _).h5 _ _ _ _)),
    fun _ _ _ _ => (TRd.card_image_union_le _ _).trans
      (add_le_add (h₁.hE _ _ _ _) ((h₂ _).hE _ _ _ _))⟩

end GRd

/-- **A table point reader of the shared tables as a game reader**, at the extra table of the view
(it reads no slice). -/
def GRd.ofTRd {Z : Type*} {V : X → Tab3 → Sh p → Z} (Rv : ∀ x, TRd (V x))
    (_h3 : ∀ x g s, (Rv x).Q3 g s = ∅) : GRd Ω O p X N where
  Q3 _ _ _ _ _ := ∅
  Q5 _ _ _ t := (Rv t.2.2).Q5 zT (shOf t)
  QE _ _ _ t := (Rv t.2.2).QE zT (shOf t)

lemma GRd.ofTRd_agree {Z : Type*} {V : X → Tab3 → Sh p → Z} {Rv : ∀ x, TRd (V x)}
    {h3 : ∀ x g s, (Rv x).Q3 g s = ∅} {ω : Ω} {l : List O} {gs gs' : Fin N → Tab3}
    {t t' : ShX (Blk → Blk) p X} (h : (GRd.ofTRd Rv h3).Agree ω l gs t gs' t') :
    t'.2.2 = t.2.2 ∧ V t.2.2 zT (shOf t') = V t.2.2 zT (shOf t) ∧
      (Rv t.2.2).Q5 zT (shOf t') = (Rv t.2.2).Q5 zT (shOf t) ∧
      (Rv t.2.2).QE zT (shOf t') = (Rv t.2.2).QE zT (shOf t) := by
  obtain ⟨e, -, e5, eE⟩ := (Rv t.2.2).cons zT (shOf t) zT (shOf t') (fun k hk => by
    simp [h3] at hk) ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
  exact ⟨h.2.1, e, e5, eE⟩

theorem GRd.ofTRd_cons {Z : Type*} {V : X → Tab3 → Sh p → Z} (Rv : ∀ x, TRd (V x))
    (h3 : ∀ x g s, (Rv x).Q3 g s = ∅) : (GRd.ofTRd (Ω := Ω) (O := O) (N := N) Rv h3).Cons := by
  intro ω l gs t gs' t' h
  obtain ⟨hx, -, e5, eE⟩ := GRd.ofTRd_agree h
  refine ⟨rfl, ?_, ?_⟩
  · show (Rv t'.2.2).Q5 zT (shOf t') = _; rw [hx]; exact e5
  · show (Rv t'.2.2).QE zT (shOf t') = _; rw [hx]; exact eE

/-- **It reads every event of the reader's value** (and of the extra table). -/
theorem GRd.ofTRd_reads {Z : Type*} {V : X → Tab3 → Sh p → Z} (Rv : ∀ x, TRd (V x))
    (h3 : ∀ x g s, (Rv x).Q3 g s = ∅) (F : Ω → List O → X → Z → Prop) :
    (GRd.ofTRd (Ω := Ω) (O := O) (N := N) Rv h3).Reads
      (fun v => F v.1 v.2.1 v.2.2.2.2.2 (V v.2.2.2.2.2 zT (shOf v.2.2.2))) := by
  intro ω l gs t gs' t' h
  obtain ⟨hx, e, -, -⟩ := GRd.ofTRd_agree h
  show F ω l t'.2.2 (V t'.2.2 zT (shOf t')) ↔ F ω l t.2.2 (V t.2.2 zT (shOf t))
  rw [hx, e]

theorem GRd.ofTRd_bnd {Z : Type*} {V : X → Tab3 → Sh p → Z} {Rv : ∀ x, TRd (V x)}
    {h3 : ∀ x g s, (Rv x).Q3 g s = ∅} {b5 bE : ℕ} (hb : ∀ x, (Rv x).Bnd 0 b5 bE) :
    (GRd.ofTRd (Ω := Ω) (O := O) (N := N) Rv h3).Bnd 0 b5 bE :=
  ⟨fun _ _ _ _ _ => le_of_eq (card_empty), fun _ _ _ t => (hb t.2.2).h5 _ _,
    fun _ _ _ t => (hb t.2.2).hE _ _⟩

end GRdOps

/-! ## The adversary's run as a game reader -/

section Run

variable {Ω O : Type*} {p : Params} {L M N : ℕ} {α : Type}
  (oaOf : Ω → List O → OracleComp specIC α)

/-- **The run of a computation chosen from the history, as a game reader.** -/
noncomputable def runGRd : GRd Ω O p (XTab L M) N where
  Q3 ω l gs t j := runQ3 (oaOf ω l) gs t j
  Q5 ω l gs t := runQ5 (oaOf ω l) gs t
  QE ω l gs t := runQE (oaOf ω l) gs t

lemma runGRd_agree {ω : Ω} {l : List O} {gs gs' : Fin N → Tab3}
    {t t' : ShX (Blk → Blk) p (XTab L M)} (h : (runGRd (L := L) (M := M) oaOf).Agree ω l gs t gs' t') :
    qlog (ansPN gs' t') (oaOf ω l) = qlog (ansPN gs t) (oaOf ω l) ∧
      runT (ansPN gs' t') (oaOf ω l) = runT (ansPN gs t) (oaOf ω l) :=
  runT_agree _ gs gs' t t' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **The run's reader is consistent.** -/
theorem runGRd_cons : (runGRd (p := p) (L := L) (M := M) (N := N) oaOf).Cons := by
  intro ω l gs t gs' t' h
  have hq := (runGRd_agree oaOf h).1
  refine ⟨?_, ?_, ?_⟩
  · funext j
    show ((qlog (ansPN gs' t') (oaOf ω l)).filterMap (dec3N j)).toFinset = _
    rw [hq]; rfl
  · show ((qlog (ansPN gs' t') (oaOf ω l)).filterMap dec5).toFinset = _
    rw [hq]; rfl
  · show ((qlog (ansPN gs' t') (oaOf ω l)).filterMap decC).toFinset = _
    rw [hq]; rfl

/-- **The run's reader reads every event of the run's output** (and of `H₂³` and the extra table,
read freely). -/
theorem runGRd_reads (F : Ω → List O → Tab2G p → XTab L M → α → Prop) :
    (runGRd (p := p) (L := L) (M := M) (N := N) oaOf).Reads
      (fun v => F v.1 v.2.1 v.2.2.2.1 v.2.2.2.2.2 (runT (ansPN v.2.2.1 v.2.2.2) (oaOf v.1 v.2.1))) := by
  intro ω l gs t gs' t' h
  have hr := (runGRd_agree oaOf h).2
  show F ω l t'.1 t'.2.2 (runT (ansPN gs' t') (oaOf ω l)) ↔
    F ω l t.1 t.2.2 (runT (ansPN gs t) (oaOf ω l))
  rw [hr, h.1, h.2.1]

/-- **The run's value is read** (`GRd.seq`'s hypothesis). -/
theorem runGRd_val (ω : Ω) (l : List O) (gs : Fin N → Tab3) (t : ShX (Blk → Blk) p (XTab L M))
    (gs' : Fin N → Tab3) (t' : ShX (Blk → Blk) p (XTab L M))
    (h : (runGRd (L := L) (M := M) oaOf).Agree ω l gs t gs' t') :
    runT (ansPN gs' t') (oaOf ω l) = runT (ansPN gs t) (oaOf ω l) :=
  (runGRd_agree oaOf h).2

/-- **The run's reader is within the run's query budget**: each slice at `q h3` keys, `H₅` at
`q h5`, the cipher at `q_E` keys. -/
theorem runGRd_bnd {q : Kind → ℕ} {qE : ℕ} (hq : ∀ ω l, QBud q qE (oaOf ω l)) :
    (runGRd (p := p) (L := L) (M := M) (N := N) oaOf).Bnd (q .h3) (q .h5) qE := by
  classical
  refine ⟨fun ω l gs t j => ?_, fun ω l gs t => ?_, fun ω l gs t => ?_⟩
  · exact card_dec_le _ _ _ _ (isQueryBoundP_kind (hq ω l).1 .h3) fun _ _ => dec3N_kind
  · exact card_dec_le _ _ _ _ (isQueryBoundP_kind (hq ω l).1 .h5) fun _ _ => dec5_kind
  · show (((qlog (ansPN gs t) (oaOf ω l)).filterMap decC).toFinset.image Prod.fst).card ≤ qE
    refine card_image_le.trans ?_
    exact card_dec_le _ _ _ _ (hq ω l).2 fun _ _ => decC_right

end Run

end VoleMole.Theft
