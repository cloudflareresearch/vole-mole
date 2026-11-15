import VoleMole.Theft.JointAdm
import VoleMole.Theft.Tables
import VoleMole.ZK.ZKExp

/-!
# The joint step for a game of proofs with point charges

`real_sim_leN_jointAdm` (`Theft/JointAdm.lean`) composes hops that are bounded for the events of a
class, each by a constant plus an expected charge in the zero-knowledge theorem's real world.
`ZKExp` (`ZK/ZKExp.lean`) gives such a hop for a distinguisher with a consistent table point
reader. Here the two are joined for a many-proof game (`Theft/Many.lean`) on the theft games'
tables with an extra uniform table (`ShX`, the other hashes read off it), whose slots are proofs
of one system, the instance and witness of slot `i` functions of the history:

* **`GRd`**: a point reader of the game's view (the slices, `H₅` and the cipher; `H₂³` and the
  extra table read freely), `GRd.Cons`, `GRd.Reads`. The class of events is the events one
  consistent game reader reads (the adversary, the verifier, the extractor).
* **The hop's reader** (`hopRd`), built by composition (`TRd.prog`, `TRd.bind`): the earlier
  simulations' programmings (`progsRd`), the later real proofs (`realFromRd`), then the game
  reader (`GRd.atRd`). Its reads are the union of theirs.
* **`zkExp_tables`**: `ZKExp` at every value of the extra table gives the hop on `ShX`.
* **`real_sim_leN_game`**: for every event the game reader reads,

      |Pr_real[Ev] − Pr_sim[Ev]| ≤ (N·ε + Σ_i (1 + B)·Pr[deltaN i] + J) / (1 − N·B),

  if the hop's charge (`ch` of `hopRd`'s reads) is at most `Σ_k w k · n i k` of the rest of the
  game's view (`hch`), with `n i k ≤ M k` read by the game reader (`hnr`), `B = Σ_k w k · M k`, and
  `J` bounds the charges summed over the slots in the simulated game.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier

/-! ## The hop with an extra table -/

section Tables

variable {p : Params} {X : Type} [Fintype X] [Nonempty X] {I W ρ C O : Type*} [Fintype ρ]
  [Fintype C]

/-- **Averaging over a shared component.** -/
lemma abs_pr_prod_sub_le_exP {α β β' : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype β']
    (P : α × β → Prop) (Q : α × β' → Prop) :
    |pr (α × β) P - pr (α × β') Q| ≤
      exP α (fun a => |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))|) := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα, exP]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

/-- **`ZKExp` at every value of the extra table gives the hop on `ShX`.** The prover and the
programming may read the extra table; the distinguisher sees it and is given, at every value
`y` of it, with a consistent table reader within the budgets. -/
theorem zkExp_tables {Rel : I → W → Prop} (prove : X → I → W → ρ → Tab3 → Sh p → O)
    (sim : I → C → O) (prog : X → I → C → Sh p → Sh p) {q3 q5 qE : ℕ} {ε : ℝ}
    (ch : X → I → O → Finset (Bytes 16) → Finset (Bytes 37) → Finset (Blk × Blk) → ℝ)
    (h : ∀ x, ZKExp Rel (prove x) sim (prog x) q3 q5 qE ε (ch x)) {x : I} {w : W} (hxw : Rel x w)
    (D : O → Tab3 → ShX (Blk → Blk) p X → Prop)
    (R : ∀ (y : X) (o : O), TRd (fun g s => D o g (atX s y)))
    (hR : ∀ y o, (R y o).Bnd q3 q5 qE) :
    |pr ((ρ × Tab3) × ShX (Blk → Blk) p X)
        (fun a => D (prove a.2.2.2 x w a.1.1 a.1.2 (shOf a.2)) a.1.2 a.2) -
      pr ((C × Tab3) × ShX (Blk → Blk) p X)
        (fun a => D (sim x a.1.1) a.1.2 (atX (prog a.2.2.2 x a.1.1 (shOf a.2)) a.2.2.2))| ≤
      ε + exP ((ρ × Tab3) × ShX (Blk → Blk) p X) (fun a =>
        ch a.2.2.2 x (prove a.2.2.2 x w a.1.1 a.1.2 (shOf a.2))
          ((R a.2.2.2 (prove a.2.2.2 x w a.1.1 a.1.2 (shOf a.2))).Q3 a.1.2 (shOf a.2))
          ((R a.2.2.2 (prove a.2.2.2 x w a.1.1 a.1.2 (shOf a.2))).Q5 a.1.2 (shOf a.2))
          ((R a.2.2.2 (prove a.2.2.2 x w a.1.1 a.1.2 (shOf a.2))).QE a.1.2 (shOf a.2))) := by
  let f₁ : X × ((ρ × Tab3) × Sh p) ≃ (ρ × Tab3) × ShX (Blk → Blk) p X :=
    ⟨fun z => (z.2.1, atX z.2.2 z.1), fun z => (z.2.2.2, (z.1, shOf z.2)),
      fun _ => rfl, fun _ => rfl⟩
  let f₂ : X × ((C × Tab3) × Sh p) ≃ (C × Tab3) × ShX (Blk → Blk) p X :=
    ⟨fun z => (z.2.1, atX z.2.2 z.1), fun z => (z.2.2.2, (z.1, shOf z.2)),
      fun _ => rfl, fun _ => rfl⟩
  rw [← pr_equiv f₁, ← pr_equiv f₂, ← exP_equiv f₁]
  refine (abs_pr_prod_sub_le_exP _ _).trans ?_
  rw [exP_prod, ← exP_const_add]
  refine exP_mono fun y => ?_
  exact h y x w hxw (fun o g s => D o g (atX s y)) (R y) (hR y)

end Tables

/-! ## Readers of the game's view -/

section GRd

variable {Ω O : Type*} {p : Params} {X : Type} {N : ℕ}

/-- **A point reader of the game's view** `(ω, l, gs, t)`: the `H₃` keys of each slice, the `H₅`
keys and the cipher points, as functions of the view (`H₂³` and the extra table read freely). -/
structure GRd (Ω O : Type*) (p : Params) (X : Type) (N : ℕ) where
  /-- The keys read of slice `j`. -/
  Q3 : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Fin N → Finset (Bytes 16)
  /-- The `H₅` keys read. -/
  Q5 : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Finset (Bytes 37)
  /-- The cipher points read. -/
  QE : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Finset (Blk × Blk)

namespace GRd

variable (R : GRd Ω O p X N)

/-- Slices and tables that agree with `(gs, t)` at the reads (the same `H₂³` and extra table). -/
def Agree (ω : Ω) (l : List O) (gs : Fin N → Tab3) (t : ShX (Blk → Blk) p X)
    (gs' : Fin N → Tab3) (t' : ShX (Blk → Blk) p X) : Prop :=
  t'.1 = t.1 ∧ t'.2.2 = t.2.2 ∧ (∀ j, ∀ k ∈ R.Q3 ω l gs t j, gs j k = gs' j k) ∧
    (∀ k ∈ R.Q5 ω l gs t, t.2.1.1 k = t'.2.1.1 k) ∧
    ∀ kz ∈ R.QE ω l gs t, t.2.1.2 kz.1 kz.2 = t'.2.1.2 kz.1 kz.2

/-- **A consistent game reader**: agreement at the reads gives the same reads. -/
def Cons : Prop :=
  ∀ ω l gs t gs' t', R.Agree ω l gs t gs' t' →
    R.Q3 ω l gs' t' = R.Q3 ω l gs t ∧ R.Q5 ω l gs' t' = R.Q5 ω l gs t ∧
      R.QE ω l gs' t' = R.QE ω l gs t

/-- **An event read by the game reader.** -/
def Reads (F : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop) : Prop :=
  ∀ ω l gs t gs' t', R.Agree ω l gs t gs' t' → (F (ω, l, gs', t') ↔ F (ω, l, gs, t))

/-- **The level sets of a charge that depends on the history and the reads are read.** -/
lemma reads_level (Y : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → ℕ)
    (hY : ∀ ω l gs t gs' t', R.Agree ω l gs t gs' t' → Y (ω, l, gs', t') = Y (ω, l, gs, t))
    (m : ℕ) : R.Reads (fun v => m < Y v) := fun ω l gs t gs' t' h => by
  simp only [hY ω l gs t gs' t' h]

/-- **The game reader at slice `i`, with the other slices `gs` and the extra table `x` fixed**, as
a table reader. -/
def atRd (hc : R.Cons) (F : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop)
    (hF : R.Reads F) (ω : Ω) (l : List O) (gs : Fin N → Tab3) (i : Fin N) (x : X) :
    TRd (fun g s => F (ω, l, Function.update gs i g, atX s x)) where
  Q3 g s := R.Q3 ω l (Function.update gs i g) (atX s x) i
  Q5 g s := R.Q5 ω l (Function.update gs i g) (atX s x)
  QE g s := R.QE ω l (Function.update gs i g) (atX s x)
  cons g s g' s' h3 hA := by
    have hAg : R.Agree ω l (Function.update gs i g) (atX s x) (Function.update gs i g')
        (atX s' x) := by
      refine ⟨hA.1, rfl, fun j k hk => ?_, hA.2.1, hA.2.2⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self] at hk ⊢; exact h3 k hk
      · simp only [Function.update_of_ne hj]
    obtain ⟨e3, e5, eE⟩ := hc _ _ _ _ _ _ hAg
    exact ⟨propext (hF _ _ _ _ _ _ hAg), by simp only [e3], e5, eE⟩

end GRd

end GRd

/-! ## The game and its hop readers -/

section Game

variable {p : Params} {X : Type} {I W C O Ω : Type*}
  (prove : X → I → W → Bytes 16 → Tab3 → Sh p → O) (sim : I → C → O)
  (prog : X → I → C → Sh p → Sh p) (xOf : Ω → List O → I) (wOf : Ω → List O → W)
  {N : ℕ}

/-- The real proof of the game: the history decides the instance and the witness. -/
noncomputable def gP (ω : Ω) (h : List O) (r : Bytes 16) (g : Tab3) (t : ShX (Blk → Blk) p X) :
    O :=
  prove t.2.2 (xOf ω h) (wOf ω h) r g (shOf t)

/-- The simulated proof of the game. -/
def gS (ω : Ω) (h : List O) (c : C) : O := sim (xOf ω h) c

/-- The programming of the game. -/
noncomputable def gPg (ω : Ω) (h : List O) (c : C) (t : ShX (Blk → Blk) p X) :
    ShX (Blk → Blk) p X :=
  atX (prog t.2.2 (xOf ω h) c (shOf t)) t.2.2

/-- **The programmings of the first `j` simulations at the extra table `x`**, on `Sh p`. -/
noncomputable def progsAt (x : X) (ω : Ω) (cs : ℕ → C) (j : ℕ) (s : Sh p) : Sh p :=
  shOf ((simPre (gS sim xOf) (gPg prog xOf) ω cs j).2 (atX s x))

/-- The programmings keep the extra table. -/
lemma simPre_atX (x : X) (ω : Ω) (cs : ℕ → C) :
    ∀ j (s : Sh p), (simPre (gS sim xOf) (gPg prog xOf) ω cs j).2 (atX s x) =
      atX (progsAt sim prog xOf x ω cs j s) x
  | 0, _ => rfl
  | j + 1, s => by
    simp only [simPre, Function.comp, progsAt]
    rw [show gPg prog xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1 (cs j) (atX s x) =
      atX (prog x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j) s) x from rfl,
      simPre_atX x ω cs j]
    rfl

lemma progsAt_succ (x : X) (ω : Ω) (cs : ℕ → C) (j : ℕ) (s : Sh p) :
    progsAt sim prog xOf x ω cs (j + 1) s =
      progsAt sim prog xOf x ω cs j
        (prog x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j) s) := by
  simp only [progsAt, simPre, Function.comp]
  rw [show gPg prog xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1 (cs j) (atX s x) =
    atX (prog x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j) s) x from rfl]

variable {sim prog xOf}

/-- `H₂³` is read freely. -/
def h23Rd : TRd (fun (_ : Tab3) (s : Sh p) => s.1) where
  Q3 _ _ := ∅
  Q5 _ _ := ∅
  QE _ _ := ∅
  cons _ _ _ _ _ hA := ⟨hA.1, rfl, rfl, rfl⟩

/-- **The reader of the first `j` programmings' `H₂³` table**, from readers of each. -/
noncomputable def progsRd (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) (x : X) (ω : Ω) (cs : ℕ → C) :
    ∀ j, TRd (fun (_ : Tab3) (s : Sh p) => (progsAt sim prog xOf x ω cs j s).1)
  | 0 => h23Rd.congr fun _ _ => rfl
  | j + 1 => (TRd.prog (L := prog x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j))
      (hkeep x _ _) (Rpg x _ _) (progsRd hkeep Rpg x ω cs j)).congr fun _ s => by rw [progsAt_succ]


lemma progsAt_keep (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2) (x : X) (ω : Ω) (cs : ℕ → C) :
    ∀ j (s : Sh p), (progsAt sim prog xOf x ω cs j s).2 = s.2
  | 0, _ => rfl
  | j + 1, s => by rw [progsAt_succ, progsAt_keep hkeep x ω cs j, hkeep]

/-- **`m` real proofs from slot `j` on, then a reader `Φ` of the history**: the reads of the
proofs and of `Φ`. -/
noncomputable def realFromRd
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) (x : X) (ω : Ω)
    (rs : ℕ → Bytes 16 × Tab3) {Φ : List O → Tab3 → Sh p → Prop} (RΦ : ∀ l, TRd (Φ l)) :
    ∀ (m : ℕ) (h : List O) (j : ℕ),
      TRd (fun g s => Φ (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m) g s)
  | 0, h, _ => RΦ h
  | m + 1, h, j => (TRd.bind (RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2)
      (fun o => realFromRd RP x ω rs RΦ m (h ++ [o]) (j + 1))).congr fun _ _ => rfl

variable [Nonempty C] in
/-- **The reader of hop `i`'s distinguisher at the extra table `x`**: the programmings of the
`i` earlier simulations, the later real proofs, then the game reader. -/
noncomputable def hopRd (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1))
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s))
    (R : GRd Ω O p X N) (hc : R.Cons) (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot (Bytes 16) C Tab3) (x : X) (o : O) :
    TRd (fun g s => distN (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) Ev i ω τ o g (atX s x)) :=
  (TRd.prog (L := progsAt sim prog xOf x ω (tapeC τ) i) (progsAt_keep hkeep x ω (tapeC τ) i)
    (progsRd hkeep Rpg x ω (tapeC τ) i)
    (realFromRd prove wOf RP x ω (tapeR τ)
      (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
      (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
      (N - (i.val + 1)) ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 ++ [o])
      (i.val + 1))).congr fun g s => by
    simp only [distN, contN]
    rw [simPre_atX]


variable [Nonempty C] [Fintype C] [Fintype X] [Nonempty X] [Fintype Ω] [Nonempty Ω] {K : Type*}
  [Fintype K]

/-- **The joint bound for a game of proofs with point charges.** The slots are proofs of one
system with `ZKExp` at every value of the extra table (`hzk`; instance and witness functions of
the history, `hrel`); the earlier simulations' programmings change only `H₂³` and are read at
points (`hkeep`, `Rpg`), the real proofs are read at points (`RP`); `R` is a consistent game
reader, and the hop readers (`hopRd`) are within the budgets (`hB`). The charge of hop `i`'s
reads in the real world is at most `Σ_k w k · n i k` of the rest of the game's view (`hch`), with
`n i k ≤ M k` read by `R` (`hnr`), and the charges sum to at most `J` in the simulated game.
Then for every event `Ev` that `R` reads,

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

`B = Σ_k w k · M k`. -/
theorem real_sim_leN_game {Rel : I → W → Prop} {q3 q5 qE : ℕ} {ε : ℝ}
    (ch : X → I → O → Finset (Bytes 16) → Finset (Bytes 37) → Finset (Blk × Blk) → ℝ)
    (hzk : ∀ x, ZKExp Rel (prove x) sim (prog x) q3 q5 qE ε (ch x))
    (hrel : ∀ ω h, Rel (xOf ω h) (wOf ω h))
    (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1))
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s))
    (R : GRd Ω O p X N) (hc : R.Cons)
    (hB : ∀ (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
      (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) i ω τ x o,
      (hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ x o).Bnd q3 q5 qE)
    (w : K → ℝ) (hw : ∀ k, 0 ≤ w k)
    (n : ℕ → K → Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → ℕ) (M : K → ℕ)
    (hn : ∀ i < N, ∀ k v, n i k v ≤ M k)
    (hnr : ∀ i < N, ∀ k ω l gs t gs' t', R.Agree ω l gs t gs' t' →
      n i k (ω, l, gs', t') = n i k (ω, l, gs, t))
    (hch : ∀ (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
      (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) (i : Fin N) ω τ (r : Bytes 16)
      (g : Tab3) (t : ShX (Blk → Blk) p X),
      ch t.2.2 (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1)
          (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t)
          ((hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ t.2.2
            (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t)).Q3 g
              (shOf t))
          ((hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ t.2.2
            (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t)).Q5 g
              (shOf t))
          ((hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ t.2.2
            (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t)).QE g
              (shOf t)) ≤
        ∑ k, w k * (n i k (contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
          (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
          ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)) : ℝ))
    {J : ℝ} (hJ : ∑ i ∈ range N, ∑ k, w k * exU _ (fun z => (n i k (viewN (C := C)
      (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, w k * M k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := C) (gP prove xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS sim xOf) (gPg prog xOf) Ev)| ≤
      (∑ i : Fin N, (ε + (1 + ∑ k, w k * M k) *
        pr _ (deltaN (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i)) + J) /
        (1 - N * ∑ k, w k * M k) := by
  refine real_sim_leN_jointAdm (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) R.Reads
    (fun _ => ε) w hw n M hn (fun i hi k l => R.reads_level (n i k) (hnr i hi k) l)
    (fun i Ev' hEv' ω τ => ?_) hJ hNB Ev hEv
  set h0 := (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1
  have key := zkExp_tables prove sim prog ch hzk (hrel ω h0)
    (fun o g t => distN (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) Ev' i ω τ o g t)
    (fun y o => hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev' hEv' i ω τ y o)
    (fun y o => hB Ev' hEv' i ω τ y o)
  refine key.trans ?_
  gcongr ε + ?_
  exact exP_mono fun a => hch Ev' hEv' i ω τ a.1.1 a.1.2 a.2

end Game

end VoleMole.Theft
