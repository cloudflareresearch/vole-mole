import VoleMole.ZK.HopsIC
import VoleMole.ZK.HopsH4Pt
import VoleMole.ZK.HopsROMExp
import VoleMole.ZK.HopsH6Exp
import VoleMole.ZK.ChainExp

/-!
# `zk_rom_ic_h23` with expected charges at the proof's points

`zk_rom_ic_h23` (`ZK/HopsIC.lean`) bounds one proof's zero-knowledge error by
`q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`, with `q₃`, `q₅`,
`q_E` worst-case budgets and every read of a hidden node's row charged. Here the same chain (H1,
grinding and programming, the programmed points recomputed, H4, the tape, H6, the simulator) is
charged by the **expected** number of the distinguisher's reads **at the proof's points**, all in
the **real** world, as `Theft.hyb_hop_exp` needs.

**The read model** (`PtReads`). The distinguisher's view is `VwIC p`: the output and the tables
`H₃`, `H₂³`, `H₅` and the cipher. A reader gives the `H₃` and `H₅` keys and the cipher **points**
`(k, z)` it reads, as functions of the view; it is **consistent** (`Cons`: two views that agree at
the reads have the same reads), which `IC.puncturePt_real` and `IC.abs_pr_hidden_one_real` need to
move the charges between worlds. An event `F` is read by `R` (`Reads`) if it depends on `H₃`,
`H₅` and the cipher only at the reads (`H₂³` is read freely). The worst-case budgets enter only
the denominators.

**The charges** (functions of the view; `ivV`: the `iv` of the output, `H₄(iv_pre ‖ μ₁ ‖ 4)` with
the base record):
* `ch3`: the `H₃` keys read (the slice is the proof's own);
* `chE`: the keys read at a CTR block of the output's `iv` (`IC.qkeys (InY iv)`);
* `ch5`: the `H₅` keys that are gate inputs of the output's `iv` (`Gate5`).
For an output that is an error (no grinding answer accepted), `chE` and `ch5` count every read.

**The hops**:
* `joint3_h4_pt`: H4 at points, the honest recomputation's reads (`rdKeys`, whole rows) counted
  with the distinguisher's: `≤ 221·(9214 + E_3[chE]) / (2¹²⁸ − 221·(q_E + 4607))`, in the world
  before the hop.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## The read model -/

/-- **The distinguisher's view** in the ideal-cipher chain: the output and the tables `H₃`,
`H₂³`, `H₅` and the cipher. -/
abbrev VwIC (p : Params) := Except String ByteArray × Tab3 × Tab2G p × Tab5F × Cipher

/-- **A reader of the view at points**: the `H₃` keys, the `H₅` keys and the cipher points it
reads, as functions of the view. -/
structure PtReads (p : Params) where
  /-- The `H₃` keys read. -/
  Q3 : VwIC p → Finset (Bytes 16)
  /-- The `H₅` keys read. -/
  Q5 : VwIC p → Finset (Bytes 37)
  /-- The cipher points `(key, input)` read. -/
  QE : VwIC p → Finset (Blk × Blk)

namespace PtReads

variable {p : Params} (R : PtReads p)

/-- The view `v` with the tables `H₃`, `H₅` and the cipher replaced. -/
def withT (v : VwIC p) (G3 : Tab3) (G5 : Tab5F) (E : Cipher) : VwIC p := (v.1, G3, v.2.2.1, G5, E)

/-- The tables `G3`, `G5`, `E` agree with the view's at its reads. -/
def Agree (v : VwIC p) (G3 : Tab3) (G5 : Tab5F) (E : Cipher) : Prop :=
  (∀ k ∈ R.Q3 v, v.2.1 k = G3 k) ∧ (∀ k ∈ R.Q5 v, v.2.2.2.1 k = G5 k) ∧
    ∀ kz ∈ R.QE v, v.2.2.2.2 kz.1 kz.2 = E kz.1 kz.2

/-- **A consistent reader**: two views that agree at the reads have the same reads. -/
def Cons : Prop :=
  ∀ v G3 G5 E, R.Agree v G3 G5 E →
    R.Q3 (withT v G3 G5 E) = R.Q3 v ∧ R.Q5 (withT v G3 G5 E) = R.Q5 v ∧
      R.QE (withT v G3 G5 E) = R.QE v

/-- **`F` is read by `R`**: it depends on `H₃`, `H₅` and the cipher only at `R`'s reads. -/
def Reads (F : VwIC p → Prop) : Prop :=
  ∀ v G3 G5 E, R.Agree v G3 G5 E → (F (withT v G3 G5 E) ↔ F v)

/-- The cipher keys read. -/
def keysE (v : VwIC p) : Finset Blk := (R.QE v).image Prod.fst

/-- **Worst-case budgets** of a reader (they enter only the denominators). -/
structure Bnd (q3 q5 qE : ℕ) : Prop where
  h3 : ∀ v, (R.Q3 v).card ≤ q3
  h5 : ∀ v, (R.Q5 v).card ≤ q5
  hE : ∀ v, (R.keysE v).card ≤ qE

lemma withT_self (v : VwIC p) : withT v v.2.1 v.2.2.2.1 v.2.2.2.2 = v := rfl

/-- **The level sets of a charge that depends on the output and the reads are read.** -/
lemma reads_level (Y : VwIC p → ℕ)
    (hY : ∀ v G3 G5 E, R.Agree v G3 G5 E → Y (withT v G3 G5 E) = Y v) (l : ℕ) :
    R.Reads (fun v => l < Y v) := fun v G3 G5 E h => by
  simp only [hY v G3 G5 E h]

end PtReads

/-! ## The charges -/

/-- **The `iv` of an output** (`H₄(iv_pre ‖ μ₁ ‖ 4)` with the base record `Hb`), none for an
error. -/
def ivV (Hb : Hashes) (st : Statement) (o : Except String ByteArray) : Option ByteArray :=
  match o with
  | .ok b => some (ivOf Hb ⟨st.params, b⟩ (st.mu1 Hb))
  | .error _ => none

/-- **A gate input of `iv`**: the input of a `c_mult` label hash of a proof with `iv`, for some
columns and label offset (`Prover.gateInputsOff`). -/
def Gate5 (p : Params) (T : CrtTables) (iv : ByteArray) (k : Bytes 37) : Prop :=
  ∃ (cols : Array (Array UInt64)) (off : W128) (e : Fin 312),
    enc5 k = (Prover.gateInputsOff p T iv cols off).getD e .empty

noncomputable instance (p : Params) (T : CrtTables) (iv : ByteArray) :
    DecidablePred (Gate5 p T iv) := Classical.decPred _

variable {p : Params}

/-- **The `H₃` charge**: the `H₃` keys read. -/
def ch3 (R : PtReads p) (v : VwIC p) : ℕ := (R.Q3 v).card

/-- **The cipher charge**: the keys read at a CTR block of the output's `iv` (every key read, for
an error). -/
noncomputable def chE (R : PtReads p) (Hb : Hashes) (st : Statement) (v : VwIC p) : ℕ :=
  match ivV Hb st v.1 with
  | some iv => (qkeys (InY iv) (R.QE v)).card
  | none => (R.keysE v).card

/-- **The `H₅` charge**: the `H₅` keys read that are gate inputs of the output's `iv` (every key
read, for an error). -/
noncomputable def ch5 (R : PtReads p) (Hb : Hashes) (T : CrtTables) (st : Statement)
    (v : VwIC p) : ℕ :=
  match ivV Hb st v.1 with
  | some iv => ((R.Q5 v).filter (Gate5 p T iv)).card
  | none => (R.Q5 v).card

namespace PtReads

variable (R : PtReads p) (Hb : Hashes) (T : CrtTables) (st : Statement)

lemma ch3_withT (hc : R.Cons) (v : VwIC p) (G3 G5 E) (h : R.Agree v G3 G5 E) :
    ch3 R (withT v G3 G5 E) = ch3 R v := by
  unfold ch3; rw [(hc v G3 G5 E h).1]

lemma chE_withT (hc : R.Cons) (v : VwIC p) (G3 G5 E) (h : R.Agree v G3 G5 E) :
    chE R Hb st (withT v G3 G5 E) = chE R Hb st v := by
  unfold chE keysE; rw [(hc v G3 G5 E h).2.2]; rfl

lemma ch5_withT (hc : R.Cons) (v : VwIC p) (G3 G5 E) (h : R.Agree v G3 G5 E) :
    ch5 R Hb T st (withT v G3 G5 E) = ch5 R Hb T st v := by
  unfold ch5; rw [(hc v G3 G5 E h).2.1]; rfl

lemma chE_le (hc : R.Bnd q3 q5 qE) (v : VwIC p) : chE R Hb st v ≤ qE := by
  unfold chE
  split
  · exact (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans (hc.hE v)
  · exact hc.hE v

lemma ch5_le (hc : R.Bnd q3 q5 qE) (v : VwIC p) : ch5 R Hb T st v ≤ q5 := by
  unfold ch5
  split
  · exact (Finset.card_filter_le _ _).trans (hc.h5 v)
  · exact hc.h5 v

lemma ch3_le (hc : R.Bnd q3 q5 qE) (v : VwIC p) : ch3 R v ≤ q3 := hc.h3 v

/-- The keys read at the CTR blocks of the output's `iv`, if the output's `iv` is `iv`, are
charged. -/
lemma qkeys_le_chE (v : VwIC p) (iv : ByteArray) (hiv : ∀ iv', ivV Hb st v.1 = some iv' → iv' = iv) :
    (qkeys (InY iv) (R.QE v)).card ≤ chE R Hb st v := by
  unfold chE
  split
  · rename_i iv' h; rw [hiv iv' h]
  · exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

end PtReads

/-! ## The worlds of the chain -/

section Worlds

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- The coins of the world before H4 (after H1, grinding and programming, the programmed points
recomputed). -/
abbrev Co3 (p : Params) := (((Bytes 16 × Bytes 16) × (Tab2G p × Grind)) × (Tab3 × Tab5F)) × Cipher

/-- The coins of the world after H4. -/
abbrev Co4 (p : Params) := ((Hidden p × (Bytes 16 × Grind)) × Vis2 p) × Cipher

/-- **The view before H4**: the hybrid's proof with the hidden part from the root seed, the
tables with `H₂³` programmed by the simulator at the points it recomputes. -/
noncomputable def view3 (c : Co3 st.params) : VwIC st.params :=
  let o := @hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2) T st w (c.1.1.1.2, c.1.1.2.2)
    (@hiddenOut (icPrg c.2) st.params (ivOfPre Hb st c.1.1.1.2) (ba (deltaOf c.1.1.2.2)) c.1.1.1.1)
  (o, c.1.2.1, @simTab (icPrg c.2) Hb T st c.1.2.2 o c.1.1.2.2 c.1.1.2.1, c.1.2.2, c.2)

/-- **The view after H4**: the ideal hidden part. -/
noncomputable def view4 (c : Co4 st.params) : VwIC st.params :=
  let o := @hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2.2) T st w c.1.1.2
    (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)
  (o, c.1.2.1, @simTab (icPrg c.2) Hb T st c.1.2.2.2 o c.1.1.2.2 c.1.2.2.1, c.1.2.2.2, c.2)

end Worlds

/-! ## H4 at points -/

section H4

variable {Hb : Hashes} {T : CrtTables} {st : Statement} {w : ByteArray}

lemma rdKeys_congr {E E' : Cipher} {iv opening delta : ByteArray}
    (h : ∀ k ∈ rdKeys E iv opening delta, E k = E' k) :
    rdKeys E iv opening delta = rdKeys E' iv opening delta := by
  unfold rdKeys; rw [recTree_ic_congr h]

/-- **The hybrid's output and the simulator's table read the cipher only at the honest reads.** -/
lemma hyb3_simTab_congr {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs)
    (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params) {E E' : Cipher}
    (hrd : ∀ k ∈ hRd E (recB Hb st w v.1 v.2.2) st (a, g, o.1, o.2.1) (deltaOf g), E k = E' k) :
    @hyb3 (icPrg E) (recB Hb st w v.1 v.2.2) T st w (a, g) o =
        @hyb3 (icPrg E') (recB Hb st w v.1 v.2.2) T st w (a, g) o ∧
      @simTab (icPrg E) Hb T st v.2.2 (@hyb3 (icPrg E) (recB Hb st w v.1 v.2.2) T st w (a, g) o) g
          v.2.1 =
        @simTab (icPrg E') Hb T st v.2.2 (@hyb3 (icPrg E') (recB Hb st w v.1 v.2.2) T st w (a, g) o)
          g v.2.1 := by
  obtain ⟨G3, G2, G5⟩ := v
  set R := recB Hb st w G3 G5 with hR
  have hout : @hyb3 (icPrg E) R T st w (a, g) o = @hyb3 (icPrg E') R T st w (a, g) o :=
    hyb3_ic_congr R T st w (a, g) o hrd
  refine ⟨hout, ?_⟩
  rw [← hout]
  unfold simTab outPre
  rcases ho : @hyb3 (icPrg E) R T st w (a, g) o with e | proof
  · rfl
  · obtain ⟨hO, hD, hI⟩ := @hyb3_ok_fields (icPrg E) st w R T cs hzk (a, g) o proof ho
    have hv : @vPre (icPrg E) (rec5 Hb G5) T st proof =
        @vPre (icPrg E') (rec5 Hb G5) T st proof := by
      refine vPre_ic_congr (rec5 Hb G5) T st proof fun k hk => hrd k ?_
      rw [ivOf, hO, hD, hI, rec5_h4, rec5_mu1] at hk
      rw [hRd, hR, recB, recH_hash_ne (by decide) (by decide) (by decide), recH_mu1]
      exact hk
    simp only [hv]

/-- **An ok output of the hybrid has the `iv` of its `iv_pre` coin.** -/
lemma ivV_hyb3 {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs) (E : Cipher)
    (b : Bytes 16 × Grind) (G3 : Tab3) (G5 : Tab5F) (o : Hidden st.params) (iv' : ByteArray)
    (h : ivV Hb st (@hyb3 (icPrg E) (recB Hb st w G3 G5) T st w b o) = some iv') :
    iv' = ivOfPre Hb st b.1 := by
  rcases ho : @hyb3 (icPrg E) (recB Hb st w G3 G5) T st w b o with e | proof
  · rw [ho] at h; cases h
  · rw [ho] at h
    obtain ⟨-, -, hI⟩ := @hyb3_ok_fields (icPrg E) st w (recB Hb st w G3 G5) T cs hzk b o
      proof ho
    simp only [ivV, Option.some.injEq] at h
    rw [← h, ivOf, hI]
    rfl

variable (Hb T st w)

/-- The view before or after H4, from the coins `x = ((a, g), v)`, the hidden part and the cipher. -/
noncomputable def vwH (x : (Bytes 16 × Grind) × Vis2 st.params) (o : Hidden st.params) (E : Cipher) :
    VwIC st.params :=
  (@hyb3 (icPrg E) (recB Hb st w x.2.1 x.2.2.2) T st w x.1 o, x.2.1,
    @simTab (icPrg E) Hb T st x.2.2.2 (@hyb3 (icPrg E) (recB Hb st w x.2.1 x.2.2.2) T st w x.1 o)
      x.1.2 x.2.2.1, x.2.2.2, E)

lemma vwH_fst (x : (Bytes 16 × Grind) × Vis2 st.params) (o : Hidden st.params) (E : Cipher) :
    (vwH Hb T st w x o E).1 = @hyb3 (icPrg E) (recB Hb st w x.2.1 x.2.2.2) T st w x.1 o := rfl

/-- **H4 at points in the chain of `zk_rom_ic_h23`**: for an event `F` read by a consistent
reader `R` of at most `q_E` cipher keys, with `221·(q_E + 4607) < 2¹²⁸`,

    |Pr_3[F] − Pr_4[F]| ≤ 221·(9214 + E_3[chE]) / (2¹²⁸ − 221·(q_E + 4607)),

`E_3` the expectation in the world before the hop. The honest recomputation's reads (whole rows
of the at most `4607` reconstructed nodes) are counted with the distinguisher's, as in
`joint3_h4`; the distinguisher's reads are charged only at the CTR blocks of the proof's `iv`. -/
theorem joint3_h4_pt (hp : SmallParams st.params) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs) (R : PtReads st.params) (hc : R.Cons) {q3 q5 qE : ℕ}
    (hb : R.Bnd q3 q5 qE) (hsmall : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (F : VwIC st.params → Prop) (hF : R.Reads F) :
    |pr (Co3 st.params) (fun c => F (view3 Hb T st w c)) -
        pr (Co4 st.params) (fun c => F (view4 Hb T st w c))| ≤
      221 * (9214 + exP (Co3 st.params) (fun c => (chE R Hb st (view3 Hb T st w c) : ℝ))) /
        (2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)) := by
  let E2 : ((Bytes 16 × Grind) × Vis2 st.params) × (Blk × Cipher) ≃ Co3 st.params :=
    { toFun := fun c => ((((c.2.1, c.1.1.1), (c.1.2.2.1, c.1.1.2)), (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => (((c.1.1.1.2, c.1.1.2.2), (c.1.2.1, c.1.1.2.1, c.1.2.2)), (c.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × Vis2 st.params) × (Hidden st.params × Cipher) ≃ Co4 st.params :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Qx : (Bytes 16 × Grind) × Vis2 st.params → Hidden st.params → Cipher → Finset (Blk × Blk) :=
    fun x o E => R.QE (vwH Hb T st w x o E) ∪
      hRd E (recB Hb st w x.2.1 x.2.2.2) st (x.1.1, x.1.2, o.1, o.2.1) (deltaOf x.1.2) ×ˢ univ
  set den : ℝ := 2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)
  have hden : 0 < den := by simp only [den]; linarith
  -- the honest reads, at every input, give equal rows
  have hrows : ∀ x o (E E' : Cipher), (∀ kz ∈ Qx x o E, E kz.1 kz.2 = E' kz.1 kz.2) →
      ∀ k ∈ hRd E (recB Hb st w x.2.1 x.2.2.2) st (x.1.1, x.1.2, o.1, o.2.1) (deltaOf x.1.2),
        E k = E' k := fun x o E E' h k hk =>
    funext fun z => h (k, z) (by
      simp only [Qx, Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
      exact Or.inr hk)
  have hvw : ∀ x o (E E' : Cipher), (∀ kz ∈ Qx x o E, E kz.1 kz.2 = E' kz.1 kz.2) →
      vwH Hb T st w x o E' = PtReads.withT (vwH Hb T st w x o E) x.2.1 x.2.2.2 E' := fun x o E E' h => by
    obtain ⟨⟨a, g⟩, v⟩ := x
    obtain ⟨h1, h2⟩ := hyb3_simTab_congr (Hb := Hb) hzk a g v o (hrows ((a, g), v) o E E' h)
    simp only [vwH, PtReads.withT]
    rw [h2, h1]
  have hagr : ∀ x o (E E' : Cipher), (∀ kz ∈ Qx x o E, E kz.1 kz.2 = E' kz.1 kz.2) →
      R.Agree (vwH Hb T st w x o E) x.2.1 x.2.2.2 E' := fun x o E E' h =>
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun kz hkz => h kz (Finset.mem_union_left _ hkz)⟩
  have hbound : ∀ x : (Bytes 16 × Grind) × Vis2 st.params,
      |pr (Blk × Cipher) (fun s => F (vwH Hb T st w x
          (@hiddenOut (icPrg s.2) st.params (ivOfPre Hb st x.1.1) (ba (deltaOf x.1.2)) s.1) s.2)) -
        pr (Hidden st.params × Cipher) (fun s => F (vwH Hb T st w x
          (hiddenIdeal (ba (deltaOf x.1.2)) s.1) s.2))| ≤
      221 * (9214 + exP (Blk × Cipher) (fun s => (chE R Hb st (vwH Hb T st w x
          (@hiddenOut (icPrg s.2) st.params (ivOfPre Hb st x.1.1) (ba (deltaOf x.1.2)) s.1) s.2)
          : ℝ))) / den := by
    intro x
    obtain ⟨⟨a, g⟩, v⟩ := x
    set iv := ivOfPre Hb st a
    have hQ : ∀ o (E E' : Cipher), (∀ kz ∈ Qx ((a, g), v) o E, E kz.1 kz.2 = E' kz.1 kz.2) →
        (F (vwH Hb T st w ((a, g), v) o E) ↔ F (vwH Hb T st w ((a, g), v) o E')) := fun o E E' h => by
      rw [hvw _ o E E' h]
      exact (hF _ _ _ _ (hagr _ o E E' h)).symm
    have hQc : ∀ o (E E' : Cipher), (∀ kz ∈ Qx ((a, g), v) o E, E kz.1 kz.2 = E' kz.1 kz.2) →
        Qx ((a, g), v) o E = Qx ((a, g), v) o E' := fun o E E' h => by
      simp only [Qx]
      rw [hvw _ o E E' h, (hc _ _ _ _ (hagr _ o E E' h)).2.2]
      have := rdKeys_congr (hrows ((a, g), v) o E E' h)
      exact congrArg (fun S => R.QE (vwH Hb T st w ((a, g), v) o E) ∪ S ×ˢ univ) this
    have hsub : ∀ o E, qkeys (InY iv) (Qx ((a, g), v) o E) ⊆
        qkeys (InY iv) (R.QE (vwH Hb T st w ((a, g), v) o E)) ∪
          hRd E (recB Hb st w v.1 v.2.2) st (a, g, o.1, o.2.1) (deltaOf g) := fun o E k hk => by
      simp only [qkeys, Finset.mem_image, Finset.mem_filter, Qx, Finset.mem_union,
        Finset.mem_product] at hk ⊢
      obtain ⟨kz, ⟨hm | hm, hP⟩, rfl⟩ := hk
      · exact Or.inl ⟨kz, ⟨hm, hP⟩, rfl⟩
      · exact Or.inr hm.1
    have hqm : ∀ o E, (qkeys (InY iv) (Qx ((a, g), v) o E)).card ≤ qE + 4607 := fun o E =>
      (Finset.card_le_card (hsub o E)).trans ((card_union_le _ _).trans (add_le_add
        ((Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans
          (hb.hE _)) (rdKeys_card _ _ _ _)))
    have h := hide_rom_query_pt st.params iv (ba (deltaOf g)) hp
      (fun o E => F (vwH Hb T st w ((a, g), v) o E)) (Qx ((a, g), v)) hQ hQc hqm (by exact_mod_cast hsmall)
    unfold IC.realPr IC.idealPr at h
    simp only [hiddenOut_ic]
    refine h.trans ?_
    have hiv : ∀ o E iv', ivV Hb st (vwH Hb T st w ((a, g), v) o E).1 = some iv' → iv' = iv := by
      intro o E iv' h
      rw [vwH_fst] at h
      exact ivV_hyb3 (Hb := Hb) hzk E (a, g) v.1 v.2.2 o iv' h
    have hcard : ∀ o E, (qkeys (InY iv) (Qx ((a, g), v) o E)).card ≤
        4607 + chE R Hb st (vwH Hb T st w ((a, g), v) o E) := fun o E => by
      have h1 := Finset.card_le_card (hsub o E)
      have h2 := card_union_le (qkeys (InY iv) (R.QE (vwH Hb T st w ((a, g), v) o E)))
        (hRd E (recB Hb st w v.1 v.2.2) st (a, g, o.1, o.2.1) (deltaOf g))
      have h3 : (hRd E (recB Hb st w v.1 v.2.2) st (a, g, o.1, o.2.1) (deltaOf g)).card ≤ 4607 :=
        rdKeys_card _ _ _ _
      have h4 := R.qkeys_le_chE Hb st (vwH Hb T st w ((a, g), v) o E) iv (hiv o E)
      omega
    have hE : expKeysY st.params iv (ba (deltaOf g)) (Qx ((a, g), v)) ≤
        4607 + exP (Blk × Cipher) (fun s => (chE R Hb st (vwH Hb T st w ((a, g), v)
          (hiddenOutE s.2 st.params iv (ba (deltaOf g)) s.1) s.2) : ℝ)) := by
      rw [← exP_const_add]
      exact exP_mono fun s => by exact_mod_cast hcard _ _
    have hcE : (0 : ℝ) ≤ expKeysY st.params iv (ba (deltaOf g)) (Qx ((a, g), v)) :=
      exP_nonneg fun _ => Nat.cast_nonneg _
    have hc221 : (221 : ℝ) * (4607 + expKeysY st.params iv (ba (deltaOf g)) (Qx ((a, g), v))) ≤
        221 * (9214 + exP (Blk × Cipher) (fun s => (chE R Hb st (vwH Hb T st w ((a, g), v)
          (hiddenOutE s.2 st.params iv (ba (deltaOf g)) s.1) s.2) : ℝ))) := by linarith
    have : (2 : ℝ) ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ) = den := rfl
    push_cast at this ⊢
    rw [this]
    exact div_le_div_of_nonneg_right hc221 hden.le
  have hb' : ∀ x : (Bytes 16 × Grind) × Vis2 st.params,
      |pr (Blk × Cipher) (fun s => F (view3 Hb T st w (E2 (x, s)))) -
        pr (Hidden st.params × Cipher) (fun s => F (view4 Hb T st w (E3 (x, s))))| ≤
      221 * (9214 + exP (Blk × Cipher) (fun s => (chE R Hb st (view3 Hb T st w (E2 (x, s))) : ℝ))) /
        den := fun x => hbound x
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine (abs_pr_prod_sub_le_exP (fun z => F (view3 Hb T st w (E2 z)))
    (fun z => F (view4 Hb T st w (E3 z))) _ hb').trans (le_of_eq ?_)
  have key : exP ((Bytes 16 × Grind) × Vis2 st.params) (fun x => exP (Blk × Cipher)
      (fun s => (chE R Hb st (view3 Hb T st w (E2 (x, s))) : ℝ))) =
      exP (Co3 st.params) (fun c => (chE R Hb st (view3 Hb T st w c) : ℝ)) :=
    (exP_prod (fun z => (chE R Hb st (view3 Hb T st w (E2 z)) : ℝ))).symm.trans
      (exP_equiv E2 (fun c => (chE R Hb st (view3 Hb T st w c) : ℝ)))
  rw [exP_div, exP_mul_left, exP_const_add, key]

end H4

end VoleMole.ZK.Sim
