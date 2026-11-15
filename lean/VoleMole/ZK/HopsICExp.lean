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

/-! ## H1 with the expected number of `H₃` reads, before H4 -/

section Pre

variable [HasPrg] (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **H1 with the tables, charged in the real world**: `joint2_h1` for a consistent reader of at
most `q₃ < 2¹²⁸` `H₃` keys, with the expected number of keys read in the real world. -/
theorem joint2_h1_real (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    (hQ3c : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      Q3 o G3 G2 G5 = Q3 o G3' G2 G5)
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) (hsmall : (q3 : ℝ) < 2 ^ 128) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) T st w (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (runP (recH Hb st w c.2.1 c.1.2 c.2.2) T st w (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2)| ≤
      exP ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ((Q3
        (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) T st w (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2).card : ℝ)) / (2 ^ 128 - q3) := by
  let wP := w.extract 0 st.params.witnessBytes
  let E0 : (Tab2G st.params × Tab5F) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2G st.params × Tab5F) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hR : ∀ G2 G5 (G3 : Tab3), runP (recH Hb st w G3 G2 G5) T st w (preR Hb T st w G5) =
      runP (recH Hb st w (fun _ => 0) G2 G5) T st w (preR Hb T st w G5) :=
    fun G2 G5 G3 => by rw [runP_agreeOff_h3' (recH_agreeOff_h3 _ (fun _ => 0) G2 G5)]
  have hP : ∀ G2 G5 (G3 : Tab3) (ρ : Bytes 16),
      proveP (recH Hb st w G3 G2 G5) T st w (preR Hb T st w G5) ρ =
        runP (recH Hb st w (fun _ => 0) G2 G5) T st w (preR Hb T st w G5) (splitSeed (G3 ρ)) :=
    fun G2 G5 G3 ρ => by simp only [proveP, recH_h3Seed, hR]
  let η : Tab2G st.params × Tab5F → ℝ := fun a => exP (Bytes 16 × Tab3) (fun b => ((Q3
    (proveP (recH Hb st w b.2 a.1 a.2) T st w (preR Hb T st w a.2) b.1) b.2 a.1 a.2).card : ℝ)) /
      (2 ^ 128 - q3)
  have hb : ∀ a : Tab2G st.params × Tab5F,
      |pr (Bytes 16 × Tab3) (fun b => D (proveP (recH Hb st w b.2 a.1 a.2) T st w
          (preR Hb T st w a.2) b.1) b.2 a.1 a.2) - pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b =>
          D (runP (recH Hb st w b.1 a.1 a.2) T st w (preR Hb T st w a.2) b.2) b.1 a.1 a.2)| ≤
        η a := by
    intro a
    obtain ⟨G2, G5⟩ := a
    let Rr : Bytes 16 × Bytes 16 → Except String ByteArray :=
      runP (recH Hb st w (fun _ => 0) G2 G5) T st w (preR Hb T st w G5)
    let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (Rr v) G3 G2 G5
    have h := h3_rom_query_real (mu1 := st.mu1 Hb) (wPrefix := wP) Hb A
      (fun v G3 => Q3 (Rr v) G3 G2 G5)
      (fun v G3 G3' hk => hQ3 (Rr v) G3 G3' G2 G5 hk) (fun v G3 G3' hk => hQ3c (Rr v) G3 G3' G2 G5 hk)
      (fun v G3 => hq3 _ G3 G2 G5) hsmall
    have e1 : pr (Bytes 16 × Tab3) (fun b => D (proveP (recH Hb st w b.2 G2 G5) T st w
        (preR Hb T st w G5) b.1) b.2 G2 G5) = pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
          A (h3Seed (Hb.withTable .h3 (seedInput (st.mu1 Hb) wP) p.2) (st.mu1 Hb) wP (ba p.1)) p.2) := by
      refine pr_congr fun b => ?_
      simp only [A, h3Seed_withTable, hP]
      rfl
    have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p => A (splitSeed p.2.2) p.2.1) =
        pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runP (recH Hb st w b.1 G2 G5) T st w
          (preR Hb T st w G5) b.2) b.1 G2 G5) := by
      rw [pr_prod_snd (α := Bytes 16) (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
        ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
      refine pr_congr fun b => ?_
      simp only [A, Rr, hR]
      rfl
    have e3 : exP (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        ((Q3 (Rr (splitSeed (p.2 p.1))) p.2 G2 G5).card : ℝ)) =
        exP (Bytes 16 × Tab3) (fun b => ((Q3 (proveP (recH Hb st w b.2 G2 G5) T st w
          (preR Hb T st w G5) b.1) b.2 G2 G5).card : ℝ)) := by
      exact congrArg (exP _) (funext fun b => by rw [hP])
    rw [e1, ← e2]
    refine h.trans (le_of_eq ?_)
    simp only [η]
    rw [← e3]
  have hb' : ∀ a : Tab2G st.params × Tab5F,
      |pr (Bytes 16 × Tab3) (fun b => D (proveP (recH Hb st w (E0 (a, b)).2.1 (E0 (a, b)).1.2
          (E0 (a, b)).2.2) T st w (preR Hb T st w (E0 (a, b)).2.2) (E0 (a, b)).1.1) (E0 (a, b)).2.1
          (E0 (a, b)).1.2 (E0 (a, b)).2.2) -
        pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runP (recH Hb st w (E1 (a, b)).2.1
          (E1 (a, b)).1.2 (E1 (a, b)).2.2) T st w (preR Hb T st w (E1 (a, b)).2.2) (E1 (a, b)).1.1)
          (E1 (a, b)).2.1 (E1 (a, b)).1.2 (E1 (a, b)).2.2)| ≤ η a := fun a => hb a
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine (abs_pr_prod_sub_le_exP (fun z => D (proveP (recH Hb st w (E0 z).2.1 (E0 z).1.2
    (E0 z).2.2) T st w (preR Hb T st w (E0 z).2.2) (E0 z).1.1) (E0 z).2.1 (E0 z).1.2 (E0 z).2.2)
    (fun z => D (runP (recH Hb st w (E1 z).2.1 (E1 z).1.2 (E1 z).2.2) T st w
      (preR Hb T st w (E1 z).2.2) (E1 z).1.1) (E1 z).2.1 (E1 z).1.2 (E1 z).2.2) η hb').trans
    (le_of_eq ?_)
  have key : exP (Tab2G st.params × Tab5F) (fun a => exP (Bytes 16 × Tab3) (fun b => ((Q3
      (proveP (recH Hb st w b.2 a.1 a.2) T st w (preR Hb T st w a.2) b.1) b.2 a.1 a.2).card : ℝ))) =
      exP ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ((Q3
        (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) T st w (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2).card : ℝ)) :=
    (exP_prod (fun z : (Tab2G st.params × Tab5F) × (Bytes 16 × Tab3) => ((Q3
      (proveP (recH Hb st w (E0 z).2.1 (E0 z).1.2 (E0 z).2.2) T st w (preR Hb T st w (E0 z).2.2)
        (E0 z).1.1) (E0 z).2.1 (E0 z).1.2 (E0 z).2.2).card : ℝ))).symm.trans
      (exP_equiv E0 (fun c => ((Q3 (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) T st w
        (preR Hb T st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2).card : ℝ)))
  rw [exP_div, key]

/-- **The hybrids before H4, charged in the real world** (`zk_pre_h4` with H1 charged by the
expected number of `H₃` keys read by the real prover's distinguisher), for any PRG. -/
theorem zk_pre_h4_real {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true) (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    (hQ3c : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      Q3 o G3 G2 G5 = Q3 o G3' G2 G5)
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) (hsmall : (q3 : ℝ) < 2 ^ 128) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, c.2.2))| ≤
      exP ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ((Q3
        (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2).card : ℝ)) / (2 ^ 128 - q3) + pr Grind (GrindBad CrtGen.tables) := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  have hpp : ∀ c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F),
      Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1) =
        proveP (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w
          (preR Hb CrtGen.tables st w c.2.2) c.1.1 := fun c => by
    have hR : RunHyp (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w cs :=
      ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
    rw [← proveP_prove _ CrtGen.tables st w hR c.1.1, prePrefix_recH]
  have e0 : pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
      D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
        c.2.1 c.1.2 c.2.2) =
      pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w
          (preR Hb CrtGen.tables st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2) :=
    pr_congr fun c => by rw [hpp c]
  have eX : exP ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ((Q3
        (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2).card : ℝ)) =
      exP ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ((Q3
        (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w
          (preR Hb CrtGen.tables st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2).card : ℝ)) :=
    congrArg (exP _) (funext fun c => by rw [hpp c])
  rw [e0, eX]
  have h1 := joint2_h1_real Hb CrtGen.tables st w D Q3 hQ3 hQ3c hq3 hsmall
  have h2 := joint2_prog Hb CrtGen.tables st w hHb hzk.q D
  have h3 := joint2_keys Hb st w hHb hzk hlab D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

end Pre

/-! ## H6 with the expected number of `H₅` reads at the proof's gate inputs -/

section H6

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)
  (QD : Except String ByteArray → (K → Bytes 4) → Finset K)

/-- **The H6 charge of a proof, any layout**: the distinguisher's `H₅` keys that guess something
(`guessOfG`: gate inputs of this proof). -/
noncomputable def chg5G (G : K → Bytes 4) (s : Shared) (f : SimFields st.params) : ℕ :=
  ((QD (outOf st s f) G).filter fun k => (guessOfG Hs T st enc s f k).Nonempty).card

lemma card_guessesG_le_chg (G : K → Bytes 4) (s : Shared) (f : SimFields st.params) :
    (guessesG Hs T st enc QD G s f).card ≤ 1 + chg5G Hs T st enc QD G s f := by
  classical
  unfold guessesG chg5G
  refine (Finset.card_insert_le _ _).trans ?_
  rw [Nat.add_comm 1]
  refine Nat.add_le_add_right ?_ 1
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.card_filter]
  convert Finset.sum_le_sum (s := QD (outOf st s f) G) fun k _ =>
    (show (guessOfG Hs T st enc s f k).card ≤ if (guessOfG Hs T st enc s f k).Nonempty then 1 else 0 by
      split_ifs with hk
      · exact card_guessOfG_le Hs T st enc s f k
      · rw [Finset.not_nonempty_iff_eq_empty.1 hk, Finset.card_empty])

set_option synthInstance.maxSize 1024 in
/-- **`pr_bad_leG` with the expected charge** (as `pr_bad_exp`, any layout):
`Pr[bad] ≤ (1 + E_f[chg5G]) / 2¹²⁸`. -/
theorem pr_bad_expG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs) (G : K → Bytes 4) (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      (1 + exP (SimFields st.params) (fun f => (chg5G Hs T st enc QD G s f : ℝ))) / 2 ^ 128 := by
  obtain ⟨h1, -, hlb, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let F := fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2
  let S := guessesG Hs T st enc QD G s
  have e1 : pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) :=
    pr_mono fun t ht => by
      have hm := bad_mem_guessesG Hs T st w cs enc sk QD hsk hlab h G s t ht
      rw [uPre_eq_thetaW hlr] at hm
      rw [fieldsOf_theta]
      exact hm
  have e2 : pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params))
        (fun y => thetaW st.params y.2 ∈ S y.1) := by
    have := (upush_fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT
      h.hnm) (fun y => thetaW st.params y.2 ∈ S y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have e3 : pr (SimFields st.params × Bytes (labelBytes st.params))
      (fun y => thetaW st.params y.2 ∈ S y.1) ≤
      exP (SimFields st.params) (fun f => ((S f).card : ℝ)) /
        Fintype.card (Bytes (labelBytes st.params)) := by
    rw [← pr_equiv (Equiv.prodComm (Bytes (labelBytes st.params)) (SimFields st.params))]
    exact pr_mem_indep_exp (thetaW st.params) (thetaW_injective hlr) S
  have hc : ((2 ^ (8 * labelBytes st.params) : ℕ) : ℝ) = 2 ^ 128 := by rw [hlb]; norm_num
  rw [Prob.card_bytes, hc] at e3
  refine (e1.trans (e2.le.trans e3)).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  rw [← exP_const_add]
  exact exP_mono fun f => by exact_mod_cast card_guessesG_le_chg Hs T st enc QD G s f

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 4000 in
/-- **`lab_rom_query_sG` with the expected charge**: `≤ (1 + E_{G,s,f}[chg5G]) / 2¹²⁸`, the
expectation over the table, the shared tape and the simulated proof's fields. -/
theorem lab_rom_query_sG_exp
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G')) :
    |pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2) -
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2))
          x.1.1 x.2.1)| ≤
      (1 + exP ((K → Bytes 4) × SimCoins st.params) (fun x =>
        (chg5G Hs T st enc (fun o G => QD o x.2.1 G) x.1 x.2.1 x.2.2 : ℝ))) / 2 ^ 128 := by
  refine (lab_romG Hs T st enc sk hsk hkey
    (fun t G => D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    (fun t G => proverKeysG Hs T st enc t ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    fun t G G' hG => hA t G G' hG).trans ?_
  let E : (K → Bytes 4) × IdealTape st.params ≃
      (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) :=
    { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
      invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E]
  let X : (K → Bytes 4) → Shared → ℝ := fun G s => exP (SimFields st.params)
    (fun f => (chg5G Hs T st enc (fun o G => QD o s G) G s f : ℝ))
  refine (pr_prod_le_exP _ (fun G => exP Shared (fun s => (1 + X G s) / 2 ^ 128))
    fun G => pr_prod_le_exP _ (fun s => (1 + X G s) / 2 ^ 128) fun s => ?_).trans (le_of_eq ?_)
  · exact pr_bad_expG Hs T st w cs enc sk (fun o G => QD o s G) hsk hlr h G s
  · calc exP (K → Bytes 4) (fun G => exP Shared (fun s => (1 + X G s) / 2 ^ 128))
        = exP (K → Bytes 4) (fun G => (1 + exP Shared (X G)) / 2 ^ 128) :=
          congrArg (exP _) (funext fun G => by rw [exP_div, exP_const_add])
      _ = (1 + exP (K → Bytes 4) (fun G => exP Shared (X G))) / 2 ^ 128 := by
          rw [exP_div, exP_const_add]
      _ = _ := by
          have key : exP (K → Bytes 4) (fun G => exP Shared (X G)) =
              exP ((K → Bytes 4) × SimCoins st.params) (fun x =>
                (chg5G Hs T st enc (fun o G => QD o x.2.1 G) x.1 x.2.1 x.2.2 : ℝ)) :=
            (congrArg (exP _) (funext fun G => (exP_prod (α := Shared) (β := SimFields st.params)
              (fun z => (chg5G Hs T st enc (fun o G' => QD o z.1 G') G z.1 z.2 : ℝ))).symm)).trans
              (exP_prod (α := K → Bytes 4) (β := SimCoins st.params) (fun x =>
                (chg5G Hs T st enc (fun o G => QD o x.2.1 G) x.1 x.2.1 x.2.2 : ℝ))).symm
          rw [key]

set_option synthInstance.maxSize 1024 in
/-- **`lab_rom_hyp_sG` with the expected charge.** -/
theorem lab_rom_hyp_sG_exp
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G')) :
    |pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st x.1))
          x.1.1 x.2) -
      pr (IdealTape st.params × (K → Bytes 4))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w x.1) x.1.1 x.2)| ≤
      (1 + exP ((K → Bytes 4) × SimCoins st.params) (fun x =>
        (chg5G Hs T st enc (fun o G => QD o x.2.1 G) x.1 x.2.1 x.2.2 : ℝ))) / 2 ^ 128 := by
  let E2 : ((Shared × PadsU st.params) × (K → Bytes 4)) × Sib ≃
      IdealTape st.params × (K → Bytes 4) :=
    { toFun := fun y => ((y.1.1.1, withSib y.1.1.2 y.2), y.1.2)
      invFun := fun x => (((x.1.1, dropSib x.1.2), x.2), x.1.2.2.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) ≃
      IdealTape st.params × (K → Bytes 4) :=
    { toFun := fun y => ((y.1.1, withSib y.1.2 y.2.2), y.2.1)
      invFun := fun x => ((x.1.1, dropSib x.1.2), (x.2, x.1.2.2.2.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e1 : pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
      D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st x.1))
        x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (K → Bytes 4) => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w
        (fillSib (Hs.withTable .h5 enc x.2) T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0)))
        x.1.1 x.2)]
    refine pr_congr fun y => ?_
    show D (proveIdeal (Hs.withTable .h5 enc y.1.2) T st w (fillSib (Hs.withTable .h5 enc y.1.2) T st
        (y.1.1.1, withSib y.1.1.2 y.2))) y.1.1.1 y.1.2 ↔ _
    rw [fillSib_withSib T st _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
  have e2 : pr (IdealTape st.params × (K → Bytes 4))
      (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w x.1) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2))
          x.1.1 x.2.1) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  exact lab_rom_query_sG_exp Hs T st w cs enc sk hsk hkey hlr h D QD hA

/-- **The `H₅` charge of a read set** at an output's `iv` (every key, without an `iv`). -/
noncomputable def ch5Q (p : Params) (T : CrtTables) (Q : Finset (Bytes 37)) :
    Option ByteArray → ℕ
  | some iv => (Q.filter (Gate5 p T iv)).card
  | none => Q.card

omit [HasPrg] in
lemma ch5_eq (R : PtReads st.params) (Hb : Hashes) (v : VwIC st.params) :
    ch5 R Hb T st v = ch5Q st.params T (R.Q5 v) (ivV Hb st v.1) := by
  unfold ch5 ch5Q
  split <;> rfl

omit [HasPrg] in
/-- An ok output of the ideal-tape prover has the shared tape's `iv_pre`. -/
lemma outOf_ivPre {s : Shared} {f : SimFields st.params} {b : ByteArray}
    (h : outOf st s f = .ok b) : (⟨st.params, b⟩ : Proof).ivPre = ba s.1 := by
  unfold outOf at h
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, δ⟩
  · rw [hf] at h; cases h
  · rw [hf] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact (fields_assemble st.params _).2.2.2.2.2.2.2.1.trans (fit_of_size (size_ba _))

/-- A key that guesses something is a gate input of the proof's `iv`. -/
lemma guessOfG_gate {s : Shared} {f : SimFields st.params} {k : Bytes 37}
    (h : (guessOfG Hs T st enc5 s f k).Nonempty) :
    Gate5 st.params T (pubOf Hs st s (deltaOf s.2.1)).iv k := by
  unfold guessOfG at h
  split at h
  · rename_i hex
    obtain ⟨v, e, he⟩ := hex
    exact ⟨_, v, e, he⟩
  · simp at h

/-- **The H6 charge is at most the view's `H₅` charge**, for a record with the base record's
`H₄` and `μ₁`. -/
lemma chg5G_le_ch5Q (Hb : Hashes) (hmu : st.mu1 Hs = st.mu1 Hb) (h4 : Hs.hash .h4 = Hb.hash .h4)
    (QD5 : Except String ByteArray → Tab5F → Finset (Bytes 37)) (G : Tab5F) (s : Shared)
    (f : SimFields st.params) :
    chg5G Hs T st enc5 QD5 G s f ≤ ch5Q st.params T (QD5 (outOf st s f) G) (ivV Hb st (outOf st s f)) := by
  unfold chg5G
  rcases ho : outOf st s f with e | b
  · exact Finset.card_filter_le _ _
  · have hiv : ivV Hb st (.ok b) = some (pubOf Hs st s (deltaOf s.2.1)).iv := by
      simp only [ivV, ivOf, outOf_ivPre st ho, pubOf, hmu, h4]
    rw [hiv]
    refine Finset.card_le_card fun k hk => ?_
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, guessOfG_gate Hs T st hk.2⟩

variable (Hb : Hashes)

/-- **H6 with the tables, charged in the simulated world**: `joint2_h6` with
`(1 + E[ch5Q]) / 2¹²⁸`, the expectation over the tables and the simulator's coins, of the
distinguisher's `H₅` keys at the gate inputs of the simulated proof's `iv`. -/
theorem joint2_h6_exp (hlr : st.params.labelRows = true)
    (hzk : ZKHyp T st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5')) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w
          (fillSib (recB Hb st w c.2.1 c.2.2.2) T st c.1)) c.1.1.2.1 c.2) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w c.1) c.1.1.2.1 c.2)| ≤
      (1 + exP ((Tab3 × Tab2G st.params) × (Tab5F × SimCoins st.params)) (fun x =>
        (ch5Q st.params T (Q5 (outOf st x.2.2.1 x.2.2.2) x.1.1
          (simTab Hb T st x.2.1 (outOf st x.2.2.1 x.2.2.2) x.2.2.1.2.1 x.1.2) x.2.1)
          (ivV Hb st (outOf st x.2.2.1 x.2.2.2)) : ℝ))) / 2 ^ 128 := by
  obtain ⟨h1, -, -, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let E6 : (Tab3 × Tab2G st.params) × (IdealTape st.params × Tab5F) ≃
      IdealTape st.params × Vis2 st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.1.2, c.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Y : Tab3 × Tab2G st.params → Tab5F × SimCoins st.params → ℝ := fun a y =>
    (ch5Q st.params T (Q5 (outOf st y.2.1 y.2.2) a.1
      (simTab Hb T st y.1 (outOf st y.2.1 y.2.2) y.2.1.2.1 a.2) y.1)
      (ivV Hb st (outOf st y.2.1 y.2.2)) : ℝ)
  let η : Tab3 × Tab2G st.params → ℝ := fun a => (1 + exP (Tab5F × SimCoins st.params) (Y a)) / 2 ^ 128
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine (abs_pr_prod_sub_le_exP (fun z => Dp Hb T st D (proveIdeal (recB Hb st w (E6 z).2.1
      (E6 z).2.2.2) T st w (fillSib (recB Hb st w (E6 z).2.1 (E6 z).2.2.2) T st (E6 z).1))
      (E6 z).1.1.2.1 (E6 z).2)
    (fun z => Dp Hb T st D (proveIdeal (recB Hb st w (E6 z).2.1 (E6 z).2.2.2) T st w (E6 z).1)
      (E6 z).1.1.2.1 (E6 z).2) η fun a => ?_).trans (le_of_eq ?_)
  swap
  · have key : exP (Tab3 × Tab2G st.params) (fun a => exP (Tab5F × SimCoins st.params) (Y a)) =
        exP ((Tab3 × Tab2G st.params) × (Tab5F × SimCoins st.params)) (fun x => Y x.1 x.2) :=
      (exP_prod (fun x => Y x.1 x.2)).symm
    simp only [η]
    rw [exP_div, exP_const_add, key]
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).withTable .h23 (enc2 st.params) (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (enc2 st.params) (fun _ => 0)
  have hbwf : HashesWF base := (hHb.withTable .h3 _ G3).withTable .h23 _ _
  have hmu : st.mu1 base = st.mu1 Hb :=
    ((a1.mu1 (by decide) (by decide) st).trans (a2.mu1 (by decide) (by decide) st)).symm
  have hh4 : base.hash .h4 = Hb.hash .h4 := ((a1 .h4 (by decide)).trans (a2 .h4 (by decide))).symm
  let sk : Shared × PadsU st.params → Fin 312 → Bytes 37 := fun c e =>
    blk 37 (sibInput base T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
  have hsk : ∀ c e, enc5 (sk c e) = sibInput base T st c.1 (withSib c.2 fun _ => fun _ => 0) e :=
    fun c e => ba_blk_of_size (sibInput_size base T st hbwf _ _ e)
  have hkey : ∀ c e, keyOf enc5 (sk c e) = sk c e :=
    fun c e => keyOf_eq (fun a b h => ba_injective h) _
  have hv5 : ∀ G : Tab5F, vIn5 (rec5 Hb G) T st = vIn5 base T st := by
    intro G
    have a0 := Hb.agreeOff_withTable .h5 enc5 G
    refine vIn5_congr T st ?_ ?_
    · exact (a0.mu1 (by decide) (by decide) st).symm.trans
        ((a1.mu1 (by decide) (by decide) st).trans (a2.mu1 (by decide) (by decide) st))
    · exact (a0 .h4 (by decide)).symm.trans ((a1 .h4 (by decide)).trans (a2 .h4 (by decide)))
  have hA : ∀ (t : IdealTape st.params) (G G' : Tab5F), (∀ k ∈ proverKeysG base T st enc5 t ∪
      (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5)
        (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1 G, G k = G' k) →
      ((fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1 G ↔
        (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1 G') := by
    intro t G G' hG
    have hp := proveIdeal_table_congrG base T st w enc5 hlab t G G'
      fun k hk => hG k (Finset.mem_union_left _ hk)
    have hpre : outPre Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) =
        outPre Hb T st G' (proveIdeal (base.withTable .h5 enc5 G) T st w t) := by
      rcases ho : proveIdeal (base.withTable .h5 enc5 G) T st w t with e | b
      · rfl
      · simp only [outPre]
        have hag : (rec5 Hb G).AgreeOff .h5 (rec5 Hb G') :=
          Hashes.AgreeOff.withTable_same (k := .h5) (Hs := Hb) (Hs' := Hb) (fun _ _ => rfl) enc5
            enc5 G G'
        refine vPre_h5_congr hag T st b fun x hx => ?_
        rw [hv5] at hx
        have hx' : x ∈ actInputs base T st t.1 t.2 :=
          vIn5_proveIdeal base T st w (base.withTable .h5 enc5 G) hzk t.1 t.2 ho x hx
        simp only [rec5, Hashes.withTable, ↓reduceIte]
        split
        · rename_i hy
          have hk : hy.choose ∈ proverKeysG base T st enc5 t := by
            rw [mem_proverKeysG, hy.choose_spec]; exact hx'
          exact congrArg ba (hG _ (Finset.mem_union_left _ hk))
        · rfl
    have hX : simTab Hb T st G' (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1.2.1 G2 =
        simTab Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1.2.1 G2 := by
      unfold simTab
      rw [← hp, ← hpre]
    show D (proveIdeal (base.withTable .h5 enc5 G) T st w t) G3
        (simTab Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1.2.1 G2) G ↔
      D (proveIdeal (base.withTable .h5 enc5 G') T st w t) G3
        (simTab Hb T st G' (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1.2.1 G2) G'
    rw [hX, ← hp]
    exact hQ5 _ G3 _ G G' fun k hk => hG k (Finset.mem_union_right _ hk)
  refine (lab_rom_hyp_sG_exp base T st w cs enc5 sk hsk hkey hlr hzk
    (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
    (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) hA).trans ?_
  refine div_le_div_of_nonneg_right (add_le_add_right (exP_mono fun x => ?_) 1) (by positivity)
  exact Nat.cast_le.2 (chg5G_le_ch5Q base T st Hb hmu hh4
    (fun o G5 => Q5 o G3 (simTab Hb T st G5 o x.2.1.2.1 G2) G5) x.1 x.2.1 x.2.2)

end H6

end VoleMole.ZK.Sim
