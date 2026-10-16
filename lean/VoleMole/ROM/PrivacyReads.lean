import VoleMole.ROM.TableReads
import VoleMole.Privacy.PermRA

/-!
# The privacy games with an interaction written as oracle computations over the tables

`Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean` and `Privacy/PomFRITRA.lean` take the
adversary's table-reading interaction as functions of the slices and the shared tables, with the
semantic budget `IBudget` (consistent table readers, `ZK.Sim.SReads`, of each slice and the
shared tables). Here the interaction is a VCVio oracle computation over the four (PomFRIT: two)
slices and the shared tables (`ROM.Reads.TSpec`), run on the game's tables (`ROM.Reads.runT`),
and its budget is the syntactic query bound `ROM.Reads.QBudget` (VCVio's `IsQueryBoundP`, per
slice and per shared table). `IBudget` is then a theorem (`AdversaryOC.iBudget`,
`ROM.Reads.sReads_runT`): consistency holds by construction.

* Moussaka: **`anonymityOC_lean_num`**, **`anonymityOC_lean_num_perm`**.
* Ratatouille: **`unlinkabilityOC_lean_num`**, **`unlinkabilityOC_lean_num_perm`**.
* PomFRIT: **`blindnessOC_lean_num`**, **`blindnessOC_lean_num_perm`**; with `H₂³` queries,
  **`blindnessOCH_lean_num`**, **`blindnessOCH_lean_num_perm`** (`blindnessRAH_lean_num(_perm)`,
  `Privacy/PomFRITRAH.lean`, with the joint budget `IBudgetH` from `QBudget` by `sReadsP_runT`:
  one computation reads both slices).

Each is the corresponding `*RA_lean_num` (`*RA_lean_num_perm`) theorem for the adversary
`A.toRA`, with the bound unchanged and the hypothesis `IBudget` replaced by `QBudget` of the
interaction's computations. Each stage of the interaction is one computation (Moussaka: the
whole transcript at a pair of requests; Ratatouille: stage 1 and stage 2; PomFRIT: the key and
messages, and the responses at a pair of requests), so the stage's messages may share queries.
-/

open OracleComp OracleSpec

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ROM.Reads

open VoleMole.ZK.Sim

/-- **Four slices** (Moussaka, Ratatouille) indexed by `Bool × Bool`. -/
def sl4 (sl : (Tab3 × Tab3) × (Tab3 × Tab3)) : Bool × Bool → Tab3
  | (false, false) => sl.1.1
  | (false, true) => sl.1.2
  | (true, false) => sl.2.1
  | (true, true) => sl.2.2

/-- **Two slices** (PomFRIT) indexed by `Bool`. -/
def sl2 (sl : Tab3 × Tab3) : Bool → Tab3
  | false => sl.1
  | true => sl.2

lemma sl4_ff (a b c d g : Tab3) :
    Function.update (sl4 ((a, b), (c, d))) (false, false) g = sl4 ((g, b), (c, d)) := by
  funext i; rcases i with ⟨_ | _, _ | _⟩ <;> simp [sl4, Function.update]

lemma sl4_ft (a b c d g : Tab3) :
    Function.update (sl4 ((a, b), (c, d))) (false, true) g = sl4 ((a, g), (c, d)) := by
  funext i; rcases i with ⟨_ | _, _ | _⟩ <;> simp [sl4, Function.update]

lemma sl4_tf (a b c d g : Tab3) :
    Function.update (sl4 ((a, b), (c, d))) (true, false) g = sl4 ((a, b), (g, d)) := by
  funext i; rcases i with ⟨_ | _, _ | _⟩ <;> simp [sl4, Function.update]

lemma sl4_tt (a b c d g : Tab3) :
    Function.update (sl4 ((a, b), (c, d))) (true, true) g = sl4 ((a, b), (c, g)) := by
  funext i; rcases i with ⟨_ | _, _ | _⟩ <;> simp [sl4, Function.update]

lemma sl2_f (a b g : Tab3) : Function.update (sl2 (a, b)) false g = sl2 (g, b) := by
  funext i; cases i <;> simp [sl2, Function.update]

lemma sl2_t (a b g : Tab3) : Function.update (sl2 (a, b)) true g = sl2 (a, g) := by
  funext i; cases i <;> simp [sl2, Function.update]

end VoleMole.ROM.Reads

namespace VoleMole.Privacy

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM.Reads

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- **The colluding adversary whose interaction is an oracle computation over the tables**: the
transcript at a pair of requests (both responses and both `(Anchor Set, digest)` choices) is a
computation querying the four `H₃` slices and the shared tables; contexts, keys and the guess as
in `AdversaryRA`. -/
structure AdversaryOC (R : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  trans : Bytes → Bytes → OracleComp (TSpec (Bool × Bool) R (preLen pI)) Trans
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop

namespace AdversaryOC

variable {R : Type} (A : AdversaryOC R)

/-- **The adversary as a function of the tables**: the transcript is the run of `trans` on the
game's slices and tables. -/
def toRA : AdversaryRA R where
  ctxIss := A.ctxIss
  ctxRed := A.ctxRed
  pk := A.pk
  respond q₀ q₁ c sl u :=
    bif c then (runT (TKey.read (sl4 sl) u) (A.trans q₀ q₁)).1.2
    else (runT (TKey.read (sl4 sl) u) (A.trans q₀ q₁)).1.1
  choose q₀ q₁ side sl u :=
    bif side then (runT (TKey.read (sl4 sl) u) (A.trans q₀ q₁)).2.2
    else (runT (TKey.read (sl4 sl) u) (A.trans q₀ q₁)).2.1
  guess := A.guess

lemma toRA_trans (q₀ q₁ : Bytes) (sl : Slices) (u : ShM R) :
    A.toRA.trans q₀ q₁ sl u = runT (TKey.read (sl4 sl) u) (A.trans q₀ q₁) := rfl

variable {A}

/-- **The query budget gives the interaction's budget** (`IBudget`): consistency by
construction. -/
theorem iBudget {i3 i2 i5 iE : ℕ} (hI : ∀ q₀ q₁, QBudget (A.trans q₀ q₁) i3 i2 i5 iE) :
    A.toRA.IBudget i3 i2 i5 iE where
  s0 q₀ q₁ g₁ gL gR := sReads_of_eq (hI q₀ q₁) (sl4 ((g₁, g₁), (gL, gR))) (false, false)
    fun t => by rw [readAt, sl4_ff]; rfl
  s1 q₀ q₁ g₀ gL gR := sReads_of_eq (hI q₀ q₁) (sl4 ((g₀, g₀), (gL, gR))) (false, true)
    fun t => by rw [readAt, sl4_ft]; rfl
  sL q₀ q₁ g₀ g₁ gR := sReads_of_eq (p := pR) (hI q₀ q₁) (sl4 ((g₀, g₁), (gR, gR))) (true, false)
    fun t => by rw [readAt, sl4_tf]; rfl
  sR q₀ q₁ g₀ g₁ gL := sReads_of_eq (p := pR) (hI q₀ q₁) (sl4 ((g₀, g₁), (gL, gL))) (true, true)
    fun t => by rw [readAt, sl4_tt]; rfl

end AdversaryOC

/-- **Theorem 4(a) (Moussaka) with an interaction that is an oracle computation over the
tables** (`anonymityRA_lean_num` for `A.toRA`, function rows): the interaction makes at most `i₃`
queries to each slice, `i₂` to `H₂³`, `i₅` to `H₅` and `i_E` to the cipher (`QBudget`); no
consistency hypothesis. -/
theorem anonymityOC_lean_num (A : AdversaryOC (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.toRA.GBudget q3 q5 qE) (hI : ∀ q₀ q₁, QBudget (A.trans q₀ q₁) i3 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.toRA.ctxRO.base.ci A.toRA.ctxRO.base.cr
      (reductionRA A.toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRA A.toRA idx leanPI leanPR false) -
        pr _ (realGameRA A.toRA idx leanPI leanPR true)| ≤
      4 * εRO (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAd 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 110 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRA_lean_num (A := A.toRA) (idx := idx) hA (AdversaryOC.iBudget hI) hhide

/-- **`anonymityOC_lean_num` with AES as uniformly random permutations**
(`anonymityRA_lean_num_perm` for `A.toRA`). -/
theorem anonymityOC_lean_num_perm (A : AdversaryOC (Equiv.Perm Blk))
    (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.toRA.GBudget q3 q5 qE) (hI : ∀ q₀ q₁, QBudget (A.trans q₀ q₁) i3 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.toRA.ctxRO.base.ci A.toRA.ctxRO.base.cr
      (reductionRA A.toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRA A.toRA idx leanPI leanPR false) -
        pr _ (realGameRA A.toRA idx leanPI leanPR true)| ≤
      4 * εROPm pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAdPm pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 110 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRA_lean_num_perm (A := A.toRA) (idx := idx) hA (AdversaryOC.iBudget hI) hhide

end Moussaka

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Spec.Ratatouille

/-- **The malicious Issuer whose interaction is an oracle computation over the tables**: stage 1
(the issuance responses and `d₁`) and stage 2 (round 1's response and `d₂`) are computations
querying the four `H₃` slices and the shared tables; key, context, balance and guess as in
`AdversaryRA`. -/
structure AdversaryOC (R : Type) (Z : Sizes) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  msg₁ : IssTr Z → OracleComp (TSpec (Bool × Bool) R (preLen pI)) M₁
  msg₂ : IssTr Z → Except Error (SpendRequest Z) → OracleComp (TSpec (Bool × Bool) R (preLen pI)) M₂
  guess : IssTr Z → Rounds Z → SlicesR → ShR R → Prop

namespace AdversaryOC

variable {R : Type} {Z : Sizes} (A : AdversaryOC R Z)

/-- **The Issuer as a function of the tables**: each stage is the run of its computation. -/
def toRA : AdversaryRA R Z where
  pk := A.pk
  ctx := A.ctx
  tInit := A.tInit
  respondIss tr c sl u :=
    bif c then (runT (TKey.read (sl4 sl) u) (A.msg₁ tr)).1.2
    else (runT (TKey.read (sl4 sl) u) (A.msg₁ tr)).1.1
  d₁ tr sl u := (runT (TKey.read (sl4 sl) u) (A.msg₁ tr)).2
  respond₁ tr rq sl u := (runT (TKey.read (sl4 sl) u) (A.msg₂ tr rq)).1
  d₂ tr rq sl u := (runT (TKey.read (sl4 sl) u) (A.msg₂ tr rq)).2
  guess := A.guess

lemma toRA_msg₁ (tr : IssTr Z) (sl : SlicesR) (u : ShR R) :
    A.toRA.msg₁ tr sl u = runT (TKey.read (sl4 sl) u) (A.msg₁ tr) := rfl

lemma toRA_msg₂ (tr : IssTr Z) (rq : Except Error (SpendRequest Z)) (sl : SlicesR) (u : ShR R) :
    A.toRA.msg₂ tr rq sl u = runT (TKey.read (sl4 sl) u) (A.msg₂ tr rq) := rfl

variable {A}

/-- **The query budgets give the interaction's budget** (`IBudget`). -/
theorem iBudget {i3 i2 i5 iE : ℕ} (h1 : ∀ tr, QBudget (A.msg₁ tr) i3 i2 i5 iE)
    (h2 : ∀ tr rq, QBudget (A.msg₂ tr rq) i3 i2 i5 iE) : A.toRA.IBudget i3 i2 i5 iE where
  a0 tr g₁ g₂ g₃ := sReads_of_eq (h1 tr) (sl4 ((g₁, g₁), (g₂, g₃))) (false, false)
    fun t => by rw [readAt, sl4_ff]; rfl
  a1 tr g₀ g₂ g₃ := sReads_of_eq (h1 tr) (sl4 ((g₀, g₀), (g₂, g₃))) (false, true)
    fun t => by rw [readAt, sl4_ft]; rfl
  a2 tr g₀ g₁ g₃ := sReads_of_eq (p := pS) (h1 tr) (sl4 ((g₀, g₁), (g₃, g₃))) (true, false)
    fun t => by rw [readAt, sl4_tf]; rfl
  a3 tr g₀ g₁ g₂ := sReads_of_eq (p := pS) (h1 tr) (sl4 ((g₀, g₁), (g₂, g₂))) (true, true)
    fun t => by rw [readAt, sl4_tt]; rfl
  b0 tr rq g₁ g₂ g₃ := sReads_of_eq (h2 tr rq) (sl4 ((g₁, g₁), (g₂, g₃))) (false, false)
    fun t => by rw [readAt, sl4_ff]; rfl
  b1 tr rq g₀ g₂ g₃ := sReads_of_eq (h2 tr rq) (sl4 ((g₀, g₀), (g₂, g₃))) (false, true)
    fun t => by rw [readAt, sl4_ft]; rfl
  b2 tr rq g₀ g₁ g₃ := sReads_of_eq (p := pS) (h2 tr rq) (sl4 ((g₀, g₁), (g₃, g₃))) (true, false)
    fun t => by rw [readAt, sl4_tf]; rfl
  b3 tr rq g₀ g₁ g₂ := sReads_of_eq (p := pS) (h2 tr rq) (sl4 ((g₀, g₁), (g₂, g₂))) (true, true)
    fun t => by rw [readAt, sl4_tt]; rfl

end AdversaryOC

/-- **Theorem 2 (Ratatouille) with an Issuer whose interaction is an oracle computation over the
tables** (`unlinkabilityRA_lean_num` for `A.toRA`, function rows): each stage makes at most `i₃`
queries to each slice, `i₂` to `H₂³`, `i₅` to `H₅` and `i_E` to the cipher (`QBudget`); no
consistency hypothesis. -/
theorem unlinkabilityOC_lean_num (A : AdversaryOC (Blk → Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.toRA.GBudget q3 q5 qE)
    (h1 : ∀ tr, QBudget (A.msg₁ tr) i3 i2 i5 iE) (h2 : ∀ tr rq, QBudget (A.msg₂ tr rq) i3 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.toRA.ctx
      (reductionRA A.toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A.toRA leanPIR leanPSR b₁ b₂) -
        pr _ (realGameRA A.toRA leanPIR leanPSR b₁' b₂')| ≤
      4 * εRO (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAd 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) + 4 * (1 / 2 ^ 110 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRA_lean_num (A := A.toRA) hA (AdversaryOC.iBudget h1 h2) hhide b₁ b₂ b₁' b₂'

/-- **`unlinkabilityOC_lean_num` with AES as uniformly random permutations**
(`unlinkabilityRA_lean_num_perm` for `A.toRA`). -/
theorem unlinkabilityOC_lean_num_perm (A : AdversaryOC (Equiv.Perm Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.toRA.GBudget q3 q5 qE)
    (h1 : ∀ tr, QBudget (A.msg₁ tr) i3 i2 i5 iE) (h2 : ∀ tr rq, QBudget (A.msg₂ tr rq) i3 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.toRA.ctx
      (reductionRA A.toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A.toRA leanPIR leanPSR b₁ b₂) -
        pr _ (realGameRA A.toRA leanPIR leanPSR b₁' b₂')| ≤
      4 * εROPm pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAdPm pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAdPm pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) +
        4 * (1 / 2 ^ 110 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRA_lean_num_perm (A := A.toRA) hA (AdversaryOC.iBudget h1 h2) hhide b₁ b₂ b₁' b₂'

end Ratatouille

/-! ## PomFRIT -/

namespace PomFRIT

open VoleMole.Spec VoleMole.Spec.PomFRIT

/-- **The Issuer whose interaction is an oracle computation over the tables**: the key and
messages, and the responses at a pair of requests, are computations querying the two sessions'
`H₃` slices and the shared tables; the guess as in `AdversaryRA`. -/
structure AdversaryOC (R : Type) where
  keyOf : OracleComp (TSpec Bool R (preLen pP)) (UOVKey × Bytes × Bytes)
  respOf : Bytes → Bytes → OracleComp (TSpec Bool R (preLen pP)) (Bytes × Bytes)
  guess : Bytes → Bytes → Option (Bytes × Bytes) → SlP → ShP R → Prop

namespace AdversaryOC

variable {R : Type} (A : AdversaryOC R)

/-- **The Issuer as a function of the tables**: each stage is the run of its computation. -/
def toRA : AdversaryRA R where
  pk sl s := (runT (TKey.read (sl2 sl) s) A.keyOf).1
  msg b sl s :=
    bif b then (runT (TKey.read (sl2 sl) s) A.keyOf).2.2
    else (runT (TKey.read (sl2 sl) s) A.keyOf).2.1
  respond t₀ t₁ i sl s :=
    bif i then (runT (TKey.read (sl2 sl) s) (A.respOf t₀ t₁)).2
    else (runT (TKey.read (sl2 sl) s) (A.respOf t₀ t₁)).1
  guess := A.guess

lemma toRA_keyOf (sl : SlP) (s : ShP R) :
    A.toRA.keyOf sl s = runT (TKey.read (sl2 sl) s) A.keyOf := rfl

lemma toRA_respOf (t₀ t₁ : Bytes) (sl : SlP) (s : ShP R) :
    A.toRA.respOf t₀ t₁ sl s = runT (TKey.read (sl2 sl) s) (A.respOf t₀ t₁) := rfl

variable {A}

/-- **The query budgets give the interaction's budget** (`IBudget`: no `H₂³` query). -/
theorem iBudget {i3 i5 iE : ℕ} (hk : QBudget A.keyOf i3 0 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 0 i5 iE) : A.toRA.IBudget i3 i5 iE where
  k0 g₁ := sReads_of_eq hk (sl2 (g₁, g₁)) false fun t => by rw [readAt, sl2_f]; rfl
  k1 g₀ := sReads_of_eq hk (sl2 (g₀, g₀)) true fun t => by rw [readAt, sl2_t]; rfl
  r0 t₀ t₁ g₁ := sReads_of_eq (hr t₀ t₁) (sl2 (g₁, g₁)) false fun t => by rw [readAt, sl2_f]; rfl
  r1 t₀ t₁ g₀ := sReads_of_eq (hr t₀ t₁) (sl2 (g₀, g₀)) true fun t => by rw [readAt, sl2_t]; rfl

/-- The read sets of a run over both slices and the shared tables. -/
def rsOfP (l : List (TKey Bool (preLen pP))) : RSP :=
  (((l.filterMap (TKey.get3 false)).toFinset, (l.filterMap (TKey.get3 true)).toFinset),
    (l.filterMap TKey.get2).toFinset, (l.filterMap TKey.get5).toFinset,
    (l.filterMap TKey.getE).toFinset)

lemma readP_congr (t t' : TbP R) (l : List (TKey Bool (preLen pP))) (h : AgP (rsOfP l) t t') :
    ∀ k ∈ l, TKey.read (m := preLen pP) (sl2 t.1) t.2 k = TKey.read (m := preLen pP) (sl2 t'.1) t'.2 k := by
  obtain ⟨h0, h1, h2, h5, hE⟩ := h
  intro k hk
  cases k with
  | h3 i x =>
    cases i with
    | false => exact h0 x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, by simp [TKey.get3]⟩))
    | true => exact h1 x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, by simp [TKey.get3]⟩))
  | h2 k => exact h2 k (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))
  | h5 x => exact h5 x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))
  | ic x => exact hE x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))

/-- **An oracle computation over both slices and the shared tables is a joint consistent table
reader** (`SReadsP`) with its query budget: the read sets are the queries of the run. -/
theorem sReadsP_runT {α : Type} {oa : OracleComp (TSpec Bool R (preLen pP)) α} {a3 a2 a5 aE : ℕ}
    (h : QBudget oa a3 a2 a5 aE) :
    SReadsP (fun t : TbP R => runT (TKey.read (m := preLen pP) (sl2 t.1) t.2) oa) a3 a2 a5 aE := by
  classical
  refine ⟨fun t => rsOfP (qlog (TKey.read (m := preLen pP) (sl2 t.1) t.2) oa), fun t t' ht => ?_,
    fun t => ?_⟩
  · obtain ⟨e1, e2⟩ := runT_congr oa _ _ (readP_congr t t' _ ht)
    exact ⟨by simp only [e1], e2⟩
  · have c := fun (P : TKey Bool (preLen pP) → Bool) {b : ℕ}
        (hP : IsQueryBoundP oa (fun k => P k = true) b) =>
      countP_qlog_le oa (TKey.read (m := preLen pP) (sl2 t.1) t.2) P hP
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get3] using c _ (h.h3 false)
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get3] using c _ (h.h3 true)
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get2] using c _ h.h2
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get5] using c _ h.h5
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_getE] using c _ h.hE

/-- **The query budgets give the interaction's joint budget** (`IBudgetH`, `H₂³` queries
allowed). -/
theorem iBudgetH {i3 i2 i5 iE : ℕ} (hk : QBudget A.keyOf i3 i2 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 i2 i5 iE) : A.toRA.IBudgetH i3 i2 i5 iE where
  k := sReadsP_runT hk
  r t₀ t₁ := sReadsP_runT (hr t₀ t₁)

end AdversaryOC

/-- **PomFRIT blindness with an Issuer whose interaction is an oracle computation over the
tables, `H₂³` queries included** (`blindnessRAH_lean_num` for `A.toRA`, function rows): each
stage makes at most `i₃` queries to each slice, `i₂` to `H₂³`, `i₅` to `H₅` and `i_E` to the
cipher (`QBudget`); no consistency hypothesis. -/
theorem blindnessOCH_lean_num (A : AdversaryOC (Blk → Blk)) {q3 q5 qE i3 i2 i5 iE : ℕ}
    (hA : A.toRA.GBudget q3 q5 qE) (hk : QBudget A.keyOf i3 i2 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 i2 i5 iE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A.toRA true)| ≤
      4 * εRO (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 110 + εRO (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_num A.toRA hA (AdversaryOC.iBudgetH hk hr)

/-- **`blindnessOCH_lean_num` with AES as uniformly random permutations**
(`blindnessRAH_lean_num_perm` for `A.toRA`). -/
theorem blindnessOCH_lean_num_perm (A : AdversaryOC (Equiv.Perm Blk)) {q3 q5 qE i3 i2 i5 iE : ℕ}
    (hA : A.toRA.GBudget q3 q5 qE) (hk : QBudget A.keyOf i3 i2 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 i2 i5 iE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A.toRA true)| ≤
      4 * εROPm pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 110 + εROPm pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_num_perm A.toRA hA (AdversaryOC.iBudgetH hk hr)

/-- **PomFRIT blindness with an Issuer whose interaction is an oracle computation over the
tables** (`blindnessRA_lean_num` for `A.toRA`, function rows): each stage makes at most `i₃`
queries to each slice, none to `H₂³`, `i₅` to `H₅` and `i_E` to the cipher (`QBudget`); no
consistency hypothesis. -/
theorem blindnessOC_lean_num (A : AdversaryOC (Blk → Blk)) {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.toRA.GBudget q3 q5 qE) (hk : QBudget A.keyOf i3 0 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 0 i5 iE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A.toRA true)| ≤
      4 * εRO (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 :=
  blindnessRA_lean_num A.toRA hA (AdversaryOC.iBudget hk hr)

/-- **`blindnessOC_lean_num` with AES as uniformly random permutations**
(`blindnessRA_lean_num_perm` for `A.toRA`). -/
theorem blindnessOC_lean_num_perm (A : AdversaryOC (Equiv.Perm Blk)) {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.toRA.GBudget q3 q5 qE) (hk : QBudget A.keyOf i3 0 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) i3 0 i5 iE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A.toRA true)| ≤
      4 * εROPm pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 :=
  blindnessRA_lean_num_perm A.toRA hA (AdversaryOC.iBudget hk hr)

end PomFRIT

end VoleMole.Privacy
