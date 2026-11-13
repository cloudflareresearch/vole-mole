import VoleMole.ZK.MainSharedGame
import VoleMole.Privacy.MoussakaMainPU
import VoleMole.Privacy.MoussakaRO

/-!
# Moussaka issuer hiding and unlinkability on `main`, with a shared `H₅` table and cipher

`anonymity_main` (`Privacy/MoussakaMain.lean`) is Theorem 4(a) on `main` (no dedicated label rows)
when each of the four proofs has its own tables. Here the four proofs **share the `H₅` table** (on
every 37-byte input) **and the cipher table**, as in the scheme; each proof keeps its own `H₃`
slice and its own `H₂³` table, both visible to the adversary, the latter programmed by the
simulator (`ZK/MainSharedGame.lean`).

## The game (`realS`)

The colluding adversary of `Moussaka.Adversary` (contexts, keys, responses and Anchor Sets chosen
from the issuance requests, without reading the tables), whose guess sees the shared tables and
the four proofs' own tables (`AdversaryS`, `ZK.Sim.GVis`). The four proofs are the executable
prover (`ZK.Sim.realRO`) for `main`'s statements, run as in `Spec/Moussaka.lean`. The redemption
proofs are computed only if §6's rule lets the redemptions happen (`allOk`): otherwise they are
never shown, and here not computed (`gameS`; in `Privacy/MoussakaMain.lean` they are computed and
hidden).

## The bound (`anonymity_main_shared0`)

    |Pr[world 0] − Pr[world 1]| ≤ 30·εS(q₃, q_E + 8·4607) + 15·(PU₀ + PU₁) + 2·εhide

* `εS q₃ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸`: H1–H4 and grinding of
  `zk_rom_ic_h23_main_num`, for each of the hops of `ZK.Sim.main_shared_le`;
* `PU_b` (`puTermS`): the probability of `ZK.Sim.bstar` **in world `b` with all four proofs
  simulated**: a simulation failed, or for some proof the label offset `d[0..16) ⊕ r` is zero, or a
  key of the guess's `H₅` read set, or an active or sibling gate input of another proof, is a gate
  input of the proof at that offset (`r` the opening of the token the proof is about).
  `Privacy/MoussakaMainSharedPU.lean` bounds it by the (PU) advantage of explicit predictors plus
  explicit collision terms;
* `εhide`: hiding of `Com`, for the reductions `redS` of the adversary with the simulators' coins
  and the tables fixed.

The guess's reads must be consistent (`AdversaryS.Cons`: it reads each `H₃` slice at `q₃` keys, the
cipher at `q_E` keys and `H₅` at the keys `R5`, and changing a table off these keys changes neither
the guess nor `R5`), which every oracle algorithm with these budgets satisfies.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## The adversary and the game -/

/-- The tables the guess sees: the shared `H₅` table and cipher, and each proof's `H₃` slice and
`H₂³` table (issuance 0, 1; redemption left, right). -/
abbrev VisS := GVis pIm pIm pRm pRm

/-- **The colluding adversary on `main` with shared tables**: `Adversary`'s interaction (not
reading the tables) and a guess that also sees the tables, with its `H₅` read set `R5`. -/
structure AdversaryS where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  choose : Bytes → Bytes → Bool → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → Prop
  R5 : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → Finset (ZK.Sim.Bytes 37)

namespace AdversaryS

variable (A : AdversaryS)

/-- The adversary's interaction as an `AdversaryM` (the guess and the read sets are not used). -/
def toM : AdversaryM :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun _ _ _ _ => True, fun _ _ _ _ => ∅,
    fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

/-- **Consistent reads**: with the requests fixed, the guess and its `H₅` read set read each `H₃`
slice at `q3` keys, the cipher at `qE` keys and `H₅` at `R5`. -/
structure Cons (q3 qE : ℕ) : Prop where
  g : ∀ q₀ q₁ y, RdT (A.guess q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE
  r : ∀ q₀ q₁ y, RdT (A.R5 q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE

end AdversaryS

variable (A : AdversaryS) (idx : AnchorSet → UOVKey → ℕ)

/-- **The game of world `b`**, as four proofs in sequence: the two issuance proofs, and the two
redemption proofs if §6's rule lets the redemptions happen. -/
def gameS (b : Bool) : Game SecM Out SW SW SW SW where
  σ₁ s := some (issStmt A.toM s false)
  σ₂ s _ := some (issStmt A.toM s true)
  σ₃ s o₁ o₂ := bif allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂) then
    redStmt A.toM (ptM A.toM idx b s o₁ o₂ false) else none
  σ₄ s o₁ o₂ _ := bif allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂) then
    redStmt A.toM (ptM A.toM idx b s o₁ o₂ true) else none

/-- What the guess gets besides the tables: the two requests and the redemptions. -/
def keyS (b : Bool) (v : GView SecM pIm pIm pRm pRm) :
    Bytes × Bytes × Option (Except Error Bytes × Except Error Bytes) :=
  ((issM A.toM v.s false v.o₁).2, (issM A.toM v.s true v.o₂).2,
    yM A.toM idx b v.s v.o₁ v.o₂ v.o₃ v.o₄)

/-- **The final event of world `b`**: the guess, on the view. -/
def evS (b : Bool) (v : GView SecM pIm pIm pRm pRm) : Prop :=
  A.guess (keyS A idx b v).1 (keyS A idx b v).2.1 (keyS A idx b v).2.2 v.vis

/-- The `H₅` read set of the final event. -/
def r5S (b : Bool) (v : GView SecM pIm pIm pRm pRm) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyS A idx b v).1 (keyS A idx b v).2.1 (keyS A idx b v).2.2 v.vis

/-- **The real game on `main` with shared tables** in world `b`: the executable prover for
`main`'s statements, one `H₅` table and one cipher for the four proofs, SHAKE for the hashes that
are not tables. -/
noncomputable def realS (b : Bool) : ℝ :=
  hyb Hashes.shake (gameS A idx b) false false false false (evS A idx b)

/-- **The (PU) term of world `b`**: `ZK.Sim.bstar` in the game with all four proofs simulated. -/
noncomputable def puTermS (b : Bool) : ℝ :=
  hyb Hashes.shake (gameS A idx b) true true true true
    (bstar Hashes.shake (gameS A idx b) (r5S A idx b))

/-! ## The hypotheses of the joint hop -/

lemma gvalidS (b : Bool) : GValid (gameS A idx b) pIm pIm pRm pRm where
  v₁ s y hy := by cases hy; exact issStmt_valid A.toM s false
  v₂ s _ y hy := by cases hy; exact issStmt_valid A.toM s true
  v₃ s o₁ o₂ y hy := by
    have hy' : y ∈ (bif allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂) then
      redStmt A.toM (ptM A.toM idx b s o₁ o₂ false) else none) := hy
    cases h : allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂)
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact ptM_valid A.toM idx b s o₁ o₂ false y hy'
  v₄ s o₁ o₂ _ y hy := by
    have hy' : y ∈ (bif allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂) then
      redStmt A.toM (ptM A.toM idx b s o₁ o₂ true) else none) := hy
    cases h : allOk A.toM.int idx (issM A.toM s false o₁) (issM A.toM s true o₂)
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact ptM_valid A.toM idx b s o₁ o₂ true y hy'

lemma rd_evS {q3 qE : ℕ} (hC : A.Cons q3 qE) (b : Bool) :
    Rd (evS A idx b) (r5S A idx b) q3 qE :=
  Rd.ofT (keyS A idx b) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun y t => A.guess y.1 y.2.1 y.2.2 t) (fun y t => A.R5 y.1 y.2.1 y.2.2 t)
    fun y => hC.g y.1 y.2.1 y.2.2

lemma rd_r5S {q3 qE : ℕ} (hC : A.Cons q3 qE) (b : Bool) :
    Rd (r5S A idx b) (r5S A idx b) q3 qE :=
  Rd.ofT (keyS A idx b) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun y t => A.R5 y.1 y.2.1 y.2.2 t) (fun y t => A.R5 y.1 y.2.1 y.2.2 t)
    fun y => hC.r y.1 y.2.1 y.2.2

/-- **The joint hop in each world**: real against simulated, `15·εS + 15·PU_b`. -/
theorem real_sim_shared {q3 qE : ℕ} (hC : A.Cons q3 qE) (b : Bool) :
    |realS A idx b - hyb Hashes.shake (gameS A idx b) true true true true (evS A idx b)| ≤
      15 * εS q3 (qE + 8 * 4607) + 15 * puTermS A idx b :=
  main_shared_le Hashes.shake (gameS A idx b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm
    small_pIm small_pRm small_pRm hashesWF_shake (gvalidS A idx b) (evS A idx b) (r5S A idx b)
    (rd_evS A idx hC b) (rd_r5S A idx hC b)


/-! ## With all proofs simulated: a function of the commitments and the nullifiers -/

/-- The simulators' coins and the raw tables (the tape of the simulated game without the
secret). -/
abbrev AuxS := USh × KS pIm × KS pIm × KS pRm × KS pRm

/-- A statement with an empty witness (the simulator's programming reads the statement only). -/
def swOf (st : Statement) : SW := (st, ByteArray.empty)

/-- The simulator's tables depend on the statement only. -/
lemma simVis_congr (Hb : Hashes) (p : Params) (c : SimCoins p) (V : VP p) {y y' : Option SW}
    (h : y.map Prod.fst = y'.map Prod.fst) (u : USh) :
    simVis Hb p c V y u = simVis Hb p c V y' u := by
  rcases y with _ | y <;> rcases y' with _ | y'
  · rfl
  · simp at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    simp only [simVis, h]

/-- §6's rule on the simulated requests, from the commitments and the simulators' coins. -/
noncomputable def okP (t₀ t₁ : Bytes) (a : AuxS) : Bool :=
  allOkT A.toM.int idx (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) t₀ t₁

/-- The guess's third input with all proofs simulated, from the commitments, the nullifiers and
the simulators' coins. -/
noncomputable def YP (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif okP A idx t₀ t₁ a then
    some (ySim A.toM.int simRM b (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) n₀ n₁ a.2.2.2.1.1.2 false,
      ySim A.toM.int simRM b (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) n₀ n₁ a.2.2.2.2.1.2 true)
  else none

/-- The public statement of the redemption of side `side` (none unless §6's rule holds). -/
noncomputable def stRP (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) (side : Bool) : Option Statement :=
  bif okP A idx t₀ t₁ a then
    some (stR (xSideM A.toM b (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) n₀ n₁ side))
  else none

/-- **The tables the guess sees with all proofs simulated**, from the commitments, the nullifiers,
the simulators' coins and the raw tables: the `H₂³` tables are programmed for the public
statements. -/
noncomputable def visP (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : VisS :=
  (a.1, (simVis Hashes.shake pIm a.2.1.1.2 a.2.1.2 (some (swOf (stI ⟨t₀, A.toM.int.ci⟩))) a.1,
    simVis Hashes.shake pIm a.2.2.1.1.2 a.2.2.1.2 (some (swOf (stI ⟨t₁, A.toM.int.ci⟩))) a.1,
    simVis Hashes.shake pRm a.2.2.2.1.1.2 a.2.2.2.1.2
      ((stRP A idx b t₀ t₁ n₀ n₁ a false).map swOf) a.1,
    simVis Hashes.shake pRm a.2.2.2.2.1.2 a.2.2.2.2.2
      ((stRP A idx b t₀ t₁ n₀ n₁ a true).map swOf) a.1))

/-- **The simulated view** as a function of the commitments `t₀, t₁`, the nullifiers `n₀, n₁`
revealed at redemption, the simulators' coins and the raw tables: the openings enter nothing. -/
noncomputable def hviewS (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Prop :=
  A.guess (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) (YP A idx b t₀ t₁ n₀ n₁ a)
    (visP A idx b t₀ t₁ n₀ n₁ a)

/-- `allOk` on simulated issuance outputs is `allOkT` on the requests and the commitments. -/
lemma allOk_sim (s : SecM) (c₁ c₂ : SimCoins pIm) :
    allOk A.toM.int idx (issM A.toM s false (some (simulate pIm c₁)))
        (issM A.toM s true (some (simulate pIm c₂))) =
      allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) :=
  allOk_eq_allOkT idx A.toM.int _ _ rfl rfl

/-- **A redemption statement of the simulated game**: none unless §6's rule holds, and then the
public statement `stR (xSideM …)` with the opening of Client `b ^^ side` as witness prefix. -/
theorem redStmt_sim (b : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (side : Bool) :
    (bif allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) then
      ∃ y, redStmt A.toM (ptM A.toM idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂))
        side) = some y ∧
        y.1 = stR (xSideM A.toM b (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
          (nOf s false) (nOf s true) side) ∧ wPre y.2 = rOf s (b ^^ side)
    else True) := by
  cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
    (tM A.toM s false) (tM A.toM s true)
  · trivial
  · have hA : allOk A.toM.int idx (issM A.toM s false (some (simulate pIm c₁)))
        (issM A.toM s true (some (simulate pIm c₂))) = true := by rw [allOk_sim, hok]
    have hr := redeemOk_pt_of_allOk idx A.toM.int hA b side
    have hfin : finT A.toM.int (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) (b ^^ side) = true := by
      have := hok
      unfold allOkT at this
      simp only [Bool.and_eq_true] at this
      cases b ^^ side
      · exact this.1.1.1.1.1
      · exact this.1.1.1.1.2
    have hsome : ∃ y, redStmt A.toM (ptM A.toM idx b s (some (simulate pIm c₁))
        (some (simulate pIm c₂)) side) = some y := by
      unfold redeemOk at hr
      unfold redStmt
      have e : ptM A.toM idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) side =
          pt A.toM.int idx b (issM A.toM s false (some (simulate pIm c₁)))
            (issM A.toM s true (some (simulate pIm c₂))) side := rfl
      rw [e]
      split at hr
      · cases hr
      · rename_i pk hk
        simp only [decide_eq_true_eq] at hr
        rw [hk]
        simp only
        simp only [hr, ↓reduceIte]
        exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := hsome
    let k : AuxM := ((c₁, Classical.arbitrary _), (c₂, Classical.arbitrary _),
      (Classical.arbitrary _, Classical.arbitrary _), (Classical.arbitrary _, Classical.arbitrary _))
    exact ⟨y, hy, redStmt_fin A.toM idx b s k side hfin y hy⟩


/-- The redemption statements of the simulated game, gated by §6's rule. -/
lemma σ₃_sim (b : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) :
    (gameS A idx b).σ₃ s (some (simulate pIm c₁)) (some (simulate pIm c₂)) =
      bif allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) then
        redStmt A.toM (ptM A.toM idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) false)
      else none := by
  show (bif allOk _ _ _ _ then _ else _) = _
  rw [allOk_sim]

lemma σ₄_sim (b : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (o : Option Out) :
    (gameS A idx b).σ₄ s (some (simulate pIm c₁)) (some (simulate pIm c₂)) o =
      bif allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) then
        redStmt A.toM (ptM A.toM idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) true)
      else none := by
  show (bif allOk _ _ _ _ then _ else _) = _
  rw [allOk_sim]

/-- **The guess's third input with all proofs simulated** is a function of the requests, the
commitments, the nullifiers and the simulators' coins. -/
theorem yS_sim (b : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (c₃ c₄ : SimCoins pRm) :
    yM A.toM idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂))
      (((gameS A idx b).σ₃ s (some (simulate pIm c₁)) (some (simulate pIm c₂))).map fun _ =>
        simulate pRm c₃)
      (((gameS A idx b).σ₄ s (some (simulate pIm c₁)) (some (simulate pIm c₂))
        (((gameS A idx b).σ₃ s (some (simulate pIm c₁)) (some (simulate pIm c₂))).map fun _ =>
          simulate pRm c₃)).map fun _ => simulate pRm c₄) =
      bif allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
        (tM A.toM s false) (tM A.toM s true) then
        some (ySim A.toM.int simRM b (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
            (nOf s false) (nOf s true) c₃ false,
          ySim A.toM.int simRM b (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
            (nOf s false) (nOf s true) c₄ true)
      else none := by
  rw [σ₄_sim, σ₃_sim]
  cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) c₁) (reqS (tM A.toM s true) c₂)
    (tM A.toM s false) (tM A.toM s true)
  · unfold yM
    rw [allOk_sim, hok]
    rfl
  · let k : AuxM := ((c₁, Classical.arbitrary _), (c₂, Classical.arbitrary _),
      (c₃, Classical.arbitrary _), (c₄, Classical.arbitrary _))
    have h := yM_sim A.toM idx b s k
    unfold ySimM at h
    rw [show allOkT A.toM.int idx (reqS (tM A.toM s false) k.1.1) (reqS (tM A.toM s true) k.2.1.1)
      (tM A.toM s false) (tM A.toM s true) = true from hok] at h
    exact h

/-- **With all four proofs simulated, what the guess gets is public**: any function of the
requests, the redemptions and the tables is the same function of `reqS`, `YP` and `visP` at the
commitments and the nullifiers. -/
theorem simS_eq {X : Sort*}
    (f : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → X) (b : Bool)
    (x : GTape SecM pIm pIm pRm pRm) :
    f (keyS A idx b (hybV Hashes.shake (gameS A idx b) true true true true x)).1
        (keyS A idx b (hybV Hashes.shake (gameS A idx b) true true true true x)).2.1
        (keyS A idx b (hybV Hashes.shake (gameS A idx b) true true true true x)).2.2
        (hybV Hashes.shake (gameS A idx b) true true true true x).vis =
      f (reqS (tM A.toM x.1 false) x.2.2.1.1.2) (reqS (tM A.toM x.1 true) x.2.2.2.1.1.2)
        (YP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
        (visP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true)
          x.2) := by
  obtain ⟨s, u, k₁, k₂, k₃, k₄⟩ := x
  have h3 := redStmt_sim A idx b s k₁.1.2 k₂.1.2 false
  have h4 := redStmt_sim A idx b s k₁.1.2 k₂.1.2 true
  have hY := yS_sim A idx b s k₁.1.2 k₂.1.2 k₃.1.2 k₄.1.2
  have hv₃ : simVis Hashes.shake pRm k₃.1.2 k₃.2
      ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u =
      simVis Hashes.shake pRm k₃.1.2 k₃.2
        ((stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
          (u, k₁, k₂, k₃, k₄) false).map swOf) u := by
    refine simVis_congr _ _ _ _ ?_ u
    rw [σ₃_sim]
    unfold stRP okP
    cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) k₁.1.2)
      (reqS (tM A.toM s true) k₂.1.2) (tM A.toM s false) (tM A.toM s true)
    · rfl
    · rw [hok] at h3
      obtain ⟨y, hy, hy1, -⟩ := h3
      simp only [Bool.cond_true, hy, Option.map_some, hy1]
      rfl
  have hv₄ : simVis Hashes.shake pRm k₄.1.2 k₄.2
      ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
        (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
          fun _ => simulate pRm k₃.1.2)) u =
      simVis Hashes.shake pRm k₄.1.2 k₄.2
        ((stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
          (u, k₁, k₂, k₃, k₄) true).map swOf) u := by
    refine simVis_congr _ _ _ _ ?_ u
    rw [σ₄_sim]
    unfold stRP okP
    cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) k₁.1.2)
      (reqS (tM A.toM s true) k₂.1.2) (tM A.toM s false) (tM A.toM s true)
    · rfl
    · rw [hok] at h4
      obtain ⟨y, hy, hy1, -⟩ := h4
      simp only [Bool.cond_true, hy, Option.map_some, hy1]
      rfl
  show f (reqS (tM A.toM s false) k₁.1.2) (reqS (tM A.toM s true) k₂.1.2)
      (yM A.toM idx b s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
        (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
          fun _ => simulate pRm k₃.1.2)
        (((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
          (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
            fun _ => simulate pRm k₃.1.2)).map fun _ => simulate pRm k₄.1.2))
      (u, (simVis Hashes.shake pIm k₁.1.2 k₁.2 (some (issStmt A.toM s false)) u,
        simVis Hashes.shake pIm k₂.1.2 k₂.2 (some (issStmt A.toM s true)) u,
        simVis Hashes.shake pRm k₃.1.2 k₃.2
          ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u,
        simVis Hashes.shake pRm k₄.1.2 k₄.2
          ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
            (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
              fun _ => simulate pRm k₃.1.2)) u)) = _
  rw [hY, hv₃, hv₄]
  rfl

/-- **With all four proofs simulated, the final event is `hviewS`** at the commitments and the
nullifiers. -/
theorem simS_iff (b : Bool) (x : GTape SecM pIm pIm pRm pRm) :
    evS A idx b (hybV Hashes.shake (gameS A idx b) true true true true x) ↔
      hviewS A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true)
        x.2 :=
  iff_of_eq (simS_eq A idx A.guess b x)

/-! ## The hiding hop and the ideal world -/

/-- **The reduction to hiding**: the adversary, with the simulators' coins and the tables fixed,
run on the commitments and nullifiers it is given. -/
noncomputable def redS (b : Bool) (a : AuxS) (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hviewS A idx b z.1 z.2.1 z.2.2.1 z.2.2.2 a

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
noncomputable def idealS (b : Bool) (x : (HTape × (Coins nfBytes × Coins nfBytes)) × AuxS) : Prop :=
  redS A idx b x.2 (hideIdeal A.toM.int.ci A.toM.int.cr x.1)

theorem hiding_hopS (b : Bool) {εhide : ℝ}
    (hhide : ∀ a, hidingAdv A.toM.int.ci A.toM.int.cr (redS A idx b a) ≤ εhide) :
    |hyb Hashes.shake (gameS A idx b) true true true true (evS A idx b) -
      pr _ (idealS A idx b)| ≤ εhide := by
  unfold hyb
  rw [pr_congr (simS_iff A idx b)]
  exact abs_pr_prod_sub_le' (fun x : HTape × AuxS => redS A idx b x.2
    (hideReal A.toM.int.ci A.toM.int.cr x.1)) _ fun a => hhide a

/-- Exchange the fresh nullifiers. -/
def swapNS : (HTape × (Coins nfBytes × Coins nfBytes)) × AuxS ≃
    (HTape × (Coins nfBytes × Coins nfBytes)) × AuxS where
  toFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  invFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **After the hiding hop the worlds coincide**, tables included. -/
theorem idealS_eq : pr _ (idealS A idx false) = pr _ (idealS A idx true) := by
  rw [← pr_equiv swapNS]
  exact pr_congr fun x => Iff.rfl

/-! ## Issuer hiding and unlinkability on `main`, shared tables -/

/-- **Theorem 4(a) on `main` (no label rows) with a shared `H₅` table and cipher, under (PU).**
For the colluding adversary whose guess reads the tables consistently (`AdversaryS.Cons q3 qE`),
if every hiding reduction of the adversary at fixed coins and tables has advantage at most
`εhide`, the two worlds of the real game differ by at most

    30·εS(q3, qE + 8·4607) + 15·(puTermS 0 + puTermS 1) + 2·εhide. -/
theorem anonymity_main_shared0 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b a, hidingAdv A.toM.int.ci A.toM.int.cr (redS A idx b a) ≤ εhide) :
    |realS A idx false - realS A idx true| ≤
      30 * εS q3 (qE + 8 * 4607) + 15 * (puTermS A idx false + puTermS A idx true) +
        2 * εhide := by
  have r0 := real_sim_shared A idx hC false
  have r1 := real_sim_shared A idx hC true
  have h0 := hiding_hopS A idx false (hhide false)
  have h1 := hiding_hopS A idx true (hhide true)
  have e := idealS_eq A idx
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Moussaka
