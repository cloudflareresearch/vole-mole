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

end VoleMole.Privacy.Moussaka
