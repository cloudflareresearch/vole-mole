import VoleMole.ZK.MainShared23
import VoleMole.Privacy.MoussakaMainSharedPU

/-!
# Moussaka issuer hiding and unlinkability on `main`, with one shared `H₂³` table

`anonymity_main_shared` (`Privacy/MoussakaMainSharedPU.lean`) is Theorem 4(a) on `main` with one
`H₅` table and one cipher for the four proofs, each proof keeping its own `H₂³` table. Here the
four proofs also **share the `H₂³` table** (`ZK/MainShared23.lean`): the real provers read one
table, the simulators program it, and the adversary sees the one programmed table (as each
proof's `H₂³` component of the view, `VisS`). Each proof keeps its own `H₃` slice.

## The game (`real23`)

The game of `realS` (`gameS`, `evS`, `r5S`: the same adversary `AdversaryS`, the same events),
run with `ZK.Sim.hyb23`: the raw `H₂³` table is drawn once, every real proof reads it.

## The bound (`anonymity_main_shared23`)

    |Pr[world 0] − Pr[world 1]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(Σ_{b,c} puAdv Com (predS23_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide

* `Δ23 = 2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸ + noHitProb + 3·2⁻¹⁰²⁴`: the programming-collision term
  of each of the 15 hop applications per world (`ZK.Sim.pr_collide_main`): a real proof reads a
  grinding point that an earlier simulation programmed;
* the (PU) predictors `predS23` are those of `predS` with the guess's read set computed on the
  shared programmed table (`r5P23`); the collision and failure terms are unchanged
  (`pr_coll₂_le` …, `pr_errS₁_le` …), since the bad event `bstar` does not look at `H₂³`;
* `εhide`: hiding of `Com` for the reductions `redS23` (the simulators' coins and the raw tables
  fixed).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate realRO progRO

variable (A : AdversaryS) (idx : Rule)

/-! ## The game with one `H₂³` table -/

/-- **The real game on `main` with all tables shared** in world `b`: the four proofs read one
`H₂³` table, one `H₅` table and one cipher. -/
noncomputable def real23 (b : Bool) : ℝ :=
  hyb23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake (gameS A idx b)
    false false false false (evS A idx b)

/-- **The (PU) term of world `b`**: `bstar` with all four proofs simulated on the shared table. -/
noncomputable def puTerm23 (b : Bool) : ℝ :=
  hyb23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake (gameS A idx b)
    true true true true (bstar Hashes.shake (gameS A idx b) (r5S A idx b))

/-- **The joint hop in each world**: real against simulated, `15·(εS + Δ23) + 15·PU_b`. -/
theorem real_sim_shared23 {q3 qE : ℕ} (hC : A.Cons q3 qE) (b : Bool) :
    |real23 A idx b - hyb23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameS A idx b) true true true true (evS A idx b)| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * puTerm23 A idx b :=
  main_shared23_le (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameS A idx b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm small_pIm small_pRm
    small_pRm hashesWF_shake (gvalidS A idx b) (evS A idx b) (r5S A idx b) (rd_evS A idx hC b)
    (rd_r5S A idx hC b)

/-! ## With all proofs simulated: a function of the commitments and the nullifiers -/

/-- The programming of a simulation with coins `c` for an optional public statement. -/
noncomputable def pgP (p : Params) (c : SimCoins p) (st : Option Statement) (u : USh)
    (G2 : Tab2G p) : Tab2G p :=
  match st with
  | some st => (progRO p Hashes.shake (withP st p) c ((G2, u) : Sh p)).1
  | none => G2

/-- A simulator's programming depends on the statement only. -/
lemma simSB_pg_eq (p : Params) (c : SimCoins p) (G3 : Tab3) (y : Option SW) :
    (simSB Hashes.shake p c G3).pg y = pgP p c (y.map Prod.fst) := by
  rcases y with _ | y <;> rfl

/-- **The shared `H₂³` table the guess sees with all proofs simulated**, from the public
statements: the raw table programmed by the four simulations, the first outermost. -/
noncomputable def tabP (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Tab2G pIm :=
  pgP pIm a.2.1.1.2 (some (stI ⟨t₀, A.toM.int.ci⟩)) a.1
    (pgP pIm a.2.2.1.1.2 (some (stI ⟨t₁, A.toM.int.ci⟩)) a.1
      (pgP pRm a.2.2.2.1.1.2 (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1
        (pgP pRm a.2.2.2.2.1.2 (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1 a.2.1.2.2)))

/-- **The tables the guess sees with all proofs simulated** on the shared `H₂³` table. -/
noncomputable def visP23 (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : VisS :=
  (a.1, ((a.2.1.2.1, tabP A idx b t₀ t₁ n₀ n₁ a), (a.2.2.1.2.1, tabP A idx b t₀ t₁ n₀ n₁ a),
    (a.2.2.2.1.2.1, tabP A idx b t₀ t₁ n₀ n₁ a), (a.2.2.2.2.2.1, tabP A idx b t₀ t₁ n₀ n₁ a)))

/-- **The simulated view** on the shared `H₂³` table, from public values. -/
noncomputable def hviewS23 (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Prop :=
  A.guess (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) (YP A idx b t₀ t₁ n₀ n₁ a)
    (visP23 A idx b t₀ t₁ n₀ n₁ a)

set_option maxRecDepth 8192 in
/-- **With all four proofs simulated on the shared tables, what the guess gets is public**: any
function of the requests, the redemptions and the tables is the same function of `reqS`, `YP`
and `visP23` at the commitments and the nullifiers. -/
theorem simS23_eq {X : Sort*}
    (f : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → X) (b : Bool)
    (x : GTape SecM pIm pIm pRm pRm) :
    f (keyS A idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameS A idx b) true true true true x)).1
        (keyS A idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameS A idx b) true true true true x)).2.1
        (keyS A idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameS A idx b) true true true true x)).2.2
        (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameS A idx b) true true true true x).vis =
      f (reqS (tM A.toM x.1 false) x.2.2.1.1.2) (reqS (tM A.toM x.1 true) x.2.2.2.1.1.2)
        (YP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
        (visP23 A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true)
          x.2) := by
  obtain ⟨s, u, k₁, k₂, k₃, k₄⟩ := x
  have h3 := redStmt_sim A idx b s k₁.1.2 k₂.1.2 false
  have h4 := redStmt_sim A idx b s k₁.1.2 k₂.1.2 true
  have hY := yS_sim A idx b s k₁.1.2 k₂.1.2 k₃.1.2 k₄.1.2
  have hs₃ : ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
      Prod.fst = stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
        (u, k₁, k₂, k₃, k₄) false := by
    rw [σ₃_sim]
    unfold stRP okP
    cases hok : allOkTG A.toM.int idx (reqS (tM A.toM s false) k₁.1.2)
      (reqS (tM A.toM s true) k₂.1.2) (tM A.toM s false) (tM A.toM s true)
    · rfl
    · rw [hok] at h3
      obtain ⟨y, hy, hy1, -⟩ := h3
      simp only [Bool.cond_true, hy, Option.map_some, hy1]
  have hs₄ : ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
      (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
        fun _ => simulate pRm k₃.1.2)).map Prod.fst =
      stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
        (u, k₁, k₂, k₃, k₄) true := by
    rw [σ₄_sim]
    unfold stRP okP
    cases hok : allOkTG A.toM.int idx (reqS (tM A.toM s false) k₁.1.2)
      (reqS (tM A.toM s true) k₂.1.2) (tM A.toM s false) (tM A.toM s true)
    · rfl
    · rw [hok] at h4
      obtain ⟨y, hy, hy1, -⟩ := h4
      simp only [Bool.cond_true, hy, Option.map_some, hy1]
  have hp₃ : (simSB Hashes.shake (pw pIm 343) k₃.1.2 k₃.2.1).pg
      ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) =
      pgP pRm k₃.1.2 (stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false)
        (nOf s true) (u, k₁, k₂, k₃, k₄) false) := by
    have e := simSB_pg_eq (pw pIm 343) k₃.1.2 k₃.2.1
      ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2)))
    rw [hs₃] at e
    exact e
  have hp₄ : (simSB Hashes.shake (pw pIm 343) k₄.1.2 k₄.2.1).pg
      ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
        (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
          fun _ => simulate pRm k₃.1.2)) =
      pgP pRm k₄.1.2 (stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false)
        (nOf s true) (u, k₁, k₂, k₃, k₄) true) := by
    have e := simSB_pg_eq (pw pIm 343) k₄.1.2 k₄.2.1
      ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
        (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
          fun _ => simulate pRm k₃.1.2))
    rw [hs₄] at e
    exact e
  show f (reqS (tM A.toM s false) k₁.1.2) (reqS (tM A.toM s true) k₂.1.2)
      (yM A.toM idx b s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
        (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
          fun _ => simulate pRm k₃.1.2)
        (((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
          (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))).map
            fun _ => simulate pRm k₃.1.2)).map fun _ => simulate pRm k₄.1.2))
      (u, ((k₁.2.1, (simSB Hashes.shake (pw pIm 256) k₁.1.2 k₁.2.1).pg
            (some (issStmt A.toM s false)) u ((simSB Hashes.shake (pw pIm 256) k₂.1.2 k₂.2.1).pg
              (some (issStmt A.toM s true)) u ((simSB Hashes.shake (pw pIm 343) k₃.1.2 k₃.2.1).pg
                ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u
                ((simSB Hashes.shake (pw pIm 343) k₄.1.2 k₄.2.1).pg
                  ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
                    (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2))
                      (some (simulate pIm k₂.1.2))).map fun _ => simulate pRm k₃.1.2)) u
                  k₁.2.2)))),
        (k₂.2.1, (simSB Hashes.shake (pw pIm 256) k₁.1.2 k₁.2.1).pg
            (some (issStmt A.toM s false)) u ((simSB Hashes.shake (pw pIm 256) k₂.1.2 k₂.2.1).pg
              (some (issStmt A.toM s true)) u ((simSB Hashes.shake (pw pIm 343) k₃.1.2 k₃.2.1).pg
                ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u
                ((simSB Hashes.shake (pw pIm 343) k₄.1.2 k₄.2.1).pg
                  ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
                    (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2))
                      (some (simulate pIm k₂.1.2))).map fun _ => simulate pRm k₃.1.2)) u
                  k₁.2.2)))),
        (k₃.2.1, (simSB Hashes.shake (pw pIm 256) k₁.1.2 k₁.2.1).pg
            (some (issStmt A.toM s false)) u ((simSB Hashes.shake (pw pIm 256) k₂.1.2 k₂.2.1).pg
              (some (issStmt A.toM s true)) u ((simSB Hashes.shake (pw pIm 343) k₃.1.2 k₃.2.1).pg
                ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u
                ((simSB Hashes.shake (pw pIm 343) k₄.1.2 k₄.2.1).pg
                  ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
                    (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2))
                      (some (simulate pIm k₂.1.2))).map fun _ => simulate pRm k₃.1.2)) u
                  k₁.2.2)))),
        (k₄.2.1, (simSB Hashes.shake (pw pIm 256) k₁.1.2 k₁.2.1).pg
            (some (issStmt A.toM s false)) u ((simSB Hashes.shake (pw pIm 256) k₂.1.2 k₂.2.1).pg
              (some (issStmt A.toM s true)) u ((simSB Hashes.shake (pw pIm 343) k₃.1.2 k₃.2.1).pg
                ((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))) u
                ((simSB Hashes.shake (pw pIm 343) k₄.1.2 k₄.2.1).pg
                  ((gameS A idx b).σ₄ s (some (simulate pIm k₁.1.2)) (some (simulate pIm k₂.1.2))
                    (((gameS A idx b).σ₃ s (some (simulate pIm k₁.1.2))
                      (some (simulate pIm k₂.1.2))).map fun _ => simulate pRm k₃.1.2)) u
                  k₁.2.2)))))) = _
  rw [hY, hp₃, hp₄]
  rfl

/-- **With all four proofs simulated, the final event is `hviewS23`.** -/
theorem simS23_iff (b : Bool) (x : GTape SecM pIm pIm pRm pRm) :
    evS A idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameS A idx b) true true true true x) ↔
      hviewS23 A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true)
        x.2 :=
  iff_of_eq (simS23_eq A idx A.guess b x)

/-! ## The hiding hop and the ideal world -/

/-- **The reduction to hiding**: the adversary, with the simulators' coins and the raw tables
fixed, run on the commitments and nullifiers it is given. -/
noncomputable def redS23 (b : Bool) (a : AuxS) (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hviewS23 A idx b z.1 z.2.1 z.2.2.1 z.2.2.2 a

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
noncomputable def idealS23 (b : Bool) (x : (HTape × (Coins nfBytes × Coins nfBytes)) × AuxS) :
    Prop :=
  redS23 A idx b x.2 (hideIdeal A.toM.int.ci A.toM.int.cr x.1)

theorem hiding_hopS23 (b : Bool) {εhide : ℝ}
    (hhide : ∀ a, hidingAdv A.toM.int.ci A.toM.int.cr (redS23 A idx b a) ≤ εhide) :
    |hyb23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A idx b) true true true true (evS A idx b) - pr _ (idealS23 A idx b)| ≤ εhide := by
  have e : hyb23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
      (gameS A idx b) true true true true (evS A idx b) =
      pr (GTape SecM pIm pIm pRm pRm) (fun x => hviewS23 A idx b (tM A.toM x.1 false)
        (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true) x.2) :=
    pr_congr (simS23_iff A idx b)
  rw [e]
  exact abs_pr_prod_sub_le' (fun x : HTape × AuxS => redS23 A idx b x.2
    (hideReal A.toM.int.ci A.toM.int.cr x.1)) _ fun a => hhide a

/-- **After the hiding hop the worlds coincide**, tables included. -/
theorem idealS23_eq : pr _ (idealS23 A idx false) = pr _ (idealS23 A idx true) := by
  rw [← pr_equiv swapNS]
  exact pr_congr fun x => Iff.rfl

/-- **Theorem 4(a) on `main` with all tables shared, `PU_b` as `bstar`.** -/
theorem anonymity_main_shared23_0 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b a, hidingAdv A.toM.int.ci A.toM.int.cr (redS23 A idx b a) ≤ εhide) :
    |real23 A idx false - real23 A idx true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puTerm23 A idx false + puTerm23 A idx true) +
        2 * εhide := by
  have r0 := real_sim_shared23 A idx hC false
  have r1 := real_sim_shared23 A idx hC true
  have h0 := hiding_hopS23 A idx false (hhide false)
  have h1 := hiding_hopS23 A idx true (hhide true)
  have e := idealS23_eq A idx
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith


/-! ## The (PU) term on the shared table: explicit predictors and numbers -/

/-- The guess's `H₅` read set with all proofs simulated on the shared `H₂³` table, from public
values. -/
noncomputable def r5P23 (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) (YP A idx b t₀ t₁ n₀ n₁ a)
    (visP23 A idx b t₀ t₁ n₀ n₁ a)

/-- **The public key set** on the shared table: the guess's `H₅` read set and the active gate
inputs of the four simulated proofs. -/
noncomputable def spubP23 (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Finset (ZK.Sim.Bytes 37) :=
  r5P23 A idx b t₀ t₁ n₀ n₁ a ∪
    ((actL Hashes.shake pIm (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2).toFinset.image (blk 37) ∪
      (actL Hashes.shake pIm (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- **The predictor for Client `c`'s opening in world `b`** on the shared table (`predS` with the
public key set `spubP23`). -/
noncomputable def predS23 (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) (c : Bool) :
    Finset (Coins rBytes) :=
  (bif c then candC Hashes.shake (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)
    else candC Hashes.shake (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)) ∪
  (bif b ^^ c then candRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)
    else candRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a))

/-- **At most `2·(q₅ + 1249)` candidates**, if the read set has at most `q₅` keys. -/
theorem card_predS23_le {q5 : ℕ} (h : ∀ q₀ q₁ y v, (A.R5 q₀ q₁ y v).card ≤ q5) (b : Bool)
    (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) (c : Bool) :
    (predS23 A idx b t₀ t₁ n₀ n₁ a c).card ≤ 2 * (q5 + 1249) := by
  have hS : (spubP23 A idx b t₀ t₁ n₀ n₁ a).card ≤ q5 + 1248 := by
    unfold spubP23
    have a₁ := card_img_le _ (actL_length_le Hashes.shake (p := pIm) (stI ⟨t₀, A.toM.int.ci⟩)
      a.1.2 a.2.1.1.2)
    have a₂ := card_img_le _ (actL_length_le Hashes.shake (p := pIm) (stI ⟨t₁, A.toM.int.ci⟩)
      a.1.2 a.2.2.1.1.2)
    have a₃ := card_img_le _ (actRP_length_le (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2
      a.2.2.2.1.1.2)
    have a₄ := card_img_le _ (actRP_length_le (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2
      a.2.2.2.2.1.2)
    have hr : (r5P23 A idx b t₀ t₁ n₀ n₁ a).card ≤ q5 := h _ _ _ _
    generalize r5P23 A idx b t₀ t₁ n₀ n₁ a = R at hr ⊢
    generalize image (blk 37) (actL Hashes.shake pIm (stI ⟨t₀, A.toM.int.ci⟩) a.1.2
      a.2.1.1.2).toFinset = X₁ at a₁ ⊢
    generalize image (blk 37) (actL Hashes.shake pIm (stI ⟨t₁, A.toM.int.ci⟩) a.1.2
      a.2.2.1.1.2).toFinset = X₂ at a₂ ⊢
    generalize image (blk 37) (actRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2
      a.2.2.2.1.1.2).toFinset = X₃ at a₃ ⊢
    generalize image (blk 37) (actRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2
      a.2.2.2.2.1.2).toFinset = X₄ at a₄ ⊢
    have u₀ := card_union_le R (X₁ ∪ X₂ ∪ X₃ ∪ X₄)
    have u₁ := card_union_le (X₁ ∪ X₂ ∪ X₃) X₄
    have u₂ := card_union_le (X₁ ∪ X₂) X₃
    have u₃ := card_union_le X₁ X₂
    omega
  have hI : ∀ (st : Statement) (cc : SimCoins pIm),
      (candC Hashes.shake st a.1.2 cc (spubP23 A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candC_le Hashes.shake mainP_pIm st a.1.2 cc _).trans (by omega)
  have hRd : ∀ (st : Option Statement) (cc : SimCoins pRm),
      (candRP st a.1.2 cc (spubP23 A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    intro st cc
    rcases st with _ | st
    · simp [candRP]
    · exact (card_candC_le Hashes.shake mainP_pRm st a.1.2 cc _).trans (by omega)
  unfold predS23
  refine (card_union_le _ _).trans ?_
  have e₁ : (bif c then candC Hashes.shake (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)
    else candC Hashes.shake (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    cases c
    · exact hI _ _
    · exact hI _ _
  have e₂ : (bif b ^^ c then candRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)
    else candRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2
      (spubP23 A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    cases b ^^ c
    · exact hRd _ _
    · exact hRd _ _
  omega

/-- Client `c`'s opening is among its predictor's candidates (shared table). -/
def winS23 (b c : Bool) (x : GTape SecM pIm pIm pRm pRm) : Prop :=
  rOf x.1 c ∈ predS23 A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false)
    (nOf x.1 true) x.2 c

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **`bstar` with all proofs simulated on the shared table**: a failed simulation, a
prediction, or a collision. -/
theorem puS23_imp (b : Bool) (x : GTape SecM pIm pIm pRm pRm)
    (h : bstar Hashes.shake (gameS A idx b) (r5S A idx b)
      (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A idx b) true true true true x)) :
    (errC pIm x.2.2.1.1.2 ∨ errC pIm x.2.2.2.1.1.2 ∨ errC pRm x.2.2.2.2.1.1.2 ∨
        errC pRm x.2.2.2.2.2.1.2) ∨
      (winS23 A idx b false x ∨ winS23 A idx b true x) ∨
      (coll₂ A x ∨ coll₃ A idx b x ∨ coll₄ A idx b x) := by
  obtain ⟨s, a⟩ := x
  have hR : r5S A idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
      Hashes.shake (gameS A idx b) true true true true (s, a)) =
      r5P23 A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a :=
    simS23_eq A idx A.R5 b (s, a)
  have key := bstar_sim Hashes.shake (gameS A idx b) hashesWF_shake s a.1.2 a.2.1.1.2 a.2.2.1.1.2
    a.2.2.2.1.1.2 a.2.2.2.2.1.2
    (r5P23 A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a)
    (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))
    (((gameS A idx b).σ₃ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))).map
      fun _ => simulate pRm a.2.2.2.1.1.2)
    (((gameS A idx b).σ₄ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))
      (((gameS A idx b).σ₃ s (some (simulate pIm a.2.1.1.2))
        (some (simulate pIm a.2.2.1.1.2))).map fun _ => simulate pRm a.2.2.2.1.1.2)).map
      fun _ => simulate pRm a.2.2.2.2.1.2)
    (qI A s false) (qI A s true) (qR A idx b (s, a) false) (qR A idx b (s, a) true)
    rfl rfl rfl rfl (qOf_iss A s false).symm (qOf_iss A s true).symm (qOf_σ₃ A idx b s a).symm
    (qOf_σ₄ A idx b s a _).symm
    (spubP23 A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a)
    (by
      unfold spubP23
      rw [actO_qR, actO_qR]
      rfl)
    (by
      rw [← hR]
      exact h)
  rcases key with he | hc | hcoll
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (mem_union_left _ hc)
    · exact Or.inr (mem_union_left _ hc)
    · have hin := candO_qR A idx b (s, a) false _ _ _ hc
      have e : (b ^^ false) = b := Bool.xor_false b
      rw [e] at hin
      have hw : winS23 A idx b b (s, a) := by
        unfold winS23 predS23
        refine mem_union_right _ ?_
        rw [Bool.xor_self]
        exact hin
      cases b
      · exact Or.inl hw
      · exact Or.inr hw
    · have hin := candO_qR A idx b (s, a) true _ _ _ hc
      have e : (b ^^ true) = !b := Bool.xor_true b
      rw [e] at hin
      have hw : winS23 A idx b (!b) (s, a) := by
        unfold winS23 predS23
        refine mem_union_right _ ?_
        rw [show (b ^^ !b) = true by cases b <;> rfl]
        exact hin
      cases b
      · exact Or.inr hw
      · exact Or.inl hw
  · exact Or.inr (Or.inr hcoll)

/-- **The predictor for Client `false`** on the shared table, in the game `PU.puAdv`. -/
noncomputable def predS23₀ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxS) : Finset (Coins rBytes) :=
  predS23 A idx b t (comM A.toM a.1.1 a.1.2) (List.ofFn n) (List.ofFn a.1.1) a.2 false

/-- **The predictor for Client `true`** on the shared table. -/
noncomputable def predS23₁ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxS) : Finset (Coins rBytes) :=
  predS23 A idx b (comM A.toM a.1.1 a.1.2) t (List.ofFn a.1.1) (List.ofFn n) a.2 true

theorem pr_winS23_false (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (winS23 A idx b false) =
      puAdv (comM A.toM) (predS23₀ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxS) ≃
      GTape SecM pIm pIm pRm pRm :=
    { toFun := fun z => ((z.1, z.2.1), z.2.2)
      invFun := fun x => (x.1.1, (x.1.2, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winS23_true (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (winS23 A idx b true) =
      puAdv (comM A.toM) (predS23₁ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxS) ≃
      GTape SecM pIm pIm pRm pRm :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-- **The (PU) term on the shared table is at most the advantage of the two explicit
predictors**, plus `4·noHitProb` and `1875·2⁻¹²⁸`. -/
theorem puTerm23_le (b : Bool) :
    puTerm23 A idx b ≤ 4 * noHitProb + puAdv (comM A.toM) (predS23₀ A idx b) +
      puAdv (comM A.toM) (predS23₁ A idx b) + 1875 / 2 ^ 128 := by
  have e : puTerm23 A idx b = pr (GTape SecM pIm pIm pRm pRm) (fun x =>
      bstar Hashes.shake (gameS A idx b) (r5S A idx b)
        (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
          (gameS A idx b) true true true true x)) := rfl
  rw [e]
  have h := (pr_mono (puS23_imp A idx b)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _)))))
    ((pr_or_le _ _).trans (add_le_add (pr_or_le _ _) ((pr_or_le _ _).trans
      (add_le_add le_rfl (pr_or_le _ _)))))))
  rw [pr_winS23_false, pr_winS23_true] at h
  have e₁ := pr_errS₁_le
  have e₂ := pr_errS₂_le
  have e₃ := pr_errS₃_le
  have e₄ := pr_errS₄_le
  have c₂ := pr_coll₂_le A
  have c₃ := pr_coll₃_le A idx b
  have c₄ := pr_coll₄_le A idx b
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) + (((624 : ℕ) + 1 : ℝ) / 2 ^ 128) +
      (((936 : ℕ) + 1 : ℝ) / 2 ^ 128) = 1875 / 2 ^ 128 := by norm_num
  linarith

/-! ## Theorem 4(a) on `main`, all tables shared, with (PU) as a game -/

/-- **Theorem 4(a) on `main` (no label rows) with one `H₂³` table, one `H₅` table and one cipher
for the four proofs, with the (PU) advantage of explicit predictors.** For the colluding
adversary whose guess reads each `H₃` slice at `q3` keys, the cipher at `qE` keys and `H₅` at the
consistent read set `R5` (`AdversaryS.Cons`),

    |Pr[world 0] − Pr[world 1]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
      + 15·(Σ_{b, c} puAdv Com (predS23_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide,

`Δ23 = 2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸ + noHitProb + 3·2⁻¹⁰²⁴` the programming-collision term of
a hop. Each predictor outputs at most `2·(q5 + 1249)` candidates if `R5` has at most `q5` keys
(`card_predS23_le`). -/
theorem anonymity_main_shared23 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b a, hidingAdv A.toM.int.ci A.toM.int.cr (redS23 A idx b a) ≤ εhide) :
    |real23 A idx false - real23 A idx true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comM A.toM) (predS23₀ A idx false) +
        puAdv (comM A.toM) (predS23₁ A idx false) + puAdv (comM A.toM) (predS23₀ A idx true) +
        puAdv (comM A.toM) (predS23₁ A idx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have h := anonymity_main_shared23_0 A idx hC hhide
  have p0 := puTerm23_le A idx false
  have p1 := puTerm23_le A idx true
  linarith

end VoleMole.Privacy.Moussaka
