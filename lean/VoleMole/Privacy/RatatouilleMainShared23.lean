import VoleMole.ZK.MainShared23
import VoleMole.Privacy.RatatouilleMainSharedPU

/-!
# Ratatouille unlinkability on `main`, with one shared `H₂³` table

`unlinkability_main_shared` (`Privacy/RatatouilleMainSharedPU.lean`) is Theorem 2 on `main` with
one `H₅` table and one cipher for the four proofs, each proof keeping its own `H₂³` table. Here
the four proofs also **share the `H₂³` table** (`ZK/MainShared23.lean`), as in the scheme.

## The game (`realSR23`)

The game of `realSR` (`gameSR`, `evSR`, `r5SR`: the same Issuer `AdversarySR`), run with
`ZK.Sim.hyb23`.

## With all proofs simulated

The table the guess sees is the raw table programmed by the four simulations, the first outermost.
Each programming is a function of the statement its request carries (`simVis_iss`, `vis₃_eq`,
`vis₄_eq`, for the `H₂³` part: `pg_of_simVis`), so the table is a function of the requests the
Issuer sees and of the coins (`vtab23`, the shared-table `Vtab`), and the simulated game is
`Ratatouille.reduction` for the Issuer `A.atS23 a` that computes it (`simSR23_iff`). Hiding and
the coincidence of the worlds are as in `Privacy/RatatouilleMainShared.lean`.

## The bound (`unlinkability_main_shared23`)

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(PU23(b₁, b₂) + PU23(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide,

`PU23(b₁, b₂)` the (PU) advantages of the three predictors `predSR23₀`, `predSR23₁`, `predSRC23`
(those of `unlinkability_main_shared` with the guess's read set computed on the shared table).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

attribute [local irreducible] simulate realRO progRO

variable [HasPrg]

/-! ## A simulator's programming of the shared table -/

/-- The programming of a simulation with coins `c` for an optional public statement. -/
noncomputable def pgR (p : Params) (c : SimCoins p) (st : Option Statement) (u : USh)
    (G2 : Tab2G p) : Tab2G p :=
  match st with
  | some st => (progRO p Hashes.shake (withP st p) c ((G2, u) : Sh p)).1
  | none => G2

lemma pgR_simVis (p : Params) (c : SimCoins p) (y : Option SW) (u : USh) (G3 : Tab3)
    (G2 : Tab2G p) : pgR p c (y.map Prod.fst) u G2 = (simVis Hashes.shake p c (G3, G2) y u).2 := by
  rcases y with _ | y <;> rfl

lemma simSB_pgR (p : Params) (c : SimCoins p) (G3 : Tab3) (y : Option SW) :
    (simSB Hashes.shake p c G3).pg y = pgR p c (y.map Prod.fst) := by
  rcases y with _ | y <;> rfl

/-- **A simulator's programming of the shared table is that of any statement with the same
`simVis`.** -/
lemma pg_of_simVis {p : Params} {c : SimCoins p} {y y' : Option SW} {u : USh}
    {st : Option Statement} (G3 : Tab3)
    (h : ∀ V : VP p, simVis Hashes.shake p c V y u = simVis Hashes.shake p c V y' u)
    (hst : y'.map Prod.fst = st) :
    (simSB Hashes.shake p c G3).pg y u = pgR p c st u := by
  funext G2
  rw [simSB_pgR, pgR_simVis p c y u G3 G2, h, ← pgR_simVis p c y' u G3 G2, hst]

variable (A : AdversarySR)

/-! ## The game with one `H₂³` table -/

/-- **The real game on `main` with all tables shared** in world `(b₁, b₂)`. -/
noncomputable def realSR23 (b₁ b₂ : Bool) : ℝ :=
  hyb23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) false false false false (evSR A b₁ b₂)

/-- **The (PU) term of world `(b₁, b₂)`**: `bstar` with all four proofs simulated on the shared
table. -/
noncomputable def puTermSR23 (b₁ b₂ : Bool) : ℝ :=
  hyb23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true
    (bstar Hashes.shake (gameSR A b₁ b₂) (r5SR A b₁ b₂))

/-- **The joint hop in each world**: real against simulated, `15·(εS + Δ23) + 15·PU_b`. -/
theorem real_sim_sharedR23 {q3 qE : ℕ} (hC : A.Cons q3 qE) (b₁ b₂ : Bool) :
    |realSR23 A b₁ b₂ - hyb23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true
        (evSR A b₁ b₂)| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * puTermSR23 A b₁ b₂ :=
  main_shared23_le (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) mainP_pIr mainP_pIr mainP_pSr mainP_pSr
    small_pIr small_pIr small_pSr small_pSr hashesWF_shake (gvalidSR A b₁ b₂) (evSR A b₁ b₂)
    (r5SR A b₁ b₂) (rd_evSR A hC b₁ b₂) (rd_r5SR A hC b₁ b₂)

/-! ## With all proofs simulated: the shared table from the requests -/

/-- **The shared `H₂³` table the guess sees with all proofs simulated**, from what it sees (the
requests), the simulators' coins and the raw table: programmed for the statements of the requests,
the first proof's programming outermost. -/
noncomputable def tab23 (g : GIn) (a : AuxSR) : Tab2G pIr :=
  pgR pIr a.2.1.1.2 (stIq A.toM g.1.1) a.1
    (pgR pIr a.2.2.1.1.2 (stIq A.toM g.1.2) a.1
      (pgR pSr a.2.2.2.1.1.2 (g.2.map fun r => stSq A.toM r.1) a.1
        (pgR pSr a.2.2.2.2.1.2 ((g.2.bind fun r => r.2).map fun r => stSq A.toM r) a.1
          a.2.1.2.2)))

/-- **The tables the guess sees with all proofs simulated on the shared table** (`vtab`). -/
noncomputable def vtab23 (g : GIn) (a : AuxSR) : VisSR :=
  (a.1, ((a.2.1.2.1, tab23 A g a), (a.2.2.1.2.1, tab23 A g a), (a.2.2.2.1.2.1, tab23 A g a),
    (a.2.2.2.2.2.1, tab23 A g a)))

set_option maxRecDepth 8192 in
/-- **With all four proofs simulated on the shared tables, what the guess gets is public**: any
function of the guess's input and the tables is the same function of `gS` and `vtab23`. -/
theorem simSR23_eq {X : Sort*} (f : GIn → VisSR → X) (b₁ b₂ : Bool)
    (x : GTape SecR pIr pIr pSr pSr) :
    f (keyMS A b₁ b₂ (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true x))
        (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true x).vis =
      f (gS A b₁ b₂ x.1 x.2) (vtab23 A (gS A b₁ b₂ x.1 x.2) x.2) := by
  obtain ⟨s, a⟩ := x
  have hg := keyS_pub A b₁ b₂ s a
  have hp₁ : (simSB Hashes.shake (pw pIr 240) a.2.1.1.2 a.2.1.2.1).pg (issStmtR A.toM s.1.1) a.1 =
      pgR pIr a.2.1.1.2 (stIq A.toM (issO A.toM s.1.1 ((issStmtR A.toM s.1.1).map
        fun _ => simulate pIr a.2.1.1.2)).req) a.1 :=
    pg_of_simVis _ (fun V => simVis_iss A.toM s.1.1 a.2.1.1.2 V a.1) (by
      cases stIq A.toM (issO A.toM s.1.1 ((issStmtR A.toM s.1.1).map
        fun _ => simulate pIr a.2.1.1.2)).req <;> rfl)
  have hp₂ : (simSB Hashes.shake (pw pIr 240) a.2.2.1.1.2 a.2.2.1.2.1).pg (issStmtR A.toM s.1.2) a.1 =
      pgR pIr a.2.2.1.1.2 (stIq A.toM (issO A.toM s.1.2 ((issStmtR A.toM s.1.2).map
        fun _ => simulate pIr a.2.2.1.1.2)).req) a.1 :=
    pg_of_simVis _ (fun V => simVis_iss A.toM s.1.2 a.2.2.1.1.2 V a.1) (by
      cases stIq A.toM (issO A.toM s.1.2 ((issStmtR A.toM s.1.2).map
        fun _ => simulate pIr a.2.2.1.1.2)).req <;> rfl)
  have hp₃ : (simSB Hashes.shake (pw pIr 847) a.2.2.2.1.1.2 a.2.2.2.1.2.1).pg
      ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1 =
      pgR pSr a.2.2.2.1.1.2 ((gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
        (oS₄ A b₁ b₂ s a)).2.map fun r => stSq A.toM r.1) a.1 :=
    pg_of_simVis _ (fun V => vis₃_eq A b₁ b₂ s a a.2.2.2.1.1.2 V a.1 rfl) (by
      rw [Option.map_map]; rfl)
  have hp₄ : (simSB Hashes.shake (pw pIr 847) a.2.2.2.2.1.2 a.2.2.2.2.2.1).pg
      ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1 =
      pgR pSr a.2.2.2.2.1.2 (((gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
        (oS₄ A b₁ b₂ s a)).2.bind fun r => r.2).map fun r => stSq A.toM r) a.1 :=
    pg_of_simVis _ (fun V => vis₄_eq A b₁ b₂ s a a.2.2.2.2.1.2 V a.1 rfl) (by
      rw [Option.map_map]; rfl)
  show f (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a))
    (a.1, ((a.2.1.2.1, (simSB Hashes.shake (pw pIr 240) a.2.1.1.2 a.2.1.2.1).pg (issStmtR A.toM s.1.1) a.1
          ((simSB Hashes.shake (pw pIr 240) a.2.2.1.1.2 a.2.2.1.2.1).pg (issStmtR A.toM s.1.2) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.1.1.2 a.2.2.2.1.2.1).pg ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.2.1.2 a.2.2.2.2.2.1).pg
            ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1 a.2.1.2.2)))),
      (a.2.2.1.2.1, (simSB Hashes.shake (pw pIr 240) a.2.1.1.2 a.2.1.2.1).pg (issStmtR A.toM s.1.1) a.1
          ((simSB Hashes.shake (pw pIr 240) a.2.2.1.1.2 a.2.2.1.2.1).pg (issStmtR A.toM s.1.2) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.1.1.2 a.2.2.2.1.2.1).pg ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.2.1.2 a.2.2.2.2.2.1).pg
            ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1 a.2.1.2.2)))),
      (a.2.2.2.1.2.1, (simSB Hashes.shake (pw pIr 240) a.2.1.1.2 a.2.1.2.1).pg (issStmtR A.toM s.1.1) a.1
          ((simSB Hashes.shake (pw pIr 240) a.2.2.1.1.2 a.2.2.1.2.1).pg (issStmtR A.toM s.1.2) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.1.1.2 a.2.2.2.1.2.1).pg ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.2.1.2 a.2.2.2.2.2.1).pg
            ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1 a.2.1.2.2)))),
      (a.2.2.2.2.2.1, (simSB Hashes.shake (pw pIr 240) a.2.1.1.2 a.2.1.2.1).pg (issStmtR A.toM s.1.1) a.1
          ((simSB Hashes.shake (pw pIr 240) a.2.2.1.1.2 a.2.2.1.2.1).pg (issStmtR A.toM s.1.2) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.1.1.2 a.2.2.2.1.2.1).pg ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1
          ((simSB Hashes.shake (pw pIr 847) a.2.2.2.2.1.2 a.2.2.2.2.2.1).pg
            ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1 a.2.1.2.2)))))) = _
  rw [hp₁, hp₂, hp₃, hp₄]
  have e₁ : (issO A.toM s.1.1 ((issStmtR A.toM s.1.1).map fun _ => simulate pIr a.2.1.1.2)).req =
      (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)).1.1 := rfl
  have e₂ : (issO A.toM s.1.2 ((issStmtR A.toM s.1.2).map
      fun _ => simulate pIr a.2.2.1.1.2)).req =
      (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)).1.2 := rfl
  rw [e₁, e₂, hg]
  rfl

/-! ## The hiding hop and the ideal world -/

/-- **The Issuer that computes the programmed shared table from what it sees**, the simulators'
coins and the raw tables fixed. -/
noncomputable def AdversarySR.atS23 (a : AuxSR) : Adversary Sizes.main :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂,
    fun tr y => A.guess (tr, y) (vtab23 A (tr, y) a)⟩

/-- **The reduction to hiding** on the shared table. -/
noncomputable def redSR23 (b₁ b₂ : Bool) (a : AuxSR) :
    Quad Nullifier → Quad (Credits → Commitment) → Prop :=
  reduction (A.atS23 a) simIR simSR b₁ b₂ (coSR a)

/-- The game after the hiding hop: uniform commitments. -/
noncomputable def idealSR23 (b₁ b₂ : Bool) (y : UTape × AuxSR) : Prop :=
  redSR23 A b₁ b₂ y.2 (hideIdeal y.1).1 (hideIdeal y.1).2

lemma redSR23_iff (b₁ b₂ : Bool) (a : AuxSR) (n : Quad Nullifier)
    (cf : Quad (Credits → Commitment)) :
    redSR23 A b₁ b₂ a n cf ↔
      A.guess (gP A.toM b₁ b₂ n (cf.1.1 A.tInit, cf.1.2 A.tInit) cf.2.1 cf.2.2 (coSR a))
        (vtab23 A (gP A.toM b₁ b₂ n (cf.1.1 A.tInit, cf.1.2 A.tInit) cf.2.1 cf.2.2 (coSR a)) a) :=
  Iff.rfl

lemma redSR23_real (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) :
    redSR23 A b₁ b₂ a (hideReal A.ctx s).1 (hideReal A.ctx s).2 ↔
      A.guess (gS A b₁ b₂ s a) (vtab23 A (gS A b₁ b₂ s a) a) := by
  have e₁ : (hideReal A.ctx s).1 = nS s := rfl
  have e₂ : ((hideReal A.ctx s).2.1.1 A.tInit, (hideReal A.ctx s).2.1.2 A.tInit) =
      tS A.toM s := rfl
  have e₃ : (hideReal A.ctx s).2.2.1 = cfS A.toM s.2.1 := rfl
  have e₄ : (hideReal A.ctx s).2.2.2 = cfS A.toM s.2.2 := rfl
  rw [redSR23_iff, e₁, e₂, e₃, e₄]
  rfl

theorem simSR23_iff (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr) :
    evSR A b₁ b₂ (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true x) ↔
      redSR23 A b₁ b₂ x.2 (hideReal A.ctx x.1).1 (hideReal A.ctx x.1).2 :=
  (iff_of_eq (simSR23_eq A A.guess b₁ b₂ x)).trans (redSR23_real A b₁ b₂ x.1 x.2).symm

theorem hiding_hopSR23 (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ a, hidingAdv A.ctx (redSR23 A b₁ b₂ a) ≤ εhide) :
    |hyb23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true (evSR A b₁ b₂) -
      pr _ (idealSR23 A b₁ b₂)| ≤ εhide := by
  have e : hyb23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true (evSR A b₁ b₂) =
      pr (GTape SecR pIr pIr pSr pSr) (fun x => redSR23 A b₁ b₂ x.2 (hideReal A.ctx x.1).1
        (hideReal A.ctx x.1).2) :=
    pr_congr (simSR23_iff A b₁ b₂)
  rw [e]
  exact abs_pr_prod_sub_le' (fun x : HTape × AuxSR => redSR23 A b₁ b₂ x.2
    (hideReal A.ctx x.1).1 (hideReal A.ctx x.1).2) _ fun a => hhide a

/-- **After the hiding hop the four worlds coincide**, tables included. -/
theorem idealSR23_eq (b₁ b₂ : Bool) :
    pr _ (idealSR23 A b₁ b₂) = pr _ (idealSR23 A false false) := by
  have h := abs_pr_prod_sub_le' (fun y : UTape × AuxSR => idealSR23 A b₁ b₂ y)
    (fun y : UTape × AuxSR => idealSR23 A false false y) (ε := 0)
    fun a => by
      rw [show pr UTape (fun u => idealSR23 A b₁ b₂ (u, a)) =
        pr UTape (fun u => idealSR23 A false false (u, a)) from
          ideal_eq_at (A.atS23 a) simIR simSR (coSR a) b₁ b₂, sub_self, abs_zero]
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-- **Theorem 2 on `main` with all tables shared, `PU` as `bstar`.** -/
theorem unlinkability_main_shared23_0 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b₁ b₂ a, hidingAdv A.ctx (redSR23 A b₁ b₂ a) ≤ εhide) (b₁ b₂ b₁' b₂' : Bool) :
    |realSR23 A b₁ b₂ - realSR23 A b₁' b₂'| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puTermSR23 A b₁ b₂ + puTermSR23 A b₁' b₂') +
        2 * εhide := by
  have r0 := real_sim_sharedR23 A hC b₁ b₂
  have r1 := real_sim_sharedR23 A hC b₁' b₂'
  have h0 := hiding_hopSR23 A b₁ b₂ (hhide b₁ b₂)
  have h1 := hiding_hopSR23 A b₁' b₂' (hhide b₁' b₂')
  have e0 := idealSR23_eq A b₁ b₂
  have e1 := idealSR23_eq A b₁' b₂'
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## The (PU) term on the shared table -/

/-! ## The public key set and the predictors -/

section Pred

variable (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
  (cf₂ cf₃ : Credits → Commitment) (a : AuxSR)

/-- The guess's `H₅` read set with all proofs simulated, from public values. -/
noncomputable def r5R23 : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (gP A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) (vtab23 A (gP A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a)

/-- **The public key set**: the guess's `H₅` read set and the active gate inputs of the four
simulated proofs. -/
noncomputable def spubR23 : Finset (ZK.Sim.Bytes 37) :=
  r5R23 A b₁ b₂ n t cf₂ cf₃ a ∪
    ((actLo (stIP A.toM t.1) a.1.2 a.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- **The predictor for the opening of Client `c`'s issued token**: the candidates, for the public
key set, of its issuance proof, of round 1's spend proof if `c = b₁`, and of round 2's spend proof
if Client `c = !b₁` spends there (`b₂ ≠ b₁`). -/
noncomputable def predIS23 (c : Bool) : Finset (Coins 16) :=
  (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 (spubR23 A b₁ b₂ n t cf₂ cf₃ a)
    else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 (spubR23 A b₁ b₂ n t cf₂ cf₃ a)) ∪
    ((bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2
        (spubR23 A b₁ b₂ n t cf₂ cf₃ a) else ∅) ∪
      (bif (b₂ != b₁) && (c != b₁) then
        candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
          (spubR23 A b₁ b₂ n t cf₂ cf₃ a) else ∅))

/-- **The predictor for the opening of round 1's change token**: the candidates of round 2's spend
proof, if the change token is spent there (`b₂ = b₁`). -/
noncomputable def predCS23 : Finset (Coins 16) :=
  bif b₂ == b₁ then candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
    (spubR23 A b₁ b₂ n t cf₂ cf₃ a) else ∅

/-- The predictor of the change token reads `cf₂` at the credit `cr₁P` only. -/
lemma predCS23_const :
    predCS23 A b₁ b₂ n t cf₂ cf₃ a =
      predCS23 A b₁ b₂ n t (fun _ => cf₂ (cr₁P A.toM b₁ n.1 t (coSR a).1)) cf₃ a := by
  unfold predCS23 spubR23 r5R23
  rw [gP_const A.toM b₁ b₂ n t cf₂ cf₃ (coSR a), st₃P_const A.toM b₁ n t cf₂ (coSR a),
    st₄P_const A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)]

variable {q5 : ℕ} (h : ∀ g v, (A.R5 g v).card ≤ q5)
include h

lemma card_spubR23_le : (spubR23 A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 + 1248 := by
  unfold spubR23
  have a₁ := card_imgo_le (p := pIr) (stIP A.toM t.1) a.1.2 a.2.1.1.2
  have a₂ := card_imgo_le (p := pIr) (stIP A.toM t.2) a.1.2 a.2.2.1.1.2
  have a₃ := card_imgo_le (p := pSr) (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2
  have a₄ := card_imgo_le (p := pSr) (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
  have hr : (r5R23 A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 := h _ _
  generalize r5R23 A b₁ b₂ n t cf₂ cf₃ a = R at hr ⊢
  generalize image (blk 37) (actLo (stIP A.toM t.1) a.1.2 a.2.1.1.2).toFinset = X₁ at a₁ ⊢
  generalize image (blk 37) (actLo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2).toFinset = X₂ at a₂ ⊢
  generalize image (blk 37) (actLo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2
    a.2.2.2.1.1.2).toFinset = X₃ at a₃ ⊢
  generalize image (blk 37) (actLo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2
    a.2.2.2.2.1.2).toFinset = X₄ at a₄ ⊢
  have u₀ := card_union_le R (X₁ ∪ X₂ ∪ X₃ ∪ X₄)
  have u₁ := card_union_le (X₁ ∪ X₂ ∪ X₃) X₄
  have u₂ := card_union_le (X₁ ∪ X₂) X₃
  have u₃ := card_union_le X₁ X₂
  omega

/-- **At most `3·(q₅ + 1249)` candidates**, if the read set has at most `q₅` keys. -/
theorem card_predIS23_le (c : Bool) : (predIS23 A b₁ b₂ n t cf₂ cf₃ a c).card ≤ 3 * (q5 + 1249) := by
  have hS := card_spubR23_le A b₁ b₂ n t cf₂ cf₃ a h
  have hI : ∀ (st : Option Statement) (cc : SimCoins pIr),
      (candCo st a.1.2 cc (spubR23 A b₁ b₂ n t cf₂ cf₃ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candCo_le mainP_pIr st a.1.2 cc _).trans (by omega)
  have hSp : ∀ (st : Option Statement) (cc : SimCoins pSr),
      (candCo st a.1.2 cc (spubR23 A b₁ b₂ n t cf₂ cf₃ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candCo_le mainP_pSr st a.1.2 cc _).trans (by omega)
  unfold predIS23
  generalize spubR23 A b₁ b₂ n t cf₂ cf₃ a = Sp at hI hSp ⊢
  have e₁ : (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 Sp
      else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 Sp).card ≤ q5 + 1249 := by
    cases c
    · exact hI _ _
    · exact hI _ _
  have e₂ : (bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp
      else ∅).card ≤ q5 + 1249 := by
    cases b₁ == c
    · exact Nat.zero_le _
    · exact hSp _ _
  have e₃ : (bif (b₂ != b₁) && (c != b₁) then
      candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅).card ≤
      q5 + 1249 := by
    cases (b₂ != b₁) && (c != b₁)
    · exact Nat.zero_le _
    · exact hSp _ _
  have u₁ := card_union_le (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 Sp
      else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 Sp)
    ((bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp else ∅) ∪
      (bif (b₂ != b₁) && (c != b₁) then
        candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅))
  have u₂ := card_union_le
    (bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp else ∅)
    (bif (b₂ != b₁) && (c != b₁) then
      candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅)
  omega

/-- **At most `q₅ + 1249` candidates.** -/
theorem card_predCS23_le : (predCS23 A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 + 1249 := by
  have hS := card_spubR23_le A b₁ b₂ n t cf₂ cf₃ a h
  unfold predCS23
  cases b₂ == b₁
  · exact Nat.zero_le _
  · exact (card_candCo_le mainP_pSr _ a.1.2 _ _).trans (by omega)

end Pred

/-! ## The events -/

/-- The opening of Client `c`'s issued token is among its predictor's candidates. -/
def winIS23 (b₁ b₂ c : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  rIss x.1 c ∈ predIS23 A b₁ b₂ (nS x.1) (tS A.toM x.1) (cfS A.toM x.1.2.1) (cfS A.toM x.1.2.2)
    x.2 c

/-- The opening of round 1's change token is among its predictor's candidates, the commitment
taken at the credit `cr₁P`. -/
def winCS23 (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  x.1.2.1.2 ∈ predCS23 A b₁ b₂ (nS x.1) (tS A.toM x.1)
    (fun _ => cfS A.toM x.1.2.1 (cr₁P A.toM b₁ (nS x.1).1 (tS A.toM x.1) (coSR x.2).1))
    (cfS A.toM x.1.2.2) x.2

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **`bstar` with all proofs simulated**: a failed simulation, a prediction, or a collision. -/
theorem puSR23_imp (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr)
    (h : bstar Hashes.shake (gameSR A b₁ b₂) (r5SR A b₁ b₂)
      (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true x)) :
    (errC pIr x.2.2.1.1.2 ∨ errC pIr x.2.2.2.1.1.2 ∨ errC pSr x.2.2.2.2.1.1.2 ∨
        errC pSr x.2.2.2.2.2.1.2) ∨
      (winIS23 A b₁ b₂ false x ∨ winIS23 A b₁ b₂ true x ∨ winCS23 A b₁ b₂ x) ∨
      (collR₂ A x ∨ collR₃ A b₁ x ∨ collR₄ A b₁ b₂ x) := by
  obtain ⟨s, a⟩ := x
  have hR : r5SR A b₁ b₂ (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true (s, a)) =
      r5R23 A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a :=
    simSR23_eq A A.R5 b₁ b₂ (s, a)
  have key := bstar_sim Hashes.shake (gameSR A b₁ b₂) hashesWF_shake s a.1.2 a.2.1.1.2 a.2.2.1.1.2
    a.2.2.2.1.1.2 a.2.2.2.2.1.2
    (r5R23 A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a)
    (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)
    (qS₁ A s) (qS₂ A s) (qS₃ A b₁ s a) (qS₄ A b₁ b₂ s a)
    rfl rfl rfl rfl (qOf_σ₁R A s).symm (qOf_σ₂R A s).symm (qOf_σ₃R A b₁ b₂ s a).symm
    (qOf_σ₄R A b₁ b₂ s a).symm
    (spubR23 A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a)
    (by
      unfold spubR23 qS₁ qS₂ qS₃ qS₄
      rw [actO_qo, actO_qo, actO_qo, actO_qo])
    (by
      rw [← hR]
      exact h)
  rcases key with he | hc | hcoll
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (mem_union_left _ (candO_qo _ _ _ _ _ hc))
    · exact Or.inr (Or.inl (mem_union_left _ (candO_qo _ _ _ _ _ hc)))
    · have hin := candO_qo _ _ _ _ _ hc
      have hw : winIS23 A b₁ b₂ b₁ (s, a) := by
        unfold winIS23 predIS23
        refine mem_union_right _ (mem_union_left _ ?_)
        rw [beq_self_eq_true]
        exact hin
      cases b₁
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
    · have hin := candO_qo _ _ _ _ _ hc
      cases hb : b₂ == b₁
      · rw [hb] at hin
        have hw : winIS23 A b₁ b₂ (!b₁) (s, a) := by
          unfold winIS23 predIS23
          refine mem_union_right _ (mem_union_right _ ?_)
          have e : ((b₂ != b₁) && ((!b₁) != b₁)) = true := by
            cases b₁ <;> cases b₂ <;> simp_all
          rw [e]
          exact hin
        cases b₁
        · exact Or.inr (Or.inl hw)
        · exact Or.inl hw
      · rw [hb] at hin
        refine Or.inr (Or.inr ?_)
        unfold winCS23
        rw [← predCS23_const]
        unfold predCS23
        rw [hb]
        exact hin
  · exact Or.inr (Or.inr hcoll)


/-! ## The predictors in the game `PU.puAdv` -/

/-- **The predictor for the opening of Client `false`'s issued token** in the game `PU.puAdv`:
public part `nf₀`, commitment `t₀ = Com(nf₀, ctx, T_init, r₀)`; auxiliary coins the other three
tokens' `(nf, r)`, the simulators' coins and the raw tables. -/
noncomputable def predSR23₀ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) :
    Finset (Coins 16) :=
  predIS23 A b₁ b₂ ((vec n, vec a.1.1.1), (vec a.1.2.1.1, vec a.1.2.2.1))
    (t, comI A.toM a.1.1.1 a.1.1.2) (cfS A.toM a.1.2.1) (cfS A.toM a.1.2.2) a.2 false

/-- **The predictor for the opening of Client `true`'s issued token.** -/
noncomputable def predSR23₁ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) :
    Finset (Coins 16) :=
  predIS23 A b₁ b₂ ((vec a.1.1.1, vec n), (vec a.1.2.1.1, vec a.1.2.2.1))
    (comI A.toM a.1.1.1 a.1.1.2, t) (cfS A.toM a.1.2.1) (cfS A.toM a.1.2.2) a.2 true

/-- **The predictor for the opening of round 1's change token** on the shared table, in the game
`PU.puAdv` for `comCh` (`predSRC` with the shared table). -/
noncomputable def predSRC23 (b₁ b₂ : Bool) (n : Coins 24 × BCh) (t : Commitment)
    (a : (Coins 24 × Coins 16) × AuxCS) : Finset (Coins 16) :=
  predCS23 A b₁ b₂ ((vec n.2.1.1.1, vec n.2.1.2.1), (vec n.1, vec a.1.1))
    (comI A.toM n.2.1.1.1 n.2.1.1.2, comI A.toM n.2.1.2.1 n.2.1.2.2) (fun _ => t) (cfS A.toM a.1)
    (auxOfS n.2.2 a.2)

theorem pr_winIS23_false (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winIS23 A b₁ b₂ false) =
      puAdv (comI A.toM) (predSR23₀ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winIS23_true (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winIS23 A b₁ b₂ true) =
      puAdv (comI A.toM) (predSR23₁ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => (((z.2.1.1, z.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.2, ((x.1.1.1, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winCS23 (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winCS23 A b₁ b₂) =
      puAdv (comCh A.toM b₁) (predSRC23 A b₁ b₂) := by
  let e : ((Coins 24 × BCh) × Coins 16) × ((Coins 24 × Coins 16) × AuxCS) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => ((z.1.1.2.1, ((z.1.1.1, z.1.2), z.2.1)), auxOfS z.1.1.2.2 z.2.2)
      invFun := fun x => (((x.1.2.1.1, (x.1.1, (x.2.2.1.1.2, x.2.2.2.1.1.2))), x.1.2.1.2),
        (x.1.2.2, (x.2.1, ((x.2.2.1.1.1, x.2.2.1.2), (x.2.2.2.1.1.1, x.2.2.2.1.2)),
          x.2.2.2.2.1, x.2.2.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-- **The (PU) term with shared tables is at most the advantage of the three explicit
predictors**, plus `4·noHitProb` (failed simulations) and `1875·2⁻¹²⁸` (collisions between
simulated proofs). -/
theorem puTermSR23_le (b₁ b₂ : Bool) :
    puTermSR23 A b₁ b₂ ≤ 4 * noHitProb + puAdv (comI A.toM) (predSR23₀ A b₁ b₂) +
      puAdv (comI A.toM) (predSR23₁ A b₁ b₂) + puAdv (comCh A.toM b₁) (predSRC23 A b₁ b₂) +
      1875 / 2 ^ 128 := by
  have e : puTermSR23 A b₁ b₂ = pr (GTape SecR pIr pIr pSr pSr) (fun x =>
      bstar Hashes.shake (gameSR A b₁ b₂) (r5SR A b₁ b₂)
        (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A b₁ b₂) true true true true x)) := rfl
  rw [e]
  have h := (pr_mono (puSR23_imp A b₁ b₂)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _)))))
    ((pr_or_le _ _).trans (add_le_add
      ((pr_or_le _ _).trans (add_le_add le_rfl (pr_or_le _ _)))
      ((pr_or_le _ _).trans (add_le_add le_rfl (pr_or_le _ _)))))))
  rw [pr_winIS23_false, pr_winIS23_true, pr_winCS23] at h
  have e₁ := pr_errSR₁_le
  have e₂ := pr_errSR₂_le
  have e₃ := pr_errSR₃_le
  have e₄ := pr_errSR₄_le
  have c₂ := pr_collR₂_le A
  have c₃ := pr_collR₃_le A b₁
  have c₄ := pr_collR₄_le A b₁ b₂
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) + (((624 : ℕ) + 1 : ℝ) / 2 ^ 128) +
      (((936 : ℕ) + 1 : ℝ) / 2 ^ 128) = 1875 / 2 ^ 128 := by norm_num
  linarith

/-! ## Theorem 2 on `main`, shared tables, with (PU) as a game -/

/-- **Theorem 2 on `main` (no label rows) with one `H₅` table and one cipher for the four proofs,
with the (PU) advantage of explicit predictors.** For the malicious Issuer whose guess reads each
`H₃` slice at `q3` keys, the cipher at `qE` keys and `H₅` at the consistent read set `R5`
(`AdversarySR.Cons`), any two worlds of the real game differ by at most

    30·εS(q3, qE + 8·4607) + 15·(PU(b₁, b₂) + PU(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide,

`PU(b₁, b₂) = puAdv comI (predSR23₀ b₁ b₂) + puAdv comI (predSR23₁ b₁ b₂) + puAdv (comCh b₁)
(predSRC23 b₁ b₂)`. The six `puAdv` terms are (PU), an assumption on Keccak-p[800,12], and `εhide`
is hiding of `Com`; every other term is a number (`noHitProb ≤ 2^{−2¹⁵}`). The predictors output
at most `3·(q5 + 1249)` (issued tokens) and `q5 + 1249` (change token) candidates if `R5` has at
most `q5` keys (`card_predIS23_le`, `card_predCS23_le`). -/
theorem unlinkability_main_shared23 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b₁ b₂ a, hidingAdv A.ctx (redSR23 A b₁ b₂ a) ≤ εhide) (b₁ b₂ b₁' b₂' : Bool) :
    |realSR23 A b₁ b₂ - realSR23 A b₁' b₂'| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comI A.toM) (predSR23₀ A b₁ b₂) +
        puAdv (comI A.toM) (predSR23₁ A b₁ b₂) + puAdv (comCh A.toM b₁) (predSRC23 A b₁ b₂) +
        (puAdv (comI A.toM) (predSR23₀ A b₁' b₂') + puAdv (comI A.toM) (predSR23₁ A b₁' b₂') +
        puAdv (comCh A.toM b₁') (predSRC23 A b₁' b₂')) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have h := unlinkability_main_shared23_0 A hC hhide b₁ b₂ b₁' b₂'
  have p0 := puTermSR23_le A b₁ b₂
  have p1 := puTermSR23_le A b₁' b₂'
  linarith


end VoleMole.Privacy.Ratatouille
