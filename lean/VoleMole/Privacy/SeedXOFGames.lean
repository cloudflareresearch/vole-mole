import VoleMole.Privacy.SeedXOF
import VoleMole.Privacy.SharedH3RA
import VoleMole.Privacy.SharedH3PomFRITRA
import VoleMole.Privacy.PermRO
import VoleMole.Prob.Bytes

/-!
# The privacy games with the seed XOF

The privacy games of `Privacy/` draw each honest request's randomness uniformly. In the scheme, it
is the output of a SHAKE128 XOF at a fresh 32-byte OS seed. Here the games get the real Clients:
each request draws a uniform seed and reads its randomness off a uniform **XOF table** (the seed
XOF as a random oracle), and the adversary reads the table too (`Privacy/SeedXOF.lean`, `RdX`).
Each privacy theorem then holds for the game with the seeds, at the extra cost of the seed-XOF hop
in each world.

## The XOF tables

* **PomFRIT** (`XofP Ctx = Coins 32 → Ctx → XOut`): `(ρ, refresher, r) =
  XOF_seed(DST ‖ seed ‖ dig(pk) ‖ msg)` (`Spec.PomFRIT.expandSeed`, `pomfrit.cpp:150-161`). The
  table's cell at a seed is the column of the XOF's answers at every context `dig(pk) ‖ msg`,
  encoded in a finite context type `Ctx` by `enc : Bytes → Ctx` (e.g. the byte strings up to a
  length bound, with `enc` the inclusion: then the table is the XOF on every input of that length).
  Session `i` reads its seed's column at its context, `dig(pk) ‖ µ_b` or `dig(pk) ‖ µ_{¬b}`
  (`ctxK`), chosen by the Issuer.
* **Moussaka** (`XofM = Bool × Coins 32 → NR × Coins 16`): `nf ‖ r ‖ ρ_iss =
  SHAKE128(ISSUE_SEED_DST ‖ seed)` and `ρ_red = SHAKE128(REDEEM_SEED_DST ‖ seed')`
  (`Spec.Moussaka.expandIssueSeed`, `expandRedeemSeed`): one table keyed by `(domain, seed)`
  (`false` the issue DST, `true` the redeem DST; the redemption reads `16` of the cell's bytes).
  Seeds `(false, j)`: Client `j`'s issuance; `(true, side)`: the redemption on `side`.
* **Ratatouille** (`XofR = Bool × Coins 32 → NRR × Coins 16`): `(nf, r, ρ) =
  SHAKE128(DST ‖ seed)` with the issue and the spend DSTs (`Spec.Ratatouille.expandSeed`).
  Seeds `(false, j)`: issuance `j`; `(true, k)`: spend `k`.

That the seed XOFs are independent of the proof system's oracles is Lemma DS
(`docs/security/domain-separation.md` §7, `ROM/DomainSep.lean`); for PomFRIT's seed XOF, whose
domain overlaps proof-system domains (finding F-DS2), part (c), on paper (the proposed `APP_TAG`
fix makes it part (a)).

## The adversary

The adversary at XOF table `g` is `A g` (an adversary of the existing game: its interaction and its
guess may depend on the table). Its budget: its whole run in the game, at every fixed tape, reads
at most `q_g` cells of the table (`hg`); for PomFRIT, its key and messages (which fix the
sessions' contexts) read at most `q_k` cells (`hk`). Every hypothesis of the existing theorem is
required of `A g` for every `g`.

## The bounds (per world, then twice in the left/right difference)

* PomFRIT: `(2·(q_k + q_g) + 1)·2⁻²⁵⁶`: a cell read hits one of the two seeds, `2q·2⁻²⁵⁶`; the two
  seeds collide, `2⁻²⁵⁶`.
* Moussaka, Ratatouille: `(2·q_g + 2)·2⁻²⁵⁶`: a cell read lies in one domain, where it can hit one
  of two seeds; a collision within a domain, `2·2⁻²⁵⁶`.

The corollaries keep the existing statements and add `2·(hop)`: `*_seed`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy

/-- **32-byte OS seeds.** -/
abbrev SeedB := Coins 32

lemma card_seedB : (Fintype.card SeedB : ℝ) = 2 ^ 256 := by
  rw [show Fintype.card SeedB = 2 ^ (8 * 32) from Prob.card_bytes 32]
  push_cast
  norm_num

namespace PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

/-! ## The seed-XOF table and the tape -/

/-- **A session's XOF output** `(ρ, refresher, r)`. -/
abbrev XOut := Coins proveSeedBytes × Coins refresherBytes × Coins uovM

/-- **The seed-XOF table**: at each seed, the XOF's answer at every context. -/
abbrev XofP (Ctx : Type) := SeedB → Ctx → XOut

variable {Ctx Y : Type} [Fintype Ctx] [DecidableEq Ctx] [Fintype Y] [Nonempty Y]

/-- **The game's tape from the sessions' columns**: session `0` reads its column at its context
`k.1`, session `1` at `k.2`; the slices and the shared tables are the rest `t`. -/
def insP (k : Ctx × Ctx) (u : Bool → Ctx → XOut) (t : SlP × Y) : (XR × XR) × Y :=
  (((u false k.1, t.1.1), (u true k.2, t.1.2)), t.2)

/-- Uniform columns at any contexts (chosen from the rest of the tape) give the uniform tape. -/
theorem hinsP (k : SlP × Y → Ctx × Ctx) (P : (XR × XR) × Y → Prop) :
    pr ((Bool → Ctx → XOut) × (SlP × Y)) (fun z => P (insP (k z.2) z.1 z.2)) =
      pr ((XR × XR) × Y) P := by
  let e : (SlP × Y) × (Bool → XOut) ≃ (XR × XR) × Y :=
    { toFun := fun w => (((w.2 false, w.1.1.1), (w.2 true, w.1.1.2)), w.1.2)
      invFun := fun z => (((z.1.1.2, z.1.2.2), z.2), fun b => bif b then z.1.2.1 else z.1.1.1)
      left_inv := fun w => by
        refine Prod.ext rfl (funext fun b => ?_)
        cases b <;> rfl
      right_inv := fun _ => rfl }
  calc pr ((Bool → Ctx → XOut) × (SlP × Y)) (fun z => P (insP (k z.2) z.1 z.2))
      = pr ((SlP × Y) × (Bool → Ctx → XOut)) (fun z => P (insP (k z.1) z.2 z.1)) :=
        (pr_equiv (Equiv.prodComm (SlP × Y) (Bool → Ctx → XOut)) _).symm
    _ = (∑ t, pr (Bool → Ctx → XOut) (fun u => P (insP (k t) u t))) /
          Fintype.card (SlP × Y) :=
        pr_prod (fun z : (SlP × Y) × (Bool → Ctx → XOut) => P (insP (k z.1) z.2 z.1))
    _ = (∑ t, pr (Bool → XOut) (fun c => P (e (t, c)))) / Fintype.card (SlP × Y) := by
        refine congrArg (· / (Fintype.card (SlP × Y) : ℝ)) (Finset.sum_congr rfl fun t _ => ?_)
        exact pr_cols (fun b => bif b then (k t).2 else (k t).1) (fun c => P (e (t, c)))
    _ = pr ((SlP × Y) × (Bool → XOut)) (fun w => P (e w)) :=
        (pr_prod (fun w : (SlP × Y) × (Bool → XOut) => P (e w))).symm
    _ = pr ((XR × XR) × Y) P := pr_equiv e P

/-- **The sessions' contexts in world `b`** from the Issuer's key and messages `(pk, µ₀, µ₁)`:
`dig(pk) ‖ µ_b` and `dig(pk) ‖ µ_{¬b}`, encoded. -/
def ctxK (enc : Bytes → Ctx) (k : UOVKey × Bytes × Bytes) (b : Bool) : Ctx × Ctx :=
  (enc (k.1.digest ++ bif b then k.2.2 else k.2.1), enc (k.1.digest ++ bif b then k.2.1 else k.2.2))

/-- **The game with the seeds**: seeds `c`, the slices and shared tables `t`, the XOF table `g`;
session `i` gets `g (c i)` at its context. -/
def seedGameP (G : XofP Ctx → Bool → (XR × XR) × Y → Prop)
    (cx : XofP Ctx → Bool → SlP × Y → Ctx × Ctx) (b : Bool) :
    (Bool → SeedB) × ((SlP × Y) × XofP Ctx) → Prop :=
  seedGame (fun g => G g b) (fun g => cx g b) insP (fun c => c)

/-- **The seed-XOF hop for PomFRIT**: if the game is `ε`-close in its worlds at every XOF table,
the game with the seeds is `ε + 2·(2(q_k + q_g) + 1)·2⁻²⁵⁶`-close. -/
theorem abs_seedGameP_sub_le (G : XofP Ctx → Bool → (XR × XR) × Y → Prop)
    (cx : XofP Ctx → Bool → SlP × Y → Ctx × Ctx) {qk qg : ℕ}
    (hk : ∀ b t, RdX (fun g => cx g b t) qk) (hg : ∀ b ω, RdX (fun g => G g b ω) qg) {ε : ℝ}
    (hε : ∀ g, |pr ((XR × XR) × Y) (G g false) - pr ((XR × XR) × Y) (G g true)| ≤ ε) :
    |pr _ (seedGameP G cx false) - pr _ (seedGameP G cx true)| ≤
      ε + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) := by
  have h := abs_pr_seedGame_sub_le G cx insP hinsP (fun c : Bool → SeedB => c) hk hg
    (δ := 2 * ((qk + qg : ℕ) : ℝ) / Fintype.card SeedB)
    (fun F hF => pr_bool_exists_mem_le F hF) false true hε
  have hc := pr_bool_not_injective_le (S := SeedB)
  rw [card_seedB] at h hc
  unfold seedGameP
  refine h.trans ?_
  have e : ((2 * (qk + qg) + 1 : ℕ) : ℝ) / 2 ^ 256 =
      1 / 2 ^ 256 + 2 * ((qk + qg : ℕ) : ℝ) / 2 ^ 256 := by
    push_cast
    ring
  rw [e]
  have : pr (Bool → SeedB) (fun c => ¬ Function.Injective ((fun c : Bool → SeedB => c) c)) ≤
      1 / 2 ^ 256 := hc
  linarith

/-! ## The games with the seeds -/

section Games

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **The Issuer's key and messages** `(pk, µ₀, µ₁)`. -/
def AdversaryRO.key (A : AdversaryRO R) : UOVKey × Bytes × Bytes := (A.pk, A.msg false, A.msg true)

/-- **`realGameRO` with the seeds**: the Issuer `A g` at XOF table `g`. -/
noncomputable def seedGameRO (enc : Bytes → Ctx) (A : XofP Ctx → AdversaryRO R) (b : Bool) :
    (Bool → SeedB) × ((SlP × ShP R) × XofP Ctx) → Prop :=
  seedGameP (fun g => realGameRO Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b) b

/-- **`realGameSh` (one shared `H₃`) with the seeds.** -/
noncomputable def seedGameSh (enc : Bytes → Ctx) (A : XofP Ctx → AdversaryRO (RowH R))
    (b : Bool) : (Bool → SeedB) × ((SlP × ShP (RowH R)) × XofP Ctx) → Prop :=
  seedGameP (fun g => realGameSh Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b) b

/-- **`realGameRA` (a table-reading Issuer) with the seeds**: the contexts are the Issuer's key and
messages at the game's slices and tables. -/
noncomputable def seedGameRA (enc : Bytes → Ctx) (A : XofP Ctx → AdversaryRA R) (b : Bool) :
    (Bool → SeedB) × ((SlP × ShP R) × XofP Ctx) → Prop :=
  seedGameP (fun g => realGameRA Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b) b

/-- **`realGameRASh` (one shared `H₃`, a table-reading Issuer) with the seeds.** -/
noncomputable def seedGameRASh (enc : Bytes → Ctx) (A : XofP Ctx → AdversaryRA (RowH R))
    (b : Bool) : (Bool → SeedB) × ((SlP × ShP (RowH R)) × XofP Ctx) → Prop :=
  seedGameP (fun g => realGameRASh Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b) b

end Games

/-! ## Blindness with the seeds -/

section Blind

variable (enc : Bytes → Ctx)

/-- **`blindnessRO_lean_num` with the seed XOF.** -/
theorem blindnessRO_lean_num_seed (A : XofP Ctx → AdversaryRO (Blk → Blk)) {q3 q5 qE qk qg : ℕ}
    (hA : ∀ g, (A g).Budget q3 q5 qE) (hk : RdX (fun g => (A g).key) qk)
    (hg : ∀ b z, RdX (fun g => realGameRO Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRO enc A false) - pr _ (seedGameRO enc A true)| ≤
      4 * εRO q3 (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 +
        2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRO Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b)
    (fun b _ => hk.map (fun k => ctxK enc k b)) hg fun g => blindnessRO_lean_num (A g) (hA g)

/-- **`blindnessRO_lean_num_perm` with the seed XOF.** -/
theorem blindnessRO_lean_num_perm_seed (A : XofP Ctx → AdversaryRO (Equiv.Perm Blk))
    {q3 q5 qE qk qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE) (hk : RdX (fun g => (A g).key) qk)
    (hg : ∀ b z, RdX (fun g => realGameRO Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRO enc A false) - pr _ (seedGameRO enc A true)| ≤
      4 * εROPm pP q3 (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 +
        2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRO Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b)
    (fun b _ => hk.map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRO_lean_num_perm (A g) (hA g)

/-- **`blindnessSh_num` with the seed XOF.** -/
theorem blindnessSh_num_seed (A : XofP Ctx → AdversaryRO (RowH (Blk → Blk))) {q3 q5 qE qk qg : ℕ}
    (hA : ∀ g, (A g).Budget q3 q5 qE) (hF : ∀ g, (A g).SliceFree)
    (hk : RdX (fun g => (A g).key) qk)
    (hg : ∀ b z, RdX (fun g => realGameSh Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameSh enc A false) - pr _ (seedGameSh enc A true)| ≤
      4 * εRO (qE + 18428) (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 +
        2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameSh Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b)
    (fun b _ => hk.map (fun k => ctxK enc k b)) hg fun g => blindnessSh_num (A g) (hA g) (hF g)

/-- **`blindnessSh_num_perm` with the seed XOF.** -/
theorem blindnessSh_num_perm_seed (A : XofP Ctx → AdversaryRO (RowH (Equiv.Perm Blk)))
    {q3 q5 qE qk qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE) (hF : ∀ g, (A g).SliceFree)
    (hk : RdX (fun g => (A g).key) qk)
    (hg : ∀ b z, RdX (fun g => realGameSh Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameSh enc A false) - pr _ (seedGameSh enc A true)| ≤
      4 * εROPm pP (qE + 18428) (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 +
        2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameSh Hashes.shake (A g)) (fun g b _ => ctxK enc (A g).key b)
    (fun b _ => hk.map (fun k => ctxK enc k b)) hg fun g =>
    blindnessSh_num_perm (A g) (hA g) (hF g)

/-- **`blindnessRA_lean_num` with the seed XOF**: the key-and-messages stage reads at most `q_k`
cells at every slices and tables. -/
theorem blindnessRA_lean_num_seed (A : XofP Ctx → AdversaryRA (Blk → Blk))
    {q3 q5 qE i3 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudget i3 i5 iE) (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRA enc A false) - pr _ (seedGameRA enc A true)| ≤
      4 * εRO (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRA Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRA_lean_num (A g) (hA g) (hI g)

/-- **`blindnessRA_lean_num_perm` with the seed XOF.** -/
theorem blindnessRA_lean_num_perm_seed (A : XofP Ctx → AdversaryRA (Equiv.Perm Blk))
    {q3 q5 qE i3 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudget i3 i5 iE) (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRA enc A false) - pr _ (seedGameRA enc A true)| ≤
      4 * εROPm pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRA Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRA_lean_num_perm (A g) (hA g) (hI g)

/-- **`blindnessRAH_lean_num` (an Issuer that reads `H₂³`) with the seed XOF.** -/
theorem blindnessRAH_lean_num_seed (A : XofP Ctx → AdversaryRA (Blk → Blk))
    {q3 q5 qE i3 i2 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudgetH i3 i2 i5 iE) (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRA enc A false) - pr _ (seedGameRA enc A true)| ≤
      4 * εRO (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRA Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRAH_lean_num (A g) (hA g) (hI g)

/-- **`blindnessRAH_lean_num_perm` with the seed XOF.** -/
theorem blindnessRAH_lean_num_perm_seed (A : XofP Ctx → AdversaryRA (Equiv.Perm Blk))
    {q3 q5 qE i3 i2 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudgetH i3 i2 i5 iE) (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRA enc A false) - pr _ (seedGameRA enc A true)| ≤
      4 * εROPm pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εROPm pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRA Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRAH_lean_num_perm (A g) (hA g) (hI g)

/-- **`blindnessRASh_num` (one shared `H₃`, a table-reading Issuer) with the seed XOF.** -/
theorem blindnessRASh_num_seed (A : XofP Ctx → AdversaryRA (RowH (Blk → Blk)))
    {q5 qE i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget 0 q5 qE) (hI : ∀ g, (A g).IBudget 0 i5 iE)
    (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRASh Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRASh enc A false) - pr _ (seedGameRASh enc A true)| ≤
      4 * εRO (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRASh Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRASh_num (A g) (hA g) (hI g)

/-- **`blindnessRASh_num_perm` with the seed XOF.** -/
theorem blindnessRASh_num_perm_seed (A : XofP Ctx → AdversaryRA (RowH (Equiv.Perm Blk)))
    {q5 qE i5 iE qk qg : ℕ} (hA : ∀ g, (A g).GBudget 0 q5 qE) (hI : ∀ g, (A g).IBudget 0 i5 iE)
    (hk : ∀ sl s, RdX (fun g => (A g).keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRASh Hashes.shake (A g) b z) qg) :
    |pr _ (seedGameRASh enc A false) - pr _ (seedGameRASh enc A true)| ≤
      4 * εROPm pP (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  abs_seedGameP_sub_le (fun g => realGameRASh Hashes.shake (A g))
    (fun g b t => ctxK enc ((A g).keyOf t.1 t.2) b)
    (fun b t => (hk t.1 t.2).map (fun k => ctxK enc k b)) hg fun g =>
    blindnessRASh_num_perm (A g) (hA g) (hI g)

end Blind

end PomFRIT

/-! ## Four requests in two domains (Moussaka, Ratatouille) -/

/-- **The four `H₃` slices and the shared tables `Y`**: the rest of a four-proof game's tape. -/
abbrev T4 (Y : Type) := ((ZK.Sim.Tab3 × ZK.Sim.Tab3) × (ZK.Sim.Tab3 × ZK.Sim.Tab3)) × Y

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **A cell of the seed-XOF table**: the issue XOF's `(nf, r, ρ_iss)`; a redemption reads the
redeem XOF's `ρ_red` off the `16`-byte component. -/
abbrev XCell := NR × Coins proveSeedBytes

/-- **The seed-XOF table**, keyed by `(domain, seed)`: `false` the issue DST, `true` the redeem
DST. -/
abbrev XofM := Bool × SeedB → XCell

variable {Y : Type} [Fintype Y] [Nonempty Y]

/-- **The game's tape from the four cells**: `(false, j)` Client `j`'s issuance, `(true, side)` the
redemption on `side`. -/
def insM (_ : Unit) (u : Bool × Bool → XCell) (t : T4 Y) : ((TIr × TIr) × (TRr × TRr)) × Y :=
  (((((u (false, false)).1, ((u (false, false)).2, t.1.1.1)),
      ((u (false, true)).1, ((u (false, true)).2, t.1.1.2))),
    (((u (true, false)).2, t.1.2.1), ((u (true, true)).2, t.1.2.2))), t.2)

/-- Uniform cells give the uniform tape (the redemptions' unused components marginalized). -/
theorem hinsM (k : T4 Y → Unit) (P : ((TIr × TIr) × (TRr × TRr)) × Y → Prop) :
    pr ((Bool × Bool → XCell) × T4 Y) (fun z => P (insM (k z.2) z.1 z.2)) =
      pr (((TIr × TIr) × (TRr × TRr)) × Y) P := by
  let E : (Bool × Bool → XCell) × T4 Y ≃ (((TIr × TIr) × (TRr × TRr)) × Y) × (NR × NR) :=
    { toFun := fun z => (insM () z.1 z.2, ((z.1 (true, false)).1, (z.1 (true, true)).1))
      invFun := fun w =>
        (fun i => bif i.1 then (bif i.2 then (w.2.2, w.1.1.2.2.1) else (w.2.1, w.1.1.2.1.1))
          else (bif i.2 then (w.1.1.1.2.1, w.1.1.1.2.2.1) else (w.1.1.1.1.1, w.1.1.1.1.2.1)),
         (((w.1.1.1.1.2.2, w.1.1.1.2.2.2), (w.1.1.2.1.2, w.1.1.2.2.2)), w.1.2))
      left_inv := fun z => by
        refine Prod.ext (funext fun i => ?_) rfl
        obtain ⟨a, b⟩ := i
        cases a <;> cases b <;> rfl
      right_inv := fun _ => rfl }
  calc pr ((Bool × Bool → XCell) × T4 Y) (fun z => P (insM (k z.2) z.1 z.2))
      = pr ((Bool × Bool → XCell) × T4 Y) (fun z => (fun w : (((TIr × TIr) × (TRr × TRr)) × Y) ×
          (NR × NR) => P w.1) (E z)) := rfl
    _ = pr ((((TIr × TIr) × (TRr × TRr)) × Y) × (NR × NR)) (fun w => P w.1) :=
        pr_equiv E (fun w => P w.1)
    _ = pr (((TIr × TIr) × (TRr × TRr)) × Y) P := pr_prod_fst (β := NR × NR) P

/-- **The game with the seeds**: seeds `c` (two per domain), the slices and shared tables `t`, the
XOF table `g`; request `i` gets the cell `g (i.1, c i)`. -/
def seedGameM (G : XofM → Bool → ((TIr × TIr) × (TRr × TRr)) × Y → Prop) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 Y × XofM) → Prop :=
  seedGame (fun g => G g b) (fun _ _ => ()) insM domKey

/-- **The seed-XOF hop for Moussaka**: `ε + 2·(2q_g + 2)·2⁻²⁵⁶`. -/
theorem abs_seedGameM_sub_le (G : XofM → Bool → ((TIr × TIr) × (TRr × TRr)) × Y → Prop)
    {qg : ℕ} (hg : ∀ b ω, RdX (fun g => G g b ω) qg) {ε : ℝ}
    (hε : ∀ g, |pr (((TIr × TIr) × (TRr × TRr)) × Y) (G g false) -
      pr (((TIr × TIr) × (TRr × TRr)) × Y) (G g true)| ≤ ε) :
    |pr _ (seedGameM G false) - pr _ (seedGameM G true)| ≤
      ε + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) := by
  have h := abs_pr_seedGame_sub_le G (fun _ _ _ => ()) insM hinsM domKey (qk := 0)
    (fun _ _ => RdX.const ()) hg (δ := 2 * ((0 + qg : ℕ) : ℝ) / Fintype.card SeedB)
    (fun F hF => pr_dom_exists_mem_le F hF) false true hε
  have hc := pr_dom_not_injective_le (S := SeedB)
  rw [card_seedB] at h hc
  unfold seedGameM
  refine h.trans ?_
  have e : ((2 * qg + 2 : ℕ) : ℝ) / 2 ^ 256 = 2 / 2 ^ 256 + 2 * ((0 + qg : ℕ) : ℝ) / 2 ^ 256 := by
    push_cast
    ring
  rw [e]
  linarith

/-! ### The games with the seeds -/

section Games

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]
  (idx : AnchorSet → UOVKey → ℕ)

/-- **`realGameRO` (Lean provers) with the seeds.** -/
noncomputable def seedGameRO (A : XofM → AdversaryRO R) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM R) × XofM) → Prop :=
  seedGameM (fun g => realGameRO (A g) idx leanPI leanPR) b

/-- **`realGameSh` (one shared `H₃`) with the seeds.** -/
noncomputable def seedGameSh (A : XofM → AdversaryRO (RowH R)) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM (RowH R)) × XofM) → Prop :=
  seedGameM (fun g => realGameSh (A g) idx) b

/-- **`realGameRA` (a table-reading interaction, Lean provers) with the seeds.** -/
noncomputable def seedGameRA (A : XofM → AdversaryRA R) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM R) × XofM) → Prop :=
  seedGameM (fun g => realGameRA (A g) idx leanPI leanPR) b

/-- **`realGameRASh` (one shared `H₃`, a table-reading interaction) with the seeds.** -/
noncomputable def seedGameRASh (A : XofM → AdversaryRA (RowH R)) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM (RowH R)) × XofM) → Prop :=
  seedGameM (fun g => realGameRASh (A g) idx) b

end Games

/-! ### Theorem 4(a) with the seeds -/

section Anon

variable (idx : AnchorSet → UOVKey → ℕ)

/-- **`anonymityRO_lean_num` with the seed XOF.** -/
theorem anonymityRO_lean_num_seed (A : XofM → AdversaryRO (Blk → Blk)) {q3 q5 qE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b c, hidingAdv (A g).base.ci (A g).base.cr
      (reductionRO (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRO (A g) idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRO idx A false) - pr _ (seedGameRO idx A true)| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRO (A g) idx leanPI leanPR) hg fun g =>
    anonymityRO_lean_num (A g) idx (hA g) (hhide g)

/-- **`anonymityRO_lean_num_perm` with the seed XOF.** -/
theorem anonymityRO_lean_num_perm_seed (A : XofM → AdversaryRO (Equiv.Perm Blk))
    {q3 q5 qE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b c, hidingAdv (A g).base.ci (A g).base.cr
      (reductionRO (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRO (A g) idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRO idx A false) - pr _ (seedGameRO idx A true)| ≤
      4 * εROPm pI q3 (q5 + 1872) (qE + 13821) + 4 * εROPm pR q3 (q5 + 1872) (qE + 13821) +
        4 * (1 / 2 ^ 113 + εROPm pR 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRO (A g) idx leanPI leanPR) hg fun g =>
    anonymityRO_lean_num_perm (A g) idx (hA g) (hhide g)

/-- **`anonymitySh_num` (one shared `H₃`) with the seed XOF.** -/
theorem anonymitySh_num_seed (A : XofM → AdversaryRO (RowH (Blk → Blk))) {q3 q5 qE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b c, hidingAdv (A g).base.ci (A g).base.cr
      (reductionRO (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameSh (A g) idx b z) qg) :
    |pr _ (seedGameSh idx A false) - pr _ (seedGameSh idx A true)| ≤
      8 * εRO (qE + 13824) (q5 + 1872) (qE + 13824) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameSh (A g) idx) hg fun g =>
    anonymitySh_num (A g) idx (hA g) (hhide g)

/-- **`anonymitySh_num_perm` with the seed XOF.** -/
theorem anonymitySh_num_perm_seed (A : XofM → AdversaryRO (RowH (Equiv.Perm Blk)))
    {q3 q5 qE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b c, hidingAdv (A g).base.ci (A g).base.cr
      (reductionRO (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameSh (A g) idx b z) qg) :
    |pr _ (seedGameSh idx A false) - pr _ (seedGameSh idx A true)| ≤
      4 * εROPm pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * εROPm pR (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + εROPm pR 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameSh (A g) idx) hg fun g =>
    anonymitySh_num_perm (A g) idx (hA g) (hhide g)

/-- **`anonymityRA_lean_num` (a table-reading interaction) with the seed XOF.** -/
theorem anonymityRA_lean_num_seed (A : XofM → AdversaryRA (Blk → Blk))
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudget i3 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).ctxRO.base.ci (A g).ctxRO.base.cr
      (reductionRA (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRA (A g) idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRA idx A false) - pr _ (seedGameRA idx A true)| ≤
      4 * εRO (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAd 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRA (A g) idx leanPI leanPR) hg fun g =>
    anonymityRA_lean_num (A := A g) (idx := idx) (hA g) (hI g) (hhide g)

/-- **`anonymityRA_lean_num_perm` with the seed XOF.** -/
theorem anonymityRA_lean_num_perm_seed (A : XofM → AdversaryRA (Equiv.Perm Blk))
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudget i3 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).ctxRO.base.ci (A g).ctxRO.base.cr
      (reductionRA (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRA (A g) idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRA idx A false) - pr _ (seedGameRA idx A true)| ≤
      4 * εROPm pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAdPm pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRA (A g) idx leanPI leanPR) hg fun g =>
    anonymityRA_lean_num_perm (A := A g) (idx := idx) (hA g) (hI g) (hhide g)

/-- **`anonymityRASh_num` (one shared `H₃`, a table-reading interaction) with the seed XOF.** -/
theorem anonymityRASh_num_seed (A : XofM → AdversaryRA (RowH (Blk → Blk)))
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget 0 q5 qE)
    (hI : ∀ g, (A g).IBudget 0 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).ctxRO.base.ci (A g).ctxRO.base.cr
      (reductionRA (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRASh (A g) idx b z) qg) :
    |pr _ (seedGameRASh idx A false) - pr _ (seedGameRASh idx A true)| ≤
      4 * εRO (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAd 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRASh (A g) idx) hg fun g =>
    anonymityRASh_num (A g) idx (hA g) (hI g) (hhide g)

/-- **`anonymityRASh_num_perm` with the seed XOF.** -/
theorem anonymityRASh_num_perm_seed (A : XofM → AdversaryRA (RowH (Equiv.Perm Blk)))
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget 0 q5 qE)
    (hI : ∀ g, (A g).IBudget 0 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).ctxRO.base.ci (A g).ctxRO.base.cr
      (reductionRA (A g) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRASh (A g) idx b z) qg) :
    |pr _ (seedGameRASh idx A false) - pr _ (seedGameRASh idx A true)| ≤
      4 * εROPm pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAdPm pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 113 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameRASh (A g) idx) hg fun g =>
    anonymityRASh_num_perm (A g) idx (hA g) (hI g) (hhide g)

end Anon

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **A cell of the seed-XOF table**: `(nf, r, ρ)`. -/
abbrev XCell := NRR × Coins 16

/-- **The seed-XOF table**, keyed by `(domain, seed)`: `false` the issue DST, `true` the spend
DST. -/
abbrev XofR := Bool × SeedB → XCell

variable {Y : Type} [Fintype Y] [Nonempty Y]

/-- **The game's tape from the four cells**: `(false, j)` issuance `j`, `(true, k)` spend `k`. -/
def insR (_ : Unit) (u : Bool × Bool → XCell) (t : T4 Y) : ((TRe × TRe) × (TRe × TRe)) × Y :=
  (((((u (false, false)).1, ((u (false, false)).2, t.1.1.1)),
      ((u (false, true)).1, ((u (false, true)).2, t.1.1.2))),
    (((u (true, false)).1, ((u (true, false)).2, t.1.2.1)),
      ((u (true, true)).1, ((u (true, true)).2, t.1.2.2)))), t.2)

/-- Uniform cells give the uniform tape. -/
theorem hinsR (k : T4 Y → Unit) (P : ((TRe × TRe) × (TRe × TRe)) × Y → Prop) :
    pr ((Bool × Bool → XCell) × T4 Y) (fun z => P (insR (k z.2) z.1 z.2)) =
      pr (((TRe × TRe) × (TRe × TRe)) × Y) P := by
  let E : (Bool × Bool → XCell) × T4 Y ≃ ((TRe × TRe) × (TRe × TRe)) × Y :=
    { toFun := fun z => insR () z.1 z.2
      invFun := fun w =>
        (fun i => bif i.1 then (bif i.2 then (w.1.2.2.1, w.1.2.2.2.1) else (w.1.2.1.1, w.1.2.1.2.1))
          else (bif i.2 then (w.1.1.2.1, w.1.1.2.2.1) else (w.1.1.1.1, w.1.1.1.2.1)),
         (((w.1.1.1.2.2, w.1.1.2.2.2), (w.1.2.1.2.2, w.1.2.2.2.2)), w.2))
      left_inv := fun z => by
        refine Prod.ext (funext fun i => ?_) rfl
        obtain ⟨a, b⟩ := i
        cases a <;> cases b <;> rfl
      right_inv := fun _ => rfl }
  exact pr_equiv E P

/-- **The game with the seeds** (worlds `(b₁, b₂)`). -/
def seedGameR (G : XofR → Bool → Bool → ((TRe × TRe) × (TRe × TRe)) × Y → Prop) (b₁ b₂ : Bool) :
    (Bool × Bool → SeedB) × (T4 Y × XofR) → Prop :=
  seedGame (fun g => G g b₁ b₂) (fun _ _ => ()) insR domKey

/-- **The seed-XOF hop for Ratatouille**: `ε + 2·(2q_g + 2)·2⁻²⁵⁶`. -/
theorem abs_seedGameR_sub_le (G : XofR → Bool → Bool → ((TRe × TRe) × (TRe × TRe)) × Y → Prop)
    {qg : ℕ} (hg : ∀ b₁ b₂ ω, RdX (fun g => G g b₁ b₂ ω) qg) {ε : ℝ} (b₁ b₂ b₁' b₂' : Bool)
    (hε : ∀ g, |pr (((TRe × TRe) × (TRe × TRe)) × Y) (G g b₁ b₂) -
      pr (((TRe × TRe) × (TRe × TRe)) × Y) (G g b₁' b₂')| ≤ ε) :
    |pr _ (seedGameR G b₁ b₂) - pr _ (seedGameR G b₁' b₂')| ≤
      ε + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) := by
  let G' : XofR → Bool × Bool → ((TRe × TRe) × (TRe × TRe)) × Y → Prop := fun g w => G g w.1 w.2
  have hε' : ∀ g, |pr (((TRe × TRe) × (TRe × TRe)) × Y) (G' g (b₁, b₂)) -
      pr (((TRe × TRe) × (TRe × TRe)) × Y) (G' g (b₁', b₂'))| ≤ ε := hε
  have hg' : ∀ w ω, RdX (fun g => G' g w ω) qg := fun w ω => hg w.1 w.2 ω
  have h := abs_pr_seedGame_sub_le G' (fun _ _ _ => ()) insR hinsR domKey
    (qk := 0) (fun _ _ => RdX.const ()) hg'
    (δ := 2 * ((0 + qg : ℕ) : ℝ) / Fintype.card SeedB)
    (fun F hF => pr_dom_exists_mem_le F hF) (b₁, b₂) (b₁', b₂') hε'
  have hc := pr_dom_not_injective_le (S := SeedB)
  rw [card_seedB] at h hc
  unfold seedGameR
  refine h.trans ?_
  have e : ((2 * qg + 2 : ℕ) : ℝ) / 2 ^ 256 = 2 / 2 ^ 256 + 2 * ((0 + qg : ℕ) : ℝ) / 2 ^ 256 := by
    push_cast
    ring
  rw [e]
  linarith

/-! ### The games with the seeds -/

section Games

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **`realGameR` (Lean provers) with the seeds.** -/
noncomputable def seedGameRO (A : XofR → AdversaryRO R Sizes.labelRows) (b₁ b₂ : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShR R) × XofR) → Prop :=
  seedGameR (fun g => realGameR (A g) leanPIR leanPSR) b₁ b₂

/-- **`realGameSh` (one shared `H₃`) with the seeds.** -/
noncomputable def seedGameSh (A : XofR → AdversaryRO (RowH R) Sizes.labelRows) (b₁ b₂ : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShR (RowH R)) × XofR) → Prop :=
  seedGameR (fun g => realGameSh (A g)) b₁ b₂

/-- **`realGameRA` (a table-reading Issuer, Lean provers) with the seeds.** -/
noncomputable def seedGameRA (A : XofR → AdversaryRA R Sizes.labelRows) (b₁ b₂ : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShR R) × XofR) → Prop :=
  seedGameR (fun g => realGameRA (A g) leanPIR leanPSR) b₁ b₂

/-- **`realGameRASh` (one shared `H₃`, a table-reading Issuer) with the seeds.** -/
noncomputable def seedGameRASh (A : XofR → AdversaryRA (RowH R) Sizes.labelRows) (b₁ b₂ : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShR (RowH R)) × XofR) → Prop :=
  seedGameR (fun g => realGameRASh (A g)) b₁ b₂

end Games

/-! ### Theorem 2 with the seeds -/

/-- **`unlinkabilityRO_lean_num` with the seed XOF.** -/
theorem unlinkabilityRO_lean_num_seed (A : XofR → AdversaryRO (Blk → Blk) Sizes.labelRows)
    {q3 q5 qE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionR (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameR (A g) leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRO A b₁ b₂) - pr _ (seedGameRO A b₁' b₂')| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameR (A g) leanPIR leanPSR) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRO_lean_num (A g) (hA g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityRO_lean_num_perm` with the seed XOF.** -/
theorem unlinkabilityRO_lean_num_perm_seed
    (A : XofR → AdversaryRO (Equiv.Perm Blk) Sizes.labelRows) {q3 q5 qE qg : ℕ} {εhide : ℝ}
    (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionR (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameR (A g) leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRO A b₁ b₂) - pr _ (seedGameRO A b₁' b₂')| ≤
      4 * εROPm pI q3 (q5 + 1872) (qE + 13821) + 4 * εROPm pS q3 (q5 + 1872) (qE + 13821) +
        4 * (1 / 2 ^ 113 + εROPm pS 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameR (A g) leanPIR leanPSR) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRO_lean_num_perm (A g) (hA g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilitySh_num` (one shared `H₃`) with the seed XOF.** -/
theorem unlinkabilitySh_num_seed (A : XofR → AdversaryRO (RowH (Blk → Blk)) Sizes.labelRows)
    {q3 q5 qE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionR (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameSh (A g) b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameSh A b₁ b₂) - pr _ (seedGameSh A b₁' b₂')| ≤
      8 * εRO (qE + 13824) (q5 + 1872) (qE + 13824) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameSh (A g)) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilitySh_num (A g) (hA g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilitySh_num_perm` with the seed XOF.** -/
theorem unlinkabilitySh_num_perm_seed
    (A : XofR → AdversaryRO (RowH (Equiv.Perm Blk)) Sizes.labelRows) {q3 q5 qE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionR (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameSh (A g) b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameSh A b₁ b₂) - pr _ (seedGameSh A b₁' b₂')| ≤
      4 * εROPm pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * εROPm pS (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + εROPm pS 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameSh (A g)) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilitySh_num_perm (A g) (hA g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityRA_lean_num` (a table-reading Issuer) with the seed XOF.** -/
theorem unlinkabilityRA_lean_num_seed (A : XofR → AdversaryRA (Blk → Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget q3 q5 qE)
    (hI : ∀ g, (A g).IBudget i3 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionRA (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRA (A g) leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRA A b₁ b₂) - pr _ (seedGameRA A b₁' b₂')| ≤
      4 * εRO (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAd 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameRA (A g) leanPIR leanPSR) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRA_lean_num (A g) (hA g) (hI g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityRA_lean_num_perm` with the seed XOF.** -/
theorem unlinkabilityRA_lean_num_perm_seed
    (A : XofR → AdversaryRA (Equiv.Perm Blk) Sizes.labelRows) {q3 q5 qE i3 i2 i5 iE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).GBudget q3 q5 qE) (hI : ∀ g, (A g).IBudget i3 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionRA (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRA (A g) leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRA A b₁ b₂) - pr _ (seedGameRA A b₁' b₂')| ≤
      4 * εROPm pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAdPm pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAdPm pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameRA (A g) leanPIR leanPSR) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRA_lean_num_perm (A g) (hA g) (hI g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityRASh_num` (one shared `H₃`, a table-reading Issuer) with the seed XOF.** -/
theorem unlinkabilityRASh_num_seed (A : XofR → AdversaryRA (RowH (Blk → Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).GBudget 0 q5 qE)
    (hI : ∀ g, (A g).IBudget 0 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionRA (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRASh (A g) b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRASh A b₁ b₂) - pr _ (seedGameRASh A b₁' b₂')| ≤
      4 * εRO (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAd 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameRASh (A g)) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRASh_num (A g) (hA g) (hI g) (hhide g) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityRASh_num_perm` with the seed XOF.** -/
theorem unlinkabilityRASh_num_perm_seed
    (A : XofR → AdversaryRA (RowH (Equiv.Perm Blk)) Sizes.labelRows) {q5 qE i2 i5 iE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).GBudget 0 q5 qE) (hI : ∀ g, (A g).IBudget 0 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).ctx
      (reductionRA (A g) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRASh (A g) b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRASh A b₁ b₂) - pr _ (seedGameRASh A b₁' b₂')| ≤
      4 * εROPm pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAdPm pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624)
          (iE + 9214) +
        2 * εAdPm pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameR_sub_le (fun g => realGameRASh (A g)) hg b₁ b₂ b₁' b₂' fun g =>
    unlinkabilityRASh_num_perm (A g) (hA g) (hI g) (hhide g) b₁ b₂ b₁' b₂'

end Ratatouille

end VoleMole.Privacy
