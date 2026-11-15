import VoleMole.ZK.MainSharedAll
import VoleMole.Privacy.MoussakaMainShared23

/-!
# Moussaka issuer hiding and unlinkability on `main`, with all tables shared

`anonymity_main_shared23` (`Privacy/MoussakaMainShared23.lean`) is Theorem 4(a) on `main` with
one `H₂³` table, one `H₅` table and one cipher for the four proofs; each proof keeps its own `H₃`
slice. Here the four proofs also **share `H₃`** (`ZK/MainSharedAll.lean`): each real proof reads
the one table at its prefix `wPrefix ‖ μ₁`, and the guess sees the one table (`AdversaryH`: it
reads it at `q₃` points, not the per-proof slices).

## The game (`realH`)

The game of `real23` (`gameS`, the same interaction) run with `ZK.Sim.realAll`: the four proofs'
`H₃` slices are the columns of one uniform table at their prefixes. The guess and its `H₅` read
set take the table as an extra input (`evH`, `r5H`); at a fixed table they are an `AdversaryS`
(`withH`), so the simulated game, hiding and the (PU) predictors of `anonymity_main_shared23`
apply table by table.

## The bound (`anonymity_main_sharedAll`)

    |Pr[world 0] − Pr[world 1]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(Σ_{b,c} puAdv Com (predH_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide + 2·2⁻¹²⁸

* `2·2⁻¹²⁸`: two of the four proofs of a world have one prefix (`realAll_close`); then the
  Clients' openings agree (`coll_imp`: issuance and redemption witnesses have different lengths,
  and each witness starts with its token's opening);
* the predictors `predH_c b` are those of `anonymity_main_shared23` for the guess at a uniform
  table that the predictor draws itself (`puAdv_avgH`);
* `εhide`: hiding of `Com` for the reductions `redS23` of the guess at every table.
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

/-! ## The adversary with one `H₃` -/

/-- The guess's tables without the per-proof `H₃` slices (the shared game has none). -/
def clrS (t : VisS) : VisS :=
  (t.1, ((fun _ => 0, t.2.1.2), (fun _ => 0, t.2.2.1.2), (fun _ => 0, t.2.2.2.1.2),
    (fun _ => 0, t.2.2.2.2.2)))

/-- **The colluding adversary on `main` with one `H₃`**: `Adversary`'s interaction (not reading the
tables) and a guess that sees the shared tables and the one `H₃` table, with its `H₅` read set. -/
structure AdversaryH where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  choose : Bytes → Bytes → Bool → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → Prop
  R5 : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisS → H3T →
    Finset (ZK.Sim.Bytes 37)

/-- **`f` reads the tables and the one `H₃` within explicit sets**: `H₅` at `R`, the cipher at
`qE` keys, `H₃` at `q3` points (prefix, `ρ`). -/
structure RdTH {X : Sort*} (f : VisS → H3T → X) (R : VisS → H3T → Finset (ZK.Sim.Bytes 37))
    (q3 qE : ℕ) : Prop where
  h5 : ∀ t T (G5 : Tab5F), (∀ k ∈ R t T, t.1.1 k = G5 k) → f ((G5, t.1.2), t.2) T = f t T
  hE : ∃ Q : VisS → H3T → Finset Blk, (∀ t T, (Q t T).card ≤ qE) ∧
    ∀ t T (E : Cipher), (∀ k ∈ Q t T, t.1.2 k = E k) → f ((t.1.1, E), t.2) T = f t T
  hT : ∃ Q : VisS → H3T → Finset (Pre × ZK.Sim.Bytes 16), (∀ t T, (Q t T).card ≤ q3) ∧
    ∀ t T T', (∀ k ∈ Q t T, T k.1 k.2 = T' k.1 k.2) → f t T' = f t T

namespace AdversaryH

variable (A : AdversaryH)

/-- **The adversary at one `H₃` table**: an `AdversaryS` whose guess sees `T` and not the
per-proof slices. -/
def withH (T : H3T) : AdversaryS :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun q₀ q₁ y t => A.guess q₀ q₁ y (clrS t) T,
    fun q₀ q₁ y t => A.R5 q₀ q₁ y (clrS t) T⟩

/-- Its interaction, at any table. -/
def base : AdversaryS := A.withH fun _ _ => 0

/-- **Consistent reads**: with the requests fixed, the guess and its `H₅` read set read `H₃` at
`q3` points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ q₀ q₁ y, RdTH (A.guess q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE
  r : ∀ q₀ q₁ y, RdTH (A.R5 q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE

end AdversaryH

variable (A : AdversaryH) (idx : AnchorSet → UOVKey → ℕ)

lemma gameS_withH (T : H3T) (b : Bool) : gameS (A.withH T) idx b = gameS A.base idx b := rfl

/-- **The final event of world `b`**, on the view and the one `H₃`. -/
def evH (b : Bool) (v : GView SecM pIm pIm pRm pRm) (T : H3T) : Prop := evS (A.withH T) idx b v

/-- Its `H₅` read set. -/
def r5H (b : Bool) (v : GView SecM pIm pIm pRm pRm) (T : H3T) : Finset (ZK.Sim.Bytes 37) :=
  r5S (A.withH T) idx b v

/-- **The real game on `main` with all tables shared** in world `b`: the four proofs read one
`H₃`, one `H₂³` table, one `H₅` table and one cipher. -/
noncomputable def realH (b : Bool) : ℝ :=
  realAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameS A.base idx b) (evH A idx b)

/-- The game with all proofs simulated, one `H₃` (read by the guess only). -/
noncomputable def simH (b : Bool) : ℝ :=
  simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameS A.base idx b) (evH A idx b)

/-! ## The hypotheses of the joint hop -/

lemma rdH_of {X : Sort*}
    {f : Bytes × Bytes × Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → X}
    {R : Bytes × Bytes × Option (Except Error Bytes × Except Error Bytes) → VisS → H3T →
      Finset (ZK.Sim.Bytes 37)} {q3 qE : ℕ} (h : ∀ y, RdTH (f y) (R y) q3 qE) (b : Bool) :
    RdH (fun (v : GView SecM pIm pIm pRm pRm) T => f (keyS A.base idx b v) (clrS v.vis) T)
      (fun v T => R (keyS A.base idx b v) (clrS v.vis) T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  refine ⟨fun v T G5 hk => (h _).h5 (clrS v.vis) T G5 hk,
    ⟨fun v T => QE (keyS A.base idx b v) (clrS v.vis) T, fun _ _ => hQEc _ _ _,
      fun v T E hk => hQE _ (clrS v.vis) T E hk⟩,
    ⟨fun v T => QT (keyS A.base idx b v) (clrS v.vis) T, fun _ _ => hQTc _ _ _,
      fun v T T' hk => hQT _ (clrS v.vis) T T' hk⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

lemma rdH_evH {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b : Bool) :
    RdH (evH A idx b) (r5H A idx b) q3 qE :=
  rdH_of A idx (f := fun y t T => A.guess y.1 y.2.1 y.2.2 t T)
    (R := fun y t T => A.R5 y.1 y.2.1 y.2.2 t T) (fun y => hC.g y.1 y.2.1 y.2.2) b

lemma rdH_r5H {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b : Bool) :
    RdH (r5H A idx b) (r5H A idx b) q3 qE :=
  rdH_of A idx (f := fun y t T => A.R5 y.1 y.2.1 y.2.2 t T)
    (R := fun y t T => A.R5 y.1 y.2.1 y.2.2 t T) (fun y => hC.r y.1 y.2.1 y.2.2) b

/-- **The joint hop in each world** with one `H₃`. -/
theorem real_sim_sharedAll {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b : Bool) :
    |realH A idx b - simH A idx b| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
          (gameS A.base idx b) (fun v T => bstar Hashes.shake (gameS A.base idx b)
            (fun v => r5H A idx b v T) v) +
        pr (GTape SecM pIm pIm pRm pRm) (fun x => ¬ DistV Hashes.shake (gameS A.base idx b)
          (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
            (gameS A.base idx b) false false false false x)) :=
  main_sharedAll_le (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameS A.base idx b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm small_pIm small_pRm
    small_pRm hashesWF_shake (gvalidS A.base idx b) (evH A idx b) (r5H A idx b)
    (rdH_evH A idx hC b) (rdH_r5H A idx hC b)

/-! ## Two proofs with one prefix -/

section Coll

variable (B : AdversaryM)

lemma issStmt_size (s : SecM) (c : Bool) : (issStmt B s c).2.size = 256 := by
  show (toBA _).size = _
  rw [size_toBA]
  exact length_encodeIssueWitness (by simp) (by simp [Adversary.cr, AdversaryM.int]) (by simp)

lemma issStmt_wPre (s : SecM) (c : Bool) : wPre (issStmt B s c).2 = rOf s c :=
  wPre_issueWitness _ _ _ _

/-- **A redemption statement of `main`'s game** (the tokens finalized): its witness has `343`
bytes and starts with the opening of Client `b ^^ side`. -/
lemma redStmt_wit (b : Bool) (s : SecM) (o₁ o₂ : Option Out) (side : Bool) (y : SW)
    (hy : y ∈ (bif allOk B.int idx (issM B s false o₁) (issM B s true o₂) then
      redStmt B (ptM B idx b s o₁ o₂ side) else none)) :
    y.2.size = 343 ∧ wPre y.2 = rOf s (b ^^ side) := by
  set i₀ := issM B s false o₁
  set i₁ := issM B s true o₂
  cases hok : allOk B.int idx i₀ i₁
  · rw [hok] at hy; cases hy
  rw [hok] at hy
  have hy' : redStmt B (ptM B idx b s o₁ o₂ side) = some y := hy
  set c := b ^^ side
  have hs : (tok B.int i₀ i₁ c).isSome = true := by
    unfold allOk at hok
    simp only [Bool.and_eq_true] at hok
    cases c
    · exact hok.1.1.1.1.1
    · exact hok.1.1.1.1.2
  have hf : finT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t c = true := by
    rw [tok_of_fin] at hs
    by_contra h
    simp [h] at hs
  have htok : tokD B.int i₀ i₁ c = ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r,
      resp B.int i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin]
    simp only [hf, ↓reduceIte, Option.getD_some]
  have hr : (bif c then i₁ else i₀).1.r = List.ofFn (rOf s c) := by cases c <;> rfl
  have hP : ptM B idx b s o₁ o₂ side = ⟨⟨(bif c then i₁ else i₀).1.nf, List.ofFn (rOf s c),
      resp B.int i₀.2 i₁.2 c⟩, (B.int.choose i₀.2 i₁.2 side).1,
      idx (B.int.choose i₀.2 i₁.2 side).1 (B.int.pk c), (B.int.choose i₀.2 i₁.2 side).2⟩ := by
    unfold ptM pt
    rw [htok, hr]
  rw [hP] at hy'
  unfold redStmt at hy'
  split at hy'
  · cases hy'
  · split_ifs at hy'
    cases hy'
    refine ⟨?_, wPre_redeemWitness _ _ _ _ _ _⟩
    show (toBA _).size = _
    rw [size_toBA]
    exact length_encodeRedeemWitness (by simp) (by rw [resp, List.length_ofFn]) _

/-- **Two proofs of a world with one prefix**: then the two Clients' openings agree (issuance and
redemption witnesses have different lengths, and each starts with its token's opening). -/
theorem coll_imp (b : Bool) (v : GView SecM pIm pIm pRm pRm)
    (h : ¬ DistV Hashes.shake (gameS A.base idx b) v) : rOf v.s false = rOf v.s true := by
  by_contra hne
  have hne' : rOf v.s true ≠ rOf v.s false := Ne.symm hne
  have i₁ : ∀ y ∈ yv₁ (gameS A.base idx b) v, y.2.size = pIm.witnessBytes ∧ wPre y.2 = rOf v.s false :=
    fun y hy => by
      cases hy; exact ⟨issStmt_size _ _ _, issStmt_wPre _ _ _⟩
  have i₂ : ∀ y ∈ yv₂ (gameS A.base idx b) v, y.2.size = pIm.witnessBytes ∧ wPre y.2 = rOf v.s true :=
    fun y hy => by
      cases hy; exact ⟨issStmt_size _ _ _, issStmt_wPre _ _ _⟩
  have r₃ : ∀ y ∈ yv₃ (gameS A.base idx b) v, y.2.size = pRm.witnessBytes ∧
      wPre y.2 = rOf v.s (b ^^ false) :=
    fun y hy => redStmt_wit idx A.base.toM b v.s v.o₁ v.o₂ false y hy
  have r₄ : ∀ y ∈ yv₄ (gameS A.base idx b) v, y.2.size = pRm.witnessBytes ∧
      wPre y.2 = rOf v.s (b ^^ true) :=
    fun y hy => redStmt_wit idx A.base.toM b v.s v.o₁ v.o₂ true y hy
  have h16 : 16 ≤ pIm.witnessBytes := by decide
  have h16' : 16 ≤ pRm.witnessBytes := by decide
  have mI : pIm.witnessBytes + 32 < preMax := by decide
  have mR : pRm.witnessBytes + 32 < preMax := by decide
  have ne : pIm.witnessBytes ≠ pRm.witnessBytes := by decide
  apply h
  refine ⟨distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (i₂ y hy).1) h16 mI mI
      fun y hy y' hy' _ => by rw [(i₁ y hy).2, (i₂ y' hy').2]; exact hne,
    distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (r₃ y hy).1) h16 mI mR
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (r₄ y hy).1) h16 mI mR
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₂ y hy).1) (fun y hy => (r₃ y hy).1) h16 mI mR
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₂ y hy).1) (fun y hy => (r₄ y hy).1) h16 mI mR
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (r₃ y hy).1) (fun y hy => (r₄ y hy).1) h16' mR mR
      fun y hy y' hy' _ => by
        rw [(r₃ y hy).2, (r₄ y' hy').2]
        cases b
        · exact hne
        · exact hne'⟩

/-- **The prefix-collision term is at most `2⁻¹²⁸`**: the two Clients' uniform openings agree. -/
theorem pr_coll_le (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (fun x => ¬ DistV Hashes.shake (gameS A.base idx b)
      (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A.base idx b) false false false false x)) ≤ 1 / 2 ^ 128 := by
  refine (pr_mono fun x hx => coll_imp A idx b _ hx).trans ?_
  have e1 := pr_prod_fst (β := USh × KS pIm × KS pIm × KS pRm × KS pRm)
    (fun s : SecM => rOf s false = rOf s true)
  refine (le_of_eq e1).trans ?_
  let e : Coins rBytes × ((Coins nfBytes × Coins nfBytes) × Coins rBytes) ≃ SecM :=
    { toFun := fun z => ((z.2.1.1, z.1), (z.2.1.2, z.2.2))
      invFun := fun s => (s.1.2, ((s.1.1, s.2.1), s.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  have := pr_mem_uniform_le (X := (Coins nfBytes × Coins nfBytes) × Coins rBytes)
    (fun z => {z.2}) (q := 0) (fun _ => by simp)
  simpa [e, rOf] using this

end Coll

/-! ## With all proofs simulated: table by table -/

/-- **The hiding hop** with one `H₃`: at every table the hop of `hiding_hopS23`. -/
theorem hiding_hopH (b : Bool) {εhide : ℝ}
    (hhide : ∀ T a, hidingAdv A.base.toM.int.ci A.base.toM.int.cr (redS23 (A.withH T) idx b a) ≤
      εhide) :
    |simH A idx b - pr (H3T × ((HTape × (Coins nfBytes × Coins nfBytes)) × AuxS)) (fun z =>
        idealS23 (A.withH z.1) idx b z.2)| ≤ εhide := by
  have c : simH A idx b = pr (H3T × GTape SecM pIm pIm pRm pRm) (fun z =>
      evS (A.withH z.1) idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameS A.base idx b) true true true true z.2)) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape SecM pIm pIm pRm pRm =>
      evS (A.withH z.1) idx b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameS A.base idx b) true true true true z.2))
  rw [c]
  refine abs_pr_prod_sub_le _ _ fun T => ?_
  have h := hiding_hopS23 (A.withH T) idx b (hhide T)
  rw [gameS_withH] at h
  exact h

/-- **After the hiding hop the worlds coincide**, at every table. -/
theorem idealH_eq :
    pr (H3T × ((HTape × (Coins nfBytes × Coins nfBytes)) × AuxS)) (fun z =>
        idealS23 (A.withH z.1) idx false z.2) =
      pr (H3T × ((HTape × (Coins nfBytes × Coins nfBytes)) × AuxS)) (fun z =>
        idealS23 (A.withH z.1) idx true z.2) := by
  rw [pr_prod, pr_prod, Finset.sum_congr rfl fun T _ => idealS23_eq (A.withH T) idx]

/-- **The bad event with one `H₃`** is the average over the table of the (PU) term of the guess
at that table. -/
theorem simAll_bstar_eq (b : Bool) :
    simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A.base idx b) (fun v T => bstar Hashes.shake (gameS A.base idx b)
          (fun v => r5H A idx b v T) v) =
      (∑ T : H3T, puTerm23 (A.withH T) idx b) / Fintype.card H3T := by
  have c : simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A.base idx b) (fun v T => bstar Hashes.shake (gameS A.base idx b)
          (fun v => r5H A idx b v T) v) =
      pr (H3T × GTape SecM pIm pIm pRm pRm) (fun z => bstar Hashes.shake (gameS A.base idx b)
        (fun v => r5H A idx b v z.1) (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343)
          (n₄ := 343) Hashes.shake (gameS A.base idx b) true true true true z.2)) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape SecM pIm pIm pRm pRm =>
      bstar Hashes.shake (gameS A.base idx b)
        (fun v => r5H A idx b v z.1) (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343)
          (n₄ := 343) Hashes.shake (gameS A.base idx b) true true true true z.2))
  have h : ∀ T : H3T, pr (GTape SecM pIm pIm pRm pRm) (fun x => bstar Hashes.shake
      (gameS A.base idx b) (fun v => r5H A idx b v T) (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256)
        (n₃ := 343) (n₄ := 343) Hashes.shake (gameS A.base idx b) true true true true x)) =
      puTerm23 (A.withH T) idx b := fun T => by
    unfold puTerm23
    rw [gameS_withH]
    rfl
  rw [c, pr_prod, Finset.sum_congr rfl fun T _ => h T]

/-- **(PU) of a predictor that draws the table itself** is the average over the table. -/
theorem puAdv_avgH {N R Tc Aux : Type*} [Fintype N] [Fintype R] [Fintype Aux] (com : N → R → Tc)
    (P : H3T → N → Tc → Aux → Finset R) :
    puAdv com (fun n t (a : Aux × H3T) => P a.2 n t a.1) =
      (∑ T : H3T, puAdv com (P T)) / Fintype.card H3T := by
  unfold puAdv
  let e : H3T × ((N × R) × Aux) ≃ (N × R) × (Aux × H3T) :=
    { toFun := fun z => (z.2.1, (z.2.2, z.1))
      invFun := fun z => (z.2.2, (z.1, z.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, pr_prod]
  rfl

/-- **The predictor for Client `false`'s opening in world `b`** with one `H₃`: it draws the table
and runs `predS23₀` for the guess at that table. -/
noncomputable def predH₀ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : ((Coins nfBytes × Coins rBytes) × AuxS) × H3T) : Finset (Coins rBytes) :=
  predS23₀ (A.withH a.2) idx b n t a.1

/-- **The predictor for Client `true`**. -/
noncomputable def predH₁ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : ((Coins nfBytes × Coins rBytes) × AuxS) × H3T) : Finset (Coins rBytes) :=
  predS23₁ (A.withH a.2) idx b n t a.1

/-- **The (PU) term with one `H₃`** is at most the advantage of the two explicit predictors, plus
`4·noHitProb` and `1875·2⁻¹²⁸`. -/
theorem simAll_bstar_le (b : Bool) :
    simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameS A.base idx b) (fun v T => bstar Hashes.shake (gameS A.base idx b)
          (fun v => r5H A idx b v T) v) ≤
      4 * noHitProb + puAdv (comM A.base.toM) (predH₀ A idx b) +
        puAdv (comM A.base.toM) (predH₁ A idx b) + 1875 / 2 ^ 128 := by
  have a0 : puAdv (comM A.base.toM) (predH₀ A idx b) =
      (∑ T : H3T, puAdv (comM A.base.toM) (predS23₀ (A.withH T) idx b)) / Fintype.card H3T :=
    puAdv_avgH (comM A.base.toM) (fun T => predS23₀ (A.withH T) idx b)
  have a1 : puAdv (comM A.base.toM) (predH₁ A idx b) =
      (∑ T : H3T, puAdv (comM A.base.toM) (predS23₁ (A.withH T) idx b)) / Fintype.card H3T :=
    puAdv_avgH (comM A.base.toM) (fun T => predS23₁ (A.withH T) idx b)
  rw [simAll_bstar_eq, a0, a1]
  have hc : (0 : ℝ) < Fintype.card H3T := by exact_mod_cast Fintype.card_pos
  have hs : ∑ T : H3T, puTerm23 (A.withH T) idx b ≤
      ∑ T : H3T, ((4 * noHitProb + 1875 / 2 ^ 128) + puAdv (comM A.base.toM)
        (predS23₀ (A.withH T) idx b) + puAdv (comM A.base.toM) (predS23₁ (A.withH T) idx b)) :=
    Finset.sum_le_sum fun T _ => by
      have := puTerm23_le (A.withH T) idx b
      have e : comM (A.withH T).toM = comM A.base.toM := rfl
      rw [e] at this
      linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  rw [div_le_iff₀ hc]
  have e2 : (4 * noHitProb + ((∑ T : H3T, puAdv (comM A.base.toM) (predS23₀ (A.withH T) idx b)) /
      Fintype.card H3T) + ((∑ T : H3T, puAdv (comM A.base.toM) (predS23₁ (A.withH T) idx b)) /
      Fintype.card H3T) + 1875 / 2 ^ 128) * Fintype.card H3T =
      Fintype.card H3T * (4 * noHitProb + 1875 / 2 ^ 128) +
        ∑ T : H3T, puAdv (comM A.base.toM) (predS23₀ (A.withH T) idx b) +
        ∑ T : H3T, puAdv (comM A.base.toM) (predS23₁ (A.withH T) idx b) := by
    field_simp
    ring
  rw [e2]
  exact hs

/-! ## Theorem 4(a) on `main` with all tables shared -/

/-- **Theorem 4(a) on `main` (no label rows) with one `H₃`, one `H₂³` table, one `H₅` table and
one cipher for the four proofs, with the (PU) advantage of explicit predictors.** For the
colluding adversary whose guess reads the one `H₃` at `q3` points, the cipher at `qE` keys and
`H₅` at the consistent read set `R5` (`AdversaryH.ConsH`),

    |Pr[world 0] − Pr[world 1]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
      + 15·(Σ_{b, c} puAdv Com (predH_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide + 2·2⁻¹²⁸,

`Δ23 = 2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸ + noHitProb + 3·2⁻¹⁰²⁴`, and `2·2⁻¹²⁸` the probability
that two proofs of a world have one prefix. Each predictor draws the table and runs
`predS23_c` (at most `2·(q5 + 1249)` candidates if `R5` has at most `q5` keys). -/
theorem anonymity_main_sharedAll {q3 qE : ℕ} (hC : A.ConsH q3 qE) {εhide : ℝ}
    (hhide : ∀ T b a, hidingAdv A.base.toM.int.ci A.base.toM.int.cr (redS23 (A.withH T) idx b a) ≤
      εhide) :
    |realH A idx false - realH A idx true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comM A.base.toM) (predH₀ A idx false) +
        puAdv (comM A.base.toM) (predH₁ A idx false) + puAdv (comM A.base.toM) (predH₀ A idx true) +
        puAdv (comM A.base.toM) (predH₁ A idx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide + 2 / 2 ^ 128 := by
  have r0 := real_sim_sharedAll A idx hC false
  have r1 := real_sim_sharedAll A idx hC true
  have c0 := pr_coll_le A idx false
  have c1 := pr_coll_le A idx true
  have p0 := simAll_bstar_le A idx false
  have p1 := simAll_bstar_le A idx true
  have h0 := hiding_hopH A idx false (fun T => hhide T false)
  have h1 := hiding_hopH A idx true (fun T => hhide T true)
  have e := idealH_eq A idx
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Moussaka
