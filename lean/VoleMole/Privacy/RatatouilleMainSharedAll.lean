import VoleMole.ZK.MainSharedAll
import VoleMole.Privacy.RatatouilleMainShared23

/-!
# Ratatouille unlinkability on `main`, with all tables shared

`unlinkability_main_shared23` (`Privacy/RatatouilleMainShared23.lean`) is Theorem 2 on `main` with
one `H₂³` table, one `H₅` table and one cipher for the four proofs; each proof keeps its own `H₃`
slice. Here the four proofs also **share `H₃`** (`ZK/MainSharedAll.lean`), and the Issuer's guess
sees the one table (`AdversaryRH`: it reads it at `q₃` points, not the per-proof slices).

## The game (`realRH`)

The game of `realSR23` (`gameSR`, the same interaction) run with `ZK.Sim.realAll`. At a fixed
table the guess is an `AdversarySR` (`withH`), so hiding, the coincidence of the worlds and the
(PU) predictors of `unlinkability_main_shared23` apply table by table.

## The bound (`unlinkability_main_sharedAll`)

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(PUH(b₁, b₂) + PUH(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide + 4·2⁻¹²⁸

* `4·2⁻¹²⁸`: in each world, two of the four proofs have one prefix (`realAll_close`); then two
  of the uniform openings agree (`coll_impR`: the two issued tokens', or the spent token's in
  round 1 and round 1's change token's), `2·2⁻¹²⁸` per world;
* `PUH(b₁, b₂)`: the three predictors of `unlinkability_main_shared23` for the guess at a uniform
  table that the predictor draws itself (`puAdv_avgH`).
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

/-! ## The Issuer with one `H₃` -/

/-- The guess's tables without the per-proof `H₃` slices (the shared game has none). -/
def clrSR (t : VisSR) : VisSR :=
  (t.1, ((fun _ => 0, t.2.1.2), (fun _ => 0, t.2.2.1.2), (fun _ => 0, t.2.2.2.1.2),
    (fun _ => 0, t.2.2.2.2.2)))

/-- **The malicious Issuer on `main` with one `H₃`**: `Adversary`'s interaction (not reading the
tables) and a guess that sees the shared tables and the one `H₃` table. -/
structure AdversaryRH where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr Sizes.main → Bool → Preimage
  d₁ : IssTr Sizes.main → Credits
  respond₁ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → SpendResponse
  d₂ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → Credits
  guess : GIn → VisSR → H3T → Prop
  R5 : GIn → VisSR → H3T → Finset (ZK.Sim.Bytes 37)

/-- **`f` reads the tables and the one `H₃` within explicit sets**: `H₅` at `R`, the cipher at
`qE` keys, `H₃` at `q3` points (prefix, `ρ`). -/
structure RdTHR {X : Sort*} (f : VisSR → H3T → X) (R : VisSR → H3T → Finset (ZK.Sim.Bytes 37))
    (q3 qE : ℕ) : Prop where
  h5 : ∀ t T (G5 : Tab5F), (∀ k ∈ R t T, t.1.1 k = G5 k) → f ((G5, t.1.2), t.2) T = f t T
  hE : ∃ Q : VisSR → H3T → Finset Blk, (∀ t T, (Q t T).card ≤ qE) ∧
    ∀ t T (E : Cipher), (∀ k ∈ Q t T, t.1.2 k = E k) → f ((t.1.1, E), t.2) T = f t T
  hT : ∃ Q : VisSR → H3T → Finset (Pre × ZK.Sim.Bytes 16), (∀ t T, (Q t T).card ≤ q3) ∧
    ∀ t T T', (∀ k ∈ Q t T, T k.1 k.2 = T' k.1 k.2) → f t T' = f t T

namespace AdversaryRH

variable (A : AdversaryRH)

/-- **The Issuer at one `H₃` table**: an `AdversarySR` whose guess sees `T` and not the
per-proof slices. -/
def withH (T : H3T) : AdversarySR :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂,
    fun g t => A.guess g (clrSR t) T, fun g t => A.R5 g (clrSR t) T⟩

/-- Its interaction, at any table. -/
def base : AdversarySR := A.withH fun _ _ => 0

/-- **Consistent reads**: with its input fixed, the guess and its `H₅` read set read `H₃` at
`q3` points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ y, RdTHR (A.guess y) (A.R5 y) q3 qE
  r : ∀ y, RdTHR (A.R5 y) (A.R5 y) q3 qE

end AdversaryRH

variable (A : AdversaryRH)

lemma gameSR_withH (T : H3T) (b₁ b₂ : Bool) : gameSR (A.withH T) b₁ b₂ = gameSR A.base b₁ b₂ := rfl

/-- **The final event of world `(b₁, b₂)`**, on the view and the one `H₃`. -/
def evRH (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr) (T : H3T) : Prop :=
  evSR (A.withH T) b₁ b₂ v

/-- Its `H₅` read set. -/
def r5RH (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr) (T : H3T) : Finset (ZK.Sim.Bytes 37) :=
  r5SR (A.withH T) b₁ b₂ v

/-- **The real game on `main` with all tables shared** in world `(b₁, b₂)`: the four proofs read
one `H₃`, one `H₂³` table, one `H₅` table and one cipher. -/
noncomputable def realRH (b₁ b₂ : Bool) : ℝ :=
  realAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
    (gameSR A.base b₁ b₂) (evRH A b₁ b₂)

/-- The game with all proofs simulated, one `H₃` (read by the guess only). -/
noncomputable def simRH (b₁ b₂ : Bool) : ℝ :=
  simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
    (gameSR A.base b₁ b₂) (evRH A b₁ b₂)

/-! ## The hypotheses of the joint hop -/

lemma rdHR_of {X : Sort*} {f : GIn → VisSR → H3T → X} {R : GIn → VisSR → H3T → Finset (ZK.Sim.Bytes 37)}
    {q3 qE : ℕ} (h : ∀ y, RdTHR (f y) (R y) q3 qE) (b₁ b₂ : Bool) :
    RdH (fun (v : GView SecR pIr pIr pSr pSr) T => f (keyMS A.base b₁ b₂ v) (clrSR v.vis) T)
      (fun v T => R (keyMS A.base b₁ b₂ v) (clrSR v.vis) T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  refine ⟨fun v T G5 hk => (h _).h5 (clrSR v.vis) T G5 hk,
    ⟨fun v T => QE (keyMS A.base b₁ b₂ v) (clrSR v.vis) T, fun _ _ => hQEc _ _ _,
      fun v T E hk => hQE _ (clrSR v.vis) T E hk⟩,
    ⟨fun v T => QT (keyMS A.base b₁ b₂ v) (clrSR v.vis) T, fun _ _ => hQTc _ _ _,
      fun v T T' hk => hQT _ (clrSR v.vis) T T' hk⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

lemma rdH_evRH {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b₁ b₂ : Bool) :
    RdH (evRH A b₁ b₂) (r5RH A b₁ b₂) q3 qE :=
  rdHR_of A (f := fun y t T => A.guess y t T) (R := fun y t T => A.R5 y t T) hC.g b₁ b₂

lemma rdH_r5RH {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b₁ b₂ : Bool) :
    RdH (r5RH A b₁ b₂) (r5RH A b₁ b₂) q3 qE :=
  rdHR_of A (f := fun y t T => A.R5 y t T) (R := fun y t T => A.R5 y t T) hC.r b₁ b₂

/-- **The joint hop in each world** with one `H₃`. -/
theorem real_sim_sharedAllR {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b₁ b₂ : Bool) :
    |realRH A b₁ b₂ - simRH A b₁ b₂| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
          (gameSR A.base b₁ b₂) (fun v T => bstar Hashes.shake (gameSR A.base b₁ b₂)
            (fun v => r5RH A b₁ b₂ v T) v) +
        pr (GTape SecR pIr pIr pSr pSr) (fun x => ¬ DistV Hashes.shake (gameSR A.base b₁ b₂)
          (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
            (gameSR A.base b₁ b₂) false false false false x)) :=
  main_sharedAll_le (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
    (gameSR A.base b₁ b₂) mainP_pIr mainP_pIr mainP_pSr mainP_pSr small_pIr small_pIr small_pSr
    small_pSr hashesWF_shake (gvalidSR A.base b₁ b₂) (evRH A b₁ b₂) (r5RH A b₁ b₂)
    (rdH_evRH A hC b₁ b₂) (rdH_r5RH A hC b₁ b₂)

/-! ## Two proofs with one prefix -/

section Coll

variable (B : AdversaryRM)

lemma issStmtR_wit (x : Coins 24 × Coins 16) :
    ∀ y ∈ issStmtR B x, y.2.size = 240 ∧ wPre y.2 = x.2 := by
  intro y hy
  refine ⟨?_, (issStmtR_pub B x).2 y hy⟩
  unfold issStmtR at hy
  split_ifs at hy
  · cases hy
  · cases hy
    show (encI _ _).size = _
    rw [encI, size_toBA, length_encodeIssueWitness]

lemma spStmt_size (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) :
    ∀ y ∈ spStmt B τ d x, y.2.size = 847 := by
  intro y hy
  unfold spStmt at hy
  split_ifs at hy
  · split at hy
    · cases hy
    · cases hy
      show (encS _ _).size = _
      rw [encS, size_toBA, length_encodeSpendWitness]
  · cases hy

/-- **Round 1's spend statement**: `847` witness bytes starting with Client `b₁`'s opening. -/
lemma σ₃R_wit (b₁ : Bool) (s : SecR) (o₁ o₂ : Option Out) (d : Credits) (y : SW)
    (hy : y ∈ (bif ok₁ₘ B s o₁ o₂ then spStmt B (τ₁ₘ B b₁ s o₁ o₂) d s.2.1 else none)) :
    y.2.size = 847 ∧ wPre y.2 = rIss s b₁ := by
  cases h : ok₁ₘ B s o₁ o₂
  · rw [h] at hy; cases hy
  · rw [h] at hy
    exact ⟨spStmt_size B _ _ _ y hy, (spStmt_pub B _ _ _).2 y hy _ (τ₁ₘ_r B b₁ s o₁ o₂ h)⟩

/-- **Round 2's spend statement**: `847` witness bytes starting with the opening of round 1's
change token (`b₂ = b₁`) or of Client `!b₁`'s issued token. -/
lemma σ₄R_wit (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) (d : Credits) (y : SW)
    (hy : y ∈ (bif ok₁ₘ B s o₁ o₂ && ok₂ₘ B b₁ s o₁ o₂ o₃ then
      spStmt B (τ₂ₘ B b₁ b₂ s o₁ o₂ o₃) d s.2.2 else none)) :
    y.2.size = 847 ∧ wPre y.2 = bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁) := by
  cases h : ok₁ₘ B s o₁ o₂ && ok₂ₘ B b₁ s o₁ o₂ o₃
  · rw [h] at hy; cases hy
  · rw [h] at hy
    rw [Bool.and_eq_true] at h
    exact ⟨spStmt_size B _ _ _ y hy,
      (spStmt_pub B _ _ _).2 y hy _ (τ₂ₘ_r B b₁ b₂ s o₁ o₂ o₃ h.1 h.2)⟩

/-- **Two proofs of a world with one prefix**: then the two issued tokens' openings agree, or
round 1's spent token's and round 1's change token's (issuance and spend witnesses have different
lengths, and each starts with its token's opening). -/
theorem coll_impR (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr)
    (h : ¬ DistV Hashes.shake (gameSR A.base b₁ b₂) v) :
    v.s.1.1.2 = v.s.1.2.2 ∨ rIss v.s b₁ = v.s.2.1.2 := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨n₁, n₂⟩ := hne
  have i₁ : ∀ y ∈ yv₁ (gameSR A.base b₁ b₂) v, y.2.size = pIr.witnessBytes ∧ wPre y.2 = v.s.1.1.2 :=
    issStmtR_wit _ _
  have i₂ : ∀ y ∈ yv₂ (gameSR A.base b₁ b₂) v, y.2.size = pIr.witnessBytes ∧ wPre y.2 = v.s.1.2.2 :=
    issStmtR_wit _ _
  have r₃ : ∀ y ∈ yv₃ (gameSR A.base b₁ b₂) v, y.2.size = pSr.witnessBytes ∧
      wPre y.2 = rIss v.s b₁ :=
    fun y hy => σ₃R_wit A.base.toM b₁ v.s v.o₁ v.o₂ _ y hy
  have r₄ : ∀ y ∈ yv₄ (gameSR A.base b₁ b₂) v, y.2.size = pSr.witnessBytes ∧
      wPre y.2 = bif b₂ == b₁ then v.s.2.1.2 else rIss v.s (!b₁) :=
    fun y hy => σ₄R_wit A.base.toM b₁ b₂ v.s v.o₁ v.o₂ v.o₃ _ y hy
  have h16 : 16 ≤ pIr.witnessBytes := by decide
  have h16' : 16 ≤ pSr.witnessBytes := by decide
  have mI : pIr.witnessBytes + 32 < preMax := by decide
  have mS : pSr.witnessBytes + 32 < preMax := by decide
  have ne : pIr.witnessBytes ≠ pSr.witnessBytes := by decide
  apply h
  refine ⟨distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (i₂ y hy).1) h16 mI mI
      fun y hy y' hy' _ => by rw [(i₁ y hy).2, (i₂ y' hy').2]; exact n₁,
    distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (r₃ y hy).1) h16 mI mS
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₁ y hy).1) (fun y hy => (r₄ y hy).1) h16 mI mS
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₂ y hy).1) (fun y hy => (r₃ y hy).1) h16 mI mS
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (i₂ y hy).1) (fun y hy => (r₄ y hy).1) h16 mI mS
      fun _ _ _ _ he => absurd he ne,
    distO_of hashesWF_shake (fun y hy => (r₃ y hy).1) (fun y hy => (r₄ y hy).1) h16' mS mS
      fun y hy y' hy' _ => by
        rw [(r₃ y hy).2, (r₄ y' hy').2]
        cases hb : b₂ == b₁
        · cases b₁
          · exact n₁
          · exact Ne.symm n₁
        · exact n₂⟩

/-- **The prefix-collision term is at most `2·2⁻¹²⁸`**: two of the uniform openings agree. -/
theorem pr_collR_le (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (fun x => ¬ DistV Hashes.shake (gameSR A.base b₁ b₂)
      (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
        (gameSR A.base b₁ b₂) false false false false x)) ≤ 2 / 2 ^ 128 := by
  refine (pr_mono fun x hx => coll_impR A b₁ b₂ _ hx).trans ?_
  refine (pr_or_le _ _).trans ?_
  have e1 := pr_prod_fst (β := USh × KS pIr × KS pIr × KS pSr × KS pSr)
    (fun s : SecR => s.1.1.2 = s.1.2.2)
  have e2 := pr_prod_fst (β := USh × KS pIr × KS pIr × KS pSr × KS pSr)
    (fun s : SecR => rIss s b₁ = s.2.1.2)
  refine (add_le_add (le_of_eq e1) (le_of_eq e2)).trans ?_
  let f1 : Coins 16 × ((Coins 24 × (Coins 24 × Coins 16)) × ((Coins 24 × Coins 16) ×
      (Coins 24 × Coins 16))) ≃ SecR :=
    { toFun := fun z => (((z.2.1.1, z.1), z.2.1.2), z.2.2)
      invFun := fun s => (s.1.1.2, ((s.1.1.1, s.1.2), s.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f2 : Coins 16 × (((Coins 24 × Coins 16) × (Coins 24 × Coins 16)) × (Coins 24 ×
      (Coins 24 × Coins 16))) ≃ SecR :=
    { toFun := fun z => (z.2.1, ((z.2.2.1, z.1), z.2.2.2))
      invFun := fun s => (s.2.1.2, (s.1, (s.2.1.1, s.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv f1, ← pr_equiv f2]
  have a1 := pr_mem_uniform_le (X := (Coins 24 × (Coins 24 × Coins 16)) × ((Coins 24 × Coins 16) ×
    (Coins 24 × Coins 16))) (fun z => {z.1.2.2}) (q := 0) (fun _ => by simp)
  have a2 := pr_mem_uniform_le (X := ((Coins 24 × Coins 16) × (Coins 24 × Coins 16)) × (Coins 24 ×
    (Coins 24 × Coins 16))) (fun z => {(bif b₁ then z.1.2 else z.1.1).2}) (q := 0)
    (fun _ => by simp)
  have q1 : pr (Coins 16 × ((Coins 24 × (Coins 24 × Coins 16)) × ((Coins 24 × Coins 16) ×
      (Coins 24 × Coins 16)))) (fun z => (f1 z).1.1.2 = (f1 z).1.2.2) =
      pr (ZK.Sim.Bytes 16 × ((Coins 24 × (Coins 24 × Coins 16)) × ((Coins 24 × Coins 16) ×
      (Coins 24 × Coins 16)))) (fun z => z.1 ∈ ({z.2.1.2.2} : Finset (ZK.Sim.Bytes 16))) :=
    pr_congr fun z => by simp [f1]
  have q2 : pr (Coins 16 × (((Coins 24 × Coins 16) × (Coins 24 × Coins 16)) × (Coins 24 ×
      (Coins 24 × Coins 16)))) (fun z => rIss (f2 z) b₁ = (f2 z).2.1.2) =
      pr (ZK.Sim.Bytes 16 × (((Coins 24 × Coins 16) × (Coins 24 × Coins 16)) × (Coins 24 ×
      (Coins 24 × Coins 16)))) (fun z => z.1 ∈ ({(bif b₁ then z.2.1.2 else z.2.1.1).2} :
        Finset (ZK.Sim.Bytes 16))) :=
    pr_congr fun z => by simp [f2, rIss, eq_comm]
  rw [q1, q2]
  have : ((0 : ℕ) + 1 : ℝ) / 2 ^ 128 + ((0 : ℕ) + 1 : ℝ) / 2 ^ 128 = 2 / 2 ^ 128 := by norm_num
  linarith

end Coll

/-! ## With all proofs simulated: table by table -/

/-- **The hiding hop** with one `H₃`: at every table the hop of `hiding_hopSR23`. -/
theorem hiding_hopRH (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ T a, hidingAdv A.ctx (redSR23 (A.withH T) b₁ b₂ a) ≤ εhide) :
    |simRH A b₁ b₂ - pr (H3T × (UTape × AuxSR)) (fun z => idealSR23 (A.withH z.1) b₁ b₂ z.2)| ≤
      εhide := by
  have c : simRH A b₁ b₂ = pr (H3T × GTape SecR pIr pIr pSr pSr) (fun z =>
      evSR (A.withH z.1) b₁ b₂ (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847)
        Hashes.shake (gameSR A.base b₁ b₂) true true true true z.2)) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape SecR pIr pIr pSr pSr =>
      evSR (A.withH z.1) b₁ b₂ (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847)
        Hashes.shake (gameSR A.base b₁ b₂) true true true true z.2))
  rw [c]
  refine abs_pr_prod_sub_le _ _ fun T => ?_
  have h := hiding_hopSR23 (A.withH T) b₁ b₂ (hhide T)
  rw [gameSR_withH] at h
  exact h

/-- **After the hiding hop the four worlds coincide**, at every table. -/
theorem idealRH_eq (b₁ b₂ : Bool) :
    pr (H3T × (UTape × AuxSR)) (fun z => idealSR23 (A.withH z.1) b₁ b₂ z.2) =
      pr (H3T × (UTape × AuxSR)) (fun z => idealSR23 (A.withH z.1) false false z.2) := by
  rw [pr_prod, pr_prod, Finset.sum_congr rfl fun T _ => idealSR23_eq (A.withH T) b₁ b₂]

/-- **The bad event with one `H₃`** is the average over the table of the (PU) term of the guess
at that table. -/
theorem simAll_bstar_eqR (b₁ b₂ : Bool) :
    simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
        (gameSR A.base b₁ b₂) (fun v T => bstar Hashes.shake (gameSR A.base b₁ b₂)
          (fun v => r5RH A b₁ b₂ v T) v) =
      (∑ T : H3T, puTermSR23 (A.withH T) b₁ b₂) / Fintype.card H3T := by
  have c : simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
        (gameSR A.base b₁ b₂) (fun v T => bstar Hashes.shake (gameSR A.base b₁ b₂)
          (fun v => r5RH A b₁ b₂ v T) v) =
      pr (H3T × GTape SecR pIr pIr pSr pSr) (fun z => bstar Hashes.shake (gameSR A.base b₁ b₂)
        (fun v => r5RH A b₁ b₂ v z.1) (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847)
          (n₄ := 847) Hashes.shake (gameSR A.base b₁ b₂) true true true true z.2)) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape SecR pIr pIr pSr pSr =>
      bstar Hashes.shake (gameSR A.base b₁ b₂)
        (fun v => r5RH A b₁ b₂ v z.1) (hybV23 (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847)
          (n₄ := 847) Hashes.shake (gameSR A.base b₁ b₂) true true true true z.2))
  have h : ∀ T : H3T, pr (GTape SecR pIr pIr pSr pSr) (fun x => bstar Hashes.shake
      (gameSR A.base b₁ b₂) (fun v => r5RH A b₁ b₂ v T) (hybV23 (p₀ := pIr) (n₁ := 240)
        (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake (gameSR A.base b₁ b₂) true true true true
          x)) = puTermSR23 (A.withH T) b₁ b₂ := fun T => by
    unfold puTermSR23
    rw [gameSR_withH]
    rfl
  rw [c, pr_prod, Finset.sum_congr rfl fun T _ => h T]

/-- **The predictor for Client `false`'s issued token** with one `H₃`: it draws the table and runs
`predSR23₀` for the guess at that table. -/
noncomputable def predHR₀ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ×
      H3T) : Finset (Coins 16) :=
  predSR23₀ (A.withH a.2) b₁ b₂ n t a.1

/-- **The predictor for Client `true`'s issued token.** -/
noncomputable def predHR₁ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ×
      H3T) : Finset (Coins 16) :=
  predSR23₁ (A.withH a.2) b₁ b₂ n t a.1

/-- **The predictor for round 1's change token.** -/
noncomputable def predHRC (b₁ b₂ : Bool) (n : Coins 24 × BCh) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × AuxCS) × H3T) : Finset (Coins 16) :=
  predSRC23 (A.withH a.2) b₁ b₂ n t a.1

/-- **The (PU) term with one `H₃`** is at most the advantage of the three explicit predictors,
plus `4·noHitProb` and `1875·2⁻¹²⁸`. -/
theorem simAll_bstar_leR (b₁ b₂ : Bool) :
    simAll (p₀ := pIr) (n₁ := 240) (n₂ := 240) (n₃ := 847) (n₄ := 847) Hashes.shake
        (gameSR A.base b₁ b₂) (fun v T => bstar Hashes.shake (gameSR A.base b₁ b₂)
          (fun v => r5RH A b₁ b₂ v T) v) ≤
      4 * noHitProb + puAdv (comI A.base.toM) (predHR₀ A b₁ b₂) +
        puAdv (comI A.base.toM) (predHR₁ A b₁ b₂) +
        puAdv (comCh A.base.toM b₁) (predHRC A b₁ b₂) + 1875 / 2 ^ 128 := by
  have a0 : puAdv (comI A.base.toM) (predHR₀ A b₁ b₂) =
      (∑ T : H3T, puAdv (comI A.base.toM) (predSR23₀ (A.withH T) b₁ b₂)) / Fintype.card H3T :=
    puAdv_avgH (comI A.base.toM) (fun T => predSR23₀ (A.withH T) b₁ b₂)
  have a1 : puAdv (comI A.base.toM) (predHR₁ A b₁ b₂) =
      (∑ T : H3T, puAdv (comI A.base.toM) (predSR23₁ (A.withH T) b₁ b₂)) / Fintype.card H3T :=
    puAdv_avgH (comI A.base.toM) (fun T => predSR23₁ (A.withH T) b₁ b₂)
  have a2 : puAdv (comCh A.base.toM b₁) (predHRC A b₁ b₂) =
      (∑ T : H3T, puAdv (comCh A.base.toM b₁) (predSRC23 (A.withH T) b₁ b₂)) /
        Fintype.card H3T :=
    puAdv_avgH (comCh A.base.toM b₁) (fun T => predSRC23 (A.withH T) b₁ b₂)
  rw [simAll_bstar_eqR, a0, a1, a2]
  have hc : (0 : ℝ) < Fintype.card H3T := by exact_mod_cast Fintype.card_pos
  have hs : ∑ T : H3T, puTermSR23 (A.withH T) b₁ b₂ ≤
      ∑ T : H3T, ((4 * noHitProb + 1875 / 2 ^ 128) +
        puAdv (comI A.base.toM) (predSR23₀ (A.withH T) b₁ b₂) +
        puAdv (comI A.base.toM) (predSR23₁ (A.withH T) b₁ b₂) +
        puAdv (comCh A.base.toM b₁) (predSRC23 (A.withH T) b₁ b₂)) :=
    Finset.sum_le_sum fun T _ => by
      have := puTermSR23_le (A.withH T) b₁ b₂
      have e : comI (A.withH T).toM = comI A.base.toM := rfl
      have e' : comCh (A.withH T).toM b₁ = comCh A.base.toM b₁ := rfl
      rw [e, e'] at this
      linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  rw [div_le_iff₀ hc]
  have e2 : (4 * noHitProb +
      ((∑ T : H3T, puAdv (comI A.base.toM) (predSR23₀ (A.withH T) b₁ b₂)) / Fintype.card H3T) +
      ((∑ T : H3T, puAdv (comI A.base.toM) (predSR23₁ (A.withH T) b₁ b₂)) / Fintype.card H3T) +
      ((∑ T : H3T, puAdv (comCh A.base.toM b₁) (predSRC23 (A.withH T) b₁ b₂)) /
        Fintype.card H3T) + 1875 / 2 ^ 128) * Fintype.card H3T =
      Fintype.card H3T * (4 * noHitProb + 1875 / 2 ^ 128) +
        ∑ T : H3T, puAdv (comI A.base.toM) (predSR23₀ (A.withH T) b₁ b₂) +
        ∑ T : H3T, puAdv (comI A.base.toM) (predSR23₁ (A.withH T) b₁ b₂) +
        ∑ T : H3T, puAdv (comCh A.base.toM b₁) (predSRC23 (A.withH T) b₁ b₂) := by
    field_simp
    ring
  rw [e2]
  exact hs

/-! ## Theorem 2 on `main` with all tables shared -/

/-- **Theorem 2 on `main` (no label rows) with one `H₃`, one `H₂³` table, one `H₅` table and one
cipher for the four proofs, with the (PU) advantage of explicit predictors.** For the malicious
Issuer whose guess reads the one `H₃` at `q3` points, the cipher at `qE` keys and `H₅` at the
consistent read set `R5` (`AdversaryRH.ConsH`), any two worlds differ by at most

    30·(εS(q3, qE + 8·4607) + Δ23) + 15·(PUH(b₁, b₂) + PUH(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸)
      + 2·εhide + 4·2⁻¹²⁸,

`PUH(b₁, b₂)` the (PU) advantages of the three predictors `predHR₀`, `predHR₁` (`comI`) and
`predHRC` (`comCh`), each drawing the table and running the predictor of
`unlinkability_main_shared23` for the guess at that table, and `4·2⁻¹²⁸` the probability that two
proofs of a world have one prefix (`2·2⁻¹²⁸` per world). -/
theorem unlinkability_main_sharedAll {q3 qE : ℕ} (hC : A.ConsH q3 qE) {εhide : ℝ}
    (hhide : ∀ T b₁ b₂ a, hidingAdv A.ctx (redSR23 (A.withH T) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |realRH A b₁ b₂ - realRH A b₁' b₂'| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comI A.base.toM) (predHR₀ A b₁ b₂) +
        puAdv (comI A.base.toM) (predHR₁ A b₁ b₂) + puAdv (comCh A.base.toM b₁) (predHRC A b₁ b₂) +
        (puAdv (comI A.base.toM) (predHR₀ A b₁' b₂') + puAdv (comI A.base.toM) (predHR₁ A b₁' b₂') +
        puAdv (comCh A.base.toM b₁') (predHRC A b₁' b₂')) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide + 4 / 2 ^ 128 := by
  have r0 := real_sim_sharedAllR A hC b₁ b₂
  have r1 := real_sim_sharedAllR A hC b₁' b₂'
  have c0 := pr_collR_le A b₁ b₂
  have c1 := pr_collR_le A b₁' b₂'
  have p0 := simAll_bstar_leR A b₁ b₂
  have p1 := simAll_bstar_leR A b₁' b₂'
  have h0 := hiding_hopRH A b₁ b₂ (fun T => hhide T b₁ b₂)
  have h1 := hiding_hopRH A b₁' b₂' (fun T => hhide T b₁' b₂')
  have e0 := idealRH_eq A b₁ b₂
  have e1 := idealRH_eq A b₁' b₂'
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Ratatouille
