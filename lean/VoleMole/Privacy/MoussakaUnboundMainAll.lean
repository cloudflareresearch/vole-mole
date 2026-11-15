import VoleMole.Privacy.MoussakaUnboundNCMainAll
import VoleMole.Privacy.MoussakaUnboundMainPU

/-!
# Unbound Moussaka issuer hiding and unlinkability on `main` (Theorem U5(a)), all tables shared

`anonymityU_main_pu` (`Privacy/MoussakaUnboundMainPU.lean`) is Theorem U5(a) on `main` with two
redemption queries and **per-proof** tables. Here the four proofs share all tables, as in the
scheme and as in the bound protocol's `anonymity_main_sharedAll`
(`Privacy/MoussakaMainSharedAll.lean`): one `H₃`, one `H₂³` table, one `H₅` table and one cipher.
The joint hop is `ZK.Sim.main_sharedAll_le`.

## The game (`realUH`)

The colluding adversary of `MoussakaUnbound.Adversary 2` (`AdversaryUH`: `ctx_iss`, the keys, the
responses and the two queries chosen from the issuance requests, not reading the tables); its
guess sees the requests, the redemptions (if the game's rule lets them happen), the shared `H₅`
table and cipher, the one `H₂³` table and `H₃`. Four slots: the two issuance proofs, and the two
redemption proofs, computed only if the rule (`allOk`) holds (they are never shown otherwise, and
a simulated one would program the shared table).

## The steps

1. The joint hop (`real_sim_UH`), with the prefix-collision term `collUH b` (the two issuance
   witnesses start with the two openings; issuance and redemption witnesses have different
   lengths; for two redemptions see `Privacy/MoussakaUnboundNCMainAll.lean`): `collUH b ≤ 2⁻¹²⁸`
   when the two queries are answered by different Clients (`collUH_le_of_who`).
2. **With all proofs simulated, the guess's input is the per-proof game's** and the `H₂³` table is
   a function of it (`tabA`: the issuance statements from the requests' commitments, the
   redemption statements from the answers), so the event is `MoussakaUnbound.reduction` for the
   adversary `atZ z` that programs the table itself from the rest `z` of the tape
   (`simUH_iff`).
3. The PRF hop (`prf_hop_UH`) and the swap of `MoussakaUnbound.idealGame_eq`, at every rest of the
   tape (`idealUH_eq`).
4. The (PU) term (`pr_bstarUH_le`): a failed simulation (`4·noHitProb`), a collision of two
   simulated proofs' sibling inputs (`1875·2⁻¹²⁸`, `pr_sib_hit_le`), or a prediction of an
   opening: the game `PU.puAdv` for `UCom` with the predictors `predUH_c b` (public part
   `nf_key`), which output the candidates of the four proofs for the public key set.

## The bound (`anonymityU_main_sharedAll`)

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(Σ_{b,c} puAdv UCom (predUH_c b) + 8·noHitProb + 3750·2⁻¹²⁸)
        + collUH 0 + collUH 1 + 2·εprf
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf pgP simSB_pg_eq)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## The colluding adversary with all tables shared -/

/-- What the guess sees besides the tables: the two requests and the redemptions. -/
abbrev KeyU := Bytes × Bytes × Option (Fin 2 → Except Error Bytes)

/-- **The colluding adversary on `main` with all tables shared**: `Adversary 2`'s interaction (not
reading the tables) and a guess that also sees the shared `H₅` table and cipher, the one `H₂³`
table and `H₃`, with its `H₅` read set. -/
structure AdversaryUH where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  queries : Bytes → Bytes → Fin 2 → Query
  guess : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → USh → Tab2G pIu → H3T → Prop
  R5 : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → USh → Tab2G pIu → H3T →
    Finset (ZK.Sim.Bytes 37)

namespace AdversaryUH

variable (A : AdversaryUH)

/-- Its interaction as an `AdversaryUM` (for `main`'s statements and outputs; the guess and the
read sets are not used). -/
def um : AdversaryUM :=
  ⟨A.ctxIss, A.pk, A.respond, A.queries, fun _ _ _ _ => True, fun _ _ _ _ => ∅,
    fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

/-- **Consistent reads**: with the requests and the redemptions fixed, the guess and its `H₅` read
set read `H₃` at `q3` points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ q₀ q₁ y, RdUH (A.guess q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE
  r : ∀ q₀ q₁ y, RdUH (A.R5 q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE

end AdversaryUH

/-- The view of the shared game. -/
abbrev GVA := GView SecU pIu pIu pRu pRu

/-- The tape of the shared game. -/
abbrev TapeA := GTape SecU pIu pIu pRu pRu

section GameA

variable (A : AdversaryUH)

/-- **The game of world `b`**: the two issuance proofs, and the two redemption proofs if the
game's rule lets the redemptions happen. -/
def gameUH (b : Bool) : Game SecU Out SW SW SW SW where
  σ₁ s := some (issStmtU A.um s false)
  σ₂ s _ := some (issStmtU A.um s true)
  σ₃ s o₁ o₂ := bif allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂) then
    redStmtU A.um (ptU A.um b s o₁ o₂ 0) else none
  σ₄ s o₁ o₂ _ := bif allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂) then
    redStmtU A.um (ptU A.um b s o₁ o₂ 1) else none

/-- What the guess gets besides the tables. -/
def keyUH (b : Bool) (v : GVA) : KeyU :=
  ((issU A.um v.s false v.o₁).2, (issU A.um v.s true v.o₂).2, yU A.um b v.s v.o₁ v.o₂ v.o₃ v.o₄)

/-- **The final event of world `b`**. -/
def evUH (b : Bool) (v : GVA) (T : H3T) : Prop :=
  A.guess (keyUH A b v).1 (keyUH A b v).2.1 (keyUH A b v).2.2 v.u v.v₁.2 T

/-- Its `H₅` read set. -/
def r5UH (b : Bool) (v : GVA) (T : H3T) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyUH A b v).1 (keyUH A b v).2.1 (keyUH A b v).2.2 v.u v.v₁.2 T

/-- **The real game on `main` with all tables shared** in world `b`. -/
noncomputable def realUH (b : Bool) : ℝ :=
  realAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameUH A b) (evUH A b)

/-- The game with all proofs simulated. -/
noncomputable def simUH (b : Bool) : ℝ :=
  simAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameUH A b) (evUH A b)

/-- **The prefix-collision term of world `b`**: two of the four real proofs have one prefix. -/
noncomputable def collUH (b : Bool) : ℝ :=
  pr TapeA (fun x => ¬ DistV Hashes.shake (gameUH A b)
    (hybV23 (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
      (gameUH A b) false false false false x))

/-! ### The hypotheses of the joint hop -/

lemma gvalidUH (b : Bool) : GValid (gameUH A b) pIu pIu pRu pRu where
  v₁ s y hy := by cases hy; exact issStmtU_valid A.um s false
  v₂ s _ y hy := by cases hy; exact issStmtU_valid A.um s true
  v₃ s o₁ o₂ y hy := by
    have hy' : y ∈ (bif allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂) then
      redStmtU A.um (ptU A.um b s o₁ o₂ 0) else none) := hy
    cases h : allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂)
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact ptU_valid A.um b s o₁ o₂ 0 y hy'
  v₄ s o₁ o₂ _ y hy := by
    have hy' : y ∈ (bif allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂) then
      redStmtU A.um (ptU A.um b s o₁ o₂ 1) else none) := hy
    cases h : allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂)
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact ptU_valid A.um b s o₁ o₂ 1 y hy'

lemma rdH_ofUH {X : Sort*} {f : KeyU → USh → Tab2G pIu → H3T → X}
    {R : KeyU → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)} {q3 qE : ℕ}
    (h : ∀ y, RdUH (f y) (R y) q3 qE) (b : Bool) :
    RdH (fun (v : GVA) T => f (keyUH A b v) v.u v.v₁.2 T)
      (fun v T => R (keyUH A b v) v.u v.v₁.2 T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  refine ⟨fun v T G5 hk => (h _).h5 v.u v.v₁.2 T G5 hk,
    ⟨fun v T => QE (keyUH A b v) v.u v.v₁.2 T, fun _ _ => hQEc _ _ _ _,
      fun v T E hk => hQE _ v.u v.v₁.2 T E hk⟩,
    ⟨fun v T => QT (keyUH A b v) v.u v.v₁.2 T, fun _ _ => hQTc _ _ _ _,
      fun v T T' hk => hQT _ v.u v.v₁.2 T T' hk⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The joint hop in each world**, the four proofs at once, all tables shared. -/
theorem real_sim_UH {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b : Bool) :
    |realUH A b - simUH A b| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * simAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
          (gameUH A b) (fun v T => bstar Hashes.shake (gameUH A b)
            (fun v => r5UH A b v T) v) + collUH A b :=
  main_sharedAll_le (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameUH A b) mainP_pIu mainP_pIu mainP_pRu mainP_pRu small_pIu small_pIu small_pRu
    small_pRu hashesWF_shake (gvalidUH A b) (evUH A b) (r5UH A b)
    (rdH_ofUH A (f := fun y u G2 T => A.guess y.1 y.2.1 y.2.2 u G2 T)
      (R := fun y u G2 T => A.R5 y.1 y.2.1 y.2.2 u G2 T) (fun y => hC.g y.1 y.2.1 y.2.2) b)
    (rdH_ofUH A (f := fun y u G2 T => A.R5 y.1 y.2.1 y.2.2 u G2 T)
      (R := fun y u G2 T => A.R5 y.1 y.2.1 y.2.2 u G2 T) (fun y => hC.r y.1 y.2.1 y.2.2) b)

end GameA

/-! ## Two proofs with one prefix -/

section CollA

variable {A : AdversaryUH}

lemma issStmtU_size (B : AdversaryUM) (s : SecU) (c : Bool) :
    (issStmtU B s c).2.size = pIu.witnessBytes := by
  show (toBA _).size = _
  rw [size_toBA]
  exact length_encodeIssueWitness (by simp [nfKeyBytes]) (by simp [rBytes])

/-- A redemption statement of the game: its witness has `559` bytes and starts with the opening of
the Client that answers the query. -/
lemma σUH_wit (b : Bool) (s : SecU) (o₁ o₂ : Option Out) (j : Fin 2) (y : SW)
    (hy : y ∈ (bif allOk A.um.int (issU A.um s false o₁) (issU A.um s true o₂) then
      redStmtU A.um (ptU A.um b s o₁ o₂ j) else none)) :
    y.2.size = pRu.witnessBytes ∧ wPre y.2 = rOfU s (who b (A.queries (issU A.um s false o₁).2
      (issU A.um s true o₂).2 j)) := by
  set i₀ := issU A.um s false o₁
  set i₁ := issU A.um s true o₂
  set c := who b (A.queries i₀.2 i₁.2 j)
  cases hok : allOk A.um.int i₀ i₁
  · rw [hok] at hy; cases hy
  rw [hok] at hy
  have hy' : redStmtU A.um (ptU A.um b s o₁ o₂ j) = some y := hy
  have hs : (tok A.um.int i₀ i₁ c).isSome = true := by
    unfold allOk at hok
    simp only [Bool.and_eq_true] at hok
    cases c
    · exact hok.1.1.1
    · exact hok.1.1.2
  have hf : finT A.um.int i₀.2 i₁.2 i₀.1.t i₁.1.t c = true := by
    rw [tok_of_fin] at hs
    by_contra h
    simp [h] at hs
  have htok : tokD A.um.int i₀ i₁ c = ⟨kOfU s c, List.ofFn (rOfU s c), resp A.um.int i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A.um.int i₀ i₁ c]
    simp only [hf, ↓reduceIte, Option.getD_some]
    cases c <;> rfl
  have hP : ptU A.um b s o₁ o₂ j = ⟨⟨kOfU s c, List.ofFn (rOfU s c), resp A.um.int i₀.2 i₁.2 c⟩,
      (A.um.int.queries i₀.2 i₁.2 j).anchors, List.ofFn (A.um.int.queries i₀.2 i₁.2 j).ctxRed,
      (A.um.int.queries i₀.2 i₁.2 j).cd⟩ := by
    unfold ptU pt
    rw [← htok]
    rfl
  rw [hP] at hy'
  unfold redStmtU at hy'
  obtain ⟨i, -, rfl⟩ := Option.mem_map.1 hy'
  refine ⟨?_, wPre_redeemWitnessU _ _ _ _ _ _⟩
  show (toBA _).size = _
  rw [size_toBA]
  exact length_encodeRedeemWitness (by simp [kOfU, nfKeyBytes]) (by simp [rBytes])
    (by rw [resp, List.length_ofFn]) _

/-- **The two queries are answered by different Clients**, in both worlds. -/
def TwoClientsU (A : AdversaryUH) : Prop :=
  ∀ (b : Bool) (q₀ q₁ : Bytes), who b (A.queries q₀ q₁ 0) ≠ who b (A.queries q₀ q₁ 1)

/-- **Two proofs of a world with one prefix**, the queries answered by different Clients: then
the two Clients' openings agree. -/
theorem coll_impUH (hW : TwoClientsU A) (b : Bool) (v : GVA)
    (h : ¬ DistV Hashes.shake (gameUH A b) v) : rOfU v.s false = rOfU v.s true := by
  by_contra hne
  have hne' : rOfU v.s true ≠ rOfU v.s false := Ne.symm hne
  have i₁ : ∀ y ∈ yv₁ (gameUH A b) v, y.2.size = pIu.witnessBytes ∧ wPre y.2 = rOfU v.s false :=
    fun y hy => by cases hy; exact ⟨issStmtU_size _ _ _, wPre_issueWitnessU _ _ _⟩
  have i₂ : ∀ y ∈ yv₂ (gameUH A b) v, y.2.size = pIu.witnessBytes ∧ wPre y.2 = rOfU v.s true :=
    fun y hy => by cases hy; exact ⟨issStmtU_size _ _ _, wPre_issueWitnessU _ _ _⟩
  have r₃ := fun y hy => σUH_wit (A := A) b v.s v.o₁ v.o₂ 0 y hy
  have r₄ := fun y hy => σUH_wit (A := A) b v.s v.o₁ v.o₂ 1 y hy
  have hw := hW b (issU A.um v.s false v.o₁).2 (issU A.um v.s true v.o₂).2
  have h16 : 16 ≤ pIu.witnessBytes := by decide
  have h16' : 16 ≤ pRu.witnessBytes := by decide
  have mI : pIu.witnessBytes + 32 < preMax := by decide
  have mR : pRu.witnessBytes + 32 < preMax := by decide
  have ne : pIu.witnessBytes ≠ pRu.witnessBytes := by decide
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
        revert hw
        generalize who b (A.queries (issU A.um v.s false v.o₁).2 (issU A.um v.s true v.o₂).2 0) = c₀
        generalize who b (A.queries (issU A.um v.s false v.o₁).2 (issU A.um v.s true v.o₂).2 1) = c₁
        cases c₀ <;> cases c₁ <;> intro hw
        · exact absurd rfl hw
        · exact hne
        · exact hne'
        · exact absurd rfl hw⟩

variable (A) in
/-- **The prefix-collision term is at most `2⁻¹²⁸`** when the two queries are answered by
different Clients: the two Clients' uniform openings agree. -/
theorem collUH_le_of_who (hW : TwoClientsU A) (b : Bool) : collUH A b ≤ 1 / 2 ^ 128 := by
  unfold collUH
  refine (pr_mono fun x hx => coll_impUH hW b _ hx).trans ?_
  have e1 := pr_prod_fst (β := USh × KS pIu × KS pIu × KS pRu × KS pRu)
    (fun s : SecU => rOfU s false = rOfU s true)
  refine (le_of_eq e1).trans ?_
  let e : Coins rBytes × ((Coins nfKeyBytes × Coins nfKeyBytes) × Coins rBytes) ≃ SecU :=
    { toFun := fun z => ((z.2.1.1, z.1), (z.2.1.2, z.2.2))
      invFun := fun s => (s.1.2, ((s.1.1, s.2.1), s.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  have := pr_mem_uniform_le (X := (Coins nfKeyBytes × Coins nfKeyBytes) × Coins rBytes)
    (fun z => {z.2}) (q := 0) (fun _ => by simp)
  simpa [e, rOfU] using this

end CollA

/-! ## The swap of the ideal worlds, at fixed simulator coins -/

section SwapAt

variable {n : ℕ} {CI CR : Type} (B : Adversary n) (simI : IssueInstance → CI → Bytes)
  (simR : RedeemInstance → CR → Bytes)

/-- **After the PRF hop the worlds coincide at every value of the simulator coins** (the swap of
`idealGame_eq` does not move the coins). -/
theorem idealGame_eq_at (cc : (CI × CI) × (Fin n → CR)) :
    pr (PTape × Table) (fun x => reduction B simI simR false cc (prfIdeal B.ci x)) =
      pr (PTape × Table) (fun x => reduction B simI simR true cc (prfIdeal B.ci x)) := by
  let W : PTape → Coins ctxBytes → Bool := fun p =>
    let t₀ := ucom (List.ofFn p.1.1) B.ci (List.ofFn p.1.2)
    let t₁ := ucom (List.ofFn p.2.1) B.ci (List.ofFn p.2.2)
    swapOf (B.queries (t₀ ++ simI ⟨t₀, B.ci⟩ cc.1.1) (t₁ ++ simI ⟨t₁, B.ci⟩ cc.1.2))
  let e : PTape × Table ≃ PTape × Table :=
    { toFun := fun x => (x.1, swapF (W x.1) x.2)
      invFun := fun x => (x.1, swapF (W x.1) x.2)
      left_inv := fun x => by simp only [swapF_swapF]
      right_inv := fun x => by simp only [swapF_swapF] }
  rw [← pr_equiv e]
  refine pr_congr fun x => ?_
  unfold reduction hview prfIdeal
  simp only [e, Equiv.coe_fn_mk]
  refine iff_of_eq (congrArg _ ?_)
  set t₀ := ucom (List.ofFn x.1.1.1) B.ci (List.ofFn x.1.1.2)
  set t₁ := ucom (List.ofFn x.1.2.1) B.ci (List.ofFn x.1.2.2)
  set q₀ := t₀ ++ simI ⟨t₀, B.ci⟩ cc.1.1
  set q₁ := t₁ ++ simI ⟨t₁, B.ci⟩ cc.1.2
  cases hC : allOkT B q₀ q₁ t₀ t₁
  · rfl
  · have hr : ctxRule (B.queries q₀ q₁) = true := by
      unfold allOkT at hC
      simp only [Bool.and_eq_true] at hC
      exact hC.2
    simp only [Bool.cond_true, Option.some.injEq]
    funext j
    have hW : W x.1 (B.queries q₀ q₁ j).ctxRed = (B.queries q₀ q₁ j).w := swapOf_eq hr j
    unfold ySim swapF who
    beta_reduce
    rw [hW]
    simp

end SwapAt

/-! ## With all proofs simulated: the per-proof game's input, and the table it determines -/

section SimA

variable (A : AdversaryUH)

/-- **The statement of an answer**: an answer `Derive ‖ π` to query `q` was proved for the query's
set, context and digest with the answer's first 32 bytes as the nullifier. -/
def stOfAnsA (q : Query) (a : Except Error Bytes) : Option Statement :=
  match a with
  | .ok bs => some (stR ⟨q.anchors.keys, bs.take nfBytes, A.um.int.ci, List.ofFn q.ctxRed, q.cd⟩)
  | .error _ => none

/-- The statement of query `j`'s answer, if the redemptions are shown. -/
def stYA (q₀ q₁ : Bytes) (y : Option (Fin 2 → Except Error Bytes)) (j : Fin 2) :
    Option Statement :=
  match y with
  | some f => stOfAnsA A (A.queries q₀ q₁ j) (f j)
  | none => none

/-- **The `H₂³` table the guess sees, from what it sees**: the raw table programmed by the four
simulations, for the issuance statements of the requests' commitments and the redemption
statements of the answers (the first outermost). -/
noncomputable def tabA (q₀ q₁ : Bytes) (y : Option (Fin 2 → Except Error Bytes))
    (c₁ c₂ : SimCoins pIu) (c₃ c₄ : SimCoins pRu) (u : USh) (G2 : Tab2G pIu) : Tab2G pIu :=
  pgP pIu c₁ (some (stI ⟨q₀.take uovM, A.um.int.ci⟩)) u
    (pgP pIu c₂ (some (stI ⟨q₁.take uovM, A.um.int.ci⟩)) u
      (pgP pRu c₃ (stYA A q₀ q₁ y 0) u (pgP pRu c₄ (stYA A q₀ q₁ y 1) u G2)))

/-- The rest of the tape: the shared tables, the four slots' coins and tables, and `H₃`. -/
abbrev RestA := AuxH × H3T

/-- **The adversary at the rest of the tape**: its guess programs the raw table itself, with the
four simulators' coins, from the requests and the answers. -/
noncomputable def atZ (z : RestA) : Adversary 2 :=
  ⟨A.ctxIss, A.pk, A.respond, A.queries, fun q₀ q₁ y =>
    A.guess q₀ q₁ y z.1.1 (tabA A q₀ q₁ y z.1.2.1.1.2 z.1.2.2.1.1.2 z.1.2.2.2.1.1.2
      z.1.2.2.2.2.1.2 z.1.1 z.1.2.1.2.2) z.2⟩

/-- The four simulators' coins of the rest of the tape, as `reduction` takes them. -/
def ccA (z : RestA) : (SimCoins pIu × SimCoins pIu) × (Fin 2 → SimCoins pRu) :=
  ((z.1.2.1.1.2, z.1.2.2.1.1.2), ![z.1.2.2.2.1.1.2, z.1.2.2.2.2.1.2])

variable {A}

/-- The statement of an answered query is the statement of its proof. -/
lemma stOfAnsA_redOutU (b : Bool) (s : SecU) (o₁ o₂ o : Option Out) (j : Fin 2) :
    stOfAnsA A (A.queries (issU A.um s false o₁).2 (issU A.um s true o₂).2 j)
        (redOutU A.um (ptU A.um b s o₁ o₂ j) o) =
      (redStmtU A.um (ptU A.um b s o₁ o₂ j)).map Prod.fst := by
  unfold redOutU redStmtU
  cases findIssuer (ptU A.um b s o₁ o₂ j).anchors
    (ucom (ptU A.um b s o₁ o₂ j).tok.k A.um.int.ci (ptU A.um b s o₁ o₂ j).tok.r)
    (ptU A.um b s o₁ o₂ j).tok.s with
  | none => rfl
  | some i =>
    show some _ = some _
    unfold xRU
    rw [List.take_left' (length_derive _ _)]
    rfl

lemma take_issU (s : SecU) (c : Bool) (o : Option Out) :
    (issU A.um s c o).2.take uovM = tUM A.um s c := by
  unfold issU
  exact List.take_left' (length_ucom _ _ _)

/-- The simulated view of world `b` on tape `x`. -/
noncomputable abbrev simVA (b : Bool) (x : TapeA) : GVA :=
  hybV23 (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameUH A b) true true true true x

set_option maxRecDepth 8192 in
/-- **The `H₂³` table of the simulated view is `tabA` of the guess's input.** -/
lemma simVA_tab (b : Bool) (x : TapeA) :
    (simVA (A := A) b x).v₁.2 = tabA A (keyUH A b (simVA (A := A) b x)).1
      (keyUH A b (simVA (A := A) b x)).2.1 (keyUH A b (simVA (A := A) b x)).2.2
      x.2.2.1.1.2 x.2.2.2.1.1.2 x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2 x.2.1 x.2.2.1.2.2 := by
  set G := gameUH A b
  set o₁ : Option Out := some (simulate pIu x.2.2.1.1.2)
  set o₂ : Option Out := some (simulate pIu x.2.2.2.1.1.2)
  set o₃ := (G.σ₃ x.1 o₁ o₂).map fun _ => simulate pRu x.2.2.2.2.1.1.2
  set o₄ := (G.σ₄ x.1 o₁ o₂ o₃).map fun _ => simulate pRu x.2.2.2.2.2.1.2
  have hM : (simVA (A := A) b x).v₁.2 =
      pgP pIu x.2.2.1.1.2 ((G.σ₁ x.1).map Prod.fst) x.2.1
        (pgP pIu x.2.2.2.1.1.2 ((G.σ₂ x.1 o₁).map Prod.fst) x.2.1
          (pgP pRu x.2.2.2.2.1.1.2 ((G.σ₃ x.1 o₁ o₂).map Prod.fst) x.2.1
            (pgP pRu x.2.2.2.2.2.1.2 ((G.σ₄ x.1 o₁ o₂ o₃).map Prod.fst) x.2.1 x.2.2.1.2.2))) := by
    show (simSB Hashes.shake pIu x.2.2.1.1.2 x.2.2.1.2.1).pg (G.σ₁ x.1) x.2.1
      ((simSB Hashes.shake pIu x.2.2.2.1.1.2 x.2.2.2.1.2.1).pg (G.σ₂ x.1 o₁) x.2.1
        ((simSB Hashes.shake pRu x.2.2.2.2.1.1.2 x.2.2.2.2.1.2.1).pg (G.σ₃ x.1 o₁ o₂) x.2.1
          ((simSB Hashes.shake pRu x.2.2.2.2.2.1.2 x.2.2.2.2.2.2.1).pg (G.σ₄ x.1 o₁ o₂ o₃)
            x.2.1 x.2.2.1.2.2))) = _
    simp only [simSB_pg_eq]
  have hk : keyUH A b (simVA (A := A) b x) =
      ((issU A.um x.1 false o₁).2, (issU A.um x.1 true o₂).2, yU A.um b x.1 o₁ o₂ o₃ o₄) := rfl
  have h3 : (G.σ₃ x.1 o₁ o₂).map Prod.fst =
      stYA A (issU A.um x.1 false o₁).2 (issU A.um x.1 true o₂).2 (yU A.um b x.1 o₁ o₂ o₃ o₄) 0 := by
    show (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else none).map _ =
      stYA A _ _ (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else
        none) 0
    cases allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂)
    · rfl
    · exact (stOfAnsA_redOutU b x.1 o₁ o₂ o₃ 0).symm
  have h4 : (G.σ₄ x.1 o₁ o₂ o₃).map Prod.fst =
      stYA A (issU A.um x.1 false o₁).2 (issU A.um x.1 true o₂).2 (yU A.um b x.1 o₁ o₂ o₃ o₄) 1 := by
    show (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else none).map _ =
      stYA A _ _ (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else
        none) 1
    cases allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂)
    · rfl
    · exact (stOfAnsA_redOutU b x.1 o₁ o₂ o₄ 1).symm
  rw [hM, hk, h3, h4]
  unfold tabA
  rw [take_issU, take_issU]
  rfl

/-- `allOk` on honest pending tokens is `allOkT` on the requests and the commitments. -/
lemma allOk_issU (B : AdversaryUM) (s : SecU) (o₁ o₂ : Option Out) :
    allOk B.int (issU B s false o₁) (issU B s true o₂) =
      allOkT B.int (issU B s false o₁).2 (issU B s true o₂).2 (tUM B s false) (tUM B s true) := by
  set i₀ := issU B s false o₁
  set i₁ := issU B s true o₂
  show allOk B.int i₀ i₁ = allOkT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t
  have htok (c : Bool) (hc : finT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD B.int i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.k, (bif c then i₁ else i₀).1.r, resp B.int i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin B.int i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hcom (c : Bool) : ucom (bif c then i₁ else i₀).1.k B.int.ci (bif c then i₁ else i₀).1.r =
      bif c then i₁.1.t else i₀.1.t := by
    cases c <;> rfl
  have hred (c : Bool) (S : AnchorSet) (hc : finT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      redeemable B.int.ci (tokD B.int i₀ i₁ c) S = okT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t c S := by
    unfold redeemable okT
    rw [htok c hc]
    simp only [hcom]
  unfold allOk allOkT
  rw [tok_of_fin B.int i₀ i₁ false, tok_of_fin B.int i₀ i₁ true]
  cases e₀ : finT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t false
  · simp
  · cases e₁ : finT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t true
    · simp
    · have : ∀ j c, redeemable B.int.ci (tokD B.int i₀ i₁ c) (B.int.queries i₀.2 i₁.2 j).anchors =
          okT B.int i₀.2 i₁.2 i₀.1.t i₁.1.t c (B.int.queries i₀.2 i₁.2 j).anchors := fun j c => by
        cases c
        · exact hred false _ e₀
        · exact hred true _ e₁
      simp only [this, Option.isSome_some, ↓reduceIte, Bool.true_and]

end SimA

/-! ## The simulated game is the reduction to the PRF, at the rest of the tape -/

section RedA

variable (A : AdversaryUH)

/-- The per-proof tape of `yU_sim`, from the four simulators' coins (its tables are not read). -/
noncomputable def auxOf (a : AuxH) : AuxU :=
  ((a.2.1.1.2, Classical.arbitrary _), (a.2.2.1.1.2, Classical.arbitrary _),
    (a.2.2.2.1.1.2, Classical.arbitrary _), (a.2.2.2.2.1.2, Classical.arbitrary _))

set_option maxRecDepth 8192 in
/-- **With all proofs simulated, the guess's input is `ySimU`'s** (the redemptions gated by the
rule are those of the per-proof game). -/
lemma keyUH_sim (b : Bool) (x : TapeA) :
    (keyUH A b (simVA (A := A) b x)).2.2 = ySimU A.um b (tUM A.um x.1 false) (tUM A.um x.1 true)
      (kOfU x.1 false) (kOfU x.1 true) (auxOf x.2) := by
  have hu := yU_sim A.um b x.1 (auxOf x.2)
  rw [← hu]
  set o₁ : Option Out := some (simulate pIu x.2.2.1.1.2)
  set o₂ : Option Out := some (simulate pIu x.2.2.2.1.1.2)
  show yU A.um b x.1 o₁ o₂ (((gameUH A b).σ₃ x.1 o₁ o₂).map fun _ => simulate pRu x.2.2.2.2.1.1.2)
    (((gameUH A b).σ₄ x.1 o₁ o₂ (((gameUH A b).σ₃ x.1 o₁ o₂).map fun _ =>
      simulate pRu x.2.2.2.2.1.1.2)).map fun _ => simulate pRu x.2.2.2.2.2.1.2) =
    yU A.um b x.1 o₁ o₂ ((redStmtU A.um (ptU A.um b x.1 o₁ o₂ 0)).map fun _ =>
      simulate pRu x.2.2.2.2.1.1.2) ((redStmtU A.um (ptU A.um b x.1 o₁ o₂ 1)).map fun _ =>
      simulate pRu x.2.2.2.2.2.1.2)
  cases hok : allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂)
  · unfold yU
    rw [hok]
    rfl
  · have e₃ : (gameUH A b).σ₃ x.1 o₁ o₂ = redStmtU A.um (ptU A.um b x.1 o₁ o₂ 0) := by
      show (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else none) = _
      rw [hok]; rfl
    have e₄ : ∀ o, (gameUH A b).σ₄ x.1 o₁ o₂ o = redStmtU A.um (ptU A.um b x.1 o₁ o₂ 1) := fun o => by
      show (bif allOk A.um.int (issU A.um x.1 false o₁) (issU A.um x.1 true o₂) then _ else none) = _
      rw [hok]; rfl
    rw [e₃, e₄]

/-- The guess's third input with all proofs simulated, in the form of `hview`. -/
lemma keyUH_sim' (b : Bool) (x : TapeA) :
    (keyUH A b (simVA (A := A) b x)).2.2 =
      bif allOkT A.um.int (reqU (tUM A.um x.1 false) x.2.2.1.1.2)
          (reqU (tUM A.um x.1 true) x.2.2.2.1.1.2) (tUM A.um x.1 false) (tUM A.um x.1 true) then
        some (fun j => ySim A.um.int simRU b (tabU (kOfU x.1 false) (kOfU x.1 true))
          (A.queries (reqU (tUM A.um x.1 false) x.2.2.1.1.2) (reqU (tUM A.um x.1 true) x.2.2.2.1.1.2)
            j) (![x.2.2.2.2.1.1.2, x.2.2.2.2.2.1.2] j))
      else none := by
  rw [keyUH_sim]
  unfold ySimU
  rw [← fin2_eta (fun j => ySim A.um.int simRU b (tabU (kOfU x.1 false) (kOfU x.1 true))
    (A.queries (reqU (tUM A.um x.1 false) x.2.2.1.1.2) (reqU (tUM A.um x.1 true) x.2.2.2.1.1.2) j)
    (![x.2.2.2.2.1.1.2, x.2.2.2.2.2.1.2] j))]
  rfl

set_option maxRecDepth 8192 in
/-- **With all proofs simulated, the event is `reduction` of the adversary at the rest of the
tape**, on the real PRF experiment of the Clients' keys and openings. -/
theorem simUH_iff (b : Bool) (x : TapeA) (T : H3T) :
    evUH A b (simVA (A := A) b x) T ↔
      reduction (atZ A (x.2, T)) simIU simRU b (ccA (x.2, T)) (prfReal A.um.int.ci x.1) := by
  unfold evUH
  rw [simVA_tab, keyUH_sim']
  exact Iff.rfl

/-- The game after the PRF hop. -/
noncomputable def idealUH (b : Bool) : ℝ :=
  pr ((PTape × Table) × RestA) (fun y =>
    reduction (atZ A y.2) simIU simRU b (ccA y.2) (prfIdeal A.um.int.ci y.1))

/-- **The PRF hop**, at every rest of the tape. -/
theorem prf_hop_UH (b : Bool) {εprf : ℝ}
    (hprf : ∀ z, prfAdv A.um.int.ci (reduction (atZ A z) simIU simRU b (ccA z)) ≤ εprf) :
    |simUH A b - idealUH A b| ≤ εprf := by
  have e : simUH A b = pr (PTape × RestA) (fun y =>
      reduction (atZ A y.2) simIU simRU b (ccA y.2) (prfReal A.um.int.ci y.1)) := by
    let g : TapeA × H3T ≃ PTape × RestA :=
      { toFun := fun z => (z.1.1, (z.1.2, z.2))
        invFun := fun y => ((y.1, y.2.1), y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    show pr (TapeA × H3T) (fun z => evUH A b (simVA (A := A) b z.1) z.2) = _
    rw [← pr_equiv g.symm]
    exact pr_congr fun y => simUH_iff A b (g.symm y).1 (g.symm y).2
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun z => hprf z

/-- **After the PRF hop the worlds coincide.** -/
theorem idealUH_eq : idealUH A false = idealUH A true := by
  have h : |idealUH A false - idealUH A true| ≤ 0 :=
    abs_pr_prod_sub_le' _ _ fun z => by
      have e := idealGame_eq_at (atZ A z) simIU simRU (ccA z)
      show |pr (PTape × Table) (fun a => reduction (atZ A z) simIU simRU false (ccA z)
        (prfIdeal (atZ A z).ci a)) - pr (PTape × Table) (fun a => reduction (atZ A z) simIU simRU
          true (ccA z) (prfIdeal (atZ A z).ci a))| ≤ 0
      rw [e, sub_self, abs_zero]
  have := abs_nonneg (idealUH A false - idealUH A true)
  have h0 : |idealUH A false - idealUH A true| = 0 := le_antisymm h this
  exact sub_eq_zero.1 (abs_eq_zero.1 h0)

end RedA

/-! ## The (PU) term: the public key set and the predictors -/

section PubA

variable (A : AdversaryUH)

/-- The active gate inputs of a simulated redemption proof (none without a statement). -/
noncomputable def actLoU (st : Option Statement) (E : Cipher) (c : SimCoins pRu) : List ByteArray :=
  match st with
  | some st => actL Hashes.shake pRu st E c
  | none => []

/-- The candidates of a simulated redemption proof (none without a statement). -/
noncomputable def candCoU (st : Option Statement) (E : Cipher) (c : SimCoins pRu)
    (S : Finset (ZK.Sim.Bytes 37)) : Finset (Coins rBytes) :=
  match st with
  | some st => candC Hashes.shake st E c S
  | none => ∅

/-- The requests, from the commitments and the issuance simulators' coins. -/
noncomputable def qP (t₀ t₁ : Bytes) (a : AuxH) : Bytes × Bytes :=
  (reqU t₀ a.2.1.1.2, reqU t₁ a.2.2.1.1.2)

/-- The rule, from public values. -/
noncomputable def okP (t₀ t₁ : Bytes) (a : AuxH) : Bool :=
  allOkT A.um.int (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 t₀ t₁

/-- The redemptions the guess sees, from the commitments, the keys and the coins. -/
noncomputable def yP (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (a : AuxH) :
    Option (Fin 2 → Except Error Bytes) :=
  bif okP A t₀ t₁ a then
    some (fun j => ySim A.um.int simRU b (tabU k₀ k₁) (A.queries (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 j)
      (![a.2.2.2.1.1.2, a.2.2.2.2.1.2] j))
  else none

/-- The statement of query `j`'s redemption proof (none unless the rule holds). -/
noncomputable def stRA (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (a : AuxH) (j : Fin 2) : Option Statement :=
  bif okP A t₀ t₁ a then some (stR (xQU A.um b (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 k₀ k₁ j)) else none

/-- **The public key set**: the guess's `H₅` read set and the active gate inputs of the four
simulated proofs, from the commitments, the keys, the coins, the raw tables and `H₃`. -/
noncomputable def spP (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (a : AuxH) (T : H3T) :
    Finset (ZK.Sim.Bytes 37) :=
  A.R5 (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 (yP A b t₀ t₁ k₀ k₁ a) a.1
      (tabA A (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 (yP A b t₀ t₁ k₀ k₁ a) a.2.1.1.2 a.2.2.1.1.2
        a.2.2.2.1.1.2 a.2.2.2.2.1.2 a.1 a.2.1.2.2) T ∪
    ((actL Hashes.shake pIu (stI ⟨t₀, A.um.int.ci⟩) a.1.2 a.2.1.1.2).toFinset.image (blk 37) ∪
      (actL Hashes.shake pIu (stI ⟨t₁, A.um.int.ci⟩) a.1.2 a.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLoU (stRA A b t₀ t₁ k₀ k₁ a 0) a.1.2 a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLoU (stRA A b t₀ t₁ k₀ k₁ a 1) a.1.2 a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- **The candidates**: those of the four simulated proofs for the public key set. -/
noncomputable def candP (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (a : AuxH) (T : H3T) :
    Finset (Coins rBytes) :=
  candC Hashes.shake (stI ⟨t₀, A.um.int.ci⟩) a.1.2 a.2.1.1.2 (spP A b t₀ t₁ k₀ k₁ a T) ∪
    candC Hashes.shake (stI ⟨t₁, A.um.int.ci⟩) a.1.2 a.2.2.1.1.2 (spP A b t₀ t₁ k₀ k₁ a T) ∪
    candCoU (stRA A b t₀ t₁ k₀ k₁ a 0) a.1.2 a.2.2.2.1.1.2 (spP A b t₀ t₁ k₀ k₁ a T) ∪
    candCoU (stRA A b t₀ t₁ k₀ k₁ a 1) a.1.2 a.2.2.2.2.1.2 (spP A b t₀ t₁ k₀ k₁ a T)

/-- **The predictor for Client `false`** in the game `PU.puAdv` for `UCom`: public part `nf_key₀`,
commitment `t₀`, auxiliary coins the other Client's `(nf_key₁, r₁)`, the simulators' coins, the
raw tables and `H₃`. -/
noncomputable def predUH₀ (b : Bool) (n : Coins nfKeyBytes) (t : Bytes)
    (a : (Coins nfKeyBytes × Coins rBytes) × RestA) : Finset (Coins rBytes) :=
  candP A b t (comU A.um a.1.1 a.1.2) (List.ofFn n) (List.ofFn a.1.1) a.2.1 a.2.2

/-- **The predictor for Client `true`.** -/
noncomputable def predUH₁ (b : Bool) (n : Coins nfKeyBytes) (t : Bytes)
    (a : (Coins nfKeyBytes × Coins rBytes) × RestA) : Finset (Coins rBytes) :=
  candP A b (comU A.um a.1.1 a.1.2) t (List.ofFn a.1.1) (List.ofFn n) a.2.1 a.2.2

lemma card_img_leU (l : List ByteArray) (h : l.length ≤ 312) :
    (l.toFinset.image (blk 37)).card ≤ 312 :=
  card_image_le.trans ((List.toFinset_card_le _).trans h)

lemma actLoU_length_le (st : Option Statement) (E : Cipher) (c : SimCoins pRu) :
    (actLoU st E c).length ≤ 312 := by
  rcases st with _ | st
  · simp [actLoU]
  · exact actL_length_le _ _ _ _

/-- **At most `4·(q₅ + 1249)` candidates**, if the read sets have at most `q₅` keys. -/
theorem card_candP_le {q5 : ℕ} (h5 : ∀ q₀ q₁ y u G2 T, (A.R5 q₀ q₁ y u G2 T).card ≤ q5) (b : Bool)
    (t₀ t₁ k₀ k₁ : Bytes) (a : AuxH) (T : H3T) :
    (candP A b t₀ t₁ k₀ k₁ a T).card ≤ 4 * (q5 + 1249) := by
  have hS : (spP A b t₀ t₁ k₀ k₁ a T).card ≤ q5 + 1248 := by
    unfold spP
    have a₁ := card_img_leU _ (actL_length_le Hashes.shake (p := pIu) (stI ⟨t₀, A.um.int.ci⟩)
      a.1.2 a.2.1.1.2)
    have a₂ := card_img_leU _ (actL_length_le Hashes.shake (p := pIu) (stI ⟨t₁, A.um.int.ci⟩)
      a.1.2 a.2.2.1.1.2)
    have a₃ := card_img_leU _ (actLoU_length_le (stRA A b t₀ t₁ k₀ k₁ a 0) a.1.2 a.2.2.2.1.1.2)
    have a₄ := card_img_leU _ (actLoU_length_le (stRA A b t₀ t₁ k₀ k₁ a 1) a.1.2 a.2.2.2.2.1.2)
    have hr := h5 (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 (yP A b t₀ t₁ k₀ k₁ a) a.1
      (tabA A (qP t₀ t₁ a).1 (qP t₀ t₁ a).2 (yP A b t₀ t₁ k₀ k₁ a) a.2.1.1.2 a.2.2.1.1.2
        a.2.2.2.1.1.2 a.2.2.2.2.1.2 a.1 a.2.1.2.2) T
    generalize A.R5 _ _ _ _ _ _ = R at hr ⊢
    generalize image (blk 37) (actL Hashes.shake pIu (stI ⟨t₀, A.um.int.ci⟩) a.1.2
      a.2.1.1.2).toFinset = X₁ at a₁ ⊢
    generalize image (blk 37) (actL Hashes.shake pIu (stI ⟨t₁, A.um.int.ci⟩) a.1.2
      a.2.2.1.1.2).toFinset = X₂ at a₂ ⊢
    generalize image (blk 37) (actLoU (stRA A b t₀ t₁ k₀ k₁ a 0) a.1.2 a.2.2.2.1.1.2).toFinset =
      X₃ at a₃ ⊢
    generalize image (blk 37) (actLoU (stRA A b t₀ t₁ k₀ k₁ a 1) a.1.2 a.2.2.2.2.1.2).toFinset =
      X₄ at a₄ ⊢
    have u₀ := card_union_le R (X₁ ∪ X₂ ∪ X₃ ∪ X₄)
    have u₁ := card_union_le (X₁ ∪ X₂ ∪ X₃) X₄
    have u₂ := card_union_le (X₁ ∪ X₂) X₃
    have u₃ := card_union_le X₁ X₂
    omega
  have hI : ∀ (st : Statement) (cc : SimCoins pIu),
      (candC Hashes.shake st a.1.2 cc (spP A b t₀ t₁ k₀ k₁ a T)).card ≤ q5 + 1249 :=
    fun st cc => (card_candC_le Hashes.shake mainP_pIu st a.1.2 cc _).trans (by omega)
  have hR : ∀ (st : Option Statement) (cc : SimCoins pRu),
      (candCoU st a.1.2 cc (spP A b t₀ t₁ k₀ k₁ a T)).card ≤ q5 + 1249 := by
    intro st cc
    rcases st with _ | st
    · simp [candCoU]
    · exact (card_candC_le Hashes.shake mainP_pRu st a.1.2 cc _).trans (by omega)
  unfold candP
  have := hI (stI ⟨t₀, A.um.int.ci⟩) a.2.1.1.2
  have := hI (stI ⟨t₁, A.um.int.ci⟩) a.2.2.1.1.2
  have := hR (stRA A b t₀ t₁ k₀ k₁ a 0) a.2.2.2.1.1.2
  have := hR (stRA A b t₀ t₁ k₀ k₁ a 1) a.2.2.2.2.1.2
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_
  omega

end PubA

/-! ## The (PU) term: the slots of the simulated game -/

section SlotsA

variable (A : AdversaryUH)

/-- The statement and opening of Client `c`'s issuance proof. -/
def qIA (s : SecU) (c : Bool) : Option (Statement × ZK.Sim.Bytes 16) :=
  some (stI ⟨tUM A.um s c, A.um.int.ci⟩, rOfU s c)

/-- The answering Client of query `j`, from the requests. -/
noncomputable def whoA (b : Bool) (x : TapeA) (j : Fin 2) : Bool :=
  who b (A.queries (qP (tUM A.um x.1 false) (tUM A.um x.1 true) x.2).1
    (qP (tUM A.um x.1 false) (tUM A.um x.1 true) x.2).2 j)

/-- The statement and opening of query `j`'s redemption proof (none unless the rule holds). -/
noncomputable def qRA (b : Bool) (x : TapeA) (j : Fin 2) : Option (Statement × ZK.Sim.Bytes 16) :=
  (stRA A b (tUM A.um x.1 false) (tUM A.um x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2 j).map
    fun st => (st, rOfU x.1 (whoA A b x j))

variable {A}

lemma qOf_issA (s : SecU) (c : Bool) : qOf (some (issStmtU A.um s c)) = qIA A s c := by
  unfold qOf qIA
  simp only [Option.map_some, Option.some.injEq]
  exact Prod.ext rfl (wPre_issueWitnessU _ _ _)

/-- With the rule passing, a redemption has a statement. -/
lemma redStmtU_some (B : AdversaryUM) (b : Bool) (s : SecU) (o₁ o₂ : Option Out) (j : Fin 2)
    (h : allOk B.int (issU B s false o₁) (issU B s true o₂) = true) :
    ∃ y, redStmtU B (ptU B b s o₁ o₂ j) = some y := by
  unfold allOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hr := h.1.2 j (who b (B.int.queries (issU B s false o₁).2 (issU B s true o₂).2 j))
  unfold redeemable at hr
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hr
  unfold redStmtU ptU pt
  simp only [hi, Option.map_some]
  exact ⟨_, rfl⟩

set_option maxRecDepth 8192 in
/-- **A redemption slot of the simulated game**: its statement is public (`stRA`) and its witness
prefix is the answering Client's opening. -/
lemma qOf_σA (b : Bool) (x : TapeA) (j : Fin 2) :
    qOf (bif allOk A.um.int (issU A.um x.1 false (some (simulate pIu x.2.2.1.1.2)))
        (issU A.um x.1 true (some (simulate pIu x.2.2.2.1.1.2))) then
      redStmtU A.um (ptU A.um b x.1 (some (simulate pIu x.2.2.1.1.2))
        (some (simulate pIu x.2.2.2.1.1.2)) j) else none) = qRA A b x j := by
  have hall := allOk_issU A.um x.1 (some (simulate pIu x.2.2.1.1.2))
    (some (simulate pIu x.2.2.2.1.1.2))
  rw [hall]
  unfold qRA stRA
  show qOf (bif okP A (tUM A.um x.1 false) (tUM A.um x.1 true) x.2 then _ else none) =
    (bif okP A (tUM A.um x.1 false) (tUM A.um x.1 true) x.2 then _ else none).map _
  cases hok : okP A (tUM A.um x.1 false) (tUM A.um x.1 true) x.2
  · rfl
  · have hA : allOk A.um.int (issU A.um x.1 false (some (simulate pIu x.2.2.1.1.2)))
        (issU A.um x.1 true (some (simulate pIu x.2.2.2.1.1.2))) = true := by rw [hall]; exact hok
    obtain ⟨y, hy⟩ := redStmtU_some A.um b x.1 _ _ j hA
    have hf := fin_of_allOkT A.um hok (whoU A.um b (tUM A.um x.1 false) (tUM A.um x.1 true)
      (auxOf x.2) j)
    obtain ⟨h1, h2⟩ := redStmtU_fin A.um b x.1 (auxOf x.2) j hf y hy
    simp only [Bool.cond_true, Option.map_some]
    rw [show redStmtU A.um (ptU A.um b x.1 (some (simulate pIu x.2.2.1.1.2))
      (some (simulate pIu x.2.2.2.1.1.2)) j) = some y from hy]
    simp only [qOf, Option.map_some, Option.some.injEq]
    rw [h1, h2]
    rfl

/-- The redemption slots depend on the tape only through the secret and the issuance simulators'
coins. -/
lemma qRA_congr (b : Bool) (x x' : TapeA) (j : Fin 2) (hs : x.1 = x'.1)
    (h₁ : x.2.2.1.1.2 = x'.2.2.1.1.2) (h₂ : x.2.2.2.1.1.2 = x'.2.2.2.1.1.2) :
    qRA A b x j = qRA A b x' j := by
  unfold qRA stRA okP whoA qP
  rw [hs, h₁, h₂]

lemma actO_qRA (b : Bool) (x : TapeA) (j : Fin 2) (E : Cipher) (c : SimCoins pRu) :
    actO Hashes.shake pRu (qRA A b x j) E c =
      actLoU (stRA A b (tUM A.um x.1 false) (tUM A.um x.1 true) (kOfU x.1 false) (kOfU x.1 true)
        x.2 j) E c := by
  unfold qRA
  rcases stRA A b (tUM A.um x.1 false) (tUM A.um x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2 j
    with _ | st <;> rfl

set_option maxRecDepth 8000 in
lemma candO_qRA (b : Bool) (x : TapeA) (j : Fin 2) (E : Cipher) (c : SimCoins pRu)
    (S : Finset (ZK.Sim.Bytes 37)) (h : candO Hashes.shake (qRA A b x j) E c S) :
    rOfU x.1 (whoA A b x j) ∈ candCoU (stRA A b (tUM A.um x.1 false) (tUM A.um x.1 true)
      (kOfU x.1 false) (kOfU x.1 true) x.2 j) E c S := by
  unfold qRA at h
  rcases hst : stRA A b (tUM A.um x.1 false) (tUM A.um x.1 true) (kOfU x.1 false) (kOfU x.1 true)
    x.2 j with _ | st
  · rw [hst] at h; exact h.elim
  · rw [hst] at h; exact h

variable (A)

/-- Client `c`'s opening is among the candidates. -/
def winA (b c : Bool) (z : TapeA × H3T) : Prop :=
  rOfU z.1.1 c ∈ candP A b (tUM A.um z.1.1 false) (tUM A.um z.1.1 true) (kOfU z.1.1 false)
    (kOfU z.1.1 true) z.1.2 z.2

/-- A sibling gate input of the first issuance proof is one of the second. -/
noncomputable def coll₂A (x : TapeA) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIu (qIA A x.1 false) x.2.1.2 x.2.2.1.1.2,
    y ∈ sibO Hashes.shake pIu (qIA A x.1 true) x.2.1.2 x.2.2.2.1.1.2

/-- A sibling gate input of an issuance proof is one of the first redemption proof. -/
noncomputable def coll₃A (b : Bool) (x : TapeA) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIu (qIA A x.1 false) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIu (qIA A x.1 true) x.2.1.2 x.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pRu (qRA A b x 0) x.2.1.2 x.2.2.2.2.1.1.2

/-- A sibling gate input of an earlier proof is one of the second redemption proof. -/
noncomputable def coll₄A (b : Bool) (x : TapeA) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIu (qIA A x.1 false) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIu (qIA A x.1 true) x.2.1.2 x.2.2.2.1.1.2 ++
      sibO Hashes.shake pRu (qRA A b x 0) x.2.1.2 x.2.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pRu (qRA A b x 1) x.2.1.2 x.2.2.2.2.2.1.2

set_option maxRecDepth 8192 in
/-- **`bstar` with all proofs simulated**: a failed simulation, a prediction of an opening by the
public candidates, or a collision of two simulated proofs. -/
theorem puUH_imp (b : Bool) (z : TapeA × H3T)
    (h : bstar Hashes.shake (gameUH A b) (fun v => r5UH A b v z.2) (simVA (A := A) b z.1)) :
    (errC pIu z.1.2.2.1.1.2 ∨ errC pIu z.1.2.2.2.1.1.2 ∨ errC pRu z.1.2.2.2.2.1.1.2 ∨
        errC pRu z.1.2.2.2.2.2.1.2) ∨
      (winA A b false z ∨ winA A b true z) ∨
      (coll₂A A z.1 ∨ coll₃A A b z.1 ∨ coll₄A A b z.1) := by
  obtain ⟨x, T⟩ := z
  set t₀ := tUM A.um x.1 false
  set t₁ := tUM A.um x.1 true
  have hR : r5UH A b (simVA (A := A) b x) T =
      A.R5 (qP t₀ t₁ x.2).1 (qP t₀ t₁ x.2).2 (yP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2)
        x.2.1 (tabA A (qP t₀ t₁ x.2).1 (qP t₀ t₁ x.2).2
          (yP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2) x.2.2.1.1.2 x.2.2.2.1.1.2
          x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2 x.2.1 x.2.2.1.2.2) T := by
    unfold r5UH
    rw [simVA_tab, keyUH_sim']
    rfl
  have key := bstar_sim Hashes.shake (gameUH A b) hashesWF_shake x.1 x.2.1.2 x.2.2.1.1.2
    x.2.2.2.1.1.2 x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2
    (A.R5 (qP t₀ t₁ x.2).1 (qP t₀ t₁ x.2).2 (yP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2)
        x.2.1 (tabA A (qP t₀ t₁ x.2).1 (qP t₀ t₁ x.2).2
          (yP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2) x.2.2.1.1.2 x.2.2.2.1.1.2
          x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2 x.2.1 x.2.2.1.2.2) T)
    (simVA (A := A) b x).o₁ (simVA (A := A) b x).o₂ (simVA (A := A) b x).o₃
    (simVA (A := A) b x).o₄
    (qIA A x.1 false) (qIA A x.1 true) (qRA A b x 0) (qRA A b x 1)
    rfl rfl rfl rfl (qOf_issA x.1 false).symm (qOf_issA x.1 true).symm (qOf_σA b x 0).symm
    (qOf_σA b x 1).symm
    (spP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2 T)
    (by
      unfold spP
      rw [actO_qRA, actO_qRA]
      rfl)
    (by
      rw [← hR]
      exact h)
  have hpick : ∀ c : Bool, rOfU x.1 c ∈ candP A b t₀ t₁ (kOfU x.1 false) (kOfU x.1 true) x.2 T →
      winA A b false (x, T) ∨ winA A b true (x, T) := fun c hc => by
    cases c
    · exact Or.inl hc
    · exact Or.inr hc
  rcases key with he | hc | hcoll
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ hc)))
    · exact Or.inr (mem_union_left _ (mem_union_left _ (mem_union_right _ hc)))
    · exact hpick _ (mem_union_left _ (mem_union_right _ (candO_qRA b x 0 _ _ _ hc)))
    · exact hpick _ (mem_union_right _ (candO_qRA b x 1 _ _ _ hc))
  · exact Or.inr (Or.inr hcoll)

end SlotsA

/-! ## The (PU) term: the probabilities -/

section PrA

variable (A : AdversaryUH)

theorem pr_errA₁_le : pr TapeA (fun x => errC pIu x.2.2.1.1.2) ≤ noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ => pr_errC_le

theorem pr_errA₂_le : pr TapeA (fun x => errC pIu x.2.2.2.1.1.2) ≤ noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ =>
    pr_errC_le

theorem pr_errA₃_le : pr TapeA (fun x => errC pRu x.2.2.2.2.1.1.2) ≤ noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_snd fun _ => pr_errC_le

theorem pr_errA₄_le : pr TapeA (fun x => errC pRu x.2.2.2.2.2.1.2) ≤ noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_fst fun _ => pr_errC_le

/-- **The two issuance proofs collide with probability `≤ 313·2⁻¹²⁸`.** -/
theorem pr_coll₂A_le : pr TapeA (coll₂A A) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_snd fun r =>
    pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  exact pr_sib_hit_le Hashes.shake mainP_pIu (stI ⟨tUM A.um s true, A.um.int.ci⟩) u.2 sh c1 c2 c3
    c5 (rOfU s true) (sibO Hashes.shake pIu (qIA A s false) u.2 k₁.1.2) (sibO_length_le _ _ _ _)

set_option maxRecDepth 8192 in
/-- **The first redemption proof collides with an issuance proof with probability
`≤ 625·2⁻¹²⁸`.** -/
theorem pr_coll₃A_le (b : Bool) : pr TapeA (coll₃A A b) ≤ ((624 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_snd fun k₄ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIu (qIA A s false) u.2 k₁.1.2 ++
      sibO Hashes.shake pIu (qIA A s true) u.2 k₂.1.2).length ≤ 624 := by
    rw [List.length_append]
    have := sibO_length_le Hashes.shake (qIA A s false) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qIA A s true) u.2 k₂.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pRu.witnessBytes,
      qRA A b (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, d, c5))), V), k₄) 0 =
      qRA A b (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄) 0 := fun d =>
    qRA_congr b _ _ 0 rfl rfl rfl
  rcases hst : qRA A b (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄) 0
    with _ | ⟨st, r⟩
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold coll₃A
      rw [hq d, hst]
      simp [sibO]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pRu st u.2 sh c1 c2
      c3 c5 r _ hlen)
    unfold coll₃A at hd
    rw [hq d, hst] at hd
    exact hd

set_option maxRecDepth 8192 in
/-- **The second redemption proof collides with an earlier proof with probability
`≤ 937·2⁻¹²⁸`.** -/
theorem pr_coll₄A_le (b : Bool) : pr TapeA (coll₄A A b) ≤ ((936 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_fst fun k₃ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIu (qIA A s false) u.2 k₁.1.2 ++
      sibO Hashes.shake pIu (qIA A s true) u.2 k₂.1.2 ++
      sibO Hashes.shake pRu (qRA A b (s, u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) 0) u.2 k₃.1.2).length ≤ 936 := by
    rw [List.length_append, List.length_append]
    have := sibO_length_le Hashes.shake (qIA A s false) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qIA A s true) u.2 k₂.1.2
    have := sibO_length_le Hashes.shake (qRA A b (s, u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) 0) u.2 k₃.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pRu.witnessBytes,
      qRA A b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) 1 =
      qRA A b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) 1 := fun d =>
    qRA_congr b _ _ 1 rfl rfl rfl
  have hq' : ∀ d : ZK.Sim.Bytes pRu.witnessBytes,
      qRA A b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) 0 =
      qRA A b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) 0 := fun d =>
    qRA_congr b _ _ 0 rfl rfl rfl
  rcases hst : qRA A b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) 1
    with _ | ⟨st, r⟩
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold coll₄A
      rw [hq d, hst]
      simp [sibO]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pRu st u.2 sh c1 c2
      c3 c5 r _ hlen)
    unfold coll₄A at hd
    rw [hq d, hq' d, hst] at hd
    exact hd

theorem pr_winA_false (b : Bool) :
    pr (TapeA × H3T) (winA A b false) = puAdv (comU A.um) (predUH₀ A b) := by
  let e : (Coins nfKeyBytes × Coins rBytes) × ((Coins nfKeyBytes × Coins rBytes) × RestA) ≃
      TapeA × H3T :=
    { toFun := fun z => (((z.1, z.2.1), z.2.2.1), z.2.2.2)
      invFun := fun x => (x.1.1.1, (x.1.1.2, (x.1.2, x.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winA_true (b : Bool) :
    pr (TapeA × H3T) (winA A b true) = puAdv (comU A.um) (predUH₁ A b) := by
  let e : (Coins nfKeyBytes × Coins rBytes) × ((Coins nfKeyBytes × Coins rBytes) × RestA) ≃
      TapeA × H3T :=
    { toFun := fun z => (((z.2.1, z.1), z.2.2.1), z.2.2.2)
      invFun := fun x => (x.1.1.2, (x.1.1.1, (x.1.2, x.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

set_option maxRecDepth 8192 in
/-- **The (PU) term of U5(a) on `main` with all tables shared**: at most the advantage of the two
explicit predictors, plus `4·noHitProb` (failed simulations) and `1875·2⁻¹²⁸` (collisions between
simulated proofs). -/
theorem pr_bstarUH_le (b : Bool) :
    simAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
        (gameUH A b) (fun v T => bstar Hashes.shake (gameUH A b) (fun v => r5UH A b v T) v) ≤
      4 * noHitProb + puAdv (comU A.um) (predUH₀ A b) + puAdv (comU A.um) (predUH₁ A b) +
        1875 / 2 ^ 128 := by
  show pr (TapeA × H3T) (fun z => bstar Hashes.shake (gameUH A b) (fun v => r5UH A b v z.2)
    (simVA (A := A) b z.1)) ≤ _
  have h := (pr_mono (puUH_imp A b)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _)))))
    ((pr_or_le _ _).trans (add_le_add (pr_or_le _ _) ((pr_or_le _ _).trans
      (add_le_add le_rfl (pr_or_le _ _)))))))
  rw [pr_winA_false, pr_winA_true] at h
  have e₁ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : TapeA => errC pIu x.2.2.1.1.2))).trans
    (pr_errA₁_le)
  have e₂ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : TapeA => errC pIu x.2.2.2.1.1.2))).trans
    (pr_errA₂_le)
  have e₃ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : TapeA => errC pRu x.2.2.2.2.1.1.2))).trans
    (pr_errA₃_le)
  have e₄ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : TapeA => errC pRu x.2.2.2.2.2.1.2))).trans
    (pr_errA₄_le)
  have c₂ := (le_of_eq (pr_prod_fst (β := H3T) (coll₂A A))).trans (pr_coll₂A_le A)
  have c₃ := (le_of_eq (pr_prod_fst (β := H3T) (coll₃A A b))).trans (pr_coll₃A_le A b)
  have c₄ := (le_of_eq (pr_prod_fst (β := H3T) (coll₄A A b))).trans (pr_coll₄A_le A b)
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) + (((624 : ℕ) + 1 : ℝ) / 2 ^ 128) +
      (((936 : ℕ) + 1 : ℝ) / 2 ^ 128) = 1875 / 2 ^ 128 := by norm_num
  linarith

end PrA

/-! ## Theorem U5(a) on `main` with all tables shared -/

section MainA

variable (A : AdversaryUH)

/-- **Theorem U5(a) on `main` (no label rows), two redemption queries, all tables shared, with the
(PU) advantage of explicit predictors.** For the colluding adversary whose guess reads `H₃` at
`q3` points, the cipher at `qE` keys and `H₅` at a consistent read set (`AdversaryUH.ConsH`), if
every PRF reduction of the adversary at the rest of the tape has advantage at most `εprf`,

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
      + 15·(Σ_{b, c} puAdv UCom (predUH_c b) + 8·noHitProb + 3750·2⁻¹²⁸)
      + collUH 0 + collUH 1 + 2·εprf.

The four `puAdv` terms are (PU) for `UCom` (bounded in the ideal-permutation model by
`puAdvPerm_unbound_le`; each predictor outputs at most `4·(q5 + 1249)` candidates,
`card_candP_le`), `collUH b` the probability that two real proofs of world `b` have one prefix
(`≤ 2⁻¹²⁸` for queries answered by different Clients, `collUH_le_of_who`). -/
theorem anonymityU_main_sharedAll {q3 qE : ℕ} (hC : A.ConsH q3 qE) {εprf : ℝ}
    (hprf : ∀ b z, prfAdv A.um.int.ci (reduction (atZ A z) simIU simRU b (ccA z)) ≤ εprf) :
    |realUH A false - realUH A true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comU A.um) (predUH₀ A false) +
        puAdv (comU A.um) (predUH₁ A false) + puAdv (comU A.um) (predUH₀ A true) +
        puAdv (comU A.um) (predUH₁ A true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        (collUH A false + collUH A true) + 2 * εprf := by
  have r0 := real_sim_UH A hC false
  have r1 := real_sim_UH A hC true
  have p0 := pr_bstarUH_le A false
  have p1 := pr_bstarUH_le A true
  have f0 := prf_hop_UH A false (hprf false)
  have f1 := prf_hop_UH A true (hprf true)
  have e := idealUH_eq A
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 f0
  have := abs_sub_le_iff.1 f1
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **U5(a) on `main` with all tables shared, for queries answered by different Clients**
(`TwoClientsU`): the prefix-collision term is `2·2⁻¹²⁸`. -/
theorem anonymityU_main_sharedAll_two (hW : TwoClientsU A) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    {εprf : ℝ}
    (hprf : ∀ b z, prfAdv A.um.int.ci (reduction (atZ A z) simIU simRU b (ccA z)) ≤ εprf) :
    |realUH A false - realUH A true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) + 15 * (puAdv (comU A.um) (predUH₀ A false) +
        puAdv (comU A.um) (predUH₁ A false) + puAdv (comU A.um) (predUH₀ A true) +
        puAdv (comU A.um) (predUH₁ A true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 / 2 ^ 128 + 2 * εprf := by
  have h := anonymityU_main_sharedAll A hC hprf
  have c0 := collUH_le_of_who A hW false
  have c1 := collUH_le_of_who A hW true
  have : (2 : ℝ) / 2 ^ 128 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by ring
  linarith

end MainA

end VoleMole.Privacy.MoussakaUnbound

