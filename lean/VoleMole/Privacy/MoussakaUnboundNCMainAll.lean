import VoleMole.Privacy.MoussakaUnboundNCMain
import VoleMole.Privacy.MoussakaNCMain

/-!
# Unbound Moussaka against a non-colluding Moderator on `main` (Theorem U5(b)), all tables shared

`anonymityNC_main_U` (`Privacy/MoussakaUnboundNCMain.lean`) is Theorem U5(b) on `main` with two
adaptive redemption queries and **per-proof** tables. Here the two redemption proofs share all
tables, as in the scheme and as in the bound protocol's 4(b') on `main`
(`Privacy/MoussakaNCMain.lean`): one `H₃` (`H3T`), one `H₂³` table, one `H₅` table and one cipher.
The joint hop is `ZK.Sim.main_sharedAll_le`, which is generic in the game.

## The game (`realNH`)

The game of `realNU` (`gameNU`: no issuance slot, the two queries proved iff both tokens finalized
and the query is valid), run with `ZK.Sim.realAll` on the shared tables. The Moderator
(`AdversaryUNCH`) chooses `ctx_iss`, the keys and the two adaptive queries without reading the
tables; its guess sees the history (or `none`), the shared `H₅` table and cipher (`USh`), the one
`H₂³` table as programmed by the game, and `H₃`.

## The steps

1. The joint hop (`real_sim_NH`, `main_sharedAll_le`), with the prefix-collision term `collNH b`:
   the probability that the two real redemption proofs of world `b` have one prefix
   `wPrefix ‖ μ₁`. If the two queries are answered by different Clients it is at most `2⁻¹²⁸`
   (`collNH_le_of_who`); see the note below for one Client.
2. **With both proofs simulated, the view is a function of the refusal bit, the history and the
   tables** (`simNH_iff`): the `H₂³` table the guess sees is the raw table programmed for the
   statements that the history determines (`tabH`: each answer is `Derive ‖ π`, and its
   statement is the query's set, context and digest with the answer's first 32 bytes). With both
   tokens finalized the history is `histT` (`hist_good`), a function of the keys and the
   simulators' coins.
3. The abort hop (`sim_hyb_NH`), the PRF hop (`prf_hop_NH`) and the swap of `pr_run_swap`
   (`idealNH_eq`; the guess reads the tables through the history only, so the swap of the
   uniform nullifier table applies unchanged).
4. **The (PU) term is statistical** (`pr_bstarNH_le`): `bstar` on the simulated proofs is a
   failed simulation, a collision of the two proofs' sibling inputs (`313·2⁻¹²⁸`), or a prediction
   of an opening from candidates computed from the keys, the coins and the tables.

## The bound (`anonymityNC_main_U_sharedAll`)

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(8·noHitProb + (8·(q₅ + 625) + 626)·2⁻¹²⁸) + collNH 0 + collNH 1
        + 2·(ψ false + ψ true) + 2·εprf

## One Client answering both queries

`main_sharedAll_le` reduces the game with one `H₃` to the game with one slice per proof by writing
the slices into the columns at the proofs' prefixes; the prefixes are a function of the view, the
proofs' randomness `ρ` is not. Two proofs with one prefix read one column, and the reduction
charges this event whole. Two redemptions by one Client in one context with one issuer index have
one witness and one statement, hence one prefix, with probability `1`. The real prover reads its
column only at its `ρ` (`realROb_g3_congr'`), so the true cost is a collision of the two `ρ`s
(`2⁻¹²⁸`), but that needs a reduction that sees `ρ`, which `main_sharedAll_le` does not provide.
For two contexts the witnesses differ in the committed Keccak states of `Derive`, which needs
injectivity of Keccak-p[800] rounds (not in Lean). So the term stays explicit, bounded here for
queries answered by different Clients.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf pgP simSB_pg_eq candO_some)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## The Moderator with all tables shared -/

/-- **`f` reads the shared tables within explicit sets**: the `H₅` table only at `R`, the cipher
at `qE` keys, `H₃` at `q3` points (the `H₂³` table freely). -/
structure RdUH {X : Sort*} (f : USh → Tab2G pIu → H3T → X)
    (R : USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)) (q3 qE : ℕ) : Prop where
  h5 : ∀ u G2 T (G5 : Tab5F), (∀ k ∈ R u G2 T, u.1 k = G5 k) → f (G5, u.2) G2 T = f u G2 T
  hE : ∃ Q : USh → Tab2G pIu → H3T → Finset Blk, (∀ u G2 T, (Q u G2 T).card ≤ qE) ∧
    ∀ u G2 T (E : Cipher), (∀ k ∈ Q u G2 T, u.2 k = E k) → f (u.1, E) G2 T = f u G2 T
  hT : ∃ Q : USh → Tab2G pIu → H3T → Finset (Pre × ZK.Sim.Bytes 16), (∀ u G2 T, (Q u G2 T).card ≤ q3) ∧
    ∀ u G2 T T', (∀ k ∈ Q u G2 T, T k.1 k.2 = T' k.1 k.2) → f u G2 T' = f u G2 T

/-- **The non-colluding Moderator on `main` with all tables shared**: `ctx_iss`, the two issuing
keys, the two adaptive queries (`next`, not reading the tables), and a guess that sees the
history (or `none`), the shared `H₅` table and cipher, the one `H₂³` table and `H₃`, with its `H₅`
read set. -/
structure AdversaryUNCH where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  next : Hist → Query
  guess : Option Hist → USh → Tab2G pIu → H3T → Prop
  R5 : Option Hist → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)

namespace AdversaryUNCH

variable (A : AdversaryUNCH)

/-- Its interaction as an `AdversaryUNC` (for `gameNU` and its lemmas; the guess is not used). -/
def unc : AdversaryUNC := ⟨A.ctxIss, A.pk, A.next, fun _ _ => True, fun _ _ => ∅, fun _ _ => ∅⟩

/-- **Consistent reads**: with the history fixed, the guess and its `H₅` read set read `H₃` at
`q3` points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ y, RdUH (A.guess y) (A.R5 y) q3 qE
  r : ∀ y, RdUH (A.R5 y) (A.R5 y) q3 qE

end AdversaryUNCH

/-- The view of the shared game. -/
abbrev GVU := GView SecN pIu pIu pRu pRu

/-- The tape of the shared game. -/
abbrev TapeU := GTape SecN pIu pIu pRu pRu

section GameH

variable (A : AdversaryUNCH) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- **The final event of world `b`**: the guess on the history, the shared tables, the one `H₂³`
table (every slot's `H₂³` component of a shared view is that table) and `H₃`. -/
def evNH (b : Bool) (v : GVU) (T : H3T) : Prop :=
  A.guess (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T

/-- Its `H₅` read set. -/
def r5NH (b : Bool) (v : GVU) (T : H3T) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T

/-- **The real game on `main` with all tables shared** in world `b`: the executable prover for the
two redemptions, one `H₃`, one `H₂³` table, one `H₅` table, one cipher. -/
noncomputable def realNH (b : Bool) : ℝ :=
  realAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameNU A.unc PI sk b) (evNH A PI sk b)

/-- The game with both redemptions simulated. -/
noncomputable def simNH (b : Bool) : ℝ :=
  simAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameNU A.unc PI sk b) (evNH A PI sk b)

/-- **The prefix-collision term of world `b`**: the two real redemption proofs have one prefix. -/
noncomputable def collNH (b : Bool) : ℝ :=
  pr TapeU (fun x => ¬ DistV Hashes.shake (gameNU A.unc PI sk b)
    (hybV23 (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
      (gameNU A.unc PI sk b) false false false false x))

/-! ### The hypotheses of the joint hop -/

lemma gvalidNH (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    GValid (gameNU A.unc PI sk b) pIu pIu pRu pRu where
  v₁ _ y hy := by cases hy
  v₂ _ _ y hy := by cases hy
  v₃ s _ _ y hy := by
    have hy' : y ∈ (bif gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 [] (A.unc.next []) then
      redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 (A.unc.next [])) else none) := hy
    cases h : (gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 [] (A.unc.next []))
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact redStmtNU_valid A.unc PI sk hsk b s _ y hy'
  v₄ s _ _ o₃ y hy := by
    have hy' : y ∈ (bif gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2
        (hist₁ A.unc PI sk b s o₃) (qN₁ A.unc PI sk b s o₃) then
      redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 (qN₁ A.unc PI sk b s o₃)) else none) := hy
    cases h : (gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 (hist₁ A.unc PI sk b s o₃)
      (qN₁ A.unc PI sk b s o₃))
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact redStmtNU_valid A.unc PI sk hsk b s _ y hy'

lemma rdH_ofNH {X : Sort*} {f : Option Hist → USh → Tab2G pIu → H3T → X}
    {R : Option Hist → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)} {q3 qE : ℕ}
    (h : ∀ y, RdUH (f y) (R y) q3 qE) (b : Bool) :
    RdH (fun (v : GVU) T => f (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T)
      (fun v T => R (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  refine ⟨fun v T G5 hk => (h _).h5 v.u v.v₁.2 T G5 hk,
    ⟨fun v T => QE (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T, fun _ _ => hQEc _ _ _ _,
      fun v T E hk => hQE _ v.u v.v₁.2 T E hk⟩,
    ⟨fun v T => QT (yNU A.unc PI sk b v.s v.o₃ v.o₄) v.u v.v₁.2 T, fun _ _ => hQTc _ _ _ _,
      fun v T T' hk => hQT _ v.u v.v₁.2 T T' hk⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The joint hop in each world**, both redemptions at once, all tables shared. -/
theorem real_sim_NH (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    (b : Bool) :
    |realNH A PI sk b - simNH A PI sk b| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * simAll (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
          (gameNU A.unc PI sk b) (fun v T => bstar Hashes.shake (gameNU A.unc PI sk b)
            (fun v => r5NH A PI sk b v T) v) + collNH A PI sk b :=
  main_sharedAll_le (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559) Hashes.shake
    (gameNU A.unc PI sk b) mainP_pIu mainP_pIu mainP_pRu mainP_pRu small_pIu small_pIu small_pRu
    small_pRu hashesWF_shake (gvalidNH A PI sk hsk b) (evNH A PI sk b) (r5NH A PI sk b)
    (rdH_ofNH A PI sk (f := fun y u G2 T => A.guess y u G2 T) (R := fun y u G2 T => A.R5 y u G2 T)
      hC.g b)
    (rdH_ofNH A PI sk (f := fun y u G2 T => A.R5 y u G2 T) (R := fun y u G2 T => A.R5 y u G2 T)
      hC.r b)

end GameH

/-! ## Two redemptions with one prefix -/

section CollH

variable {A : AdversaryUNCH} {PI : NIZK IssueInstance} {sk : Bool → Signer}

lemma redStmtU_size (B : AdversaryUM) (P : RedeemPt) (hp : tokWF P.tok) :
    ∀ y ∈ redStmtU B P, y.2.size = pRu.witnessBytes := by
  intro y hy
  unfold redStmtU at hy
  obtain ⟨i, -, rfl⟩ := Option.mem_map.1 hy
  show (toBA _).size = _
  rw [size_toBA]
  exact length_encodeRedeemWitness hp.1 hp.2.1 hp.2.2 i

/-- A redemption statement of the game: its witness has `559` bytes and starts with the opening of
the Client that answers the query. -/
lemma σNH_wit (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) (s : SecN) (H : Hist) (q : Query)
    (y : SW) (hy : y ∈ (bif gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 H q then
      redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 q) else none)) :
    y.2.size = pRu.witnessBytes ∧ wPre y.2 = (bif who b q then s.2 else s.1).2.1 := by
  cases hg : gN A.unc PI sk s
  · rw [hg] at hy; cases hy
  · cases hv : validNC A.unc.nc PI sk s.1 s.2 H q
    · rw [hg, hv] at hy; cases hy
    · rw [hg, hv] at hy
      have hy' : redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 q) = some y := hy
      refine ⟨redStmtU_size _ _ ?_ y hy, (redStmt_good hsk hg b q y hy').2⟩
      unfold ptNC
      cases who b q
      · exact tokDNC_wf A.unc.nc PI sk hsk false s.1
      · exact tokDNC_wf A.unc.nc PI sk hsk true s.2

/-- **The two queries are answered by different Clients**, in both worlds and whatever the
answer to the first. -/
def TwoClients (A : AdversaryUNCH) : Prop :=
  ∀ (b : Bool) (a : Except Error Bytes), who b (A.next [(A.next [], a)]) ≠ who b (A.next [])

/-- **Two redemptions of a world with one prefix**, answered by different Clients: then the two
Clients' openings agree. -/
theorem coll_impNH (hsk : ∀ c, (sk c).Correct (A.pk c)) (hW : TwoClients A) (b : Bool)
    (v : GVU) (h : ¬ DistV Hashes.shake (gameNU A.unc PI sk b) v) :
    v.s.1.2.1 = v.s.2.2.1 := by
  by_contra hne
  have r₃ : ∀ y ∈ yv₃ (gameNU A.unc PI sk b) v, y.2.size = pRu.witnessBytes ∧
      wPre y.2 = (bif who b (A.next []) then v.s.2 else v.s.1).2.1 :=
    fun y hy => σNH_wit hsk b v.s [] _ y hy
  have r₄ : ∀ y ∈ yv₄ (gameNU A.unc PI sk b) v, y.2.size = pRu.witnessBytes ∧
      wPre y.2 = (bif who b (qN₁ A.unc PI sk b v.s v.o₃) then v.s.2 else v.s.1).2.1 :=
    fun y hy => σNH_wit hsk b v.s _ _ y hy
  have hw : who b (qN₁ A.unc PI sk b v.s v.o₃) ≠ who b (A.next []) := hW b _
  have n₁ : ∀ y ∈ yv₁ (gameNU A.unc PI sk b) v, y.2.size = pIu.witnessBytes :=
    fun y hy => by cases hy
  have n₂ : ∀ y ∈ yv₂ (gameNU A.unc PI sk b) v, y.2.size = pIu.witnessBytes :=
    fun y hy => by cases hy
  have h16 : 16 ≤ pIu.witnessBytes := by decide
  have h16' : 16 ≤ pRu.witnessBytes := by decide
  have mI : pIu.witnessBytes + 32 < preMax := by decide
  have mR : pRu.witnessBytes + 32 < preMax := by decide
  apply h
  have e₁ : ∀ y, y ∉ yv₁ (gameNU A.unc PI sk b) v := fun y hy => Option.not_mem_none y hy
  have e₂ : ∀ y, y ∉ yv₂ (gameNU A.unc PI sk b) v := fun y hy => Option.not_mem_none y hy
  refine ⟨distO_of hashesWF_shake n₁ n₂ h16 mI mI fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₁ (fun y hy => (r₃ y hy).1) h16 mI mR fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₁ (fun y hy => (r₄ y hy).1) h16 mI mR fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₂ (fun y hy => (r₃ y hy).1) h16 mI mR fun y hy => (e₂ y hy).elim,
    distO_of hashesWF_shake n₂ (fun y hy => (r₄ y hy).1) h16 mI mR fun y hy => (e₂ y hy).elim,
    distO_of hashesWF_shake (fun y hy => (r₃ y hy).1) (fun y hy => (r₄ y hy).1) h16' mR mR
      fun y hy y' hy' _ => by
        rw [(r₃ y hy).2, (r₄ y' hy').2]
        cases e3 : who b (A.next []) <;> cases e4 : who b (qN₁ A.unc PI sk b v.s v.o₃)
        · exact absurd (e4.trans e3.symm) hw
        · exact hne
        · exact Ne.symm hne
        · exact absurd (e4.trans e3.symm) hw⟩

variable (A PI sk) in
/-- **The prefix-collision term is at most `2⁻¹²⁸`** when the two queries are answered by
different Clients: the two Clients' uniform openings agree. -/
theorem collNH_le_of_who (hsk : ∀ c, (sk c).Correct (A.pk c)) (hW : TwoClients A) (b : Bool) :
    collNH A PI sk b ≤ 1 / 2 ^ 128 := by
  unfold collNH
  refine (pr_mono fun x hx => coll_impNH hsk hW b _ hx).trans ?_
  have e1 := pr_prod_fst (β := USh × KS pIu × KS pIu × KS pRu × KS pRu)
    (fun s : SecN => s.1.2.1 = s.2.2.1)
  refine (le_of_eq e1).trans ?_
  let e : Coins rBytes × ((Coins nfKeyBytes × Coins proveSeedBytes) × IssT) ≃ SecN :=
    { toFun := fun z => ((z.2.1.1, z.1, z.2.1.2), z.2.2)
      invFun := fun s => (s.1.2.1, ((s.1.1, s.1.2.2), s.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  have := pr_mem_uniform_le (X := (Coins nfKeyBytes × Coins proveSeedBytes) × IssT)
    (fun z => {z.2.2.1}) (q := 0) (fun _ => by simp)
  simpa [e] using this

end CollH

/-! ## With both redemptions simulated: a function of the refusal bit, the history and the tables -/

section SimH

variable (A : AdversaryUNCH)

/-- **The statement of a history entry**: an answer `Derive ‖ π` was proved for the query's
set, context and digest, with the answer's first 32 bytes as the nullifier; a refused query was
not proved. -/
def stOfAns (q : Query) (a : Except Error Bytes) : Option Statement :=
  match a with
  | .ok bs => some (stR ⟨q.anchors.keys, bs.take nfBytes, A.unc.um.int.ci, List.ofFn q.ctxRed, q.cd⟩)
  | .error _ => none

/-- The statement of entry `j` of a history. -/
def stAt (H : Hist) (j : ℕ) : Option Statement :=
  match H[j]? with
  | some e => stOfAns A e.1 e.2
  | none => none

/-- **The `H₂³` table the guess sees after a history**: the raw table `G2` programmed by the two
simulations for the statements of the history's two entries (the first outermost). -/
noncomputable def tabH (H : Hist) (c₃ c₄ : SimCoins pRu) (u : USh) (G2 : Tab2G pIu) : Tab2G pIu :=
  pgP pRu c₃ (stAt A H 0) u (pgP pRu c₄ (stAt A H 1) u G2)

/-- **The simulated game's event** from the refusal bit `g`, the history, the simulators' coins,
the raw tables and `H₃`. -/
noncomputable def hvNH (g : Bool) (H : Hist) (c₃ c₄ : SimCoins pRu) (u : USh) (G2 : Tab2G pIu)
    (T : H3T) : Prop :=
  A.guess (bif g then some H else none) u (bif g then tabH A H c₃ c₄ u G2 else G2) T

variable {A} {PI : NIZK IssueInstance} {sk : Bool → Signer}

/-- The statement of an answered query is the statement of its proof. -/
lemma stOfAns_redOutU (b : Bool) (x₀ x₁ : IssT) (q : Query) (o : Option Out) :
    stOfAns A q (redOutU A.unc.um (ptNC A.unc.nc PI sk b x₀ x₁ q) o) =
      (redStmtU A.unc.um (ptNC A.unc.nc PI sk b x₀ x₁ q)).map Prod.fst := by
  unfold redOutU redStmtU
  cases findIssuer (ptNC A.unc.nc PI sk b x₀ x₁ q).anchors
    (ucom (ptNC A.unc.nc PI sk b x₀ x₁ q).tok.k A.unc.um.int.ci (ptNC A.unc.nc PI sk b x₀ x₁ q).tok.r)
    (ptNC A.unc.nc PI sk b x₀ x₁ q).tok.s with
  | none => rfl
  | some i =>
    show some _ = some _
    unfold xRU
    rw [List.take_left' (length_derive _ _)]
    rfl

/-- A slot's statement, gated as in the game, is the statement of its history entry. -/
lemma σ_map_fst (b : Bool) (s : SecN) (hg : gN A.unc PI sk s = true) (H : Hist) (q : Query)
    (o : Option Out) :
    (bif gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 H q then
        redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 q) else none).map Prod.fst =
      stOfAns A q (ansN A.unc PI sk b s H q o) := by
  unfold ansN
  rw [hg]
  cases validNC A.unc.nc PI sk s.1 s.2 H q
  · rfl
  · exact (stOfAns_redOutU b s.1 s.2 q o).symm

set_option maxRecDepth 8192 in
/-- **With both redemptions simulated, the final event is `hvNH`** at the refusal bit, the history
`histT` (a function of the keys and the simulators' coins), the coins and the raw tables. -/
theorem simNH_iff (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool)
    (x : TapeU) (T : H3T) :
    evNH A PI sk b (hybV23 (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559)
        Hashes.shake (gameNU A.unc PI sk b) true true true true x) T ↔
      hvNH A (gN A.unc PI sk x.1) (histT A.unc b (x.1.1.1, x.1.2.1) x.2.2.2.2.1.1.2
        x.2.2.2.2.2.1.2) x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2 x.2.1 x.2.2.1.2.2 T := by
  set G := gameNU A.unc PI sk b
  set c₃ := x.2.2.2.2.1.1.2
  set c₄ := x.2.2.2.2.2.1.2
  set u := x.2.1
  set G2 := x.2.2.1.2.2
  set o₃ := (G.σ₃ x.1 none none).map fun _ => simulate pRu c₃ with ho₃
  set o₄ := (G.σ₄ x.1 none none o₃).map fun _ => simulate pRu c₄ with ho₄
  have hM : (hybV23 (p₀ := pIu) (n₁ := 232) (n₂ := 232) (n₃ := 559) (n₄ := 559)
      Hashes.shake G true true true true x).v₁.2 =
      pgP pRu c₃ ((G.σ₃ x.1 none none).map Prod.fst) u
        (pgP pRu c₄ ((G.σ₄ x.1 none none o₃).map Prod.fst) u G2) := by
    show (simSB Hashes.shake pIu x.2.2.1.1.2 x.2.2.1.2.1).pg none u
      ((simSB Hashes.shake pIu x.2.2.2.1.1.2 x.2.2.2.1.2.1).pg none u
        ((simSB Hashes.shake pRu c₃ x.2.2.2.2.1.2.1).pg (G.σ₃ x.1 none none) u
          ((simSB Hashes.shake pRu c₄ x.2.2.2.2.2.2.1).pg (G.σ₄ x.1 none none o₃) u G2))) = _
    simp only [simSB_pg_eq]
    rfl
  show A.guess (yNU A.unc PI sk b x.1 o₃ o₄) u _ T ↔ _
  rw [hM]
  unfold hvNH
  cases hg : gN A.unc PI sk x.1
  · have h3 : G.σ₃ x.1 none none = none := by
      show (bif gN A.unc PI sk x.1 && _ then _ else none) = none
      rw [hg]; rfl
    have h4 : G.σ₄ x.1 none none o₃ = none := by
      show (bif gN A.unc PI sk x.1 && _ then _ else none) = none
      rw [hg]; rfl
    have hy : yNU A.unc PI sk b x.1 o₃ o₄ = none := by
      unfold yNU; rw [hg]; rfl
    rw [h3, h4, hy]
    rfl
  · have hy := yNU_sim A.unc PI sk b x.1 c₃ c₄
    have hg' : ((tokNC A.unc.nc PI sk false x.1.1).isSome &&
        (tokNC A.unc.nc PI sk true x.1.2).isSome) = true := hg
    rw [hg', Bool.cond_true, hist_good hsk hK b x.1 c₃ c₄ hg] at hy
    have hy' : yNU A.unc PI sk b x.1 o₃ o₄ = some (histN A.unc PI sk b x.1 o₃ o₄) := by
      unfold yNU; rw [hg]; rfl
    have hH : histN A.unc PI sk b x.1 o₃ o₄ = histT A.unc b (x.1.1.1, x.1.2.1) c₃ c₄ :=
      Option.some.inj (hy'.symm.trans hy)
    have s3 : (G.σ₃ x.1 none none).map Prod.fst = stAt A (histN A.unc PI sk b x.1 o₃ o₄) 0 :=
      σ_map_fst b x.1 hg [] _ o₃
    have s4 : (G.σ₄ x.1 none none o₃).map Prod.fst = stAt A (histN A.unc PI sk b x.1 o₃ o₄) 1 :=
      σ_map_fst b x.1 hg _ _ o₄
    rw [s3, s4, hy', ← hH]
    rfl

end SimH

/-! ## The abort hop, the PRF hop and the swap -/

section HopsH

variable (A : AdversaryUNCH) (PI : NIZK IssueInstance) (sk : Bool → Signer)

lemma simNH_eq (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool) :
    simNH A PI sk b = pr (TapeU × H3T) (fun z =>
      hvNH A (gN A.unc PI sk z.1.1) (histT A.unc b (z.1.1.1.1, z.1.1.2.1) z.1.2.2.2.2.1.1.2
        z.1.2.2.2.2.2.1.2) z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2 z.1.2.1 z.1.2.2.1.2.2 z.2) :=
  pr_congr fun z => simNH_iff hsk hK b z.1 z.2

/-- The hybrid: both issuances counted as successful. -/
noncomputable def hybNH (b : Bool) : ℝ :=
  pr (TapeU × H3T) (fun z =>
    hvNH A true (histT A.unc b (z.1.1.1.1, z.1.1.2.1) z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2)
      z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2 z.1.2.1 z.1.2.2.1.2.2 z.2)

/-- **The abort hop**: replacing the refusal bit by `true` costs `ψ false + ψ true` (identical
until an honest issuance fails). -/
theorem sim_hyb_NH (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool) :
    |simNH A PI sk b - hybNH A b| ≤ psi A.unc.nc PI sk false + psi A.unc.nc PI sk true := by
  rw [simNH_eq A PI sk hsk hK b]
  have hb := abs_pr_sub_le_of_agree
    (fun z : TapeU × H3T => hvNH A (gN A.unc PI sk z.1.1) (histT A.unc b (z.1.1.1.1, z.1.1.2.1)
      z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2) z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2 z.1.2.1
      z.1.2.2.1.2.2 z.2)
    (fun z => hvNH A true (histT A.unc b (z.1.1.1.1, z.1.1.2.1) z.1.2.2.2.2.1.1.2
      z.1.2.2.2.2.2.1.2) z.1.2.2.2.2.1.1.2 z.1.2.2.2.2.2.1.2 z.1.2.1 z.1.2.2.1.2.2 z.2)
    (fun z => failNC A.unc.nc PI sk false z.1.1.1 = true ∨ failNC A.unc.nc PI sk true z.1.1.2 = true)
    fun z hz => by
      simp only [not_or, Bool.not_eq_true] at hz
      have hg : gN A.unc PI sk z.1.1 = true := by
        unfold gN
        rw [tokNC_isSome A.unc.nc PI sk hsk, tokNC_isSome A.unc.nc PI sk hsk, hz.1, hz.2]
        rfl
      rw [hg]
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  have m0 : pr (TapeU × H3T) (fun z => failNC A.unc.nc PI sk false z.1.1.1 = true) =
      psi A.unc.nc PI sk false := by
    rw [pr_prod_fst (fun x : TapeU => failNC A.unc.nc PI sk false x.1.1 = true),
      pr_prod_fst (fun s : SecN => failNC A.unc.nc PI sk false s.1 = true),
      pr_prod_fst (fun x : IssT => failNC A.unc.nc PI sk false x = true)]
    rfl
  have m1 : pr (TapeU × H3T) (fun z => failNC A.unc.nc PI sk true z.1.1.2 = true) =
      psi A.unc.nc PI sk true := by
    rw [pr_prod_fst (fun x : TapeU => failNC A.unc.nc PI sk true x.1.2 = true),
      pr_prod_fst (fun s : SecN => failNC A.unc.nc PI sk true s.2 = true),
      pr_prod_snd (fun x : IssT => failNC A.unc.nc PI sk true x = true)]
    rfl
  rw [m0, m1]

/-- The rest of the tape: the openings and issuance seeds, the shared tables and the four slots'
coins and tables, and `H₃`. -/
abbrev RestH := ((Coins rBytes × Coins proveSeedBytes) × (Coins rBytes × Coins proveSeedBytes)) ×
  (USh × KS pIu × KS pIu × KS pRu × KS pRu) × H3T

/-- Split the tape into the keys and the rest. -/
def splitH : TapeU × H3T ≃ KTape × RestH where
  toFun z := ((z.1.1.1.1, z.1.1.2.1), (((z.1.1.1.2.1, z.1.1.1.2.2), (z.1.1.2.2.1, z.1.1.2.2.2)),
    z.1.2, z.2))
  invFun y := ((((y.1.1, y.2.1.1.1, y.2.1.1.2), (y.1.2, y.2.1.2.1, y.2.1.2.2)), y.2.2.1), y.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The adaptive run of the two simulated queries in world `b` on a nullifier table `O`. -/
noncomputable def runH (b : Bool) (O : Bool → Coins ctxBytes → Bytes) (c₃ c₄ : SimCoins pRu) : Hist :=
  interact A.next (fun H q => ctxOk H q) refused
    (List.ofFn fun j q => ySim A.unc.nc.base simRU b O q (![c₃, c₄] j)) []

/-- **The reduction to the PRF** at the rest of the tape: the guess on the run with the table it is
given. -/
noncomputable def redNH (b : Bool) (z : RestH) (O : Bool → Coins ctxBytes → Bytes) : Prop :=
  hvNH A true (runH A b O z.2.1.2.2.2.1.1.2 z.2.1.2.2.2.2.1.2) z.2.1.2.2.2.1.1.2 z.2.1.2.2.2.2.1.2
    z.2.1.1 z.2.1.2.1.2.2 z.2.2

/-- The game after the PRF hop. -/
noncomputable def idealNH (b : Bool) : ℝ :=
  pr (Table × RestH) (fun y => redNH A b y.2 (tbl y.1))

/-- **The PRF hop**. -/
theorem prf_hop_NH (b : Bool) {εprf : ℝ} (hprf : ∀ z, prfAdvNC (redNH A b z) ≤ εprf) :
    |hybNH A b - idealNH A b| ≤ εprf := by
  have e : hybNH A b = pr (KTape × RestH) (fun y => redNH A b y.2 (keyTable y.1)) := by
    unfold hybNH
    rw [← pr_equiv (splitH).symm]
    rfl
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun z => hprf z

/-- **After the PRF hop the worlds coincide**: the guess reads the uniform table only through the
run, and the swap of `pr_run_swap` exchanges the runs. -/
theorem idealNH_eq : idealNH A false = idealNH A true :=
  pr_run_swap simRU A.unc.nc.base (fun _ => A.next) (fun _ H q => ctxOk H q) (fun _ _ _ h => h)
    (fun z : RestH => ![z.2.1.2.2.2.1.1.2, z.2.1.2.2.2.2.1.2])
    (fun z H => A.guess (some H) z.2.1.1
      (tabH A H z.2.1.2.2.2.1.1.2 z.2.1.2.2.2.2.1.2 z.2.1.1 z.2.1.2.1.2.2) z.2.2)

end HopsH

end VoleMole.Privacy.MoussakaUnbound
