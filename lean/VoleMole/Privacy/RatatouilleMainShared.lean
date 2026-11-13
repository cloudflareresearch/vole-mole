import VoleMole.ZK.MainSharedGame
import VoleMole.Privacy.RatatouilleMainPub
import VoleMole.Privacy.RatatouilleRO

/-!
# Ratatouille unlinkability on `main`, with a shared `H₅` table and cipher

`unlinkability_main` (`Privacy/RatatouilleMain.lean`) is Theorem 2 on `main` (no dedicated label
rows) when each of the four proofs has its own tables. Here the four proofs **share the `H₅`
table** (on every 37-byte input) **and the cipher table**, as in the scheme; each proof keeps its
own `H₃` slice and its own `H₂³` table, both visible to the adversary, the latter programmed by the
simulator (`ZK/MainSharedGame.lean`). This is the instance of `ZK.Sim.main_shared_le` for
Ratatouille, as `Privacy/MoussakaMainShared.lean` is for Moussaka.

## The game (`realSR`)

The malicious Issuer of `Ratatouille.Adversary` (key, context, initial balance, responses, refunds
and amounts chosen from the transcripts, without reading the tables), whose guess sees the shared
tables and the four proofs' own tables (`AdversarySR`, `ZK.Sim.GVis`). The four proofs (two
issuances, round 1's spend, round 2's spend) are the executable prover (`ZK.Sim.realRO`) for
`main`'s statements, run as in `Spec/Ratatouille.lean`. A spend proof is computed only if its
round runs (`ok₁ₘ`, `ok₂ₘ`): otherwise the request is not shown, and here the proof is not
computed (`gameSR`; in `Privacy/RatatouilleMain.lean` it is computed and hidden). The guess's input
is `Privacy/RatatouilleMain.lean`'s `gR`.

## With all proofs simulated (`simSR_eq`, `simSR_iff`)

The guess's input is public (`gR_pub`). The tables the guess sees are the raw tables with each
proof's `H₂³` table programmed for its statement. **The programming is a function of the
requests** (`vtab`, §10.2's `Vtab` for this model): an issuance statement is the request's
commitment, a spend statement the request's nullifier, amount and new commitment (`stIq`, `stSq`),
and a simulation that produced no proof programs independently of its statement
(`ZK.Sim.progRO_of_error`; `simVis_iss`, `simVis_sp`). So the simulated game is
`Ratatouille.reduction` for the Issuer `A.atS a` whose guess computes `vtab` from what it sees,
the simulators' coins and the raw tables `a`. The hiding hop and the coincidence of the worlds are
then those of `Privacy/Ratatouille.lean`, for every `a` (`hiding_hopSR`, `idealSR_eq`).

## The bound (`unlinkability_main_shared0`)

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]|
      ≤ 30·εS(q₃, q_E + 8·4607) + 15·(PU(b₁, b₂) + PU(b₁', b₂')) + 2·εhide

with `εS` as in `ZK.Sim.main_shared_le`, `PU` (`puTermSR`) the probability of `ZK.Sim.bstar` in
the world with all four proofs simulated (bounded in `Privacy/RatatouilleMainSharedPU.lean`), and
`εhide` the hiding of `Com` for the reductions `redSR`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] simulate realRO progRO

/-! ## The simulator's programming as a function of the requests -/

/-- A statement with an empty witness (the simulator's programming reads the statement only). -/
def swOf (st : Statement) : SW := (st, ByteArray.empty)

variable [HasPrg]

/-- **The simulator's tables depend on the statement only, and not on it if the simulation
failed.** -/
lemma simVis_stmt {p : Params} (c : SimCoins p) (V : VP p) (y y' : SW) (u : USh)
    (h : y.1 = y'.1 ∨ ∃ e, simulate p c = .error e) :
    simVis Hashes.shake p c V (some y) u = simVis Hashes.shake p c V (some y') u := by
  rcases h with h | ⟨e, he⟩
  · simp only [simVis, h]
  · simp only [simVis]
    rw [progRO_of_error Hashes.shake he (withP y.1 p) (withP y'.1 p)]

section Requests

variable (B : AdversaryRM)

/-- **The statement of an issuance proof, from the request**: the request's commitment (a dummy
one if the Client threw; the programming is then independent of it). -/
def stIq (req : Except Error (IssueRequest Sizes.main)) : Option Statement :=
  if B.tInit = 0 then none else
  some (stI ⟨match req with
    | .ok q => issueReqC q
    | .error _ => dummyC, B.tInit, B.ctx⟩)

/-- **The statement of a spend proof, from the request**: its nullifier, amount and new
commitment. -/
def stSq (rq : Except Error (SpendRequest Sizes.main)) : Statement :=
  match rq with
  | .ok q => stS ⟨B.pk, (SpendReq.parse q).nf, (SpendReq.parse q).d, (SpendReq.parse q).cNext,
      B.ctx⟩
  | .error _ => stS ⟨B.pk, nf0, 0, dummyC, B.ctx⟩

/-- The request of a simulated issuance. -/
lemma issO_req_sim (x : Coins 24 × Coins 16) (c : SimCoins pIr) (hT : ¬ B.tInit = 0) :
    (issO B x (some (simulate pIr c))).req =
      match vecOf Sizes.main.issue (simulate pIr c) with
      | none => .error .runtime
      | some pf => .ok (issueReqBytes (comI B x.1 x.2) pf) := by
  unfold issO issOutOf issueM
  simp only [hT, ↓reduceIte, pfR]
  cases vecOf Sizes.main.issue (simulate pIr c) <;> rfl

/-- **The programming of a simulated issuance is the one of its request's statement.** -/
lemma simVis_iss (x : Coins 24 × Coins 16) (c : SimCoins pIr) (V : VP pIr) (u : USh) :
    simVis Hashes.shake pIr c V (issStmtR B x) u =
      simVis Hashes.shake pIr c V ((stIq B (issO B x ((issStmtR B x).map
        fun _ => simulate pIr c)).req).map swOf) u := by
  unfold issStmtR stIq
  by_cases hT : B.tInit = 0
  · simp only [hT, ↓reduceIte, Option.map_none]
  · simp only [hT, ↓reduceIte, Option.map_some]
    rw [issO_req_sim B x c hT]
    rcases hv : vecOf Sizes.main.issue (simulate pIr c) with _ | pf
    · exact simVis_stmt c V _ _ u (Or.inr (vecOf_none_simulate (by decide) hv))
    · refine simVis_stmt c V _ _ u (Or.inl ?_)
      simp only [swOf, issueReqC_mk]
      rfl

/-- The statement and the request of a simulated spend of a token that passes the refusal
test. -/
lemma spO_req_sim (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (c : SimCoins pSr)
    (hok : (tokIface B.int).ok τ d = true) :
    ∃ t' w, spStmt B τ d x = some (stS ⟨B.pk, τ.nf, d, com (vec x.1) B.ctx t' (vec x.2), B.ctx⟩, w) ∧
      (spO B τ d x (some (simulate pSr c))).req =
        match vecOf Sizes.main.spend (simulate pSr c) with
        | none => .error .runtime
        | some pf => .ok (SpendReq.toBytes ⟨τ.nf, d, com (vec x.1) B.ctx t' (vec x.2), pf⟩) := by
  simp only [tokIface, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hv, hc⟩ := hok
  have hv' : τ.Valid B.pk B.ctx := hv
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hc
  refine ⟨t', encS ⟨B.pk, τ.nf, d, com (vec x.1) B.ctx t' (vec x.2), B.ctx⟩
    ⟨τ.t, τ.r, τ.x, τ.s, vec x.1, t', vec x.2⟩, ?_, ?_⟩
  · unfold spStmt
    simp only [hv', not_true_eq_false, ↓reduceIte, ht']
  · unfold spO spOutOf spendM
    simp only [hv', not_true_eq_false, ↓reduceIte, ht', pfR]
    cases vecOf Sizes.main.spend (simulate pSr c) <;> rfl

/-- **The programming of a simulated spend is the one of its request's statement**, for a token
that passes the refusal test. -/
lemma simVis_sp (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (c : SimCoins pSr)
    (V : VP pSr) (u : USh) (hok : (tokIface B.int).ok τ d = true) :
    simVis Hashes.shake pSr c V (spStmt B τ d x) u =
      simVis Hashes.shake pSr c V (some (swOf (stSq B (spO B τ d x ((spStmt B τ d x).map
        fun _ => simulate pSr c)).req))) u := by
  obtain ⟨t', w, hst, hreq⟩ := spO_req_sim B τ d x c hok
  rw [hst, Option.map_some, hreq]
  rcases hv : vecOf Sizes.main.spend (simulate pSr c) with _ | pf
  · exact simVis_stmt c V _ _ u (Or.inr (vecOf_none_simulate (by decide) hv))
  · refine simVis_stmt c V _ _ u (Or.inl ?_)
    simp only [swOf, stSq, parse_toBytes]

lemma gR_snd_of_ok₁ (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ o₄ : Option Out)
    (h : ok₁ₘ B s o₁ o₂ = true) :
    (gR B b₁ b₂ s o₁ o₂ o₃ o₄).2 = some ((sp₁ₘ B b₁ s o₁ o₂ o₃).req,
      bif ok₂ₘ B b₁ s o₁ o₂ o₃ then
        some (spO B (τ₂ₘ B b₁ b₂ s o₁ o₂ o₃) (d₂ₘ B b₁ s o₁ o₂ o₃) s.2.2 o₄).req else none) := by
  rw [gR_eq]
  unfold vG
  rw [show vOk₁ B.int (tokIface B.int) (issO B s.1.1 o₁) (issO B s.1.2 o₂) = true from h]
  rfl

end Requests

/-! ## The adversary and the game -/

/-- The tables the guess sees: the shared `H₅` table and cipher, and each proof's `H₃` slice and
`H₂³` table (issuance 0, 1; round 1's spend, round 2's spend). -/
abbrev VisSR := GVis pIr pIr pSr pSr

/-- **The malicious Issuer on `main` with shared tables**: `Adversary`'s interaction (not reading
the tables) and a guess that also sees the tables, with its `H₅` read set `R5`. -/
structure AdversarySR where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr Sizes.main → Bool → Preimage
  d₁ : IssTr Sizes.main → Credits
  respond₁ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → SpendResponse
  d₂ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → Credits
  guess : GIn → VisSR → Prop
  R5 : GIn → VisSR → Finset (ZK.Sim.Bytes 37)

namespace AdversarySR

variable (A : AdversarySR)

/-- The Issuer's interaction as an `AdversaryRM` (the guess and the read sets are not used). -/
def toM : AdversaryRM :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂, fun _ _ => True, fun _ _ => ∅,
    fun _ _ => ∅, fun _ _ => ∅, fun _ _ => ∅⟩

/-- **Consistent reads**: with its input fixed, the guess and its `H₅` read set read each `H₃`
slice at `q3` keys, the cipher at `qE` keys and `H₅` at `R5`. -/
structure Cons (q3 qE : ℕ) : Prop where
  g : ∀ y, RdT (A.guess y) (A.R5 y) q3 qE
  r : ∀ y, RdT (A.R5 y) (A.R5 y) q3 qE

end AdversarySR

variable (A : AdversarySR)

/-- **The game of world `(b₁, b₂)`**, as four proofs in sequence: the two issuance proofs, round
1's spend proof if the round runs, round 2's spend proof if both rounds run. -/
def gameSR (b₁ b₂ : Bool) : Game SecR Out SW SW SW SW where
  σ₁ s := issStmtR A.toM s.1.1
  σ₂ s _ := issStmtR A.toM s.1.2
  σ₃ s o₁ o₂ := bif ok₁ₘ A.toM s o₁ o₂ then
    spStmt A.toM (τ₁ₘ A.toM b₁ s o₁ o₂) (A.d₁ (trₘ A.toM s o₁ o₂)) s.2.1 else none
  σ₄ s o₁ o₂ o₃ := bif ok₁ₘ A.toM s o₁ o₂ && ok₂ₘ A.toM b₁ s o₁ o₂ o₃ then
    spStmt A.toM (τ₂ₘ A.toM b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A.toM b₁ s o₁ o₂ o₃) s.2.2 else none

/-- What the guess gets besides the tables (`gR`). -/
def keyMS (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr) : GIn :=
  gR A.toM b₁ b₂ v.s v.o₁ v.o₂ v.o₃ v.o₄

/-- **The final event of world `(b₁, b₂)`**: the guess, on the view. -/
def evSR (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr) : Prop :=
  A.guess (keyMS A b₁ b₂ v) v.vis

/-- The `H₅` read set of the final event. -/
def r5SR (b₁ b₂ : Bool) (v : GView SecR pIr pIr pSr pSr) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyMS A b₁ b₂ v) v.vis

/-- **The real game on `main` with shared tables** in world `(b₁, b₂)`: the executable prover for
`main`'s statements, one `H₅` table and one cipher for the four proofs, SHAKE for the hashes that
are not tables. -/
noncomputable def realSR (b₁ b₂ : Bool) : ℝ :=
  hyb Hashes.shake (gameSR A b₁ b₂) false false false false (evSR A b₁ b₂)

/-- **The (PU) term of world `(b₁, b₂)`**: `ZK.Sim.bstar` in the game with all four proofs
simulated. -/
noncomputable def puTermSR (b₁ b₂ : Bool) : ℝ :=
  hyb Hashes.shake (gameSR A b₁ b₂) true true true true
    (bstar Hashes.shake (gameSR A b₁ b₂) (r5SR A b₁ b₂))

/-! ## The hypotheses of the joint hop -/

lemma gvalidSR (b₁ b₂ : Bool) : GValid (gameSR A b₁ b₂) pIr pIr pSr pSr where
  v₁ s := issStmtR_valid A.toM s.1.1
  v₂ s _ := issStmtR_valid A.toM s.1.2
  v₃ s o₁ o₂ y hy := by
    have hy' : y ∈ (bif ok₁ₘ A.toM s o₁ o₂ then
      spStmt A.toM (τ₁ₘ A.toM b₁ s o₁ o₂) (A.d₁ (trₘ A.toM s o₁ o₂)) s.2.1 else none) := hy
    cases h : ok₁ₘ A.toM s o₁ o₂
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact spStmt_valid A.toM _ _ _ y hy'
  v₄ s o₁ o₂ o₃ y hy := by
    have hy' : y ∈ (bif ok₁ₘ A.toM s o₁ o₂ && ok₂ₘ A.toM b₁ s o₁ o₂ o₃ then
      spStmt A.toM (τ₂ₘ A.toM b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A.toM b₁ s o₁ o₂ o₃) s.2.2 else none) := hy
    cases h : ok₁ₘ A.toM s o₁ o₂ && ok₂ₘ A.toM b₁ s o₁ o₂ o₃
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact spStmt_valid A.toM _ _ _ y hy'

lemma rd_evSR {q3 qE : ℕ} (hC : A.Cons q3 qE) (b₁ b₂ : Bool) :
    Rd (evSR A b₁ b₂) (r5SR A b₁ b₂) q3 qE :=
  Rd.ofT (keyMS A b₁ b₂) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun y t => A.guess y t) (fun y t => A.R5 y t) fun y => hC.g y

lemma rd_r5SR {q3 qE : ℕ} (hC : A.Cons q3 qE) (b₁ b₂ : Bool) :
    Rd (r5SR A b₁ b₂) (r5SR A b₁ b₂) q3 qE :=
  Rd.ofT (keyMS A b₁ b₂) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun y t => A.R5 y t) (fun y t => A.R5 y t) fun y => hC.r y

/-- **The joint hop in each world**: real against simulated, `15·εS + 15·PU`. -/
theorem real_sim_sharedR {q3 qE : ℕ} (hC : A.Cons q3 qE) (b₁ b₂ : Bool) :
    |realSR A b₁ b₂ - hyb Hashes.shake (gameSR A b₁ b₂) true true true true (evSR A b₁ b₂)| ≤
      15 * εS q3 (qE + 8 * 4607) + 15 * puTermSR A b₁ b₂ :=
  main_shared_le Hashes.shake (gameSR A b₁ b₂) mainP_pIr mainP_pIr mainP_pSr mainP_pSr small_pIr
    small_pIr small_pSr small_pSr hashesWF_shake (gvalidSR A b₁ b₂) (evSR A b₁ b₂)
    (r5SR A b₁ b₂) (rd_evSR A hC b₁ b₂) (rd_r5SR A hC b₁ b₂)

/-! ## With all proofs simulated: the public world, and the tables from the requests -/

/-- The simulators' coins and the raw tables (the tape of the simulated game without the
secret). -/
abbrev AuxSR := USh × KS pIr × KS pIr × KS pSr × KS pSr

/-- The simulators' coins. -/
def coSR (a : AuxSR) : CoR := ((a.2.1.1.2, a.2.2.1.1.2), (a.2.2.2.1.1.2, a.2.2.2.2.1.2))

/-- **The tables the guess sees with all proofs simulated, from what it sees** (the requests), the
simulators' coins and the raw tables: each proof's `H₂³` table is programmed for the statement of
its request (§10.2's `Vtab`). -/
noncomputable def vtab (g : GIn) (a : AuxSR) : VisSR :=
  (a.1, (simVis Hashes.shake pIr a.2.1.1.2 a.2.1.2 ((stIq A.toM g.1.1).map swOf) a.1,
    simVis Hashes.shake pIr a.2.2.1.1.2 a.2.2.1.2 ((stIq A.toM g.1.2).map swOf) a.1,
    simVis Hashes.shake pSr a.2.2.2.1.1.2 a.2.2.2.1.2
      (g.2.map fun r => swOf (stSq A.toM r.1)) a.1,
    simVis Hashes.shake pSr a.2.2.2.2.1.2 a.2.2.2.2.2
      ((g.2.bind fun r => r.2).map fun r => swOf (stSq A.toM r)) a.1))

/-- **The guess's input with all proofs simulated**, from the secret (through the nullifiers and
the commitments only) and the simulators' coins. -/
noncomputable def gS (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) : GIn :=
  gP A.toM b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) (coSR a)

section SimView

variable (b₁ b₂ : Bool) (s : SecR) (a : AuxSR)

/-- The outputs of the simulated game. -/
noncomputable def oS₁ : Option Out := (issStmtR A.toM s.1.1).map fun _ => simulate pIr a.2.1.1.2

noncomputable def oS₂ : Option Out :=
  (issStmtR A.toM s.1.2).map fun _ => simulate pIr a.2.2.1.1.2

noncomputable def oS₃ : Option Out :=
  ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)).map fun _ => simulate pSr a.2.2.2.1.1.2

noncomputable def oS₄ : Option Out :=
  ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)).map
    fun _ => simulate pSr a.2.2.2.2.1.2

lemma oS₃_eq (h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) = true) :
    oS₃ A b₁ b₂ s a = (spStmt A.toM (τ₁ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a))
      (A.toM.d₁ (trₘ A.toM s (oS₁ A s a) (oS₂ A s a))) s.2.1).map
        fun _ => simulate pSr (coSR a).2.1 := by
  unfold oS₃
  show (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) then _ else none).map _ = _
  rw [h]
  rfl

lemma oS₄_eq (h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) = true)
    (h' : ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) = true) :
    oS₄ A b₁ b₂ s a = (spStmt A.toM
      (τ₂ₘ A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a))
      (d₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) s.2.2).map
        fun _ => simulate pSr (coSR a).2.2 := by
  unfold oS₄
  show (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) &&
    ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) then _ else none).map _ = _
  rw [h, h']
  rfl

/-- **With all proofs simulated, the guess's input is public.** -/
theorem keyS_pub : gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
    (oS₄ A b₁ b₂ s a) = gS A b₁ b₂ s a :=
  gR_pub A.toM b₁ b₂ s (coSR a) _ _ _ _ rfl rfl (oS₃_eq A b₁ b₂ s a) (oS₄_eq A b₁ b₂ s a)

/-- **Round 1's spend proof is programmed for its request's statement.** -/
lemma vis₃_eq (c : SimCoins pSr) (V : VP pSr) (u : USh)
    (hc : c = a.2.2.2.1.1.2) :
    simVis Hashes.shake pSr c V ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) u =
      simVis Hashes.shake pSr c V ((gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
        (oS₄ A b₁ b₂ s a)).2.map fun r => swOf (stSq A.toM r.1)) u := by
  subst hc
  show simVis Hashes.shake pSr _ V (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) then _ else none) u
    = _
  cases h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a)
  · rw [gR_of_not_ok₁ A.toM b₁ b₂ s _ _ _ _ h]
    rfl
  · rw [gR_snd_of_ok₁ A.toM b₁ b₂ s _ _ _ _ h, Option.map_some, Bool.cond_true]
    have e := simVis_sp A.toM (τ₁ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a))
      (A.toM.d₁ (trₘ A.toM s (oS₁ A s a) (oS₂ A s a))) s.2.1 a.2.2.2.1.1.2 V u
      (ok_of_ok₁ (B := A.toM.int) b₁ h)
    have e₃ : oS₃ A b₁ b₂ s a = (spStmt A.toM (τ₁ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a))
        (A.toM.d₁ (trₘ A.toM s (oS₁ A s a) (oS₂ A s a))) s.2.1).map
          fun _ => simulate pSr a.2.2.2.1.1.2 := oS₃_eq A b₁ b₂ s a h
    refine e.trans ?_
    rw [← e₃]
    rfl

/-- **Round 2's spend proof is programmed for its request's statement.** -/
lemma vis₄_eq (c : SimCoins pSr) (V : VP pSr) (u : USh)
    (hc : c = a.2.2.2.2.1.2) :
    simVis Hashes.shake pSr c V
        ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) u =
      simVis Hashes.shake pSr c V (((gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a)
        (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)).2.bind fun r => r.2).map
          fun r => swOf (stSq A.toM r)) u := by
  subst hc
  show simVis Hashes.shake pSr _ V (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) &&
    ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) then _ else none) u = _
  cases h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a)
  · rw [gR_of_not_ok₁ A.toM b₁ b₂ s _ _ _ _ h]
    rfl
  · rw [gR_snd_of_ok₁ A.toM b₁ b₂ s _ _ _ _ h]
    cases h' : ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
    · rfl
    · simp only [Bool.and_self, Bool.cond_true, Option.bind_some, Option.map_some]
      have e := simVis_sp A.toM (τ₂ₘ A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a))
        (d₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) s.2.2 a.2.2.2.2.1.2 V u
        (ok_of_ok₂ (B := A.toM.int) b₁ b₂ h')
      have e₄ : oS₄ A b₁ b₂ s a = (spStmt A.toM
          (τ₂ₘ A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a))
          (d₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) s.2.2).map
            fun _ => simulate pSr a.2.2.2.2.1.2 := oS₄_eq A b₁ b₂ s a h h'
      refine e.trans ?_
      rw [← e₄]

end SimView

/-- **With all four proofs simulated, what the guess gets is public**: any function of the guess's
input and the tables is the same function of `gS` and `vtab`. -/
theorem simSR_eq {X : Sort*} (f : GIn → VisSR → X) (b₁ b₂ : Bool)
    (x : GTape SecR pIr pIr pSr pSr) :
    f (keyMS A b₁ b₂ (hybV Hashes.shake (gameSR A b₁ b₂) true true true true x))
        (hybV Hashes.shake (gameSR A b₁ b₂) true true true true x).vis =
      f (gS A b₁ b₂ x.1 x.2) (vtab A (gS A b₁ b₂ x.1 x.2) x.2) := by
  obtain ⟨s, a⟩ := x
  have hg := keyS_pub A b₁ b₂ s a
  have hv₁ := simVis_iss A.toM s.1.1 a.2.1.1.2 a.2.1.2 a.1
  have hv₂ := simVis_iss A.toM s.1.2 a.2.2.1.1.2 a.2.2.1.2 a.1
  have hv₃ := vis₃_eq A b₁ b₂ s a a.2.2.2.1.1.2 a.2.2.2.1.2 a.1 rfl
  have hv₄ := vis₄_eq A b₁ b₂ s a a.2.2.2.2.1.2 a.2.2.2.2.2 a.1 rfl
  show f (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a))
    (a.1, (simVis Hashes.shake pIr a.2.1.1.2 a.2.1.2 (issStmtR A.toM s.1.1) a.1,
      simVis Hashes.shake pIr a.2.2.1.1.2 a.2.2.1.2 (issStmtR A.toM s.1.2) a.1,
      simVis Hashes.shake pSr a.2.2.2.1.1.2 a.2.2.2.1.2
        ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) a.1,
      simVis Hashes.shake pSr a.2.2.2.2.1.2 a.2.2.2.2.2
        ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) a.1)) = _
  rw [hv₁, hv₂, hv₃, hv₄]
  have e₁ : (issO A.toM s.1.1 ((issStmtR A.toM s.1.1).map fun _ => simulate pIr a.2.1.1.2)).req =
      (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)).1.1 := rfl
  have e₂ : (issO A.toM s.1.2 ((issStmtR A.toM s.1.2).map
      fun _ => simulate pIr a.2.2.1.1.2)).req =
      (gR A.toM b₁ b₂ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)).1.2 := rfl
  rw [e₁, e₂, hg]
  rfl

/-! ## The hiding hop and the ideal world -/

/-- **The Issuer that computes the programmed tables from what it sees**, the simulators' coins
and the raw tables fixed. -/
noncomputable def AdversarySR.atS (a : AuxSR) : Adversary Sizes.main :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂,
    fun tr y => A.guess (tr, y) (vtab A (tr, y) a)⟩

/-- **The reduction to hiding**: `Ratatouille.reduction` for the Issuer `A.atS a`, the simulators'
coins and the raw tables `a` fixed. It evaluates each commitment function once. -/
noncomputable def redSR (b₁ b₂ : Bool) (a : AuxSR) :
    Quad Nullifier → Quad (Credits → Commitment) → Prop :=
  reduction (A.atS a) simIR simSR b₁ b₂ (coSR a)

/-- The game after the hiding hop: uniform commitments. -/
noncomputable def idealSR (b₁ b₂ : Bool) (y : UTape × AuxSR) : Prop :=
  redSR A b₁ b₂ y.2 (hideIdeal y.1).1 (hideIdeal y.1).2

/-- **The reduction is the guess on the public world**, for any nullifiers and commitment
functions; the issued tokens' functions are read at `T_init`. -/
lemma redSR_iff (b₁ b₂ : Bool) (a : AuxSR) (n : Quad Nullifier)
    (cf : Quad (Credits → Commitment)) :
    redSR A b₁ b₂ a n cf ↔
      A.guess (gP A.toM b₁ b₂ n (cf.1.1 A.tInit, cf.1.2 A.tInit) cf.2.1 cf.2.2 (coSR a))
        (vtab A (gP A.toM b₁ b₂ n (cf.1.1 A.tInit, cf.1.2 A.tInit) cf.2.1 cf.2.2 (coSR a)) a) :=
  Iff.rfl

/-- The reduction on the honest commitments is the guess on the public values. -/
lemma redSR_real (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) :
    redSR A b₁ b₂ a (hideReal A.ctx s).1 (hideReal A.ctx s).2 ↔
      A.guess (gS A b₁ b₂ s a) (vtab A (gS A b₁ b₂ s a) a) := by
  have e₁ : (hideReal A.ctx s).1 = nS s := rfl
  have e₂ : ((hideReal A.ctx s).2.1.1 A.tInit, (hideReal A.ctx s).2.1.2 A.tInit) =
      tS A.toM s := rfl
  have e₃ : (hideReal A.ctx s).2.2.1 = cfS A.toM s.2.1 := rfl
  have e₄ : (hideReal A.ctx s).2.2.2 = cfS A.toM s.2.2 := rfl
  rw [redSR_iff, e₁, e₂, e₃, e₄]
  rfl

/-- **With all four proofs simulated, the final event is the reduction on the honest
commitments.** -/
theorem simSR_iff (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr) :
    evSR A b₁ b₂ (hybV Hashes.shake (gameSR A b₁ b₂) true true true true x) ↔
      redSR A b₁ b₂ x.2 (hideReal A.ctx x.1).1 (hideReal A.ctx x.1).2 :=
  (iff_of_eq (simSR_eq A A.guess b₁ b₂ x)).trans (redSR_real A b₁ b₂ x.1 x.2).symm

theorem hiding_hopSR (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ a, hidingAdv A.ctx (redSR A b₁ b₂ a) ≤ εhide) :
    |hyb Hashes.shake (gameSR A b₁ b₂) true true true true (evSR A b₁ b₂) -
      pr _ (idealSR A b₁ b₂)| ≤ εhide := by
  unfold hyb
  rw [pr_congr (simSR_iff A b₁ b₂)]
  exact abs_pr_prod_sub_le' (fun x : HTape × AuxSR => redSR A b₁ b₂ x.2
    (hideReal A.ctx x.1).1 (hideReal A.ctx x.1).2) _ fun a => hhide a

/-- **In the ideal world the four worlds coincide, for every Issuer and all simulator coins**
(`Ratatouille.idealGame_eq` with the coins fixed): a permutation of the three nullifiers `nf₀`,
`nf₁`, `nf'₁` maps one world to another. -/
theorem ideal_eq_at {CI CS : Type} (B : Adversary Sizes.main)
    (simI : IssueInstance → CI → Option (IssueProof Sizes.main))
    (simS : SpendInstance → CS → Option (SpendProof Sizes.main)) (co : (CI × CI) × (CS × CS))
    (b₁ b₂ : Bool) :
    pr UTape (fun u => idealGame B simI simS b₁ b₂ (u, co)) =
      pr UTape (fun u => idealGame B simI simS false false (u, co)) := by
  have e (c₁ c₂ : Bool) (u : UTape) : idealGame B simI simS c₁ c₂ (u, co) ↔
      idealW B simI simS (bif c₁ then vec u.1.2.1 else vec u.1.1.1)
        (bif c₂ == c₁ then vec u.2.1.1 else bif c₁ then vec u.1.1.1 else vec u.1.2.1)
        (vec u.1.1.2) (vec u.1.2.2) (vec u.2.1.2) (vec u.2.2.2) co :=
    idealGame_iff B simI simS c₁ c₂ (u, co)
  rw [pr_congr (e b₁ b₂), pr_congr (e false false)]
  cases b₁ <;> cases b₂ <;>
    simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.cond_true,
      Bool.cond_false]
  · rw [← pr_equiv (permU (⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun u => idealW B simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
        (vec u.2.1.2) (vec u.2.2.2) co)]
    exact pr_congr fun _ => Iff.rfl
  · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.2.2, z.1), fun z => (z.2.2, z.1, z.2.1),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun u => idealW B simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
        (vec u.2.1.2) (vec u.2.2.2) co)]
    exact pr_congr fun _ => Iff.rfl
  · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.1, z.2.2), fun z => (z.2.1, z.1, z.2.2),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun u => idealW B simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
        (vec u.2.1.2) (vec u.2.2.2) co)]
    exact pr_congr fun _ => Iff.rfl

/-- **After the hiding hop the four worlds coincide**, tables included. -/
theorem idealSR_eq (b₁ b₂ : Bool) :
    pr _ (idealSR A b₁ b₂) = pr _ (idealSR A false false) := by
  have h := abs_pr_prod_sub_le' (fun y : UTape × AuxSR => idealSR A b₁ b₂ y)
    (fun y : UTape × AuxSR => idealSR A false false y) (ε := 0)
    fun a => by
      rw [show pr UTape (fun u => idealSR A b₁ b₂ (u, a)) =
        pr UTape (fun u => idealSR A false false (u, a)) from
          ideal_eq_at (A.atS a) simIR simSR (coSR a) b₁ b₂, sub_self, abs_zero]
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-! ## Unlinkability on `main`, shared tables -/

/-- **Theorem 2 on `main` (no label rows) with a shared `H₅` table and cipher, under (PU).** For
the malicious Issuer whose guess reads the tables consistently (`AdversarySR.Cons q3 qE`), if
every hiding reduction of the Issuer at fixed coins and tables has advantage at most `εhide`, any
two worlds of the real game differ by at most

    30·εS(q3, qE + 8·4607) + 15·(puTermSR (b₁, b₂) + puTermSR (b₁', b₂')) + 2·εhide. -/
theorem unlinkability_main_shared0 {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b₁ b₂ a, hidingAdv A.ctx (redSR A b₁ b₂ a) ≤ εhide) (b₁ b₂ b₁' b₂' : Bool) :
    |realSR A b₁ b₂ - realSR A b₁' b₂'| ≤
      30 * εS q3 (qE + 8 * 4607) + 15 * (puTermSR A b₁ b₂ + puTermSR A b₁' b₂') +
        2 * εhide := by
  have r0 := real_sim_sharedR A hC b₁ b₂
  have r1 := real_sim_sharedR A hC b₁' b₂'
  have h0 := hiding_hopSR A b₁ b₂ (hhide b₁ b₂)
  have h1 := hiding_hopSR A b₁' b₂' (hhide b₁' b₂')
  have e0 := idealSR_eq A b₁ b₂
  have e1 := idealSR_eq A b₁' b₂'
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Ratatouille
