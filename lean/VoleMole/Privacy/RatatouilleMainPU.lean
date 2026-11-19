import VoleMole.Privacy.RatatouilleMainPub

/-!
# Ratatouille on `main`: the (PU) term as the advantage of explicit predictors

`unlinkability_main` (`Privacy/RatatouilleMain.lean`) bounds Theorem 2 on `main` by
`8·εRF + 15·(puTermR (b₁, b₂) + puTermR (b₁', b₂')) + 2·εhide`, with `puTermR` an event of the game
with all four proofs simulated. Here that event is reduced to the game `Privacy.PU.puAdv`.

**Three openings, three predictors.** The witness prefix of an issuance proof is the opening of
the issued token. The prefix of round 1's spend proof is the opening of the token spent: Client
`b₁`'s issued token. The prefix of round 2's spend proof is the opening of round 1's change token
(`b₂ = b₁`) or of Client `!b₁`'s issued token. With all proofs simulated the guess's input, the
statements and hence the candidate sets are functions of the nullifiers, the commitments, the
simulators' coins and the tables (`Privacy/RatatouilleMainPub.lean`: `gR_pub`, `σ₃_pub`,
`σ₄_pub`). So:

* `predR₀`, `predR₁` predict the opening of Client `0`'s, `1`'s issued token from its commitment
  `Com(nf, ctx, T_init, r)` (`comI`): the candidates of its issuance proof, of round 1's spend proof
  if it is the spender, and of round 2's spend proof if it spends its issued token there. At most
  `3·(q₅ + 1)` candidates (`card_predI_le`).
* `predRC` predicts the opening of round 1's change token from its commitment
  `Com(nf', ctx, t', r')` at the credit `t' = clientCheck(τ₁.t, τ₁.x, d₁)`. That credit is a function
  of the issuance part (the issued tokens and the issuance simulators' coins), which is independent
  of `(nf', r')`: it goes into the public input, and the commitment is `PU.comCredit` (`comCh`).
  The candidates are those of round 2's spend proof if `b₂ = b₁`: at most `q₅ + 1`
  (`card_predC_le`).

The opening of round 2's new token is no proof's witness prefix.

**Proofs that are computed but not shown.** If round 1 is refused, both spend proofs are computed
for tokens that may be dummies and are not shown; if round 2 is refused, its proof is. Their
witness prefix is then no secret, but the guess's read set does not depend on the proof's uniform
field `d`, so the event has probability `≤ (q₅ + 1)·2⁻¹²⁸` (`pr_hidR₃_le`, `pr_hidR₄_le`, from
`ZK.Sim.pr_d3_le`, `pr_d4_le`).

**`puTermR_le`**: `puTermR (b₁, b₂) ≤ puAdv comI predR₀ + puAdv comI predR₁ + puAdv comCh predRC +
2·(q₅ + 1)·2⁻¹²⁸`, and **`unlinkability_main_pu`**: Theorem 2 on `main` with

    8·εRF(q₃, q_E) + 15·(Σ_{worlds} (puAdv comI predR₀ + puAdv comI predR₁ + puAdv comCh predRC)
      + 4·(q₅ + 1)·2⁻¹²⁸) + 2·εhide.

`comI` and `comCh` are the concrete `Spec.Ratatouille.com`, one truncated call of
Keccak-p[800,12] (`comI_eq_comP`, `comCh_eq_comP`); the six `puAdv` terms are (PU), an assumption
on Keccak-p[800,12]. In the ideal-permutation model each is at most
`(c + q)/(2¹²⁸ − q) + q/(2⁵⁴⁴ − q)` (`PU.puAdvPerm_ratatouille_le`,
`PU.puAdvPerm_ratatouille_credit_le`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

attribute [local irreducible] simulate proveIdeal proveE firstHit

variable (A : AdversaryRM) [HasPrg]

/-! ## The commitments are truncated calls of Keccak-p[800,12] -/

/-- **`comI` is `PU.comP` at Keccak-p[800,12]**, for the state `XR ctx T_init`. -/
theorem comI_eq_comP (n : Coins 24) (r : Coins 16) :
    comI A n r = Vector.ofFn (comP kp800 (XR A.ctx.fn A.tInit.toNat) (trunc 32 68) n r) :=
  ratatouille_com_eq_comP A.ctx A.tInit n r

/-- **`comCh` is `PU.comP` at Keccak-p[800,12]**, for a state that is injective in the opening
for every public input. -/
theorem comCh_eq_comP (b₁ : Bool) (n : Coins 24 × BCh) (r : Coins 16) :
    comCh A b₁ n r = Vector.ofFn (comP kp800
      (fun n : Coins 24 × BCh => XR A.ctx.fn (crCh A b₁ n.2).toNat n.1) (trunc 32 68) n r) :=
  comCredit_eq_comP A.ctx (crCh A b₁) n r

/-! ## Candidate sets for optional statements -/

/-- The candidates of a simulated proof (none without a statement). -/
noncomputable def candJo {p : Params} (hm : MainP p) (st : Option Statement)
    (S5 : Finset (SKey p)) (k : SimCoins p) : Finset (ZK.Sim.Bytes 16) :=
  match st with
  | some st => candJ Hashes.shake CrtGen.tables hm st S5 k
  | none => ∅

lemma card_candJo_le {p : Params} (hm : MainP p) (st : Option Statement) (S5 : Finset (SKey p))
    (k : SimCoins p) : (candJo hm st S5 k).card ≤ S5.card + 1 := by
  rcases st with _ | st
  · exact Nat.zero_le _
  · exact card_candJ_le _ _ hm st S5 k

-- (The defeq checks on the simulator's coins exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **On the simulator slot, `predJ` is membership in `candJo`** of the public statement, for the
witness prefix. -/
lemma predJ_candJo {p : Params} (hm : MainP p) (S5 : Finset (SKey p)) (y : Option SW)
    (k : SimCoins p × Vis p) (st : Option Statement) (hst : y.map Prod.fst = st)
    (r : ZK.Sim.Bytes 16) (hr : ∀ z ∈ y, wPre z.2 = r)
    (h : predJ Hashes.shake CrtGen.tables hm S5 ((simP p).obs y k)) :
    r ∈ candJo hm st S5 k.1 := by
  rcases y with _ | y
  · exact (predJ_simP_none _ _ _ _ _ h).elim
  · rw [predJ_simP, hr y rfl] at h
    rw [← hst]
    exact h

/-! ## The predictors -/

/-- The simulators' coins and the tables (the tape of the simulated game without the secret). -/
abbrev AuxR := (SimCoins pIr × Vis pIr) × (SimCoins pIr × Vis pIr) × (SimCoins pSr × Vis pSr) ×
  (SimCoins pSr × Vis pSr)

/-- The simulators' coins. -/
def coR (k : AuxR) : CoR := ((k.1.1, k.2.1.1), (k.2.2.1.1, k.2.2.2.1))

/-- The tables. -/
def visR (k : AuxR) : VisR := (k.1.2, k.2.1.2, k.2.2.1.2, k.2.2.2.2)

section Pred

variable (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
  (cf₂ cf₃ : Credits → Commitment) (k : AuxR)

/-- **The candidate sets of the four simulated proofs**, from the nullifiers, the commitments, the
simulators' coins and the tables. -/
noncomputable def candR₁ : Finset (Coins 16) :=
  candJo mainP_pIr (stIP A t.1) (A.R₁ (gP A b₁ b₂ n t cf₂ cf₃ (coR k)) (visR k)) k.1.1

noncomputable def candR₂ : Finset (Coins 16) :=
  candJo mainP_pIr (stIP A t.2) (A.R₂ (gP A b₁ b₂ n t cf₂ cf₃ (coR k)) (visR k)) k.2.1.1

noncomputable def candR₃ : Finset (Coins 16) :=
  candJo mainP_pSr (st₃P A b₁ n t cf₂ (coR k)) (A.R₃ (gP A b₁ b₂ n t cf₂ cf₃ (coR k)) (visR k))
    k.2.2.1.1

noncomputable def candR₄ : Finset (Coins 16) :=
  candJo mainP_pSr (st₄P A b₁ b₂ n t cf₂ cf₃ (coR k))
    (A.R₄ (gP A b₁ b₂ n t cf₂ cf₃ (coR k)) (visR k)) k.2.2.2.1

/-- **The predictor for the opening of Client `c`'s issued token**: the candidates of its issuance
proof, of round 1's spend proof if `c = b₁`, and of round 2's spend proof if Client `c = !b₁`
spends there (`b₂ ≠ b₁`). -/
noncomputable def predI (c : Bool) : Finset (Coins 16) :=
  (bif c then candR₂ A b₁ b₂ n t cf₂ cf₃ k else candR₁ A b₁ b₂ n t cf₂ cf₃ k) ∪
    ((bif b₁ == c then candR₃ A b₁ b₂ n t cf₂ cf₃ k else ∅) ∪
      (bif (b₂ != b₁) && (c != b₁) then candR₄ A b₁ b₂ n t cf₂ cf₃ k else ∅))

/-- **The predictor for the opening of round 1's change token**: the candidates of round 2's spend
proof, if the change token is spent there (`b₂ = b₁`). -/
noncomputable def predC : Finset (Coins 16) :=
  bif b₂ == b₁ then candR₄ A b₁ b₂ n t cf₂ cf₃ k else ∅

/-- The predictor of the change token reads `cf₂` at the credit `cr₁P` only. -/
lemma predC_const :
    predC A b₁ b₂ n t cf₂ cf₃ k =
      predC A b₁ b₂ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t (coR k).1)) cf₃ k := by
  unfold predC candR₄
  rw [gP_const, st₄P_const]

variable {q5 : ℕ} (h₁ : ∀ g v, (A.R₁ g v).card ≤ q5) (h₂ : ∀ g v, (A.R₂ g v).card ≤ q5)
  (h₃ : ∀ g v, (A.R₃ g v).card ≤ q5) (h₄ : ∀ g v, (A.R₄ g v).card ≤ q5)
include h₁ h₂ h₃ h₄

/-- **At most `3·(q₅ + 1)` candidates**, if every read set has at most `q₅` keys. -/
theorem card_predI_le (c : Bool) : (predI A b₁ b₂ n t cf₂ cf₃ k c).card ≤ 3 * (q5 + 1) := by
  have e₁ : (candR₁ A b₁ b₂ n t cf₂ cf₃ k).card ≤ q5 + 1 :=
    (card_candJo_le _ _ _ _).trans (Nat.succ_le_succ (h₁ _ _))
  have e₂ : (candR₂ A b₁ b₂ n t cf₂ cf₃ k).card ≤ q5 + 1 :=
    (card_candJo_le _ _ _ _).trans (Nat.succ_le_succ (h₂ _ _))
  have e₃ : (candR₃ A b₁ b₂ n t cf₂ cf₃ k).card ≤ q5 + 1 :=
    (card_candJo_le _ _ _ _).trans (Nat.succ_le_succ (h₃ _ _))
  have e₄ : (candR₄ A b₁ b₂ n t cf₂ cf₃ k).card ≤ q5 + 1 :=
    (card_candJo_le _ _ _ _).trans (Nat.succ_le_succ (h₄ _ _))
  unfold predI
  generalize candR₁ A b₁ b₂ n t cf₂ cf₃ k = C₁ at e₁ ⊢
  generalize candR₂ A b₁ b₂ n t cf₂ cf₃ k = C₂ at e₂ ⊢
  generalize candR₃ A b₁ b₂ n t cf₂ cf₃ k = C₃ at e₃ ⊢
  generalize candR₄ A b₁ b₂ n t cf₂ cf₃ k = C₄ at e₄ ⊢
  have a : (bif c then C₂ else C₁).card ≤ q5 + 1 := by
    cases c
    · exact e₁
    · exact e₂
  have a' : (bif b₁ == c then C₃ else ∅).card ≤ q5 + 1 := by
    cases b₁ == c
    · exact Nat.zero_le _
    · exact e₃
  have a'' : (bif (b₂ != b₁) && (c != b₁) then C₄ else ∅).card ≤ q5 + 1 := by
    cases (b₂ != b₁) && (c != b₁)
    · exact Nat.zero_le _
    · exact e₄
  have u₁ := card_union_le (bif c then C₂ else C₁)
    ((bif b₁ == c then C₃ else ∅) ∪ (bif (b₂ != b₁) && (c != b₁) then C₄ else ∅))
  have u₂ := card_union_le (bif b₁ == c then C₃ else ∅)
    (bif (b₂ != b₁) && (c != b₁) then C₄ else ∅)
  omega

/-- **At most `q₅ + 1` candidates.** -/
theorem card_predC_le : (predC A b₁ b₂ n t cf₂ cf₃ k).card ≤ q5 + 1 := by
  unfold predC
  cases b₂ == b₁
  · exact Nat.zero_le _
  · exact (card_candJo_le _ _ _ _).trans (Nat.succ_le_succ (h₄ _ _))

end Pred

/-! ## The simulated game on the tape `SecR × AuxR` -/

/-- The simulated issuance proofs. -/
noncomputable def so₁ (s : SecR) (c₁ : SimCoins pIr) : Option Out :=
  (issStmtR A s.1.1).map fun _ => simulate pIr c₁

noncomputable def so₂ (s : SecR) (c₂ : SimCoins pIr) : Option Out :=
  (issStmtR A s.1.2).map fun _ => simulate pIr c₂

/-- The statement and witness of round 1's spend proof. -/
noncomputable def sσ₃ (b₁ : Bool) (s : SecR) (c₁ c₂ : SimCoins pIr) : Option SW :=
  spStmt A (τ₁ₘ A b₁ s (so₁ A s c₁) (so₂ A s c₂)) (A.d₁ (trₘ A s (so₁ A s c₁) (so₂ A s c₂))) s.2.1

/-- Round 1's simulated spend proof. -/
noncomputable def so₃ (b₁ : Bool) (s : SecR) (c₁ c₂ : SimCoins pIr) (c₃ : SimCoins pSr) :
    Option Out :=
  (sσ₃ A b₁ s c₁ c₂).map fun _ => simulate pSr c₃

/-- The statement and witness of round 2's spend proof. -/
noncomputable def sσ₄ (b₁ b₂ : Bool) (s : SecR) (c₁ c₂ : SimCoins pIr) (c₃ : SimCoins pSr) :
    Option SW :=
  spStmt A (τ₂ₘ A b₁ b₂ s (so₁ A s c₁) (so₂ A s c₂) (so₃ A b₁ s c₁ c₂ c₃))
    (d₂ₘ A b₁ s (so₁ A s c₁) (so₂ A s c₂) (so₃ A b₁ s c₁ c₂ c₃)) s.2.2

/-- Round 2's simulated spend proof. -/
noncomputable def so₄ (b₁ b₂ : Bool) (s : SecR) (c₁ c₂ : SimCoins pIr) (c₃ c₄ : SimCoins pSr) :
    Option Out :=
  (sσ₄ A b₁ b₂ s c₁ c₂ c₃).map fun _ => simulate pSr c₄

/-- The guess's input in the simulated game. -/
noncomputable def sg (b₁ b₂ : Bool) (x : SecR × AuxR) : GIn :=
  gR A b₁ b₂ x.1 (so₁ A x.1 x.2.1.1) (so₂ A x.1 x.2.2.1.1)
    (so₃ A b₁ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)
    (so₄ A b₁ b₂ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1 x.2.2.2.2.1)

/-- The event of `puTermR`, unfolded. -/
lemma puEvR_iff (b₁ b₂ : Bool) (x : SecR × AuxR) :
    ev (gameₘ A b₁ b₂) (simP pIr) (simP pIr) (simP pSr) (simP pSr)
      (predAll Hashes.shake CrtGen.tables mainP_pIr mainP_pIr mainP_pSr mainP_pSr
        (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂)) x ↔
    (predJ Hashes.shake CrtGen.tables mainP_pIr (A.R₁ (sg A b₁ b₂ x) (visR x.2))
        ((simP pIr).obs (issStmtR A x.1.1.1) x.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pIr (A.R₂ (sg A b₁ b₂ x) (visR x.2))
        ((simP pIr).obs (issStmtR A x.1.1.2) x.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pSr (A.R₃ (sg A b₁ b₂ x) (visR x.2))
        ((simP pSr).obs (sσ₃ A b₁ x.1 x.2.1.1 x.2.2.1.1) x.2.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pSr (A.R₄ (sg A b₁ b₂ x) (visR x.2))
        ((simP pSr).obs (sσ₄ A b₁ b₂ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1) x.2.2.2.2)) :=
  Iff.rfl

/-- **The guess's input of the simulated game is public.** -/
lemma sg_pub (b₁ b₂ : Bool) (x : SecR × AuxR) :
    sg A b₁ b₂ x = gP A b₁ b₂ (nS x.1) (tS A x.1) (cfS A x.1.2.1) (cfS A x.1.2.2) (coR x.2) :=
  gR_pub A b₁ b₂ x.1 (coR x.2) _ _ _ _ rfl rfl (fun _ => rfl) (fun _ _ => rfl)

/-! ## The events -/

/-- The opening of Client `c`'s issued token is among its predictor's candidates. -/
def winI (b₁ b₂ c : Bool) (x : SecR × AuxR) : Prop :=
  rIss x.1 c ∈ predI A b₁ b₂ (nS x.1) (tS A x.1) (cfS A x.1.2.1) (cfS A x.1.2.2) x.2 c

/-- The opening of round 1's change token is among its predictor's candidates, the commitment
taken at the credit `cr₁P`. -/
def winC (b₁ b₂ : Bool) (x : SecR × AuxR) : Prop :=
  x.1.2.1.2 ∈ predC A b₁ b₂ (nS x.1) (tS A x.1)
    (fun _ => cfS A x.1.2.1 (cr₁P A b₁ (nS x.1).1 (tS A x.1) (coR x.2).1)) (cfS A x.1.2.2) x.2

/-- The witness prefix of an optional statement (zero if there is none). -/
def hidRo (y : Option SW) : ZK.Sim.Bytes 16 :=
  match y with
  | some y => wPre y.2
  | none => fun _ => 0

/-- The candidates for the label offset of a hidden spend proof, from a read set, the simulator's
shared tape and its corrections. -/
noncomputable def hidGo (y : Option SW) (S5 : Finset (SKey pSr)) (sh : Shared)
    (c : ZK.Sim.Bytes (16 * pSr.correctionBytes)) : Finset W128 :=
  match y with
  | some y => guessSet Hashes.shake CrtGen.tables (withP y.1 pSr) S5 sh (fieldsCD c (zeroB _))
  | none => ∅

lemma card_hidGo_le (y : Option SW) (S5 : Finset (SKey pSr)) (sh : Shared)
    (c : ZK.Sim.Bytes (16 * pSr.correctionBytes)) : (hidGo y S5 sh c).card ≤ S5.card + 1 := by
  rcases y with _ | y
  · exact Nat.zero_le _
  · exact card_guessSet_le _ _ _ _ _ _

/-- **The prediction of a spend proof, with `d` separated**: the target and the candidates do not
read the simulator's `d`. -/
lemma predJ_hido (y : Option SW) (S5 : Finset (SKey pSr)) (k : SimCoins pSr × Vis pSr)
    (h : predJ Hashes.shake CrtGen.tables mainP_pSr S5 ((simP pSr).obs y k)) :
    thetaMain (pre16 mainP_pSr.hw k.1.2.2.2.2.1) (hidRo y) ∈ hidGo y S5 k.1.1 k.1.2.1 := by
  rcases y with _ | y
  · exact (predJ_simP_none _ _ _ _ _ h).elim
  · rw [predJ_simP, mem_candJ] at h
    have e := guessSet_fieldsCD Hashes.shake CrtGen.tables y.1 S5 k.1.1 k.1.2.1 (zeroB _)
      k.1.2.2.2.2.1
    show _ ∈ guessSet Hashes.shake CrtGen.tables (withP y.1 pSr) S5 k.1.1
      (fieldsCD k.1.2.1 (zeroB _))
    rw [e]
    exact h

/-- Round 1's spend proof is hidden (the round is refused), and its `d` makes its witness prefix
a candidate. -/
def hidR₃ (b₁ : Bool) (x : SecR × AuxR) : Prop :=
  thetaMain (pre16 mainP_pSr.hw x.2.2.2.1.1.2.2.2.2.1) (hidRo (sσ₃ A b₁ x.1 x.2.1.1 x.2.2.1.1)) ∈
    hidGo (sσ₃ A b₁ x.1 x.2.1.1 x.2.2.1.1)
      (A.R₃ (trₘ A x.1 (so₁ A x.1 x.2.1.1) (so₂ A x.1 x.2.2.1.1), none) (visR x.2))
      x.2.2.2.1.1.1 x.2.2.2.1.1.2.1

/-- Round 2's spend proof is hidden, and its `d` makes its witness prefix a candidate. -/
def hidR₄ (b₁ b₂ : Bool) (x : SecR × AuxR) : Prop :=
  thetaMain (pre16 mainP_pSr.hw x.2.2.2.2.1.2.2.2.2.1)
      (hidRo (sσ₄ A b₁ b₂ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)) ∈
    hidGo (sσ₄ A b₁ b₂ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)
      (A.R₄ (gR' A b₁ x.1 (so₁ A x.1 x.2.1.1) (so₂ A x.1 x.2.2.1.1)
        (so₃ A b₁ x.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)) (visR x.2))
      x.2.2.2.2.1.1 x.2.2.2.2.1.2.1

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **The (PU) event implies a prediction or a hit of a hidden proof's `d`.** -/
theorem puEvR_imp (b₁ b₂ : Bool) (x : SecR × AuxR)
    (h : ev (gameₘ A b₁ b₂) (simP pIr) (simP pIr) (simP pSr) (simP pSr)
      (predAll Hashes.shake CrtGen.tables mainP_pIr mainP_pIr mainP_pSr mainP_pSr
        (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂)) x) :
    (winI A b₁ b₂ false x ∨ winI A b₁ b₂ true x ∨ winC A b₁ b₂ x) ∨
      hidR₃ A b₁ x ∨ hidR₄ A b₁ b₂ x := by
  rw [puEvR_iff] at h
  have hg := sg_pub A b₁ b₂ x
  obtain ⟨s, k⟩ := x
  set o₁ := so₁ A s k.1.1 with ho₁
  set o₂ := so₂ A s k.2.1.1 with ho₂
  set o₃ := so₃ A b₁ s k.1.1 k.2.1.1 k.2.2.1.1 with ho₃
  have e₁ : o₁ = (issStmtR A s.1.1).map fun _ => simulate pIr (coR k).1.1 := rfl
  have e₂ : o₂ = (issStmtR A s.1.2).map fun _ => simulate pIr (coR k).1.2 := rfl
  have e₃ : ok₁ₘ A s o₁ o₂ = true → o₃ = (spStmt A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂))
      s.2.1).map fun _ => simulate pSr (coR k).2.1 := fun _ => rfl
  rcases h with h | h | h | h
  · -- issuance of Client `false`
    have hin := predJ_candJo mainP_pIr _ _ _ _ (issStmtR_pub A s.1.1).1 s.1.1.2
      (issStmtR_pub A s.1.1).2 h
    rw [hg] at hin
    exact Or.inl (Or.inl (mem_union_left _ hin))
  · -- issuance of Client `true`
    have hin := predJ_candJo mainP_pIr _ _ _ _ (issStmtR_pub A s.1.2).1 s.1.2.2
      (issStmtR_pub A s.1.2).2 h
    rw [hg] at hin
    exact Or.inl (Or.inr (Or.inl (mem_union_left _ hin)))
  · -- round 1's spend
    cases hok : ok₁ₘ A s o₁ o₂
    · have hgn : sg A b₁ b₂ (s, k) = (trₘ A s o₁ o₂, none) := gR_of_not_ok₁ A b₁ b₂ s _ _ _ _ hok
      rw [hgn] at h
      exact Or.inr (Or.inl (predJ_hido _ _ _ h))
    · have hin := predJ_candJo mainP_pSr _ _ _ _ (σ₃_pub A b₁ s (coR k) o₁ o₂ e₁ e₂ hok)
        (rIss s b₁) (σ₃_wPre A b₁ s (coR k) o₁ o₂ e₁ e₂ hok) h
      rw [hg] at hin
      have hw : winI A b₁ b₂ b₁ (s, k) := by
        unfold winI predI
        refine mem_union_right _ (mem_union_left _ ?_)
        rw [beq_self_eq_true]
        exact hin
      cases b₁
      · exact Or.inl (Or.inl hw)
      · exact Or.inl (Or.inr (Or.inl hw))
  · -- round 2's spend
    cases hok : ok₁ₘ A s o₁ o₂ && ok₂ₘ A b₁ s o₁ o₂ o₃
    · have hgn : sg A b₁ b₂ (s, k) = gR' A b₁ s o₁ o₂ o₃ := gR_eq_gR' A b₁ b₂ s _ _ _ _ hok
      rw [hgn] at h
      exact Or.inr (Or.inr (predJ_hido _ _ _ h))
    · rw [Bool.and_eq_true] at hok
      have hin := predJ_candJo mainP_pSr _ _ _ _
        (σ₄_pub A b₁ b₂ s (coR k) o₁ o₂ o₃ e₁ e₂ e₃ hok.1 hok.2) _
        (σ₄_wPre A b₁ b₂ s (coR k) o₁ o₂ o₃ e₁ e₂ e₃ hok.1 hok.2) h
      rw [hg] at hin
      cases hb : b₂ == b₁
      · rw [hb] at hin
        have hw : winI A b₁ b₂ (!b₁) (s, k) := by
          unfold winI predI
          refine mem_union_right _ (mem_union_right _ ?_)
          have e : ((b₂ != b₁) && ((!b₁) != b₁)) = true := by
            cases b₁ <;> cases b₂ <;> simp_all
          rw [e]
          exact hin
        cases b₁
        · exact Or.inl (Or.inr (Or.inl hw))
        · exact Or.inl (Or.inl hw)
      · rw [hb] at hin
        refine Or.inl (Or.inr (Or.inr ?_))
        unfold winC
        rw [← predC_const]
        unfold predC
        rw [hb]
        exact hin

/-! ## The predictors in the game `PU.puAdv` -/

/-- **The predictor for the opening of Client `false`'s issued token** in the game `PU.puAdv`:
public part `nf₀`, commitment `t₀ = Com(nf₀, ctx, T_init, r₀)`; auxiliary coins the other three
tokens' `(nf, r)`, the simulators' coins and the tables. -/
noncomputable def predR₀ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxR) :
    Finset (Coins 16) :=
  predI A b₁ b₂ ((vec n, vec a.1.1.1), (vec a.1.2.1.1, vec a.1.2.2.1))
    (t, comI A a.1.1.1 a.1.1.2) (cfS A a.1.2.1) (cfS A a.1.2.2) a.2 false

/-- **The predictor for the opening of Client `true`'s issued token.** -/
noncomputable def predR₁ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxR) :
    Finset (Coins 16) :=
  predI A b₁ b₂ ((vec a.1.1.1, vec n), (vec a.1.2.1.1, vec a.1.2.2.1))
    (comI A a.1.1.1 a.1.1.2, t) (cfS A a.1.2.1) (cfS A a.1.2.2) a.2 true

/-- The tables and the spend simulators' coins (the change predictor's auxiliary coins besides
round 2's new token). -/
abbrev AuxC := Vis pIr × Vis pIr × (SimCoins pSr × Vis pSr) × (SimCoins pSr × Vis pSr)

/-- The tape of the simulators, from the issuance coins (public input) and the rest. -/
def auxOf (c : SimCoins pIr × SimCoins pIr) (a : AuxC) : AuxR :=
  ((c.1, a.1), (c.2, a.2.1), a.2.2.1, a.2.2.2)

/-- **The predictor for the opening of round 1's change token** in the game `PU.puAdv` for
`comCh`: public part `nf'` and the issuance part `b` (the issued tokens' `(nf, r)` and the issuance
simulators' coins, which determine the credit), commitment `t = Com(nf', ctx, crCh b, r')`;
auxiliary coins round 2's new token's `(nf, r)`, the spend simulators' coins and the tables. -/
noncomputable def predRC (b₁ b₂ : Bool) (n : Coins 24 × BCh) (t : Commitment)
    (a : (Coins 24 × Coins 16) × AuxC) : Finset (Coins 16) :=
  predC A b₁ b₂ ((vec n.2.1.1.1, vec n.2.1.2.1), (vec n.1, vec a.1.1))
    (comI A n.2.1.1.1 n.2.1.1.2, comI A n.2.1.2.1 n.2.1.2.2) (fun _ => t) (cfS A a.1)
    (auxOf n.2.2 a.2)

theorem pr_winI_false (b₁ b₂ : Bool) :
    pr (SecR × AuxR) (winI A b₁ b₂ false) = puAdv (comI A) (predR₀ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxR) ≃
      SecR × AuxR :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winI_true (b₁ b₂ : Bool) :
    pr (SecR × AuxR) (winI A b₁ b₂ true) = puAdv (comI A) (predR₁ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxR) ≃
      SecR × AuxR :=
    { toFun := fun z => (((z.2.1.1, z.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.2, ((x.1.1.1, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winC (b₁ b₂ : Bool) :
    pr (SecR × AuxR) (winC A b₁ b₂) = puAdv (comCh A b₁) (predRC A b₁ b₂) := by
  let e : ((Coins 24 × BCh) × Coins 16) × ((Coins 24 × Coins 16) × AuxC) ≃ SecR × AuxR :=
    { toFun := fun z => ((z.1.1.2.1, ((z.1.1.1, z.1.2), z.2.1)), auxOf z.1.1.2.2 z.2.2)
      invFun := fun x => (((x.1.2.1.1, (x.1.1, (x.2.1.1, x.2.2.1.1))), x.1.2.1.2),
        (x.1.2.2, (x.2.1.2, x.2.2.1.2, x.2.2.2.1, x.2.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-! ## The hidden proofs -/

theorem pr_hidR₃_le {q5 : ℕ} (h₃ : ∀ g v, (A.R₃ g v).card ≤ q5) (b₁ : Bool) :
    pr (SecR × AuxR) (hidR₃ A b₁) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d3_le (S := SecR) (K₁ := SimCoins pIr × Vis pIr) (K₂ := SimCoins pIr × Vis pIr)
    (Sh := Shared) (C := ZK.Sim.Bytes (16 * pSr.correctionBytes))
    (X := ZK.Sim.Bytes (pSr.nMask * pSr.nMultBytes))
    (Y := ZK.Sim.Bytes 64) (Z := ZK.Sim.Bytes (16 * (pSr.qsDegree - 1))) (V := Vis pSr)
    (K₄ := SimCoins pSr × Vis pSr) mainP_pSr.hw
    (fun ω => hidRo (sσ₃ A b₁ ω.1 ω.2.1.1 ω.2.2.1.1))
    (fun ω => hidGo (sσ₃ A b₁ ω.1 ω.2.1.1 ω.2.2.1.1)
      (A.R₃ (trₘ A ω.1 (so₁ A ω.1 ω.2.1.1) (so₂ A ω.1 ω.2.2.1.1), none)
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.1.1.1 ω.2.2.2.1.1.2.1)
    (q := q5)
    (fun ω => (card_hidGo_le _ _ _ _).trans (Nat.succ_le_succ (h₃ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

theorem pr_hidR₄_le {q5 : ℕ} (h₄ : ∀ g v, (A.R₄ g v).card ≤ q5) (b₁ b₂ : Bool) :
    pr (SecR × AuxR) (hidR₄ A b₁ b₂) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d4_le (S := SecR) (K₁ := SimCoins pIr × Vis pIr) (K₂ := SimCoins pIr × Vis pIr)
    (K₃ := SimCoins pSr × Vis pSr)
    (Sh := Shared) (C := ZK.Sim.Bytes (16 * pSr.correctionBytes))
    (X := ZK.Sim.Bytes (pSr.nMask * pSr.nMultBytes))
    (Y := ZK.Sim.Bytes 64) (Z := ZK.Sim.Bytes (16 * (pSr.qsDegree - 1))) (V := Vis pSr)
    mainP_pSr.hw
    (fun ω => hidRo (sσ₄ A b₁ b₂ ω.1 ω.2.1.1 ω.2.2.1.1 ω.2.2.2.1.1))
    (fun ω => hidGo (sσ₄ A b₁ b₂ ω.1 ω.2.1.1 ω.2.2.1.1 ω.2.2.2.1.1)
      (A.R₄ (gR' A b₁ ω.1 (so₁ A ω.1 ω.2.1.1) (so₂ A ω.1 ω.2.2.1.1)
          (so₃ A b₁ ω.1 ω.2.1.1 ω.2.2.1.1 ω.2.2.2.1.1))
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.2.1.1 ω.2.2.2.2.1.2.1)
    (q := q5)
    (fun ω => (card_hidGo_le _ _ _ _).trans (Nat.succ_le_succ (h₄ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

/-! ## The reduction -/

/-- `puTermR` on the tape `SecR × AuxR`. -/
theorem puTermR_eq (b₁ b₂ : Bool) :
    puTermR A b₁ b₂ = pr (SecR × AuxR) (ev (gameₘ A b₁ b₂) (simP pIr) (simP pIr) (simP pSr)
      (simP pSr) (predAll Hashes.shake CrtGen.tables mainP_pIr mainP_pIr mainP_pSr mainP_pSr
        (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂))) := by
  unfold puTermR
  exact pr_inst_irrel _ _ _

/-- **The (PU) term is at most the advantage of the three explicit predictors**, plus
`2·(q₅ + 1)·2⁻¹²⁸` for the spend proofs that are not shown. -/
theorem puTermR_le {q5 : ℕ} (h₃ : ∀ g v, (A.R₃ g v).card ≤ q5)
    (h₄ : ∀ g v, (A.R₄ g v).card ≤ q5) (b₁ b₂ : Bool) :
    puTermR A b₁ b₂ ≤ puAdv (comI A) (predR₀ A b₁ b₂) + puAdv (comI A) (predR₁ A b₁ b₂) +
      puAdv (comCh A b₁) (predRC A b₁ b₂) + 2 * ((q5 + 1) / 2 ^ 128) := by
  rw [puTermR_eq]
  have h := (pr_mono (puEvR_imp A b₁ b₂)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl (pr_or_le _ _))) (pr_or_le _ _)))
  rw [pr_winI_false, pr_winI_true, pr_winC] at h
  have a₃ := pr_hidR₃_le A h₃ b₁
  have a₄ := pr_hidR₄_le A h₄ b₁ b₂
  exact h.trans (by linarith)

/-! ## Theorem 2 on `main`, with (PU) as a game -/

/-- **Theorem 2 on `main` (no label rows), with the (PU) advantage of explicit predictors.**
`unlinkability_main` with `puTermR` replaced by `puTermR_le`: for the malicious Issuer whose guess
reads each `H₃` and cipher table at `q3`, `qE` keys and each `H₅` table at a consistent read set of
at most `q5` keys, any two worlds of the real game on `main` differ by at most

    8·εRF(q3, qE) + 15·(PU(b₁, b₂) + PU(b₁', b₂') + 4·(q5 + 1)·2⁻¹²⁸) + 2·εhide,

`PU(b₁, b₂) = puAdv comI (predR₀ b₁ b₂) + puAdv comI (predR₁ b₁ b₂) + puAdv (comCh b₁)
(predRC b₁ b₂)`. The predictors of the issued tokens' openings output at most `3·(q5 + 1)`
candidates and the predictor of the change token's opening at most `q5 + 1` (`card_predI_le`,
`card_predC_le`). The six `puAdv` terms are the only ones that are not explicit numbers besides
`εhide`: they are (PU), an assumption on Keccak-p[800,12]. -/
theorem unlinkability_main_pu {q3 q5 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons)
    (h₃ : ∀ g v, (A.R₃ g v).card ≤ q5) (h₄ : ∀ g v, (A.R₄ g v).card ≤ q5) {εhide : ℝ}
    (hhide : ∀ v b₁ b₂ co,
      hidingAdv (A.atV v).ctx (reduction (A.atV v) simIR simSR b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |realMainR A b₁ b₂ - realMainR A b₁' b₂'| ≤
      8 * εRF q3 qE + 15 * (puAdv (comI A) (predR₀ A b₁ b₂) + puAdv (comI A) (predR₁ A b₁ b₂) +
        puAdv (comCh A b₁) (predRC A b₁ b₂) + (puAdv (comI A) (predR₀ A b₁' b₂') +
        puAdv (comI A) (predR₁ A b₁' b₂') + puAdv (comCh A b₁') (predRC A b₁' b₂')) +
        4 * ((q5 + 1) / 2 ^ 128)) + 2 * εhide := by
  have h := unlinkability_main A hA hC hhide b₁ b₂ b₁' b₂'
  have p0 := puTermR_le A h₃ h₄ b₁ b₂
  have p1 := puTermR_le A h₃ h₄ b₁' b₂'
  linarith

end VoleMole.Privacy.Ratatouille
