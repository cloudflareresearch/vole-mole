import VoleMole.Privacy.MoussakaNC
import VoleMole.Privacy.MoussakaDelta
import VoleMole.ZK.ReadsROPerm
import VoleMole.ZK.VerifyReadsRO
import VoleMole.ZK.SharedH3

/-!
# Moussaka against a non-colluding Moderator in the random-oracle and ideal-cipher model

`Privacy/MoussakaNC.lean` proves Theorem 4(b′) (`security/moussaka.md` §6) from per-proof zero
knowledge of the redemption proofs. Here the adversary's guess also sees the random tables, and
**every proof and every verification of the game runs on the same tables**: the shared tables
`ShM R` (`H₂³`, `H₅`, the cipher with rows in `R`) and one `H₃` slice per proof (the two issuance
proofs, the two redemptions), as in `Privacy/MoussakaRO.lean`.

## The game (`realGameNCRO`)

Client `c` sends `issue_request` with its proof computed on the tables (prover `PI`, its slice);
the honest Anchor `c` answers with `issue_response`, **verifying the proof with `V` on the same
tables** (for the Lean instance the executable verifier `ZK.Sim.verRO`, `leanVI`), then running
`derive_preimage` (any signer correct for its key); the Client runs `finalize_issue`; §6's refusal
rule; the redemptions are `redeem_request` with the prover `PR` on the tables. The adversary
(`AdversaryNCRO`: contexts, keys, Anchor Sets and digests, none of which read the tables) sees the
redemptions or the refusal, the four slices and the tables, with a read budget (`Budget`).

## The hops

1. **The redemption proofs simulated** (`hopL_NCRO`, `hopR_NCRO`, from `ZeroKnowledgeRO` of the
   redemption proofs). The game is written with the issuance requests and the Anchors'
   verifications on the tables **after** the redemption simulations' `H₂³` programming
   (`gameNCROS`; with real redemptions nothing is programmed, so this is the real game,
   `realGameNCRO_iff`). Each reduction then runs both issuance proofs and both verifications on
   the tables it is given, so they cost **no collision term**, only reads: the prover's `624` `H₅`
   and `4607` cipher keys and the verifier's `312` and `4607` (`ZK/VerifyReadsRO.lean`) per
   Client. The redemption statements do not depend on the tables: the token is `tokW`
   (`derive_preimage` on the commitment), and it is the Client's token whenever the redemptions
   happen (`tokDNC_eq_tokW`); the simulations program only if all four checks of `tokW` pass
   (`okW`, a function of the Clients' coins). The left hop has no collision term; the right one has
   `deltaNC` (the right real proof reads `H₂³` at the left simulation's block), `≤ noHitProb +
   2⁻¹⁰²⁴` for the Lean prover (`deltaNC_le`: the statement does not depend on the left
   simulation's coins, unlike in 4(a), whose redemption statements are the adversary's choices
   after the simulated requests).
2. **The issuance slices the guess sees made independent** (`sim_fresh_NC`, `2·q₃·2⁻¹²⁸`): an
   issuance proof reads its slice only at its randomness `ρ` (`SliceAt`; `realRO_h3_val`), so the
   guess's view of the slice differs from an independent one only if it reads the slice at `ρ`
   (`abs_pr_fiber`). Needed for the swap below, which exchanges the Clients' tapes.
3. **The abort hop** (`fresh_hyb_NC`, `φ false + φ true`), as in `Privacy/MoussakaNC.lean`: unless a
   `derive_preimage` fails, the refusal bit is the symmetric `accV x₀ && accV x₁ && KNC` and the
   programming condition is `KNC` (`simFresh_iff_hyb`).
4. **The swap** (`hybFresh_eq`): the symmetric hybrid's worlds coincide.

## Results

* **`anonymityNCRO`** (any proof systems with read budgets) and, with the Lean prover and verifier,
  **`anonymityNCRO_leanG`** (every row type with `ZKRow R`), `anonymityNCRO_lean_num` (function
  rows), `anonymityNCRO_lean_num_perm` (permutation rows):

      |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴)
                          + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸,

  about `2⁻¹⁰³·²` plus the budget terms and the abort term (`2496 = 2·(624 + 312) + 624`,
  `23035 = 2·(4607 + 4607) + 4607`: both Clients' proof and verification and the other
  redemption). `anonymityNCRO_vinegarRO`: the abort term `2·(δ₀^256 + δ₁^256)` averaged over the
  Anchors' vinegar tables.
* **`unlinkabilityNCRO`**, `unlinkabilityNCRO_leanG`, `unlinkabilityNCRO_lean_num`,
  `unlinkabilityNCRO_lean_num_perm`: one Anchor, any index rule, no abort term.

Nothing is assumed of the issuance proofs' zero knowledge or of `Com`. Restrictions: the
adversary's choices do not read the tables (as in `Privacy/MoussakaRO.lean`), the `H₃` slices are
per proof, and the seed XOF's outputs are uniform.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R]

/-! ## The game -/

/-- **The non-colluding adversary in the random-oracle model** (the Moderator): contexts, the two
issuing keys, the Anchor Set and digest per side, and a guess from the two redemption requests (or
the refusal) that also sees the four proofs' `H₃` slices and the shared tables. It sees no
issuance, and its choices do not read the tables. -/
structure AdversaryNCRO (R : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  choose : Bool → AnchorSet × Bytes
  guess : Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop

/-- The adversary as a non-colluding adversary of `Privacy/MoussakaNC.lean` (its guess unused). -/
def AdversaryNCRO.nc (A : AdversaryNCRO R) : AdversaryNC :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.choose, fun _ => True⟩

/-- The adversary as a random-oracle adversary of `Privacy/MoussakaRO.lean` (for the redemption
slots; responses unused). -/
def AdversaryNCRO.ro (A : AdversaryNCRO R) : AdversaryRO R :=
  ⟨A.ctxIss, A.ctxRed, A.pk, fun _ _ _ => 0, fun _ _ side => A.choose side,
    fun _ _ y sl s => A.guess y sl s⟩

/-- **The adversary's budget**: its guess reads each `H₃` slice at `q3` keys, `H₅` at `q5` and the
cipher at `qE` keys (each with everything else fixed), and `H₂³` freely. -/
structure AdversaryNCRO.Budget (A : AdversaryNCRO R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ y (g₁ gL gR : Tab3) s, Rd3 (fun g => A.guess y ((g, g₁), (gL, gR)) s) q3
  h31 : ∀ y (g₀ gL gR : Tab3) s, Rd3 (fun g => A.guess y ((g₀, g), (gL, gR)) s) q3
  h3L : ∀ y (g₀ g₁ gR : Tab3) s, Rd3 (fun g => A.guess y ((g₀, g₁), (g, gR)) s) q3
  h3R : ∀ y (g₀ g₁ gL : Tab3) s, Rd3 (fun g => A.guess y ((g₀, g₁), (gL, g)) s) q3
  h5 : ∀ y sl, Rd5 (A.guess y sl) q5
  hE : ∀ y sl, RdE (A.guess y sl) qE

/-- An Anchor's verifier of issuance proofs in the random-oracle model: the verdict on a proof for
an instance, on the shared tables. -/
abbrev VerifierRO (R : Type) := Bytes → IssueInstance → ShM R → Bool

/-- **A Client's issuance proof system on the tables `v`**: the prover with its `H₃` slice `g`,
and the Anchors' verifier, both on `v`. -/
def nizkV (PI : ProverRO R IssueInstance) (V : VerifierRO R) (g : Tab3) (v : ShM R) :
    NIZK IssueInstance :=
  ⟨fun w x rho => PI w x rho g v, fun pf x => V pf x v⟩

/-- A real issuance tape's coins `(nf, r, ρ_iss)`. -/
def issCoins (x : TIr) : IssT := (x.1.1, x.1.2, x.2.1)

section Game

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer)

/-- Client `c`'s issuance request on the tables `v` (tape `x`: coins, randomness, slice). -/
def issNC (x : TIr) (v : ShM R) : PendingToken × Bytes :=
  issReal A.nc.base (nizkV PI V x.2.2 v) (issCoins x)

/-- Client `c`'s issuance succeeded on the tables `v` (the Anchor `c` verified the request on `v`)
and the token is redeemable at its index in both sets. -/
def goodV (c : Bool) (x : TIr) (v : ShM R) : Bool :=
  goodNC A.nc idx (nizkV PI V x.2.2 v) sk c (issNC A PI V x v)

/-- The refusal bit: both Clients succeeded. -/
def GV (x₀ x₁ : TIr) (v : ShM R) : Bool :=
  goodV A idx PI V sk false x₀ v && goodV A idx PI V sk true x₁ v

/-- The dummy token. -/
def dummyTok : Token := ⟨List.replicate nfBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- **Client `c`'s token if its request is accepted** (the Anchor's `derive_preimage` on the
commitment; the dummy if it fails): it does not depend on the tables. -/
def tokW (c : Bool) (x : TIr) : Token :=
  (((sk c).derivePreimage (tNC A.nc (issCoins x))).map fun s =>
    (⟨List.ofFn x.1.1, List.ofFn x.1.2, s⟩ : Token)).getD dummyTok

/-- The redemption point of side `side` in world `b`, with the token `tokW`. -/
def ptW (b : Bool) (x₀ x₁ : TIr) (side : Bool) : RedeemPt :=
  ⟨tokW A sk (b ^^ side) (bif b ^^ side then x₁ else x₀), (A.choose side).1,
    idx (A.choose side).1 (A.pk (b ^^ side)), (A.choose side).2⟩

/-- Client `c`'s token `tokW` passes its check at its index in the set of side `side`. -/
def okC (c side : Bool) (x : TIr) : Bool :=
  redeemOk A.ro.base.ci A.ro.base.cr (tokW A sk c x) (A.choose side).1 (idx (A.choose side).1 (A.pk c))

/-- **Both tokens `tokW` pass their checks in both sets** (does not depend on the tables). -/
def okW (x₀ x₁ : TIr) : Bool :=
  okC A idx sk false false x₀ && okC A idx sk false true x₀ && okC A idx sk true false x₁ &&
    okC A idx sk true true x₁

/-- **The view in world `b`** from the issuance tapes, two redemption slots, the issuance slices
the adversary sees (`h₀`, `h₁`; in the game the Clients' own) and the tables `t`: the redemption
slots program `H₂³` (when `okW` allows the redemptions), the issuance requests and the Anchors'
verifications run on the programmed tables `v`, the refusal bit is `GV` on `v`, and the adversary
looks at `v`. With real redemption slots nothing is programmed. -/
def gameNCROS (b : Bool) (x₀ x₁ : TIr) (sL sR : RedSlot R) (h₀ h₁ : Tab3) (t : ShM R) : Prop :=
  A.guess (bif GV A idx PI V sk x₀ x₁ (sL.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ false)
        (sR.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ true) t)) then
      some (sL.out (ptW A idx sk b x₀ x₁ false) (sL.prog (okW A idx sk x₀ x₁)
          (ptW A idx sk b x₀ x₁ false) (sR.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ true) t)),
        sR.out (ptW A idx sk b x₀ x₁ true) (sL.prog (okW A idx sk x₀ x₁)
          (ptW A idx sk b x₀ x₁ false) (sR.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ true) t)))
      else none)
    ((h₀, h₁), (sL.slice, sR.slice))
    (sL.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ false)
      (sR.prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ true) t))

/-- **The view in world `b`**, the adversary seeing the Clients' own slices. -/
def gameNCRO (b : Bool) (x₀ x₁ : TIr) (sL sR : RedSlot R) (t : ShM R) : Prop :=
  gameNCROS A idx PI V sk b x₀ x₁ sL sR x₀.2.2 x₁.2.2 t

/-- The game with the redemption slots drawn by `gL`, `gR`. -/
def gameNCROT {TL TR : Type} (b : Bool) (gL : TL → RedSlot R) (gR : TR → RedSlot R)
    (x : ((TIr × TIr) × (TL × TR)) × ShM R) : Prop :=
  gameNCRO A idx PI V sk b x.1.1.1 x.1.1.2 (gL x.1.2.1) (gR x.1.2.2) x.2

/-- Client `c`'s proof system on the tables of the tape `x` (its own slice). -/
def nizkC (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) (c : Bool) : NIZK IssueInstance :=
  nizkV PI V (bif c then x.1.1.2 else x.1.1.1).2.2 x.2

/-- Client `c`'s `issue_request` on the tables of the tape `x`. -/
def issC (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) (c : Bool) : PendingToken × Bytes :=
  issReal A.nc.base (nizkC PI V x c) (issCoins (bif c then x.1.1.2 else x.1.1.1))

/-- The real redemption point of side `side` in world `b`: Client `b ^^ side`'s token after the
honest Anchor's `issue_response` and `finalize_issue`. -/
def ptC (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) (b side : Bool) : RedeemPt :=
  ⟨tokDNC A.nc (nizkC PI V x (b ^^ side)) sk (b ^^ side) (issC A PI V x (b ^^ side)),
    (A.choose side).1, idx (A.choose side).1 (A.pk (b ^^ side)), (A.choose side).2⟩

/-- **The real game in world `b`**: the spec's protocol on the shared tables `t = x.2`. Client `c`
sends `issue_request` (the prover with its slice on `t`), the honest Anchor `c` answers with
`issue_response` (it verifies the proof with `V` on `t`, then runs `derive_preimage`), the Client
runs `finalize_issue`; if both tokens are redeemable at their indices in both sets, the left
redemption is Client `b`'s `redeem_request` and the right one Client `¬b`'s (the prover on `t`),
else both are refused. The adversary sees the redemptions (or the refusal), the four slices and
`t`. -/
def realGameNCRO (PR : ProverRO R RedeemInstance) (b : Bool)
    (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) : Prop :=
  A.guess (bif goodNC A.nc idx (nizkC PI V x false) sk false (issC A PI V x false) &&
      goodNC A.nc idx (nizkC PI V x true) sk true (issC A PI V x true) then
      some ((redRealRO A.ro PR x.1.2.1).out (ptC A idx PI V sk x b false) x.2,
        (redRealRO A.ro PR x.1.2.2).out (ptC A idx PI V sk x b true) x.2)
      else none)
    ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2, x.1.2.2.2)) x.2

end Game

/-! ## The tokens, the refusal bit and the redemption points -/

section Tokens

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer)

/-- **An accepted request carries the token `tokW`.** -/
lemma tokDNC_eq_tokW (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : TIr) (v : ShM R)
    (h : goodV A idx PI V sk c x v = true) :
    tokDNC A.nc (nizkV PI V x.2.2 v) sk c (issNC A PI V x v) = tokW A sk c x := by
  unfold goodV goodNC at h
  simp only [Bool.and_eq_true] at h
  have hs := h.1.1
  have htok := tokNC_issReal A.nc (nizkV PI V x.2.2 v) sk hsk c (issCoins x)
  unfold tokDNC tokW
  unfold issNC
  rw [htok]
  unfold issNC at hs
  rw [htok] at hs
  split_ifs at hs ⊢ with ha
  · rfl
  · simp at hs

/-- **With the redemptions allowed, both tokens `tokW` pass their checks** (`okW`). -/
lemma okW_of_GV (hsk : ∀ c, (sk c).Correct (A.pk c)) (x₀ x₁ : TIr) (v : ShM R)
    (h : GV A idx PI V sk x₀ x₁ v = true) : okW A idx sk x₀ x₁ = true := by
  unfold GV at h
  simp only [Bool.and_eq_true] at h
  have e₀ := tokDNC_eq_tokW A idx PI V sk hsk false x₀ v h.1
  have e₁ := tokDNC_eq_tokW A idx PI V sk hsk true x₁ v h.2
  have h₀ := h.1
  have h₁ := h.2
  unfold goodV goodNC okNC at h₀ h₁
  rw [e₀] at h₀
  rw [e₁] at h₁
  simp only [Bool.and_eq_true] at h₀ h₁
  unfold okW okC
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h₀.1.2, h₀.2⟩, h₁.1.2⟩, h₁.2⟩

/-- `GV` false when `okW` is. -/
lemma GV_false_of_okW (hsk : ∀ c, (sk c).Correct (A.pk c)) (x₀ x₁ : TIr) (v : ShM R)
    (h : okW A idx sk x₀ x₁ = false) : GV A idx PI V sk x₀ x₁ v = false := by
  cases hg : GV A idx PI V sk x₀ x₁ v
  · rfl
  · rw [okW_of_GV A idx PI V sk hsk x₀ x₁ v hg] at h
    cases h

/-- The tokens `tokW` are well formed. -/
lemma tokW_wf (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : TIr) :
    (tokW A sk c x).r.length = rBytes ∧ (tokW A sk c x).s.length = uovN ∧
      (tokW A sk c x).nf.length = nfBytes := by
  unfold tokW
  cases hd : (sk c).derivePreimage (tNC A.nc (issCoins x)) with
  | none => simp [dummyTok]
  | some s =>
    have hs := (hsk c _ s (length_com _ _ _ _) hd).1
    simp [hs]

/-- With `okW`, the redemption point of each side passes the Client's check. -/
lemma redeemOk_ptW (x₀ x₁ : TIr) (h : okW A idx sk x₀ x₁ = true) (b side : Bool) :
    redeemOk A.ro.base.ci A.ro.base.cr (ptW A idx sk b x₀ x₁ side).tok
      (ptW A idx sk b x₀ x₁ side).anchors (ptW A idx sk b x₀ x₁ side).i = true := by
  unfold okW at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases b <;> cases side <;> assumption

/-- **The real game is the game with real redemption slots.** -/
theorem realGameNCRO_iff (hsk : ∀ c, (sk c).Correct (A.pk c)) (PR : ProverRO R RedeemInstance)
    (b : Bool) (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) :
    realGameNCRO A idx PI V sk PR b x ↔
      gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR) x := by
  have hG : (goodNC A.nc idx (nizkC PI V x false) sk false (issC A PI V x false) &&
      goodNC A.nc idx (nizkC PI V x true) sk true (issC A PI V x true)) =
      GV A idx PI V sk x.1.1.1 x.1.1.2 x.2 := rfl
  unfold realGameNCRO gameNCROT gameNCRO gameNCROS
  rw [hG]
  simp only [redRealRO]
  cases hg : GV A idx PI V sk x.1.1.1 x.1.1.2 x.2
  · simp only [Bool.cond_false]
  · have hpt (side : Bool) : ptC A idx PI V sk x b side = ptW A idx sk b x.1.1.1 x.1.1.2 side := by
      unfold GV at hg
      simp only [Bool.and_eq_true] at hg
      have e₀ := tokDNC_eq_tokW A idx PI V sk hsk false _ _ hg.1
      have e₁ := tokDNC_eq_tokW A idx PI V sk hsk true _ _ hg.2
      unfold ptC ptW
      cases hc : b ^^ side
      · exact congrArg (fun t => (⟨t, _, _, _⟩ : RedeemPt)) e₀
      · exact congrArg (fun t => (⟨t, _, _, _⟩ : RedeemPt)) e₁
    rw [hpt false, hpt true]

end Tokens

/-! ## What the game reads -/

section Reads

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer)

/-- The verifier answering `β` to everything. -/
def constV (β : Bool) : NIZK IssueInstance := ⟨fun _ _ _ => [], fun _ _ => β⟩

/-- **The Anchor's success reads the proof system only through its verdict on the request.** -/
lemma goodNC_verify (B : AdversaryNC) (Z : NIZK IssueInstance) (c : Bool) (i : PendingToken × Bytes) :
    goodNC B idx Z sk c i =
      goodNC B idx (constV (Z.verify (i.2.drop uovM) ⟨i.2.take uovM, B.base.ci⟩)) sk c i := rfl

lemma issNC_eq (x : TIr) (v : ShM R) : issNC A PI V x v = (issRealRO A.ro PI x).out v := rfl

variable {A idx PI V sk} {q3 q5 qE r5 rE v5 vE : ℕ}

/-- **A Client's success reads `H₅` at the prover's and the verifier's keys.** -/
lemma rd5_goodV (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hV5 : ∀ pf x, Rd5 (V pf x) v5)
    (c : Bool) (x : TIr) : Rd5 (fun v => goodV A idx PI V sk c x v) (r5 + v5) := by
  have e : (fun v => goodV A idx PI V sk c x v) = fun v =>
      (fun (i : PendingToken × Bytes) (v : ShM R) =>
        goodNC A.nc idx (constV (V (i.2.drop uovM) ⟨i.2.take uovM, A.nc.base.ci⟩ v)) sk c i)
        ((issRealRO A.ro PI x).out v) v := by
    funext v
    exact goodNC_verify idx sk A.nc _ c _
  rw [e]
  exact (rd5_issReal hPI5 x).bind (f := fun (i : PendingToken × Bytes) (v : ShM R) =>
    goodNC A.nc idx (constV (V (i.2.drop uovM) ⟨i.2.take uovM, A.nc.base.ci⟩ v)) sk c i)
    fun i => (hV5 _ _).map fun β => goodNC A.nc idx (constV β) sk c i

lemma rdE_goodV (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE) (hVE : ∀ pf x, RdE (V pf x) vE)
    (c : Bool) (x : TIr) : RdE (fun v => goodV A idx PI V sk c x v) (rE + vE) := by
  have e : (fun v => goodV A idx PI V sk c x v) = fun v =>
      (fun (i : PendingToken × Bytes) (v : ShM R) =>
        goodNC A.nc idx (constV (V (i.2.drop uovM) ⟨i.2.take uovM, A.nc.base.ci⟩ v)) sk c i)
        ((issRealRO A.ro PI x).out v) v := by
    funext v
    exact goodNC_verify idx sk A.nc _ c _
  rw [e]
  exact (rdE_issReal hPIE x).bind (f := fun (i : PendingToken × Bytes) (v : ShM R) =>
    goodNC A.nc idx (constV (V (i.2.drop uovM) ⟨i.2.take uovM, A.nc.base.ci⟩ v)) sk c i)
    fun i => (hVE _ _).map fun β => goodNC A.nc idx (constV β) sk c i

/-- **The refusal bit reads `H₅` at both Clients' prover and verifier keys.** -/
lemma rd5_GV (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hV5 : ∀ pf x, Rd5 (V pf x) v5)
    (x₀ x₁ : TIr) : Rd5 (fun v => GV A idx PI V sk x₀ x₁ v) (r5 + v5 + (r5 + v5)) :=
  (rd5_goodV hPI5 hV5 false x₀).bind fun g => (rd5_goodV hPI5 hV5 true x₁).map fun g' => g && g'

lemma rdE_GV (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE) (hVE : ∀ pf x, RdE (V pf x) vE)
    (x₀ x₁ : TIr) : RdE (fun v => GV A idx PI V sk x₀ x₁ v) (rE + vE + (rE + vE)) :=
  (rdE_goodV hPIE hVE false x₀).bind fun g => (rdE_goodV hPIE hVE true x₁).map fun g' => g && g'

/-- **The view reads** what the refusal bit, the two redemption outputs and the guess read. -/
lemma rd5_viewNC (hA : A.Budget q3 q5 qE) {Gf : ShM R → Bool} {yL yR : ShM R → Except Error Bytes}
    {a b c : ℕ} (hG : Rd5 Gf a) (hL : Rd5 yL b) (hR : Rd5 yR c) (sl : Slices) :
    Rd5 (fun u => A.guess (bif Gf u then some (yL u, yR u) else none) sl u) (a + (b + c) + q5) :=
  (hG.bind (f := fun g u => (g, yL u, yR u)) fun g =>
      (hL.bind (f := fun y u => (g, y, yR u)) fun y => hR.map fun z => (g, y, z))).bind
    (f := fun o u => A.guess (bif o.1 then some o.2 else none) sl u) fun _ => hA.h5 _ _

lemma rdE_viewNC (hA : A.Budget q3 q5 qE) {Gf : ShM R → Bool} {yL yR : ShM R → Except Error Bytes}
    {a b c : ℕ} (hG : RdE Gf a) (hL : RdE yL b) (hR : RdE yR c) (sl : Slices) :
    RdE (fun u => A.guess (bif Gf u then some (yL u, yR u) else none) sl u) (a + (b + c) + qE) :=
  (hG.bind (f := fun g u => (g, yL u, yR u)) fun g =>
      (hL.bind (f := fun y u => (g, y, yR u)) fun y => hR.map fun z => (g, y, z))).bind
    (f := fun o u => A.guess (bif o.1 then some o.2 else none) sl u) fun _ => hA.hE _ _

end Reads

/-! ## The two redemption hops -/

section Hops

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer) (PR : ProverRO R RedeemInstance)
  {CR : Type} (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The rest of the game around the left redemption's output `o` (slice `g`) on the tables `u`:
the right redemption real. -/
def FLNC (b : Bool) (γ : (TIr × TIr) × TRr) (o : Except Error Bytes) (g : Tab3) (u : ShM R) : Prop :=
  A.guess (bif GV A idx PI V sk γ.1.1 γ.1.2 u then
      some (o, (redRealRO A.ro PR γ.2).out (ptW A idx sk b γ.1.1 γ.1.2 true) u) else none)
    ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u

/-- The left simulation's programming in the right hop. -/
def LNC (b : Bool) (γ : (TIr × TIr) × TRs CR) (s : ShM R) : ShM R :=
  if okW A idx sk γ.1.1 γ.1.2 = true then
    progR (xROf A.ro (ptW A idx sk b γ.1.1 γ.1.2 false)) γ.2.1 s else s

/-- The rest of the game around the right redemption's output: the left one simulated. -/
def FRNC (b : Bool) (γ : (TIr × TIr) × TRs CR) (o : Except Error Bytes) (g : Tab3) (u : ShM R) :
    Prop :=
  A.guess (bif GV A idx PI V sk γ.1.1 γ.1.2 u then
      some (redSim A.ro.base simR γ.2.1 (ptW A idx sk b γ.1.1 γ.1.2 false), o) else none)
    ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) u

/-- **The collision term of the right hop**: the right redemption's real proof on the tables the
left simulation programmed differs from the one on the original tables. -/
noncomputable def deltaNC [Fintype CR] (b : Bool) : ℝ :=
  pr (((TIr × TIr) × TRs CR) × ((Coins proveSeedBytes × Tab3) × ShM R)) fun z =>
    (redRealRO A.ro PR z.2.1).out (ptW A idx sk b z.1.1.1 z.1.1.2 true)
        (LNC A idx sk progR b z.1 z.2.2) ≠
      (redRealRO A.ro PR z.2.1).out (ptW A idx sk b z.1.1.1 z.1.1.2 true) z.2.2

variable {A idx PI V sk PR simR progR} {q3 q5 qE r5 rE v5 vE m5 mE : ℕ}

/-- **The left hop**: the left redemption simulated, `ε` (no collision term: nothing was programmed
before). The reduction runs both issuances, both verifications and the right redemption. -/
theorem hopL_NCRO [Fintype CR] [Nonempty CR] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    {ε : ℝ} (hε : 0 ≤ ε) (hR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE)) ε)
    (b : Bool) :
    |pr _ (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)) -
      pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR))| ≤ ε := by
  have h := hop_ro (Γ := (TIr × TIr) × TRr) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CR) (S := ShM R)
    (fun γ ρ g s => (redRealRO A.ro PR (ρ, g)).out (ptW A idx sk b γ.1.1 γ.1.2 false) s)
    (fun γ c => redSim A.ro.base simR c (ptW A idx sk b γ.1.1 γ.1.2 false))
    (fun γ c s => if okW A idx sk γ.1.1 γ.1.2 = true then
      progR (xROf A.ro (ptW A idx sk b γ.1.1 γ.1.2 false)) c s else s)
    (fun _ s => s) (FLNC A idx PI V sk PR b) (ε := ε) fun γ => ?_
  · have hδ : pr (((TIr × TIr) × TRr) × ((Coins proveSeedBytes × Tab3) × ShM R)) (fun z =>
        (redRealRO A.ro PR (z.2.1.1, z.2.1.2)).out (ptW A idx sk b z.1.1.1 z.1.1.2 false) z.2.2 ≠
          (redRealRO A.ro PR (z.2.1.1, z.2.1.2)).out (ptW A idx sk b z.1.1.1 z.1.1.2 false) z.2.2) =
        0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    rw [← pr_equiv eqvL (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)),
      ← pr_equiv eqvL (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · set p := ptW A idx sk b γ.1.1 γ.1.2 false with hp
    cases hok : okW A idx sk γ.1.1 γ.1.2
    · -- The redemptions do not happen: this proof is not read.
      have e : ∀ o g u, FLNC A idx PI V sk PR b γ o g u ↔ A.guess none
          ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u := fun o g u => by
        simp only [FLNC, GV_false_of_okW A idx PI V sk hsk _ _ u hok, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pr_congr fun a => e _ _ _, pr_congr fun a => e _ _ _]
      exact (hop_ro_unused (ρ := Coins proveSeedBytes) (C := CR) (fun g u =>
        A.guess none ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u)).trans hε
    · have hwf := tokW_wf A sk hsk (b ^^ false) (bif b ^^ false then γ.1.2 else γ.1.1)
      obtain ⟨hrel, hreal, hsim⟩ := redeem_facts A.ro simR PR p hwf.1 hwf.2.1 hwf.2.2
        (redeemOk_ptW A idx sk γ.1.1 γ.1.2 hok b false)
      simp only [↓reduceIte]
      refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
        (pr_congr fun a => ?_)) (hR (xROf A.ro p) (wROf A.ro p) hrel
        (fun o g s => FLNC A idx PI V sk PR b γ (.ok (p.tok.nf ++ o)) g s)
        ⟨fun o s => hA.h3L _ _ _ _ _,
          fun o g => rd5_viewNC hA (rd5_GV hPI5 hV5 _ _) (Rd5.const _) (rd5_redReal hPR5 _ _) _,
          fun o g => rdE_viewNC hA (rdE_GV hPIE hVE _ _) (RdE.const _) (rdE_redReal hPRE _ _) _⟩)
      · rw [hreal]
      · rw [hsim]

/-- **The right hop**: the right redemption simulated, `ε` plus the collision term `deltaNC`. -/
theorem hopR_NCRO [Fintype CR] [Nonempty CR] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE))
      ε) (b : Bool) :
    |pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR)) -
      pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR))| ≤
      ε + deltaNC A idx sk PR progR b := by
  have h := hop_ro (Γ := (TIr × TIr) × TRs CR) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CR) (S := ShM R)
    (fun γ ρ g s => (redRealRO A.ro PR (ρ, g)).out (ptW A idx sk b γ.1.1 γ.1.2 true) s)
    (fun γ c => redSim A.ro.base simR c (ptW A idx sk b γ.1.1 γ.1.2 true))
    (fun γ c s => if okW A idx sk γ.1.1 γ.1.2 = true then
      progR (xROf A.ro (ptW A idx sk b γ.1.1 γ.1.2 true)) c s else s)
    (LNC A idx sk progR b) (FRNC A idx PI V sk simR b) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqvR (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR)),
      ← pr_equiv eqvR (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR)
        (redSimRO A.ro simR progR))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · set p := ptW A idx sk b γ.1.1 γ.1.2 true with hp
    have hL : IsProg (LNC A idx sk progR b γ) m5 mE :=
      IsProg.ite _ (hpR _ _) (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _))
    cases hok : okW A idx sk γ.1.1 γ.1.2
    · have e : ∀ o g u, FRNC A idx PI V sk simR b γ o g u ↔ A.guess none
          ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) u := fun o g u => by
        simp only [FRNC, GV_false_of_okW A idx PI V sk hsk _ _ u hok, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pr_congr fun a => e _ _ _, pr_congr fun a => e _ _ _]
      exact (hop_ro_unused (ρ := Coins proveSeedBytes) (C := CR) (fun g u =>
        A.guess none ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) (LNC A idx sk progR b γ u))).trans hε
    · have hwf := tokW_wf A sk hsk (b ^^ true) (bif b ^^ true then γ.1.2 else γ.1.1)
      obtain ⟨hrel, hreal, hsim⟩ := redeem_facts A.ro simR PR p hwf.1 hwf.2.1 hwf.2.2
        (redeemOk_ptW A idx sk γ.1.1 γ.1.2 hok b true)
      simp only [↓reduceIte]
      refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
        (pr_congr fun a => ?_)) (hR (xROf A.ro p) (wROf A.ro p) hrel
        (fun o g s => FRNC A idx PI V sk simR b γ (.ok (p.tok.nf ++ o)) g (LNC A idx sk progR b γ s))
        ⟨fun o s => hA.h3R _ _ _ _ _,
          fun o g => (rd5_viewNC hA (rd5_GV hPI5 hV5 _ _) (Rd5.const _) (Rd5.const _) _).comp_prog hL,
          fun o g => (rdE_viewNC hA (rdE_GV hPIE hVE _ _) (RdE.const _) (RdE.const _) _).comp_prog hL⟩)
      · rw [hreal]
      · rw [hsim]

end Hops

/-! ## Hiding the issuance slices from the guess -/

section Slice

/-- An `H₃` answer (`32` bytes). -/
abbrev H3Val := VoleMole.ZK.Sim.Bytes 32

/-- **Re-randomizing a slice the guess sees.** If a proof uses its slice `g` only through `g ρ`
(at its uniform randomness `ρ`) and the guess reads the slice it sees at `≤ q` keys, then letting
the guess see an independent slice instead costs `≤ q·2⁻¹²⁸`: the two differ only if the guess reads
the slice at `ρ`, which is independent of everything it sees. -/
theorem abs_pr_fiber (Φ : Tab3 → H3Val → Prop) {q : ℕ} (hΦ : ∀ u, Rd3 (fun g => Φ g u) q) :
    |pr (Coins proveSeedBytes × Tab3) (fun a => Φ a.2 (a.2 a.1)) -
      pr ((Coins proveSeedBytes × Tab3) × Tab3) (fun a => Φ a.2 (a.1.2 a.1.1))| ≤ q / 2 ^ 128 := by
  classical
  choose Q hQc hQ using hΦ
  -- The real side: the slice is `g'` with its answer at `ρ` replaced by `u`.
  have e1 : pr (Coins proveSeedBytes × Tab3) (fun a => Φ a.2 (a.2 a.1)) =
      pr (Coins proveSeedBytes × (H3Val × Tab3)) (fun a =>
        Φ (Function.update a.2.2 a.1 a.2.1) a.2.1) := by
    rw [pr_prod, pr_prod]
    refine congrArg (· / (Fintype.card (Coins proveSeedBytes) : ℝ))
      (Finset.sum_congr rfl fun ρ _ => ?_)
    let e : H3Val × Tab3 ≃ Tab3 × H3Val :=
      { toFun := fun a => (Function.update a.2 ρ a.1, a.2 ρ)
        invFun := fun a => (a.1 ρ, Function.update a.1 ρ a.2)
        left_inv := fun a => by simp
        right_inv := fun a => by simp }
    rw [← pr_prod_fst (β := H3Val) (fun g : Tab3 => Φ g (g ρ)), ← pr_equiv e]
    refine pr_congr fun a => ?_
    simp [e]
  -- The ideal side: the proof's answer `u` is independent of the slice the guess sees.
  have e2 : pr ((Coins proveSeedBytes × Tab3) × Tab3) (fun a => Φ a.2 (a.1.2 a.1.1)) =
      pr (Coins proveSeedBytes × (H3Val × Tab3)) (fun a => Φ a.2.2 a.2.1) := by
    rw [← pr_equiv (Equiv.prodAssoc (Coins proveSeedBytes) Tab3 Tab3).symm, pr_prod, pr_prod]
    refine congrArg (· / (Fintype.card (Coins proveSeedBytes) : ℝ))
      (Finset.sum_congr rfl fun ρ _ => ?_)
    simp only [Equiv.prodAssoc_symm_apply]
    rw [← pr_equiv (Equiv.prodComm Tab3 Tab3), ← pr_equiv (Equiv.prodComm Tab3 H3Val), pr_prod,
      pr_prod]
    refine congrArg (· / (Fintype.card Tab3 : ℝ)) (Finset.sum_congr rfl fun g' _ => ?_)
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact pr_eval ρ (fun u => Φ g' u)
  rw [e1, e2]
  refine (abs_pr_sub_le_of_agree _ _ (fun a : Coins proveSeedBytes × (H3Val × Tab3) =>
    a.1 ∈ Q a.2.1 a.2.2) fun a ha => ?_).trans ?_
  · refine iff_of_eq (hQ a.2.1 a.2.2 _ fun k hk => ?_)
    have hne : k ≠ a.1 := fun h => ha (h ▸ hk)
    rw [Function.update_of_ne hne]
  · have h := pr_mem_indep_le (α := Coins proveSeedBytes) (β := H3Val × Tab3) id
      Function.injective_id (fun b => Q b.1 b.2) (q := q) fun b => hQc b.1 b.2
    rw [show Fintype.card (Coins proveSeedBytes) = 2 ^ 128 from card_bytes16] at h
    refine le_of_eq_of_le (pr_congr fun a => Iff.rfl) (h.trans_eq ?_)
    norm_num

/-- **The slice hop for one Client**: a view `W x h r` of a Client's tape `x` (the proof using its
slice only at its randomness: `hW`), the slice `h` the guess sees (read at `≤ q` keys) and the rest
`r`; seeing the Client's own slice or an independent one is `q·2⁻¹²⁸`-close. -/
theorem abs_pr_slice_hop {Rest : Type*} [Fintype Rest] [Nonempty Rest] (W : TIr → Tab3 → Rest → Prop)
    {q : ℕ}
    (hW : ∀ (n : NR) (ρ ρ' : Coins proveSeedBytes) (g g' : Tab3) h r, g ρ = g' ρ' →
      (W (n, (ρ, g)) h r ↔ W (n, (ρ', g')) h r))
    (hR : ∀ x r, Rd3 (fun h => W x h r) q) :
    |pr (TIr × Rest) (fun z => W z.1 z.1.2.2 z.2) -
      pr ((TIr × Tab3) × Rest) (fun z => W z.1.1 z.1.2 z.2)| ≤ q / 2 ^ 128 := by
  let e1 : (NR × Rest) × (Coins proveSeedBytes × Tab3) ≃ TIr × Rest :=
    { toFun := fun a => ((a.1.1, a.2), a.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (NR × Rest) × ((Coins proveSeedBytes × Tab3) × Tab3) ≃ (TIr × Tab3) × Rest :=
    { toFun := fun a => (((a.1.1, a.2.1), a.2.2), a.1.2)
      invFun := fun z => ((z.1.1.1, z.2), (z.1.1.2, z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  refine abs_pr_prod_sub_le _ _ fun nr => ?_
  have h := abs_pr_fiber (fun g u => W (nr.1, ((0 : Coins proveSeedBytes), fun _ => u)) g nr.2)
    fun u => hR _ _
  refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
    (pr_congr fun a => ?_)) h
  · exact hW nr.1 _ _ _ _ _ _ rfl
  · exact hW nr.1 _ _ _ _ _ _ rfl

end Slice

/-! ## The view depends on a Client's randomness and slice only through its `H₃` answer -/

section Congr

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer)

/-- **The prover uses its slice only at its randomness**: `PI w x ρ g s` depends on `(ρ, g)` only
through `g ρ` (`H₃` at the seed input `wPrefix ‖ μ₁ ‖ ρ ‖ 3`; `realROb_h3_val` for the Lean
prover). -/
def SliceAt (PI : ProverRO R IssueInstance) : Prop :=
  ∀ w x (ρ ρ' : Coins proveSeedBytes) (g g' : Tab3) s, g ρ = g' ρ' →
    PI w x (List.ofFn ρ) g s = PI w x (List.ofFn ρ') g' s

variable {A idx PI V sk}

lemma issNC_congr (hPI : SliceAt PI) {x x' : TIr} (h1 : x.1 = x'.1) (h2 : x.2.2 x.2.1 = x'.2.2 x'.2.1)
    (v : ShM R) : issNC A PI V x v = issNC A PI V x' v := by
  rw [issNC_eq, issNC_eq, issRealRO_out, issRealRO_out, h1, hPI _ _ _ _ _ _ v h2]

lemma goodV_congr (hPI : SliceAt PI) {x x' : TIr} (h1 : x.1 = x'.1) (h2 : x.2.2 x.2.1 = x'.2.2 x'.2.1)
    (c : Bool) (v : ShM R) : goodV A idx PI V sk c x v = goodV A idx PI V sk c x' v := by
  unfold goodV
  rw [goodNC_verify, goodNC_verify (Z := nizkV PI V x'.2.2 v), issNC_congr hPI h1 h2]
  rfl

lemma tokW_congr {x x' : TIr} (h1 : x.1 = x'.1) (c : Bool) : tokW A sk c x = tokW A sk c x' := by
  unfold tokW tNC issCoins
  simp only [h1]

lemma okW_congr₀ {x₀ x₀' : TIr} (h1 : x₀.1 = x₀'.1) (x₁ : TIr) :
    okW A idx sk x₀ x₁ = okW A idx sk x₀' x₁ := by
  simp only [okW, okC, tokW_congr (A := A) (sk := sk) h1]

lemma okW_congr₁ (x₀ : TIr) {x₁ x₁' : TIr} (h1 : x₁.1 = x₁'.1) :
    okW A idx sk x₀ x₁ = okW A idx sk x₀ x₁' := by
  simp only [okW, okC, tokW_congr (A := A) (sk := sk) h1]

lemma ptW_congr₀ {x₀ x₀' : TIr} (h1 : x₀.1 = x₀'.1) (x₁ : TIr) (b side : Bool) :
    ptW A idx sk b x₀ x₁ side = ptW A idx sk b x₀' x₁ side := by
  unfold ptW
  cases b ^^ side
  · simp only [Bool.cond_false, tokW_congr (A := A) (sk := sk) h1]
  · rfl

lemma ptW_congr₁ (x₀ : TIr) {x₁ x₁' : TIr} (h1 : x₁.1 = x₁'.1) (b side : Bool) :
    ptW A idx sk b x₀ x₁ side = ptW A idx sk b x₀ x₁' side := by
  unfold ptW
  cases b ^^ side
  · rfl
  · simp only [Bool.cond_true, tokW_congr (A := A) (sk := sk) h1]

/-- **The game depends on Client `0`'s randomness and slice only through its `H₃` answer.** -/
lemma gameNCROS_congr₀ (hPI : SliceAt PI) (b : Bool) {x₀ x₀' : TIr} (h1 : x₀.1 = x₀'.1)
    (h2 : x₀.2.2 x₀.2.1 = x₀'.2.2 x₀'.2.1) (x₁ : TIr) (sL sR : RedSlot R) (h₀ h₁ : Tab3)
    (t : ShM R) :
    gameNCROS A idx PI V sk b x₀ x₁ sL sR h₀ h₁ t ↔ gameNCROS A idx PI V sk b x₀' x₁ sL sR h₀ h₁ t := by
  unfold gameNCROS GV
  simp only [okW_congr₀ (A := A) (idx := idx) (sk := sk) h1 x₁, ptW_congr₀ (A := A) (idx := idx)
    (sk := sk) h1 x₁, goodV_congr (A := A) (idx := idx) (V := V) (sk := sk) hPI h1 h2]

/-- The same for Client `1`. -/
lemma gameNCROS_congr₁ (hPI : SliceAt PI) (b : Bool) (x₀ : TIr) {x₁ x₁' : TIr} (h1 : x₁.1 = x₁'.1)
    (h2 : x₁.2.2 x₁.2.1 = x₁'.2.2 x₁'.2.1) (sL sR : RedSlot R) (h₀ h₁ : Tab3) (t : ShM R) :
    gameNCROS A idx PI V sk b x₀ x₁ sL sR h₀ h₁ t ↔ gameNCROS A idx PI V sk b x₀ x₁' sL sR h₀ h₁ t := by
  unfold gameNCROS GV
  simp only [okW_congr₁ (A := A) (idx := idx) (sk := sk) x₀ h1, ptW_congr₁ (A := A) (idx := idx)
    (sk := sk) x₀ h1, goodV_congr (A := A) (idx := idx) (V := V) (sk := sk) hPI h1 h2]

end Congr

/-! ## The simulated game with independent slices -/

section Fresh

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer) {CR : Type} (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The game with both redemptions simulated, the guess seeing the slices `h₀`, `h₁`; the tape
`((x₁, h₁), (((x₀, h₀), (cL, cR)), t))`. -/
def simFreshNC (b : Bool) (z : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) : Prop :=
  gameNCROS A idx PI V sk b z.2.1.1.1 z.1.1 (redSimRO A.ro simR progR z.2.1.2.1)
    (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2 z.2.2

variable {A idx PI V sk simR progR}

/-- **Both slices the guess sees made independent**: `2·q₃·2⁻¹²⁸`. -/
theorem sim_fresh_NC [Fintype CR] [Nonempty CR] {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hPI : SliceAt PI) (b : Bool) :
    |pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)) -
      pr _ (simFreshNC A idx PI V sk simR progR b)| ≤ 2 * (q3 / 2 ^ 128) := by
  -- Client `0`'s slice.
  have h0 := abs_pr_slice_hop (Rest := (TIr × (TRs CR × TRs CR)) × ShM R)
    (fun x₀ h r => gameNCROS A idx PI V sk b x₀ r.1.1 (redSimRO A.ro simR progR r.1.2.1)
      (redSimRO A.ro simR progR r.1.2.2) h r.1.1.2.2 r.2)
    (fun n ρ ρ' g g' h r hg => gameNCROS_congr₀ (x₀ := (n, (ρ, g))) (x₀' := (n, (ρ', g'))) hPI b
      rfl hg _ _ _ _ _ _)
    (fun x r => hA.h30 _ _ _ _ _)
  -- Client `1`'s slice.
  have h1 := abs_pr_slice_hop (Rest := ((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)
    (fun x₁ h r => gameNCROS A idx PI V sk b r.1.1.1 x₁ (redSimRO A.ro simR progR r.1.2.1)
      (redSimRO A.ro simR progR r.1.2.2) r.1.1.2 h r.2)
    (fun n ρ ρ' g g' h r hg => gameNCROS_congr₁ (x₁ := (n, (ρ, g))) (x₁' := (n, (ρ', g'))) hPI b _
      rfl hg _ _ _ _ _)
    (fun x r => hA.h31 _ _ _ _ _)
  let e0 : TIr × ((TIr × (TRs CR × TRs CR)) × ShM R) ≃ ((TIr × TIr) × (TRs CR × TRs CR)) × ShM R :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 : TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) ≃
      (TIr × Tab3) × ((TIr × (TRs CR × TRs CR)) × ShM R) :=
    { toFun := fun z => ((z.2.1.1.1, z.2.1.1.2), ((z.1, z.2.1.2), z.2.2))
      invFun := fun y => (y.2.1.1, (((y.1.1, y.1.2), y.2.1.2), y.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have p0 : pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)) =
      pr (TIr × ((TIr × (TRs CR × TRs CR)) × ShM R)) (fun z => gameNCROS A idx PI V sk b z.1 z.2.1.1
        (redSimRO A.ro simR progR z.2.1.2.1) (redSimRO A.ro simR progR z.2.1.2.2) z.1.2.2
        z.2.1.1.2.2 z.2.2) := by
    rw [← pr_equiv e0]
    rfl
  have p1 : pr ((TIr × Tab3) × ((TIr × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.1.1 z.2.1.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.1.2 z.2.1.1.2.2 z.2.2) =
      pr (TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.2.1.1.1 z.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2.2 z.2.2) := by
    rw [← pr_equiv e1]
    rfl
  have p2 : pr _ (simFreshNC A idx PI V sk simR progR b) =
      pr ((TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.2.1.1.1 z.1.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2 z.2.2) := rfl
  rw [p0, p2]
  rw [p1] at h0
  calc _ ≤ _ := abs_sub_le _ (pr (TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.2.1.1.1 z.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2.2 z.2.2)) _
    _ ≤ q3 / 2 ^ 128 + q3 / 2 ^ 128 := add_le_add h0 h1
    _ = 2 * (q3 / 2 ^ 128) := by ring

end Fresh

/-! ## The abort hop and the symmetric hybrid -/

section Hyb

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (PI : ProverRO R IssueInstance)
  (V : VerifierRO R) (sk : Bool → Signer) {CR : Type} (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → ShM R → ShM R)

/-- Both issuers' keys are found (at the Clients' indices) in both sets. -/
def KNC : Bool :=
  (foundNC A.nc idx false false && foundNC A.nc idx false true) &&
    (foundNC A.nc idx true false && foundNC A.nc idx true true)

/-- The Anchor accepts the Client's request on the tables `v` (an Anchor-independent test). -/
def accV (x : TIr) (v : ShM R) : Bool := accNC A.nc (nizkV PI V x.2.2 v) (issNC A PI V x v).2

/-- The redemption instance of side `side` in world `b` from the nullifiers. -/
def xSNC (b : Bool) (n₀ n₁ : Bytes) (side : Bool) : RedeemInstance :=
  ⟨(A.choose side).1.keys, bif b ^^ side then n₁ else n₀, A.ro.base.ci, A.ro.base.cr,
    (A.choose side).2⟩

/-- The tables of the symmetric hybrid: both simulations program iff the keys are found. -/
def vNC (b : Bool) (n₀ n₁ : Bytes) (cL cR : CR) (t : ShM R) : ShM R :=
  if KNC A idx = true then progR (xSNC A b n₀ n₁ false) cL (progR (xSNC A b n₀ n₁ true) cR t) else t

/-- **The symmetric hybrid** with the slices `h₀`, `h₁` seen: the refusal bit is
`accV x₀ && accV x₁ && KNC` on the programmed tables, and the redemptions are the nullifiers with
simulated proofs. -/
def hybV (b : Bool) (x₀ x₁ : TIr) (cL cR : TRs CR) (h₀ h₁ : Tab3) (t : ShM R) : Prop :=
  A.guess (bif (accV A PI V x₀ (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t) &&
        accV A PI V x₁ (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t)) &&
        KNC A idx then
      some (ySimNC A.nc simR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 false,
        ySimNC A.nc simR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cR.1 true) else none)
    ((h₀, h₁), (cL.2, cR.2)) (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t)

/-- The symmetric hybrid on the tape of `simFreshNC`. -/
def hybFreshNC (b : Bool) (z : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) : Prop :=
  hybV A idx PI V simR progR b z.2.1.1.1 z.1.1 z.2.1.2.1 z.2.1.2.2 z.2.1.1.2 z.1.2 z.2.2

variable {A idx PI V sk simR progR}

/-- Unless `derive_preimage` fails, the token `tokW` is `(nf, r, s)` with `pk(s) = t`. -/
lemma tokW_of_derive (hsk : ∀ c, (sk c).Correct (A.pk c)) {c : Bool} {x : TIr}
    (hd : (sk c).derivePreimage (tNC A.nc (issCoins x)) ≠ none) :
    ∃ s, tokW A sk c x = ⟨List.ofFn x.1.1, List.ofFn x.1.2, s⟩ ∧
      (A.pk c).eval s = tNC A.nc (issCoins x) := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hd
  refine ⟨s, ?_, (hsk c _ s (length_com _ _ _ _) hs).2⟩
  unfold tokW
  rw [hs]
  rfl

/-- Unless `derive_preimage` fails, `okC` is "the key is found" (sound index rule). -/
lemma okC_eq_found (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) {c : Bool} {x : TIr}
    (hd : (sk c).derivePreimage (tNC A.nc (issCoins x)) ≠ none) (side : Bool) :
    okC A idx sk c side x = foundNC A.nc idx c side := by
  obtain ⟨s, hs, hc⟩ := tokW_of_derive hsk hd
  unfold okC
  rw [hs]
  show redeemOk A.ro.base.ci A.ro.base.cr ⟨List.ofFn x.1.1, List.ofFn x.1.2, s⟩ (A.choose side).1
      (idx (A.choose side).1 (A.pk c)) = ((A.choose side).1.keys[idx (A.choose side).1 (A.pk c)]?).isSome
  unfold redeemOk
  cases hk : (A.choose side).1.keys[idx (A.choose side).1 (A.pk c)]? with
  | none => rfl
  | some k =>
    simp only [Option.isSome_some, decide_eq_true_eq]
    rw [hidx _ _ _ hk, hc]
    rfl

lemma tokW_nf (hsk : ∀ c, (sk c).Correct (A.pk c)) {c : Bool} {x : TIr}
    (hd : (sk c).derivePreimage (tNC A.nc (issCoins x)) ≠ none) :
    (tokW A sk c x).nf = List.ofFn x.1.1 := by
  obtain ⟨s, hs, -⟩ := tokW_of_derive hsk hd
  rw [hs]

/-- **Unless a `derive_preimage` fails, the simulated game is the symmetric hybrid.** -/
theorem simFresh_iff_hyb (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) (b : Bool)
    (x₀ x₁ : TIr) (cL cR : TRs CR) (h₀ h₁ : Tab3) (t : ShM R)
    (hd₀ : (sk false).derivePreimage (tNC A.nc (issCoins x₀)) ≠ none)
    (hd₁ : (sk true).derivePreimage (tNC A.nc (issCoins x₁)) ≠ none) :
    gameNCROS A idx PI V sk b x₀ x₁ (redSimRO A.ro simR progR cL) (redSimRO A.ro simR progR cR)
        h₀ h₁ t ↔ hybV A idx PI V simR progR b x₀ x₁ cL cR h₀ h₁ t := by
  have hok : okW A idx sk x₀ x₁ = KNC A idx := by
    unfold okW KNC
    rw [okC_eq_found hsk hidx hd₀, okC_eq_found hsk hidx hd₀, okC_eq_found hsk hidx hd₁,
      okC_eq_found hsk hidx hd₁]
    simp only [Bool.and_assoc]
  have hnf (side : Bool) : (ptW A idx sk b x₀ x₁ side).tok.nf =
      bif b ^^ side then List.ofFn x₁.1.1 else List.ofFn x₀.1.1 := by
    unfold ptW
    cases b ^^ side
    · exact tokW_nf hsk hd₀
    · exact tokW_nf hsk hd₁
  have hx (side : Bool) : xROf A.ro (ptW A idx sk b x₀ x₁ side) =
      xSNC A b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) side := by
    unfold xROf xSNC
    rw [hnf side]
    rfl
  have hv : (redSimRO A.ro simR progR cL).prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ false)
      ((redSimRO A.ro simR progR cR).prog (okW A idx sk x₀ x₁) (ptW A idx sk b x₀ x₁ true) t) =
      vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t := by
    unfold vNC
    simp only [redSimRO, hok, hx]
    cases KNC A idx <;> simp
  have hG (v : ShM R) : GV A idx PI V sk x₀ x₁ v = ((accV A PI V x₀ v && accV A PI V x₁ v) &&
      KNC A idx) := by
    unfold GV goodV
    rw [show issNC A PI V x₀ v = issReal A.nc.base (nizkV PI V x₀.2.2 v) (issCoins x₀) from rfl,
      show issNC A PI V x₁ v = issReal A.nc.base (nizkV PI V x₁.2.2 v) (issCoins x₁) from rfl,
      good_eq_of_derive A.nc idx _ sk hsk hidx false _ hd₀,
      good_eq_of_derive A.nc idx _ sk hsk hidx true _ hd₁]
    unfold accV KNC
    have e : ∀ a₀ a₁ f₀ f₁ f₂ f₃ : Bool, ((a₀ && (f₀ && f₁)) && (a₁ && (f₂ && f₃))) =
        ((a₀ && a₁) && ((f₀ && f₁) && (f₂ && f₃))) := by decide
    rw [e]
    rfl
  unfold gameNCROS hybV
  rw [hv, hG]
  cases hc : ((accV A PI V x₀ (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t) &&
      accV A PI V x₁ (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t)) &&
      KNC A idx)
  · simp only [Bool.cond_false, redSimRO]
  · have hK : KNC A idx = true := by
      simp only [Bool.and_eq_true] at hc
      exact hc.2
    have hok' : okW A idx sk x₀ x₁ = true := hok.trans hK
    have hy (c : CR) (side : Bool) : (redSimRO A.ro simR progR (c, default)).out
        (ptW A idx sk b x₀ x₁ side) (vNC A idx progR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) cL.1 cR.1 t) =
        ySimNC A.nc simR b (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) c side := by
      simp only [redSimRO]
      rw [redSim_of_ok A.ro.base simR c _ (redeemOk_ptW A idx sk x₀ x₁ hok' b side), hnf side]
      unfold ySimNC
      rw [show (ptW A idx sk b x₀ x₁ side).anchors = (A.choose side).1 from rfl,
        show (ptW A idx sk b x₀ x₁ side).cd = (A.choose side).2 from rfl]
      rfl
    have hyL := hy cL.1 false
    have hyR := hy cR.1 true
    simp only [redSimRO] at hyL hyR ⊢
    rw [hyL, hyR]

lemma pr_tape_x₀ {CR : Type} [Fintype CR] [Nonempty CR] (P : NR → Prop) :
    pr ((TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z => P z.2.1.1.1.1) =
      pr NR P := by
  let e : NR × ((TIr × Tab3) × ((((Coins proveSeedBytes × Tab3) × Tab3) × (TRs CR × TRs CR)) ×
      ShM R)) ≃ (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) :=
    { toFun := fun a => (a.2.1, ((((a.1, a.2.2.1.1.1), a.2.2.1.1.2), a.2.2.1.2), a.2.2.2))
      invFun := fun z => (z.2.1.1.1.1, (z.1, (((z.2.1.1.1.2, z.2.1.1.2), z.2.1.2), z.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_prod_fst P

lemma pr_tape_x₁ {CR : Type} [Fintype CR] [Nonempty CR] (P : NR → Prop) :
    pr ((TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z => P z.1.1.1) =
      pr NR P := by
  let e : NR × (((Coins proveSeedBytes × Tab3) × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) ×
      ShM R)) ≃ (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) :=
    { toFun := fun a => (((a.1, a.2.1.1), a.2.1.2), a.2.2)
      invFun := fun z => (z.1.1.1, ((z.1.1.2, z.1.2), z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_prod_fst P

/-- **The abort hop**: replacing the refusal bit and the programming condition by the symmetric
ones costs `φ false + φ true` (identical until a `derive_preimage` fails). -/
theorem fresh_hyb_NC [Fintype CR] [Nonempty CR] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hidx : IdxSound idx) (b : Bool) :
    |pr _ (simFreshNC A idx PI V sk simR progR b) - pr _ (hybFreshNC A idx PI V simR progR b)| ≤
      phi A.nc sk false + phi A.nc sk true := by
  refine (abs_pr_sub_le_of_agree _ _ (fun z :
      (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) =>
      (sk false).derivePreimage (com (List.ofFn z.2.1.1.1.1.1) A.nc.base.ci A.nc.base.cr
          (List.ofFn z.2.1.1.1.1.2)) = none ∨
        (sk true).derivePreimage (com (List.ofFn z.1.1.1.1) A.nc.base.ci A.nc.base.cr
          (List.ofFn z.1.1.1.2)) = none) fun z hz => ?_).trans
    ((pr_or_le _ _).trans (le_of_eq ?_))
  · simp only [not_or] at hz
    exact simFresh_iff_hyb hsk hidx b _ _ _ _ _ _ _ hz.1 hz.2
  · rw [pr_tape_x₀ (fun y : NR => (sk false).derivePreimage
        (com (List.ofFn y.1) A.nc.base.ci A.nc.base.cr (List.ofFn y.2)) = none),
      pr_tape_x₁ (fun y : NR => (sk true).derivePreimage
        (com (List.ofFn y.1) A.nc.base.ci A.nc.base.cr (List.ofFn y.2)) = none)]
    rfl

/-- Exchange the two Clients' tapes (keeping the slices the guess sees). -/
def swapNC {CR : Type} : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) ≃
    (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) where
  toFun z := ((z.2.1.1.1, z.1.2), (((z.1.1, z.2.1.1.2), z.2.1.2), z.2.2))
  invFun z := ((z.2.1.1.1, z.1.2), (((z.1.1, z.2.1.1.2), z.2.1.2), z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma xSNC_swap (n₀ n₁ : Bytes) (side : Bool) : xSNC A false n₀ n₁ side = xSNC A true n₁ n₀ side := by
  cases side <;> rfl

lemma hybV_swap (x₀ x₁ : TIr) (cL cR : TRs CR) (h₀ h₁ : Tab3) (t : ShM R) :
    hybV A idx PI V simR progR false x₀ x₁ cL cR h₀ h₁ t ↔
      hybV A idx PI V simR progR true x₁ x₀ cL cR h₀ h₁ t := by
  have hv : vNC A idx progR false (List.ofFn x₀.1.1) (List.ofFn x₁.1.1) =
      vNC A idx progR true (List.ofFn x₁.1.1) (List.ofFn x₀.1.1) := by
    funext cL cR t
    simp only [vNC, xSNC_swap]
  unfold hybV
  rw [hv, Bool.and_comm (accV A PI V x₀ _), ySimNC_swap, ySimNC_swap]

/-- **The symmetric hybrid's worlds coincide** (a swap of the Clients' tapes). -/
theorem hybFresh_eq [Fintype CR] :
    pr _ (hybFreshNC A idx PI V simR progR false) = pr _ (hybFreshNC A idx PI V simR progR true) := by
  rw [← pr_equiv swapNC]
  exact pr_congr fun z => hybV_swap _ _ _ _ _ _ _

/-- **One Anchor: the simulated game's worlds coincide** (a swap of the Clients' tapes; any index
rule). -/
theorem simFresh_eq_one [Fintype CR] (hpk : A.pk false = A.pk true) (hs : sk false = sk true) :
    pr _ (simFreshNC A idx PI V sk simR progR false) =
      pr _ (simFreshNC A idx PI V sk simR progR true) := by
  have htok : tokW A sk false = tokW A sk true := by
    funext x
    simp only [tokW, hs]
  have hokC (side : Bool) : okC A idx sk false side = okC A idx sk true side := by
    funext x
    simp only [okC, htok, hpk]
  have hgood : goodV A idx PI V sk false = goodV A idx PI V sk true := by
    funext x v
    have hpk' : A.nc.pk false = A.nc.pk true := hpk
    simp only [goodV, goodNC, okNC, tokDNC, tokNC, respNC, hpk', hs]
  have hok (x₀ x₁ : TIr) : okW A idx sk x₀ x₁ = okW A idx sk x₁ x₀ := by
    unfold okW
    rw [hokC false, hokC true]
    have e : ∀ a b c d : Bool, (a && b && c && d) = (c && d && a && b) := by decide
    exact e _ _ _ _
  have hpt (x₀ x₁ : TIr) (side : Bool) : ptW A idx sk false x₀ x₁ side = ptW A idx sk true x₁ x₀ side := by
    unfold ptW
    cases side
    · simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.cond_false, Bool.cond_true,
        htok, hpk]
    · simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.cond_false, Bool.cond_true,
        htok, hpk]
  have hG (x₀ x₁ : TIr) (v : ShM R) : GV A idx PI V sk x₀ x₁ v = GV A idx PI V sk x₁ x₀ v := by
    unfold GV
    rw [hgood, Bool.and_comm]
  rw [← pr_equiv swapNC]
  refine pr_congr fun z => ?_
  simp only [simFreshNC, swapNC, Equiv.coe_fn_mk]
  unfold gameNCROS
  rw [hok, hpt, hpt, hG]

end Hyb

/-! ## Theorem 4(b′) in the random-oracle and ideal-cipher model -/

section Main

variable {A : AdversaryNCRO R} {idx : AnchorSet → UOVKey → ℕ} {PI : ProverRO R IssueInstance}
  {V : VerifierRO R} {sk : Bool → Signer} {PR : ProverRO R RedeemInstance}
  {CR : Type} [Fintype CR] [Nonempty CR] {simR : RedeemInstance → CR → Bytes}
  {progR : RedeemInstance → CR → ShM R → ShM R} {q3 q5 qE r5 rE v5 vE m5 mE : ℕ}

/-- One world: the real game against the simulated game with independent slices. -/
theorem real_simFresh_NC (hsk : ∀ c, (sk c).Correct (A.pk c)) (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) (b : Bool) :
    |pr _ (realGameNCRO A idx PI V sk PR b) - pr _ (simFreshNC A idx PI V sk simR progR b)| ≤
      εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
        (εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE) +
          deltaNC A idx sk PR progR b) + 2 * (q3 / 2 ^ 128) := by
  have e0 : pr _ (realGameNCRO A idx PI V sk PR b) =
      pr _ (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)) :=
    pr_congr fun x => realGameNCRO_iff A idx PI V sk hsk PR b x
  have h1 := hopL_NCRO (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hV5 hVE hPR5 hPRE
    (hεR _ _) (hR _ _) b
  have h2 := hopR_NCRO (idx := idx) (PI := PI) (V := V) (PR := PR) hsk hA hPI5 hPIE hV5 hVE hpR
    (hεR _ _) (hR _ _) b
  have h3 := sim_fresh_NC (idx := idx) (V := V) (sk := sk) (simR := simR) (progR := progR) hA hPI3 b
  rw [e0]
  have := abs_sub_le (pr _ (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)))
    (pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR)))
    (pr _ (simFreshNC A idx PI V sk simR progR b))
  have := abs_sub_le (pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR)))
    (pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)))
    (pr _ (simFreshNC A idx PI V sk simR progR b))
  linarith

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model, for any proof systems.** The real
game runs the spec on the shared tables: the Clients' issuance proofs (`PI`, each with its `H₃`
slice), the honest Anchors' verification of them (`V`, on the same tables) and `derive_preimage`
(signers correct for their keys), and the redemption proofs (`PR`); the adversary's guess sees the
redemptions or the refusal, the four slices and the tables (budget `q₃, q₅, q_E`). If the issuance
prover reads `H₅` and the cipher at `r₅`, `r_E` keys and its slice only at its randomness, the
verifier at `v₅`, `v_E` keys, the redemption prover at `r₅`, `r_E` keys, its simulator's
programming at `m₅`, `m_E` keys, the redemption proofs are `ZeroKnowledgeRO` (error `εR`) and the
index rule is sound, then the two worlds differ by at most

    2·(εR(hop L) + εR(hop R)) + Σ_b deltaNC b + 2·(φ false + φ true) + 4·q₃·2⁻¹²⁸,

`deltaNC` the right hop's programming-collision term and `φ c` the abort probability of
`Privacy/MoussakaNC.lean`. Nothing is assumed of the issuance proofs' zero knowledge or of `Com`. -/
theorem anonymityNCRO (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) :
    |pr _ (realGameNCRO A idx PI V sk PR false) - pr _ (realGameNCRO A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNC A idx sk PR progR false + deltaNC A idx sk PR progR true) +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 * (q3 / 2 ^ 128) := by
  have h0 := real_simFresh_NC (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hR hεR false
  have h1 := real_simFresh_NC (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hR hεR true
  have g0 := fresh_hyb_NC (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx false
  have g1 := fresh_hyb_NC (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx true
  have he := hybFresh_eq (A := A) (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR)
  rw [abs_le] at h0 h1 g0 g1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, g0.1, g0.2, g1.1, g1.2]

/-- **Unlinkability against a non-colluding Moderator in the random-oracle and ideal-cipher
model**: one Anchor (equal keys and signers), any index rule, no abort term:

    2·(εR(hop L) + εR(hop R)) + Σ_b deltaNC b + 4·q₃·2⁻¹²⁸. -/
theorem unlinkabilityNCRO (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) :
    |pr _ (realGameNCRO A idx PI V sk PR false) - pr _ (realGameNCRO A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNC A idx sk PR progR false + deltaNC A idx sk PR progR true) + 4 * (q3 / 2 ^ 128) := by
  have h0 := real_simFresh_NC (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hR hεR false
  have h1 := real_simFresh_NC (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hR hεR true
  have he := simFresh_eq_one (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR) hpk hs
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

end Main

/-! ## With the Lean prover and verifier -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **The Lean prover reads its `H₃` slice only at its randomness**: two (randomness, slice) pairs
with the same answer give the same proof (`Prover.prove` reads its randomness only through `H₃`). -/
theorem _root_.VoleMole.ZK.Sim.realRO_h3_val {R : Type} [CipherRow R] {p : Params} {Hb : Hashes}
    {st : Statement} {w : ByteArray} {ρ ρ' : VoleMole.ZK.Sim.Bytes 16} {g g' : Tab3} (s : ShG R p)
    (h : g ρ = g' ρ') : realRO p Hb st w ρ g s = realRO p Hb st w ρ' g' s := by
  have hv (G : Tab3) (r : VoleMole.ZK.Sim.Bytes 16) :
      (recHp p Hb st w G s.1 s.2.1).hash .h3
        ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++ ba r).push 3) = ba (G r) := by
    rw [recHp_h3]
    have e := Hashes.withTable_enc Hb .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes))
      G r
    rw [keyOf_eq (seedInput_injective _ _)] at e
    exact e
  unfold realRO realROb Prover.prove
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)),
    recHp_mu1, recHp_mu1, hv g ρ, hv g' ρ', h,
    @voleGenAt_agreeOff_h3 (icPrg (rowFn s.2.2)) _ _ (recHp_agreeOff_h3 g g' s.1 s.2.1),
    proveCommit_agreeOff_h3 (recHp_agreeOff_h3 g g' s.1 s.2.1)]

variable [CipherRow R]

/-- **The honest Anchors' verifier in the random-oracle model**: the executable Lean verifier of
the issuance statement, on the shared tables (`ZK.Sim.verRO`: `H₂³` and `H₅` the tables, the
cipher the shared table, SHAKE for the other hashes). -/
noncomputable def leanVI : VerifierRO R := fun pf x s =>
  (verRO pI Hashes.shake (stI x) (toBA pf) s).accept

lemma leanVI_rd5 (pf : Bytes) (x : IssueInstance) : Rd5 (leanVI (R := R) pf x) 312 :=
  (verRO_rd5 (stI x) (toBA pf)).map Transcript.accept

lemma leanVI_rdE (pf : Bytes) (x : IssueInstance) : RdE (leanVI (R := R) pf x) 4607 :=
  (verRO_rdE (stI x) (toBA pf)).map Transcript.accept

lemma leanPI_sliceAt : SliceAt (leanPI (R := R)) := by
  intro w x ρ ρ' g g' s h
  rw [leanPI_ofFn, leanPI_ofFn, realRO_h3_val s h]

lemma leanPI_rd5 (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPI (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w) (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPI_rdE (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPI (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPR_rd5 (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPR (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w) (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPR_rdE (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPR (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer)

/-- **The collision term of the right hop**: `deltaNC b ≤ noHitProb + 2⁻¹⁰²⁴`. The right
redemption's statement does not depend on the left simulation's coins (the adversary's choices do
not read anything), so its grinding prefix's `ã` is the left simulation's uniform `ã` with
probability `≤ noHitProb + 2⁻¹⁰²⁴` (`pr_simTail_eq_le`), and otherwise the left programming does
not touch its grinding block (`realRO_ne_tail`). -/
theorem deltaNC_le (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    deltaNC A idx sk leanPR leanProgR b ≤ noHitProb + 1 / 2 ^ 1024 := by
  unfold deltaNC
  -- The real right proof's tail, a function of the issuance tapes and the proof's coins.
  let tl : (TIr × TIr) → (Coins proveSeedBytes × Tab3) × ShM R → ByteArray := fun xx a =>
    preTail (blk (preLen pR) (preRO Hashes.shake (stR (xROf A.ro (ptW A idx sk b xx.1 xx.2 true)))
      (toBA (wROf A.ro (ptW A idx sk b xx.1 xx.2 true))) a.1.1 a.1.2 a.2))
  refine (pr_mono (Q := fun z : ((TIr × TIr) × TRs (SimCoins pR)) × ((Coins proveSeedBytes × Tab3) ×
      ShM R) => tl z.1.1 z.2 = simTail z.1.2.1) fun z hz => ?_).trans ?_
  · set p := ptW A idx sk b z.1.1.1 z.1.1.2 true with hp
    cases hok : redeemOk A.ro.base.ci A.ro.base.cr p.tok p.anchors p.i
    · exact absurd (redRealRO_out_not_ok A.ro leanPR _ p hok _ _) hz
    · have hwf := tokW_wf A sk hsk (b ^^ true) (bif b ^^ true then z.1.1.2 else z.1.1.1)
      obtain ⟨hrel, hreal, -⟩ := redeem_facts A.ro (leanSim pR) leanPR p hwf.1 hwf.2.1 hwf.2.2 hok
      rw [hreal, hreal, leanPR_ofFn, leanPR_ofFn] at hz
      have h1 : realRO pR Hashes.shake (stR (xROf A.ro p)) (toBA (wROf A.ro p)) z.2.1.1 z.2.1.2
          (LNC A idx sk leanProgR b z.1 z.2.2) ≠
          realRO pR Hashes.shake (stR (xROf A.ro p)) (toBA (wROf A.ro p)) z.2.1.1 z.2.1.2 z.2.2 :=
        fun e => hz (by rw [e])
      have hL := ProgAt.ite (okW A idx sk z.1.1.1 z.1.1.2 = true)
        (progRO_progAt (R := R) Hashes.shake (stR (xROf A.ro (ptW A idx sk b z.1.1.1 z.1.1.2 false)))
          z.1.2.1)
      have hT : ∀ s : ShM R, ∀ b' ∈ (if okW A idx sk z.1.1.1 z.1.1.2 = true then
          {simBlk Hashes.shake (stR (xROf A.ro (ptW A idx sk b z.1.1.1 z.1.1.2 false))) z.1.2.1 s}
          else ∅ : Finset (VoleMole.ZK.Sim.Bytes (preLen pI))),
          preTail b' ∈ ({simTail z.1.2.1} : Finset ByteArray) := by
        intro s b' hb
        by_cases hc : okW A idx sk z.1.1.1 z.1.1.2 = true
        · simp only [hc, ↓reduceIte] at hb
          have hb' : b' = simBlk Hashes.shake (stR (xROf A.ro (ptW A idx sk b z.1.1.1 z.1.1.2 false)))
              z.1.2.1 s := Finset.mem_singleton.1 hb
          rw [hb']
          exact Finset.mem_singleton.2 (preTail_simBlk hashesWF_shake rfl _ _)
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
          exact absurd hb (Finset.notMem_empty _)
      have := realRO_ne_tail (zkHypR _ _ hrel) hashesWF_shake hlab_pR hL hT _ _ _ h1
      exact Finset.mem_singleton.1 this
  · refine pr_le_of_snd fun a => pr_le_of_fst fun xx => pr_le_of_snd fun g' => ?_
    have h := pr_simTail_eq_le (p := pR) (tl xx a)
    rw [tail_pR] at h
    exact h

/-- **Theorem 4(b′) with the Lean prover and verifier, for every type of cipher rows** (`ZKRow R`):
the issuance proofs are the Lean prover's, verified by the honest Anchors with the Lean verifier on
the same tables, the redemption proofs the Lean prover's; every term explicit:

    4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸. -/
theorem anonymityNCRO_leanG [ZKRow R] (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 * (q3 / 2 ^ 128) := by
  have h := anonymityNCRO (A := A) (idx := idx) (PI := leanPI) (V := leanVI) (sk := sk) (PR := leanPR)
    (simR := leanSim pR) (progR := leanProgR) (εR := ZKRow.εz R pR q3) hsk hidx hA
    leanPI_rd5 leanPI_rdE leanPI_sliceAt leanVI_rd5 leanVI_rdE leanPR_rd5 leanPR_rdE
    (fun x c => progRO_isProg c) (fun a c => leanPR_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _)
  have m1 := ZKRow.εz_mono (R := R) pR (q3 := q3) (q3' := q3) le_rfl
    (show 624 + 312 + (624 + 312) + (0 + 624) + q5 ≤ q5 + 2496 by omega)
    (show 4607 + 4607 + (4607 + 4607) + (0 + 4607) + qE ≤ qE + 23035 by omega)
  have m2 := ZKRow.εz_mono (R := R) pR (q3 := q3) (q3' := q3) le_rfl
    (show 624 + 312 + (624 + 312) + (0 + 0) + q5 + 312 ≤ q5 + 2496 by omega)
    (show 4607 + 4607 + (4607 + 4607) + (0 + 0) + qE + 4607 ≤ qE + 23035 by omega)
  have d0 := deltaNC_le A idx sk hsk false
  have d1 := deltaNC_le A idx sk hsk true
  generalize (2 : ℝ) ^ 1024 = K at d0 d1 ⊢
  linarith

/-- **Unlinkability against a non-colluding Moderator with the Lean prover and verifier**, every
type of cipher rows: one Anchor, any index rule,

    4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 4·q₃·2⁻¹²⁸. -/
theorem unlinkabilityNCRO_leanG [ZKRow R] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hpk : A.pk false = A.pk true) (hs : sk false = sk true) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) := by
  have h := unlinkabilityNCRO (A := A) (idx := idx) (PI := leanPI) (V := leanVI) (sk := sk)
    (PR := leanPR) (simR := leanSim pR) (progR := leanProgR) (εR := ZKRow.εz R pR q3) hsk hpk hs hA
    leanPI_rd5 leanPI_rdE leanPI_sliceAt leanVI_rd5 leanVI_rdE leanPR_rd5 leanPR_rdE
    (fun x c => progRO_isProg c) (fun a c => leanPR_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _)
  have m1 := ZKRow.εz_mono (R := R) pR (q3 := q3) (q3' := q3) le_rfl
    (show 624 + 312 + (624 + 312) + (0 + 624) + q5 ≤ q5 + 2496 by omega)
    (show 4607 + 4607 + (4607 + 4607) + (0 + 4607) + qE ≤ qE + 23035 by omega)
  have m2 := ZKRow.εz_mono (R := R) pR (q3 := q3) (q3' := q3) le_rfl
    (show 624 + 312 + (624 + 312) + (0 + 0) + q5 + 312 ≤ q5 + 2496 by omega)
    (show 4607 + 4607 + (4607 + 4607) + (0 + 0) + qE + 4607 ≤ qE + 23035 by omega)
  have d0 := deltaNC_le A idx sk hsk false
  have d1 := deltaNC_le A idx sk hsk true
  generalize (2 : ℝ) ^ 1024 = K at d0 d1 ⊢
  linarith

end Lean

/-! ## The two cipher row types -/

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model** (AES's rows uniform functions,
the PRF view): with the Lean prover and verifier on the shared tables, the two worlds differ by at
most

    4·εRO(q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸,

`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`, about
`2⁻¹⁰³·²` plus the budget terms and the abort term. -/
theorem anonymityNCRO_lean_num (A : AdversaryNCRO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * εRO q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 * (q3 / 2 ^ 128) :=
  anonymityNCRO_leanG A idx sk hsk hidx hA

/-- **Theorem 4(b′) with AES as uniformly random permutations** (the adversary reads whole
permutations: forward and inverse queries): the same with `εROPm`. -/
theorem anonymityNCRO_lean_num_perm (A : AdversaryNCRO (Equiv.Perm Blk))
    (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hidx : IdxSound idx) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * εROPm pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 * (q3 / 2 ^ 128) :=
  anonymityNCRO_leanG A idx sk hsk hidx hA

/-- **Unlinkability against a non-colluding Moderator in the random-oracle and ideal-cipher
model** (function rows): one Anchor, any index rule,
`4·εRO(q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 4·q₃·2⁻¹²⁸`. -/
theorem unlinkabilityNCRO_lean_num (A : AdversaryNCRO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * εRO q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) + 4 * (q3 / 2 ^ 128) :=
  unlinkabilityNCRO_leanG A idx sk hsk hpk hs hA

/-- Unlinkability with AES as uniformly random permutations: the same with `εROPm`. -/
theorem unlinkabilityNCRO_lean_num_perm (A : AdversaryNCRO (Equiv.Perm Blk))
    (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hpk : A.pk false = A.pk true) (hs : sk false = sk true) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCRO A idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRO A idx leanPI leanVI sk leanPR true)| ≤
      4 * εROPm pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) :=
  unlinkabilityNCRO_leanG A idx sk hsk hpk hs hA

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model and the vinegar random-oracle
model** (every type of cipher rows): the Anchors' signers fail only when all 256 vinegars of their
uniform table at the target are bad (`hfail`, as in `anonymityNC_vinegarRO`); averaged over the
vinegar tables the abort term is `2·(δ₀^256 + δ₁^256)`, with no assumption on `Com`. -/
theorem anonymityNCRO_vinegarRO {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop) (A : AdversaryNCRO R)
    (idx : AnchorSet → UOVKey → ℕ) (skW : VTab Vin → Bool → Signer)
    (hsk : ∀ w c, (skW w c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) (fun z =>
        realGameNCRO A idx leanPI leanVI (skW z.1) leanPR false z.2) -
      pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) (fun z =>
        realGameNCRO A idx leanPI leanVI (skW z.1) leanPR true z.2)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) +
        2 * (pr Vin (fun v => ¬ Good false v) ^ 256 + pr Vin (fun v => ¬ Good true v) ^ 256) := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  have hphi (c : Bool) : (∑ w, phi A.nc (skW w) c) / Fintype.card (VTab Vin) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
    have := pr_fail_vinegar Good A.nc skW hfail c
    rw [pr_prod] at this
    exact this
  set K := 4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
    4 * (q3 / 2 ^ 128) with hK
  have hw (w : VTab Vin) : |pr _ (realGameNCRO A idx leanPI leanVI (skW w) leanPR false) -
      pr _ (realGameNCRO A idx leanPI leanVI (skW w) leanPR true)| ≤
        K + 2 * (phi A.nc (skW w) false + phi A.nc (skW w) true) := by
    have := anonymityNCRO_leanG A idx (skW w) (hsk w) hidx hA
    rw [hK]
    generalize (2 : ℝ) ^ 1024 = M at this ⊢
    linarith
  refine (abs_pr_prod_sub_le_avg (fun z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R) =>
      realGameNCRO A idx leanPI leanVI (skW z.1) leanPR false z.2)
    (fun z => realGameNCRO A idx leanPI leanVI (skW z.1) leanPR true z.2)
    (fun w => K + 2 * (phi A.nc (skW w) false + phi A.nc (skW w) true)) hw).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hcard.ne', ← Finset.mul_sum, mul_div_assoc, Finset.sum_add_distrib,
    add_div]
  have := hphi false
  have := hphi true
  gcongr

end VoleMole.Privacy.Moussaka
