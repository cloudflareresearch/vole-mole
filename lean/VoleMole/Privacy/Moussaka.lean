import VoleMole.Privacy.Basic
import VoleMole.Spec.Moussaka

/-!
# Moussaka issuer hiding and unlinkability on the executable spec (`security/moussaka.md` §6)

Game ANON in the colluding mode (Theorem 4a): the adversary plays every Anchor and the Moderator.
It chooses the contexts and the two issuing keys `pk false`, `pk true` (arbitrary, rogue keys
allowed; equal keys give unlinkability, different keys issuer hiding), sees both Clients' issuance
requests, answers them, and then chooses, per side, an Anchor Set `S` and a challenge digest `cd`.
In world `b` the left redemption is Client `b`'s token and the right one Client `¬b`'s. The Client
looks up its issuer's index in `S` itself (`idx`, any rule). As §6 requires, the redemptions happen
only if both tokens finalized and both are redeemable at their own index in both sets; otherwise
both are refused. The adversary computes the finalization outcomes and the refusal itself (they
depend only on its view). Its responses are 119 bytes, the C++ `std::array` type: the spec's
`finalizeIssue` accepts any length, and a token with `|s| ≠ 119` would make `redeemRequest` prove a
witness outside `RedeemRel`.

The game runs `Spec/Moussaka.lean`'s `issueRequest`, `finalizeIssue` and `redeemRequest`, with the
seed expansions' outputs `(nf, r, ρ_iss)` and `ρ_red` uniform (`issueRequest_eq`,
`redeemRequest_eq`): the step "the adversary never queries the seed XOF at a Client's 32-byte seed"
is a random-oracle step that stays on paper, as in the note.

## Assumptions

* Zero knowledge of both proof systems (`Privacy.ZeroKnowledge` for `IssueRel` and `RedeemRel`,
  with errors `εI`, `εR`), against distinguishers that may know the witness. With the label-row
  fix this is `lean/docs/zk.md`'s theorem. **On `main` no efficient simulator satisfies it**: a
  distinguisher that knows `r = w[0..16)` computes the label offset and runs the test of
  `lean/docs/zk.md` Prop. 4.1. There the note's joint (PU) hop over the four proofs
  (`ZK/Relations.lean`, `moussaka_main_zk`) replaces it; that hop is on paper.
* Hiding of `Com` in the note's two-instance form (`hidingAdv`): given `t₀ = Com(nf₀, ·, r₀)`,
  `t₁ = Com(nf₁, ·, r₁)`, distinguish `(nf₀, nf₁)` from fresh uniform `(nf₀*, nf₁*)`. It is a
  computational assumption on Keccak-p[800], so it is stated for the explicit reductions
  `reduction A idx simI simR b c` (the adversary with the simulator coins `c` fixed), not for all
  distinguishers.

## Results

* `issue_close`, `redeem_close`: one real and one simulated proof are close as protocol messages.
* `simGame_iff`: with all four proofs simulated, the view is a function `hview` of the commitments
  `t₀, t₁`, the nullifiers and the simulator coins: `r` enters nothing else.
* `idealGame_eq`: after the hiding hop (fresh nullifiers), the worlds coincide exactly (swap of
  the fresh nullifiers).
* **`anonymity`**: `|Pr[A accepts in world 0] − Pr[A accepts in world 1]| ≤ 4εI + 4εR + 2εhide`
  (Theorem 4a's `2·ε_ZK^joint + 2·Adv^hide_Com`; the note's `2⁻¹⁹²` term for `nf₀ = nf₁` is not
  needed, because the fresh nullifiers are exchanged as a pair).
-/

open Finset

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The spec with the seed expansions' outputs given -/

/-- `issueRequest` with the output `(nf, r, ρ_iss)` of `expand_issue_seed` as arguments. -/
def issueRequestOf (PI : NIZK IssueInstance) (ctxIss ctxRed nf r rho : Bytes) :
    PendingToken × Bytes :=
  let t := com nf ctxIss ctxRed r
  (⟨nf, r, ctxIss, ctxRed, t⟩, t ++ PI.prove (encodeIssueWitness nf ctxIss ctxRed r) ⟨t, ctxIss⟩ rho)

theorem issueRequest_eq (PI : NIZK IssueInstance) (ctxIss ctxRed seed : Bytes) :
    issueRequest PI ctxIss ctxRed seed =
      issueRequestOf PI ctxIss ctxRed (expandIssueSeed seed).1 (expandIssueSeed seed).2.1
        (expandIssueSeed seed).2.2 := rfl

/-- `redeemRequest` with `ρ_red = expand_redeem_seed(seed')` as an argument. -/
def redeemRequestOf (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet) (i : ℕ)
    (ctxIss ctxRed cd rho : Bytes) : Except Error Bytes :=
  match A.keys[i]? with
  | none => .error .indexOutOfRange
  | some pk =>
    if pk.eval tok.s = com tok.nf ctxIss ctxRed tok.r then
      .ok (tok.nf ++ PR.prove (encodeRedeemWitness tok.nf ctxIss ctxRed tok.r tok.s i)
        ⟨A.keys, tok.nf, ctxIss, ctxRed, cd⟩ rho)
    else .error .invalidToken

theorem redeemRequest_eq (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet) (i : ℕ)
    (ctxIss ctxRed cd seed : Bytes) :
    redeemRequest PR tok A i ctxIss ctxRed cd seed =
      redeemRequestOf PR tok A i ctxIss ctxRed cd (expandRedeemSeed seed) := rfl

/-- The prover of a `NIZK` with its randomness `ρ` uniform (16 bytes). -/
def proveR {I : Type} (Z : NIZK I) (x : I) (w : Bytes) (ρ : Coins proveSeedBytes) : Bytes :=
  Z.prove w x (List.ofFn ρ)

/-! ## The game -/

/-- The colluding adversary: contexts, the two issuing keys (Client `false`, Client `true`), the
Anchors' responses, the Anchor Set and challenge digest per side (`false` = left), and the
Moderator's guess from the issuance requests and the two redemption requests (or `none`: refused). -/
structure Adversary where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  choose : Bytes → Bytes → Bool → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Prop

/-- Where a redemption is asked: the token, the Anchor Set, the Client's index and the digest. -/
structure RedeemPt where
  tok : Token
  anchors : AnchorSet
  i : ℕ
  cd : Bytes

variable (A : Adversary) (idx : AnchorSet → UOVKey → ℕ)

/-- `ctx_iss`, `ctx_red` as byte lists. -/
def Adversary.ci : Bytes := List.ofFn A.ctxIss
def Adversary.cr : Bytes := List.ofFn A.ctxRed

/-- Client `c`'s token after `finalize_issue` on the adversary's response. -/
def tok (i₀ i₁ : PendingToken × Bytes) (c : Bool) : Option Token :=
  finalizeIssue (A.pk c) (bif c then i₁ else i₀).1 (List.ofFn (A.respond i₀.2 i₁.2 c))

/-- The token, or a well-formed dummy when finalization failed (then nothing is redeemed). -/
def tokD (i₀ i₁ : PendingToken × Bytes) (c : Bool) : Token :=
  (tok A i₀ i₁ c).getD ⟨List.replicate nfBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- The Client's validity check at index `i` of `S` (`moussaka.cpp:196-211`). -/
def redeemOk (ci cr : Bytes) (t : Token) (S : AnchorSet) (i : ℕ) : Bool :=
  match S.keys[i]? with
  | none => false
  | some pk => decide (pk.eval t.s = com t.nf ci cr t.r)

/-- Client `c` can redeem at its own index in the set of side `side`. -/
def okAt (i₀ i₁ : PendingToken × Bytes) (c side : Bool) : Bool :=
  redeemOk A.ci A.cr (tokD A i₀ i₁ c) (A.choose i₀.2 i₁.2 side).1
    (idx (A.choose i₀.2 i₁.2 side).1 (A.pk c))

/-- §6's rule: both tokens finalized, and each is redeemable at its own index in both sets. -/
def allOk (i₀ i₁ : PendingToken × Bytes) : Bool :=
  (tok A i₀ i₁ false).isSome && (tok A i₀ i₁ true).isSome &&
    okAt A idx i₀ i₁ false false && okAt A idx i₀ i₁ false true &&
    okAt A idx i₀ i₁ true false && okAt A idx i₀ i₁ true true

/-- The redemption of side `side` (`false` = left) in world `b`: Client `b ^^ side`'s token. -/
def pt (b : Bool) (i₀ i₁ : PendingToken × Bytes) (side : Bool) : RedeemPt :=
  ⟨tokD A i₀ i₁ (b ^^ side), (A.choose i₀.2 i₁.2 side).1,
    idx (A.choose i₀.2 i₁.2 side).1 (A.pk (b ^^ side)), (A.choose i₀.2 i₁.2 side).2⟩

/-- The adversary's guess from the issuance outputs and the two redemption requests. -/
def post (i₀ i₁ : PendingToken × Bytes) (yL yR : Except Error Bytes) : Prop :=
  A.guess i₀.2 i₁.2 (bif allOk A idx i₀ i₁ then some (yL, yR) else none)

/-- The view in world `b`, given the issuance outputs and the two redemption provers. -/
def view (b : Bool) (i₀ i₁ : PendingToken × Bytes) (redL redR : RedeemPt → Except Error Bytes) :
    Prop :=
  post A idx i₀ i₁ (redL (pt A idx b i₀ i₁ false)) (redR (pt A idx b i₀ i₁ true))

/-- The game with the two issuance slots and the two redemption slots drawn by `g₀ g₁ gL gR`. -/
def game {T₀ T₁ TL TR : Type} (b : Bool) (g₀ : T₀ → PendingToken × Bytes)
    (g₁ : T₁ → PendingToken × Bytes) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (x : (T₀ × T₁) × (TL × TR)) : Prop :=
  view A idx b (g₀ x.1.1) (g₁ x.1.2) (gL x.2.1) (gR x.2.2)

/-- A real issuance from `(nf, r, ρ_iss)`. -/
def issReal (PI : NIZK IssueInstance) (x : Coins nfBytes × Coins rBytes × Coins proveSeedBytes) :
    PendingToken × Bytes :=
  issueRequestOf PI A.ci A.cr (List.ofFn x.1) (List.ofFn x.2.1) (List.ofFn x.2.2)

/-- A real redemption from `ρ_red`. -/
def redReal (PR : NIZK RedeemInstance) (ρ : Coins proveSeedBytes) (p : RedeemPt) :
    Except Error Bytes :=
  redeemRequestOf PR p.tok p.anchors p.i A.ci A.cr p.cd (List.ofFn ρ)

/-- **The real game** in world `b`. -/
def realGame (PI : NIZK IssueInstance) (PR : NIZK RedeemInstance) (b : Bool) :=
  game A idx b (issReal A PI) (issReal A PI) (redReal A PR) (redReal A PR)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)

/-- A simulated issuance from `(nf, r)` and simulator coins. -/
def issSim (x : Coins nfBytes × Coins rBytes × CI) : PendingToken × Bytes :=
  let t := com (List.ofFn x.1) A.ci A.cr (List.ofFn x.2.1)
  (⟨List.ofFn x.1, List.ofFn x.2.1, A.ci, A.cr, t⟩, t ++ simI ⟨t, A.ci⟩ x.2.2)

/-- A simulated redemption, with the Client's checks unchanged. -/
def redSim (c : CR) (p : RedeemPt) : Except Error Bytes :=
  match p.anchors.keys[p.i]? with
  | none => .error .indexOutOfRange
  | some pk =>
    if pk.eval p.tok.s = com p.tok.nf A.ci A.cr p.tok.r then
      .ok (p.tok.nf ++ simR ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩ c)
    else .error .invalidToken

/-! ## One proof at a time -/

variable {T₀ T₁ TL TR T₀' T₁' TL' TR' : Type} [Fintype T₀] [Fintype T₁] [Fintype TL] [Fintype TR]
  [Fintype T₀'] [Fintype T₁'] [Fintype TL'] [Fintype TR']

theorem game_hop₀ [Nonempty T₁] [Nonempty TL] [Nonempty TR] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₀' : T₀' → PendingToken × Bytes}
    (g₁ : T₁ → PendingToken × Bytes) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (h : Close ε g₀ g₀') :
    |pr _ (game A idx b g₀ g₁ gL gR) - pr _ (game A idx b g₀' g₁ gL gR)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le' _ _ fun x₁ =>
    h (fun o => view A idx b o (g₁ x₁) (gL y.1) (gR y.2))

theorem game_hop₁ [Nonempty T₀] [Nonempty TL] [Nonempty TR] (b : Bool) {ε : ℝ}
    (g₀ : T₀ → PendingToken × Bytes) {g₁ : T₁ → PendingToken × Bytes}
    {g₁' : T₁' → PendingToken × Bytes} (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (h : Close ε g₁ g₁') :
    |pr _ (game A idx b g₀ g₁ gL gR) - pr _ (game A idx b g₀ g₁' gL gR)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le _ _ fun x₀ =>
    h (fun o => view A idx b (g₀ x₀) o (gL y.1) (gR y.2))

/-- Issuance outputs whose pending tokens have a 16-byte `r` (so the dummy-or-real tokens of the
view are well formed). -/
def WellFormed {T : Type} (g : T → PendingToken × Bytes) : Prop := ∀ x, (g x).1.r.length = rBytes

theorem getD_finalizeIssue (pk : UOVKey) (p : PendingToken) (s : Bytes) (d : Token) :
    (finalizeIssue pk p s).getD d = d ∨ (finalizeIssue pk p s).getD d = ⟨p.nf, p.r, s⟩ := by
  unfold finalizeIssue
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem tokD_wf {i₀ i₁ : PendingToken × Bytes} (h₀ : i₀.1.r.length = rBytes)
    (h₁ : i₁.1.r.length = rBytes) (c : Bool) :
    (tokD A i₀ i₁ c).r.length = rBytes ∧ (tokD A i₀ i₁ c).s.length = uovN := by
  rcases getD_finalizeIssue (A.pk c) (bif c then i₁ else i₀).1 (List.ofFn (A.respond i₀.2 i₁.2 c))
    ⟨List.replicate nfBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩ with h | h <;>
    rw [tokD, tok, h]
  · exact ⟨List.length_replicate, List.length_replicate⟩
  · exact ⟨by cases c <;> assumption, List.length_ofFn⟩

theorem game_hopL [Nonempty T₀] [Nonempty T₁] [Nonempty TR] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes} (h₀ : WellFormed g₀)
    (h₁ : WellFormed g₁) {gL : TL → RedeemPt → Except Error Bytes}
    {gL' : TL' → RedeemPt → Except Error Bytes} (gR : TR → RedeemPt → Except Error Bytes)
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      Close ε (fun t => gL t p) (fun t => gL' t p)) :
    |pr _ (game A idx b g₀ g₁ gL gR) - pr _ (game A idx b g₀ g₁ gL' gR)| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le' _ _ fun xR =>
    h (pt A idx b (g₀ x.1) (g₁ x.2) false) (tokD_wf A (h₀ _) (h₁ _) _).1
      (tokD_wf A (h₀ _) (h₁ _) _).2
      (fun y => post A idx (g₀ x.1) (g₁ x.2) y (gR xR (pt A idx b (g₀ x.1) (g₁ x.2) true)))

theorem game_hopR [Nonempty T₀] [Nonempty T₁] [Nonempty TL] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes} (h₀ : WellFormed g₀)
    (h₁ : WellFormed g₁) (gL : TL → RedeemPt → Except Error Bytes)
    {gR : TR → RedeemPt → Except Error Bytes} {gR' : TR' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      Close ε (fun t => gR t p) (fun t => gR' t p)) :
    |pr _ (game A idx b g₀ g₁ gL gR) - pr _ (game A idx b g₀ g₁ gL gR')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le _ _ fun xL =>
    h (pt A idx b (g₀ x.1) (g₁ x.2) true) (tokD_wf A (h₀ _) (h₁ _) _).1
      (tokD_wf A (h₀ _) (h₁ _) _).2
      (fun y => post A idx (g₀ x.1) (g₁ x.2) (gL xL (pt A idx b (g₀ x.1) (g₁ x.2) false)) y)

theorem issReal_wf (PI : NIZK IssueInstance) : WellFormed (issReal A PI) := fun x => by
  simp [issReal, issueRequestOf, rBytes]

theorem issSim_wf : WellFormed (issSim A simI) := fun x => by simp [issSim, rBytes]

/-- **One issuance proof.** A real and a simulated issuance are `εI`-close. -/
theorem issue_close [Fintype CI] (PI : NIZK IssueInstance) {εI : ℝ}
    (hI : ZeroKnowledge IssueRel (proveR PI) simI εI) : Close εI (issReal A PI) (issSim A simI) := by
  refine Close.congr (Close.prod_right (X := fun nf y => issReal A PI (nf, y))
    (Y := fun nf y => issSim A simI (nf, y)) fun nf => Close.congr
      (Close.prod_right (X := fun r ρ => issReal A PI (nf, r, ρ))
        (Y := fun r c => issSim A simI (nf, r, c)) fun r => ?_) (fun _ => rfl) (fun _ => rfl))
    (fun _ => rfl) (fun _ => rfl)
  have hrel : IssueRel ⟨com (List.ofFn nf) A.ci A.cr (List.ofFn r), A.ci⟩
      (encodeIssueWitness (List.ofFn nf) A.ci A.cr (List.ofFn r)) :=
    ⟨_, _, _, by simp [nfBytes], by simp [rBytes], by simp [Adversary.cr, ctxBytes], rfl, rfl⟩
  exact (hI _ _ hrel).map fun π =>
    ((⟨List.ofFn nf, List.ofFn r, A.ci, A.cr, com (List.ofFn nf) A.ci A.cr (List.ofFn r)⟩ :
      PendingToken), com (List.ofFn nf) A.ci A.cr (List.ofFn r) ++ π)

/-- **One redemption proof.** At every redemption point with a well-formed token, a real and a
simulated redemption are `εR`-close: if the Client's check fails both refuse alike, otherwise the
witness satisfies `RedeemRel` and zero knowledge applies. -/
theorem redeem_close [Fintype CR] [Nonempty CR] (PR : NIZK RedeemInstance) {εR : ℝ} (hε : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRel (proveR PR) simR εR) (p : RedeemPt)
    (hr : p.tok.r.length = rBytes) (hs : p.tok.s.length = uovN) :
    Close εR (fun ρ => redReal A PR ρ p) (fun c => redSim A simR c p) := by
  intro D
  unfold redReal redSim redeemRequestOf
  cases hk : p.anchors.keys[p.i]? with
  | none => exact close_const hε _ D
  | some pk =>
    by_cases he : pk.eval p.tok.s = com p.tok.nf A.ci A.cr p.tok.r
    · have hrel : RedeemRel ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩
          (encodeRedeemWitness p.tok.nf A.ci A.cr p.tok.r p.tok.s p.i) :=
        ⟨_, _, _, pk, hr, hs, hk, rfl, he⟩
      simp only [he, ite_true]
      exact (hR _ _ hrel).map (fun π => (Except.ok (p.tok.nf ++ π) : Except Error Bytes)) D
    · simp only [he, ite_false]
      exact close_const hε _ D

/-! ## All proofs simulated: the view is a function of the commitments and nullifiers -/

/-- The adversary's response to Client `c`, from the two issuance requests. -/
def resp (q₀ q₁ : Bytes) (c : Bool) : Bytes := List.ofFn (A.respond q₀ q₁ c)

/-- `finalize_issue` succeeds for Client `c`, checked against the commitment `t_c` it sent. -/
def finT (q₀ q₁ t₀ t₁ : Bytes) (c : Bool) : Bool :=
  decide ((A.pk c).eval (resp A q₀ q₁ c) = bif c then t₁ else t₀)

/-- Client `c` is redeemable at its index in the set of side `side`, checked against `t_c`. -/
def okT (q₀ q₁ t₀ t₁ : Bytes) (c side : Bool) : Bool :=
  match (A.choose q₀ q₁ side).1.keys[idx (A.choose q₀ q₁ side).1 (A.pk c)]? with
  | none => false
  | some pk => decide (pk.eval (resp A q₀ q₁ c) = bif c then t₁ else t₀)

/-- §6's rule, as a function of the requests and the commitments. -/
def allOkT (q₀ q₁ t₀ t₁ : Bytes) : Bool :=
  finT A q₀ q₁ t₀ t₁ false && finT A q₀ q₁ t₀ t₁ true && okT A idx q₀ q₁ t₀ t₁ false false &&
    okT A idx q₀ q₁ t₀ t₁ false true && okT A idx q₀ q₁ t₀ t₁ true false &&
    okT A idx q₀ q₁ t₀ t₁ true true

/-- A simulated redemption request of side `side` in world `b`: the nullifier `n_{b ^^ side}` and a
simulated proof. -/
def ySim (b : Bool) (q₀ q₁ n₀ n₁ : Bytes) (c : CR) (side : Bool) : Except Error Bytes :=
  .ok ((bif b ^^ side then n₁ else n₀) ++ simR ⟨(A.choose q₀ q₁ side).1.keys,
    bif b ^^ side then n₁ else n₀, A.ci, A.cr, (A.choose q₀ q₁ side).2⟩ c)

theorem redSim_of_ok (c : CR) (p : RedeemPt) (h : redeemOk A.ci A.cr p.tok p.anchors p.i = true) :
    redSim A simR c p = .ok (p.tok.nf ++ simR ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩ c) := by
  unfold redeemOk at h
  unfold redSim
  split at h
  · cases h
  · simp only [decide_eq_true_eq] at h
    simp [h]

theorem tok_of_fin (i₀ i₁ : PendingToken × Bytes) (c : Bool) :
    tok A i₀ i₁ c = if finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c then
      some ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩
    else none := by
  have ht : (bif c then i₁ else i₀).1.t = bif c then i₁.1.t else i₀.1.t := by cases c <;> rfl
  unfold tok finT finalizeIssue resp
  rw [ht]
  by_cases h : (A.pk c).eval (List.ofFn (A.respond i₀.2 i₁.2 c)) = bif c then i₁.1.t else i₀.1.t
  · simp only [h, decide_true, ↓reduceIte]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **With simulated redemptions, the view reads the issuance outputs only through the requests,
the commitments and the nullifiers** (for honest pending tokens, `t = Com(nf, ·, r)`). -/
theorem post_redSim (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cL cR : CR)
    (h₀ : i₀.1.t = com i₀.1.nf A.ci A.cr i₀.1.r) (h₁ : i₁.1.t = com i₁.1.nf A.ci A.cr i₁.1.r) :
    post A idx i₀ i₁ (redSim A simR cL (pt A idx b i₀ i₁ false))
        (redSim A simR cR (pt A idx b i₀ i₁ true)) ↔
      A.guess i₀.2 i₁.2 (bif allOkT A idx i₀.2 i₁.2 i₀.1.t i₁.1.t then
        some (ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cL false,
          ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cR true) else none) := by
  have htok (c : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD A i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hok (c side : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      okAt A idx i₀ i₁ c side = okT A idx i₀.2 i₁.2 i₀.1.t i₁.1.t c side := by
    unfold okAt okT redeemOk
    rw [htok c hc]
    cases c <;> simp only [Bool.cond_false, Bool.cond_true, ← h₀, ← h₁]
  have hall : allOk A idx i₀ i₁ = allOkT A idx i₀.2 i₁.2 i₀.1.t i₁.1.t := by
    unfold allOk allOkT
    rw [tok_of_fin A i₀ i₁ false, tok_of_fin A i₀ i₁ true]
    cases e₀ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t false
    · simp
    · cases e₁ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t true
      · simp
      · simp [hok _ _ e₀, hok _ _ e₁]
  unfold post
  rw [hall]
  refine iff_of_eq (congrArg _ ?_)
  cases hC : allOkT A idx i₀.2 i₁.2 i₀.1.t i₁.1.t
  · rfl
  · unfold allOkT at hC
    simp only [Bool.and_eq_true] at hC
    obtain ⟨⟨⟨⟨⟨f₀, f₁⟩, o₁⟩, o₂⟩, o₃⟩, o₄⟩ := hC
    have hk (c side : Bool) (h : okT A idx i₀.2 i₁.2 i₀.1.t i₁.1.t c side = true) :
        redeemOk A.ci A.cr (tokD A i₀ i₁ c) (A.choose i₀.2 i₁.2 side).1
          (idx (A.choose i₀.2 i₁.2 side).1 (A.pk c)) = true := by
      have := hok c side (by cases c <;> assumption)
      rw [← this] at h
      exact h
    cases b
    · rw [redSim_of_ok A simR _ _ (hk false false o₁), redSim_of_ok A simR _ _ (hk true true o₄)]
      simp only [pt, htok false f₀, htok true f₁, ySim, Bool.false_xor, Bool.cond_false,
        Bool.cond_true]
    · rw [redSim_of_ok A simR _ _ (hk true false o₃), redSim_of_ok A simR _ _ (hk false true o₂)]
      simp only [pt, htok false f₀, htok true f₁, ySim, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.cond_false, Bool.cond_true]

/-- The game with all four proofs simulated. -/
def simGame (b : Bool) :=
  game A idx b (issSim A simI) (issSim A simI) (redSim A simR) (redSim A simR)

/-- The view with all four proofs simulated, as a function of the commitments `t₀, t₁`, the
nullifiers `n₀, n₁` revealed at redemption, and the simulator coins: the openings do not
appear. -/
def hview (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (cI₀ cI₁ : CI) (cL cR : CR) : Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.ci⟩ cI₁
  A.guess q₀ q₁ (bif allOkT A idx q₀ q₁ t₀ t₁ then
    some (ySim A simR b q₀ q₁ n₀ n₁ cL false, ySim A simR b q₀ q₁ n₀ n₁ cR true) else none)

theorem simGame_iff (b : Bool)
    (x : ((Coins nfBytes × Coins rBytes × CI) × (Coins nfBytes × Coins rBytes × CI)) × (CR × CR)) :
    simGame A idx simI simR b x ↔
      hview A idx simI simR b (com (List.ofFn x.1.1.1) A.ci A.cr (List.ofFn x.1.1.2.1))
        (com (List.ofFn x.1.2.1) A.ci A.cr (List.ofFn x.1.2.2.1)) (List.ofFn x.1.1.1)
        (List.ofFn x.1.2.1) x.1.1.2.2 x.1.2.2.2 x.2.1 x.2.2 :=
  post_redSim A idx simR b _ _ _ _ rfl rfl

/-! ## The hiding hop -/

/-- The two-instance tape of the hiding experiment: `(nf₀, r₀)`, `(nf₁, r₁)`. -/
abbrev HTape := (Coins nfBytes × Coins rBytes) × (Coins nfBytes × Coins rBytes)

/-- The real hiding experiment: both commitments and the committed nullifiers. -/
def hideReal (ci cr : Bytes) (x : HTape) : Bytes × Bytes × Bytes × Bytes :=
  (com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), com (List.ofFn x.2.1) ci cr (List.ofFn x.2.2),
    List.ofFn x.1.1, List.ofFn x.2.1)

/-- The ideal hiding experiment: both commitments and fresh uniform nullifiers. -/
def hideIdeal (ci cr : Bytes) (x : HTape × (Coins nfBytes × Coins nfBytes)) :
    Bytes × Bytes × Bytes × Bytes :=
  (com (List.ofFn x.1.1.1) ci cr (List.ofFn x.1.1.2), com (List.ofFn x.1.2.1) ci cr (List.ofFn x.1.2.2),
    List.ofFn x.2.1, List.ofFn x.2.2)

/-- **The hiding advantage** of `D` (`security/moussaka.md` §3.2, `Adv^hide_Com`, for contexts
`(ctx_iss, ctx_red)`). -/
noncomputable def hidingAdv (ci cr : Bytes) (D : Bytes × Bytes × Bytes × Bytes → Prop) : ℝ :=
  |pr HTape (fun x => D (hideReal ci cr x)) -
    pr (HTape × (Coins nfBytes × Coins nfBytes)) (fun x => D (hideIdeal ci cr x))|

/-- **The reduction to hiding**: the adversary, with the simulator coins `c` fixed, run on the
commitments and nullifiers it is given. -/
def reduction (b : Bool) (c : (CI × CI) × (CR × CR)) (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hview A idx simI simR b z.1 z.2.1 z.2.2.1 z.2.2.2 c.1.1 c.1.2 c.2.1 c.2.2

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
def idealGame (b : Bool) (x : (HTape × (Coins nfBytes × Coins nfBytes)) × ((CI × CI) × (CR × CR))) :
    Prop :=
  reduction A idx simI simR b x.2 (hideIdeal A.ci A.cr x.1)

/-- Regroup the simulated game's tape as the hiding tape and the simulator coins. -/
def regroup :
    ((Coins nfBytes × Coins rBytes × CI) × (Coins nfBytes × Coins rBytes × CI)) × (CR × CR) ≃
      HTape × ((CI × CI) × (CR × CR)) where
  toFun x := (((x.1.1.1, x.1.1.2.1), (x.1.2.1, x.1.2.2.1)), ((x.1.1.2.2, x.1.2.2.2), x.2))
  invFun y := (((y.1.1.1, y.1.1.2, y.2.1.1), (y.1.2.1, y.1.2.2, y.2.1.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem hiding_hop [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv A.ci A.cr (reduction A idx simI simR b c) ≤ εhide) :
    |pr _ (simGame A idx simI simR b) - pr _ (idealGame A idx simI simR b)| ≤ εhide := by
  rw [← pr_equiv regroup.symm (simGame A idx simI simR b),
    pr_congr fun y => simGame_iff A idx simI simR b (regroup.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- Exchange the fresh nullifiers. -/
def swapN : (HTape × (Coins nfBytes × Coins nfBytes)) × ((CI × CI) × (CR × CR)) ≃
    (HTape × (Coins nfBytes × Coins nfBytes)) × ((CI × CI) × (CR × CR)) where
  toFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  invFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **After the hiding hop the worlds coincide**: world `b` reveals the fresh `n_b` on the left and
`n_{¬b}` on the right, and the fresh pair is exchangeable. -/
theorem idealGame_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGame A idx simI simR false) = pr _ (idealGame A idx simI simR true) := by
  rw [← pr_equiv swapN]
  exact pr_congr fun x => Iff.rfl

/-! ## Issuer hiding and unlinkability -/

/-- **Theorem 4(a) (colluding mode), from uniform seed expansions.** If the issuance and redemption
proofs are `εI`- and `εR`-zero-knowledge (the label-row fix; not on `main`, see above) and every
reduction `reduction A idx simI simR b c` has hiding advantage at most `εhide`, then for every
adversary playing all Anchors and the Moderator, with any keys, Anchor Sets and digests, the
acceptance probabilities in the two worlds differ by at most `4εI + 4εR + 2εhide`. -/
theorem anonymity [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (PI : NIZK IssueInstance)
    (PR : NIZK RedeemInstance) {εI εR εhide : ℝ} (hεR : 0 ≤ εR)
    (hI : ZeroKnowledge IssueRel (proveR PI) simI εI)
    (hR : ZeroKnowledge RedeemRel (proveR PR) simR εR)
    (hhide : ∀ b c, hidingAdv A.ci A.cr (reduction A idx simI simR b c) ≤ εhide) :
    |pr _ (realGame A idx PI PR false) - pr _ (realGame A idx PI PR true)| ≤
      4 * εI + 4 * εR + 2 * εhide := by
  have hiss := issue_close A simI PI hI
  have hred := fun p hr hs => redeem_close A simR PR hεR hR p hr hs
  have hw (b : Bool) : |pr _ (realGame A idx PI PR b) - pr _ (idealGame A idx simI simR b)| ≤
      2 * εI + 2 * εR + εhide := by
    set p0 := pr _ (realGame A idx PI PR b)
    set p1 := pr _ (game A idx b (issSim A simI) (issReal A PI) (redReal A PR) (redReal A PR))
    set p2 := pr _ (game A idx b (issSim A simI) (issSim A simI) (redReal A PR) (redReal A PR))
    set p3 := pr _ (game A idx b (issSim A simI) (issSim A simI) (redSim A simR) (redReal A PR))
    set p4 := pr _ (simGame A idx simI simR b)
    set p5 := pr _ (idealGame A idx simI simR b)
    have h1 : |p0 - p1| ≤ εI := game_hop₀ A idx b (issReal A PI) (redReal A PR) (redReal A PR) hiss
    have h2 : |p1 - p2| ≤ εI := game_hop₁ A idx b (issSim A simI) (redReal A PR) (redReal A PR) hiss
    have h3 : |p2 - p3| ≤ εR :=
      game_hopL A idx b (issSim_wf A simI) (issSim_wf A simI) (redReal A PR) hred
    have h4 : |p3 - p4| ≤ εR :=
      game_hopR A idx b (issSim_wf A simI) (issSim_wf A simI) (redSim A simR) hred
    have h5 : |p4 - p5| ≤ εhide := hiding_hop A idx simI simR b (hhide b)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGame_eq] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (idealGame A idx simI simR true)) _
    _ ≤ (2 * εI + 2 * εR + εhide) + (2 * εI + 2 * εR + εhide) :=
        add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εI + 4 * εR + 2 * εhide := by ring

end VoleMole.Privacy.Moussaka
