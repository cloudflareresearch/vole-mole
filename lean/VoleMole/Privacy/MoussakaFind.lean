import VoleMole.Privacy.Moussaka

/-!
# Theorem 4(a) for `main`'s Client: the index from `find_issuer`

Since `21be618` the Client no longer takes its issuer's index from the caller: `redeem_request`
finds it from the token (`Spec.Moussaka.redeemRequest`, `findIssuer`: the last key of `S` that
verifies `(s, t)`), and refuses only if no key does. The index now depends on the token, so this
Client is not an index rule of `Privacy/Moussaka.lean` (a function of `S` and the issuer's key).
This file is that game with `main`'s Client; everything else is unchanged and reused
(`Privacy.Moussaka`: the adversary, the issuance slots, `issue_close`, the hiding experiment).

**Game.** As `Privacy/Moussaka.lean`: the adversary plays every Anchor and the Moderator, chooses
the contexts and the two issuing keys, sees and answers both issuance requests, and chooses per
side an Anchor Set and a digest. In world `b` the left redemption is Client `b`'s token and the
right one Client `¬b`'s, each run with `redeemRequest` (`find_issuer`). The refusal rule: both
redemptions happen only if both tokens finalized and `find_issuer` succeeds for both tokens in
both sets; otherwise both are refused. The adversary can compute this bit itself: it depends on its
responses and the commitments only (`allOkT`).

The index `find_issuer` returns may be a foreign key's (one that also verifies the token); the
redemption witness then uses that key, which `RedeemRel` allows, and zero knowledge hides which.

**Assumptions and bound.** As `Privacy.Moussaka.anonymity`: per-proof zero knowledge of both
relations (`εI`, `εR`; on `main` only the joint (PU) hop holds, on paper, since Moussaka keeps the
witness-derived CRT masks) and hiding of `Com` for the explicit reductions (`εhide`).
**`anonymity`**: `≤ 4εI + 4εR + 2εhide`.
-/

open Finset

namespace VoleMole.Privacy.MoussakaFind

open VoleMole.Spec VoleMole.Spec.Moussaka
open VoleMole.Privacy.Moussaka (Adversary tok tokD tokD_wf WellFormed issReal issSim issReal_wf
  issSim_wf IssueRelW RedeemRelW issue_close resp finT tok_of_fin hidingAdv hideReal hideIdeal HTape
  proveR regroup swapN)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The spec with `ρ_red` given -/

/-- `redeemRequest` with `ρ_red = expand_redeem_seed(seed')` as an argument. -/
def redeemRequestOf (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (ctxIss ctxRed cd rho : Bytes) : Except Error Bytes :=
  match findIssuer A (com tok.nf ctxIss ctxRed tok.r) tok.s with
  | none => .error .invalidToken
  | some i =>
    .ok (tok.nf ++ PR.prove (encodeRedeemWitness tok.nf ctxIss ctxRed tok.r tok.s i)
      ⟨A.keys, tok.nf, ctxIss, ctxRed, cd⟩ rho)

theorem redeemRequest_eq (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (ctxIss ctxRed cd seed : Bytes) :
    redeemRequest PR tok A ctxIss ctxRed cd seed =
      redeemRequestOf PR tok A ctxIss ctxRed cd (expandRedeemSeed seed) := rfl

/-! ## The game -/

/-- Where a redemption is asked: the token, the Anchor Set and the digest. -/
structure RedeemPt where
  tok : Token
  anchors : AnchorSet
  cd : Bytes

variable (A : Adversary)

/-- The Client's `find_issuer` succeeds for token `t` in `S`. -/
def redeemable (ci cr : Bytes) (t : Token) (S : AnchorSet) : Bool :=
  (findIssuer S (com t.nf ci cr t.r) t.s).isSome

/-- Client `c` can redeem in the set of side `side`. -/
def okAt (i₀ i₁ : PendingToken × Bytes) (c side : Bool) : Bool :=
  redeemable A.ci A.cr (tokD A i₀ i₁ c) (A.choose i₀.2 i₁.2 side).1

/-- The rule: both tokens finalized, and both are redeemable in both sets. -/
def allOk (i₀ i₁ : PendingToken × Bytes) : Bool :=
  (tok A i₀ i₁ false).isSome && (tok A i₀ i₁ true).isSome &&
    okAt A i₀ i₁ false false && okAt A i₀ i₁ false true &&
    okAt A i₀ i₁ true false && okAt A i₀ i₁ true true

/-- The redemption of side `side` (`false` = left) in world `b`: Client `b ^^ side`'s token. -/
def pt (b : Bool) (i₀ i₁ : PendingToken × Bytes) (side : Bool) : RedeemPt :=
  ⟨tokD A i₀ i₁ (b ^^ side), (A.choose i₀.2 i₁.2 side).1, (A.choose i₀.2 i₁.2 side).2⟩

/-- The adversary's guess from the issuance outputs and the two redemption requests. -/
def post (i₀ i₁ : PendingToken × Bytes) (yL yR : Except Error Bytes) : Prop :=
  A.guess i₀.2 i₁.2 (bif allOk A i₀ i₁ then some (yL, yR) else none)

/-- The view in world `b`, given the issuance outputs and the two redemption provers. -/
def view (b : Bool) (i₀ i₁ : PendingToken × Bytes) (redL redR : RedeemPt → Except Error Bytes) :
    Prop :=
  post A i₀ i₁ (redL (pt A b i₀ i₁ false)) (redR (pt A b i₀ i₁ true))

/-- The game with the two issuance slots and the two redemption slots drawn by `g₀ g₁ gL gR`. -/
def game {T₀ T₁ TL TR : Type} (b : Bool) (g₀ : T₀ → PendingToken × Bytes)
    (g₁ : T₁ → PendingToken × Bytes) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (x : (T₀ × T₁) × (TL × TR)) : Prop :=
  view A b (g₀ x.1.1) (g₁ x.1.2) (gL x.2.1) (gR x.2.2)

/-- A real redemption from `ρ_red`, with `main`'s `find_issuer`. -/
def redReal (PR : NIZK RedeemInstance) (ρ : Coins proveSeedBytes) (p : RedeemPt) :
    Except Error Bytes :=
  redeemRequestOf PR p.tok p.anchors A.ci A.cr p.cd (List.ofFn ρ)

/-- **The real game** in world `b`. -/
def realGame (PI : NIZK IssueInstance) (PR : NIZK RedeemInstance) (b : Bool) :=
  game A b (issReal A PI) (issReal A PI) (redReal A PR) (redReal A PR)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)

/-- A simulated redemption, with the Client's `find_issuer` unchanged. -/
def redSim (c : CR) (p : RedeemPt) : Except Error Bytes :=
  match findIssuer p.anchors (com p.tok.nf A.ci A.cr p.tok.r) p.tok.s with
  | none => .error .invalidToken
  | some _ => .ok (p.tok.nf ++ simR ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩ c)

/-! ## One proof at a time -/

variable {T₀ T₁ TL TR T₀' T₁' TL' TR' : Type} [Fintype T₀] [Fintype T₁] [Fintype TL] [Fintype TR]
  [Fintype T₀'] [Fintype T₁'] [Fintype TL'] [Fintype TR']

theorem game_hop₀ [Nonempty T₁] [Nonempty TL] [Nonempty TR] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₀' : T₀' → PendingToken × Bytes}
    (g₁ : T₁ → PendingToken × Bytes) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (h : Close ε g₀ g₀') :
    |pr _ (game A b g₀ g₁ gL gR) - pr _ (game A b g₀' g₁ gL gR)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le' _ _ fun x₁ =>
    h (fun o => view A b o (g₁ x₁) (gL y.1) (gR y.2))

theorem game_hop₁ [Nonempty T₀] [Nonempty TL] [Nonempty TR] (b : Bool) {ε : ℝ}
    (g₀ : T₀ → PendingToken × Bytes) {g₁ : T₁ → PendingToken × Bytes}
    {g₁' : T₁' → PendingToken × Bytes} (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (h : Close ε g₁ g₁') :
    |pr _ (game A b g₀ g₁ gL gR) - pr _ (game A b g₀ g₁' gL gR)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le _ _ fun x₀ =>
    h (fun o => view A b (g₀ x₀) o (gL y.1) (gR y.2))

theorem game_hopL [Nonempty T₀] [Nonempty T₁] [Nonempty TR] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes} (h₀ : WellFormed g₀)
    (h₁ : WellFormed g₁) {gL : TL → RedeemPt → Except Error Bytes}
    {gL' : TL' → RedeemPt → Except Error Bytes} (gR : TR → RedeemPt → Except Error Bytes)
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gL t p) (fun t => gL' t p)) :
    |pr _ (game A b g₀ g₁ gL gR) - pr _ (game A b g₀ g₁ gL' gR)| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le' _ _ fun xR =>
    h (pt A b (g₀ x.1) (g₁ x.2) false) (tokD_wf A (h₀ _) (h₁ _) _).1
      (tokD_wf A (h₀ _) (h₁ _) _).2.1 (tokD_wf A (h₀ _) (h₁ _) _).2.2
      (fun y => post A (g₀ x.1) (g₁ x.2) y (gR xR (pt A b (g₀ x.1) (g₁ x.2) true)))

theorem game_hopR [Nonempty T₀] [Nonempty T₁] [Nonempty TL] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes} (h₀ : WellFormed g₀)
    (h₁ : WellFormed g₁) (gL : TL → RedeemPt → Except Error Bytes)
    {gR : TR → RedeemPt → Except Error Bytes} {gR' : TR' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gR t p) (fun t => gR' t p)) :
    |pr _ (game A b g₀ g₁ gL gR) - pr _ (game A b g₀ g₁ gL gR')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le _ _ fun xL =>
    h (pt A b (g₀ x.1) (g₁ x.2) true) (tokD_wf A (h₀ _) (h₁ _) _).1
      (tokD_wf A (h₀ _) (h₁ _) _).2.1 (tokD_wf A (h₀ _) (h₁ _) _).2.2
      (fun y => post A (g₀ x.1) (g₁ x.2) (gL xL (pt A b (g₀ x.1) (g₁ x.2) false)) y)

/-- **One redemption proof.** At every redemption point with a well-formed token, a real and a
simulated redemption are `εR`-close: if `find_issuer` fails both refuse alike, otherwise the
witness at the index it returns satisfies `RedeemRel` and zero knowledge applies. -/
theorem redeem_close [Fintype CR] [Nonempty CR] (PR : NIZK RedeemInstance) {εR : ℝ} (hε : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) (p : RedeemPt)
    (hr : p.tok.r.length = rBytes) (hs : p.tok.s.length = uovN) (hn : p.tok.nf.length = nfBytes) :
    Close εR (fun ρ => redReal A PR ρ p) (fun c => redSim A simR c p) := by
  intro D
  unfold redReal redSim redeemRequestOf
  cases hf : findIssuer p.anchors (com p.tok.nf A.ci A.cr p.tok.r) p.tok.s with
  | none => exact close_const hε _ D
  | some i =>
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    have hrel : RedeemRelW ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩
        (encodeRedeemWitness p.tok.nf A.ci A.cr p.tok.r p.tok.s i) :=
      ⟨⟨_, _, _, pk, hr, hs, hk, rfl, he⟩, p.anchors.valid.2.1, hn,
        by simp [Adversary.ci, ctxBytes], by simp [Adversary.cr, ctxBytes]⟩
    exact (hR _ _ hrel).map (fun π => (Except.ok (p.tok.nf ++ π) : Except Error Bytes)) D

/-! ## All proofs simulated: the view is a function of the commitments and nullifiers -/

/-- Client `c`'s `find_issuer` succeeds in the set of side `side`, checked against `t_c`. -/
def okT (q₀ q₁ t₀ t₁ : Bytes) (c side : Bool) : Bool :=
  (findIssuer (A.choose q₀ q₁ side).1 (bif c then t₁ else t₀) (resp A q₀ q₁ c)).isSome

/-- The rule, as a function of the requests and the commitments. -/
def allOkT (q₀ q₁ t₀ t₁ : Bytes) : Bool :=
  finT A q₀ q₁ t₀ t₁ false && finT A q₀ q₁ t₀ t₁ true && okT A q₀ q₁ t₀ t₁ false false &&
    okT A q₀ q₁ t₀ t₁ false true && okT A q₀ q₁ t₀ t₁ true false &&
    okT A q₀ q₁ t₀ t₁ true true

/-- A simulated redemption request of side `side` in world `b`: the nullifier `n_{b ^^ side}` and a
simulated proof. -/
def ySim (b : Bool) (q₀ q₁ n₀ n₁ : Bytes) (c : CR) (side : Bool) : Except Error Bytes :=
  .ok ((bif b ^^ side then n₁ else n₀) ++ simR ⟨(A.choose q₀ q₁ side).1.keys,
    bif b ^^ side then n₁ else n₀, A.ci, A.cr, (A.choose q₀ q₁ side).2⟩ c)

theorem redSim_of_ok (c : CR) (p : RedeemPt) (h : redeemable A.ci A.cr p.tok p.anchors = true) :
    redSim A simR c p = .ok (p.tok.nf ++ simR ⟨p.anchors.keys, p.tok.nf, A.ci, A.cr, p.cd⟩ c) := by
  unfold redeemable at h
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
  unfold redSim
  rw [hi]

/-- **With simulated redemptions, the view reads the issuance outputs only through the requests,
the commitments and the nullifiers** (for honest pending tokens, `t = Com(nf, ·, r)`). -/
theorem post_redSim (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cL cR : CR)
    (h₀ : i₀.1.t = com i₀.1.nf A.ci A.cr i₀.1.r) (h₁ : i₁.1.t = com i₁.1.nf A.ci A.cr i₁.1.r) :
    post A i₀ i₁ (redSim A simR cL (pt A b i₀ i₁ false))
        (redSim A simR cR (pt A b i₀ i₁ true)) ↔
      A.guess i₀.2 i₁.2 (bif allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t then
        some (ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cL false,
          ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cR true) else none) := by
  have htok (c : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD A i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hok (c side : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      okAt A i₀ i₁ c side = okT A i₀.2 i₁.2 i₀.1.t i₁.1.t c side := by
    unfold okAt okT redeemable
    rw [htok c hc]
    cases c <;> simp only [Bool.cond_false, Bool.cond_true, ← h₀, ← h₁]
  have hall : allOk A i₀ i₁ = allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t := by
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
  cases hC : allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t
  · rfl
  · unfold allOkT at hC
    simp only [Bool.and_eq_true] at hC
    obtain ⟨⟨⟨⟨⟨f₀, f₁⟩, o₁⟩, o₂⟩, o₃⟩, o₄⟩ := hC
    have hk (c side : Bool) (h : okT A i₀.2 i₁.2 i₀.1.t i₁.1.t c side = true) :
        redeemable A.ci A.cr (tokD A i₀ i₁ c) (A.choose i₀.2 i₁.2 side).1 = true := by
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
  game A b (issSim A simI) (issSim A simI) (redSim A simR) (redSim A simR)

/-- The view with all four proofs simulated, as a function of the commitments `t₀, t₁`, the
nullifiers `n₀, n₁` revealed at redemption, and the simulator coins: the openings do not
appear. -/
def hview (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (cI₀ cI₁ : CI) (cL cR : CR) : Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.ci⟩ cI₁
  A.guess q₀ q₁ (bif allOkT A q₀ q₁ t₀ t₁ then
    some (ySim A simR b q₀ q₁ n₀ n₁ cL false, ySim A simR b q₀ q₁ n₀ n₁ cR true) else none)

theorem simGame_iff (b : Bool)
    (x : ((Coins nfBytes × Coins rBytes × CI) × (Coins nfBytes × Coins rBytes × CI)) × (CR × CR)) :
    simGame A simI simR b x ↔
      hview A simI simR b (com (List.ofFn x.1.1.1) A.ci A.cr (List.ofFn x.1.1.2.1))
        (com (List.ofFn x.1.2.1) A.ci A.cr (List.ofFn x.1.2.2.1)) (List.ofFn x.1.1.1)
        (List.ofFn x.1.2.1) x.1.1.2.2 x.1.2.2.2 x.2.1 x.2.2 :=
  post_redSim A simR b _ _ _ _ rfl rfl

/-! ## The hiding hop -/

/-- **The reduction to hiding**: the adversary, with the simulator coins `c` fixed, run on the
commitments and nullifiers it is given. -/
def reduction (b : Bool) (c : (CI × CI) × (CR × CR)) (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hview A simI simR b z.1 z.2.1 z.2.2.1 z.2.2.2 c.1.1 c.1.2 c.2.1 c.2.2

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
def idealGame (b : Bool) (x : (HTape × (Coins nfBytes × Coins nfBytes)) × ((CI × CI) × (CR × CR))) :
    Prop :=
  reduction A simI simR b x.2 (hideIdeal A.ci A.cr x.1)

theorem hiding_hop [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv A.ci A.cr (reduction A simI simR b c) ≤ εhide) :
    |pr _ (simGame A simI simR b) - pr _ (idealGame A simI simR b)| ≤ εhide := by
  rw [← pr_equiv regroup.symm (simGame A simI simR b),
    pr_congr fun y => simGame_iff A simI simR b (regroup.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- **After the hiding hop the worlds coincide** (swap of the fresh nullifiers). -/
theorem idealGame_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGame A simI simR false) = pr _ (idealGame A simI simR true) := by
  rw [← pr_equiv swapN]
  exact pr_congr fun x => Iff.rfl

/-! ## Issuer hiding and unlinkability -/

/-- **Theorem 4(a) (colluding mode) for `main`'s Client** (`redeemRequest`, `find_issuer`), from
uniform seed expansions. If the issuance and redemption proofs are `εI`- and `εR`-zero-knowledge
and every reduction `reduction A simI simR b c` has hiding advantage at most `εhide`, then for
every adversary playing all Anchors and the Moderator, with any keys, Anchor Sets and digests, the
acceptance probabilities in the two worlds differ by at most `4εI + 4εR + 2εhide`. -/
theorem anonymity [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (PI : NIZK IssueInstance)
    (PR : NIZK RedeemInstance) {εI εR εhide : ℝ} (hεR : 0 ≤ εR)
    (hI : ZeroKnowledge IssueRelW (proveR PI) simI εI)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hhide : ∀ b c, hidingAdv A.ci A.cr (reduction A simI simR b c) ≤ εhide) :
    |pr _ (realGame A PI PR false) - pr _ (realGame A PI PR true)| ≤
      4 * εI + 4 * εR + 2 * εhide := by
  have hiss := issue_close A simI PI hI
  have hred := fun p hr hs hn => redeem_close A simR PR hεR hR p hr hs hn
  have hw (b : Bool) : |pr _ (realGame A PI PR b) - pr _ (idealGame A simI simR b)| ≤
      2 * εI + 2 * εR + εhide := by
    set p0 := pr _ (realGame A PI PR b)
    set p1 := pr _ (game A b (issSim A simI) (issReal A PI) (redReal A PR) (redReal A PR))
    set p2 := pr _ (game A b (issSim A simI) (issSim A simI) (redReal A PR) (redReal A PR))
    set p3 := pr _ (game A b (issSim A simI) (issSim A simI) (redSim A simR) (redReal A PR))
    set p4 := pr _ (simGame A simI simR b)
    set p5 := pr _ (idealGame A simI simR b)
    have h1 : |p0 - p1| ≤ εI := game_hop₀ A b (issReal A PI) (redReal A PR) (redReal A PR) hiss
    have h2 : |p1 - p2| ≤ εI := game_hop₁ A b (issSim A simI) (redReal A PR) (redReal A PR) hiss
    have h3 : |p2 - p3| ≤ εR :=
      game_hopL A b (issSim_wf A simI) (issSim_wf A simI) (redReal A PR) hred
    have h4 : |p3 - p4| ≤ εR :=
      game_hopR A b (issSim_wf A simI) (issSim_wf A simI) (redSim A simR) hred
    have h5 : |p4 - p5| ≤ εhide := hiding_hop A simI simR b (hhide b)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGame_eq] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (idealGame A simI simR true)) _
    _ ≤ (2 * εI + 2 * εR + εhide) + (2 * εI + 2 * εR + εhide) :=
        add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εI + 4 * εR + 2 * εhide := by ring

end VoleMole.Privacy.MoussakaFind
