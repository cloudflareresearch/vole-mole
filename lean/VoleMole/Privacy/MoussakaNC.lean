import VoleMole.Privacy.SeedXOF
import VoleMole.Privacy.MoussakaLean
import VoleMole.Spec.MoussakaLabelRows

/-!
# Moussaka issuer hiding and unlinkability against a non-colluding Moderator (Theorem 4(b))

Game ANON in the non-colluding mode of `security/moussaka.md` §6: the adversary is the Moderator
alone. It chooses the contexts, the two issuing keys `pk false`, `pk true` and, per side, an Anchor
Set `S` and a challenge digest `cd`; it sees **no issuance**. Honest Anchors with signers
`sk false`, `sk true` (any `Signer` correct for its key: abstract `derive_preimage`, the keys
possibly chosen by the adversary) answer the Clients' requests with `Spec.Moussaka.issueResponseLR`
(the Anchor checks the request's length, verifies the issuance proof, then runs `derive_preimage`;
the length is the label-row layout's `45 + 7528` bytes, that of the Lean prover of the
random-oracle games: with `main`'s `issueResponse`, `45 + 7272`, the honest Anchor would reject
every label-row request as malformed, `Privacy/MoussakaPqov.lean`), and the Clients run
`finalizeIssue`. In world `b` the left redemption is Client `b`'s token and the right one Client
`¬b`'s. §6's refusal rule is as in `Privacy.Moussaka.view`: both redemptions happen only if both
tokens finalized and each is redeemable at its own index in both sets; otherwise both are refused.
The adversary sees the two redemption requests (or the refusal) and guesses.

The seed expansions' outputs `(nf, r, ρ_iss)` and `ρ_red` are uniform, as in
`Privacy/Moussaka.lean`.

## The hops

1. Both redemption proofs are replaced by simulated ones (`hopL_NC`, `hopR_NC`; `εR` each, from
   `Privacy.Moussaka.redeem_close`). The issuance proofs are never seen: they are **not**
   simulated, and nothing is assumed of the issuance proof system `PI` (not even completeness).
2. With simulated redemptions the view is a function of the refusal bit, the two nullifiers and
   the simulator coins (`simNC_iff`). The commitments and openings appear nowhere, so no hiding
   assumption is used.
3. **The abort term.** The refusal bit is `good false x₀ && good true x₁`, where `good c x` says
   that Client `c`'s issuance (on tape `x`) succeeded and its token is redeemable at its index in
   both sets. With a sound index rule (`IdxSound`: the index the Client takes from `S` holds its
   issuer's map, or nothing), `good c x` is `acc x && K c` (the Anchor accepted the request, a
   function of `x` alone; `K c`, a constant: the key is found in both sets), **unless**
   `derive_preimage` fails on Client `c`'s commitment (`good_eq_of_derive`). Replacing it by the
   symmetric `acc x₀ && acc x₁ && K false && K true` costs `φ false + φ true` per world
   (`sim_hyb_NC`), where `φ c` is the probability that `sk c` fails on
   `Com(nf, ctx_iss, ctx_red, r)` for uniform `(nf, r)` (`phi`).
4. The resulting hybrid is symmetric in the two Clients' tapes, so the worlds coincide exactly
   (`hybNC_eq`, a swap of the tapes; no `2⁻¹⁹²` term for `nf₀ = nf₁`).

## Results

* **`anonymityNC`** (Theorem 4(b), corrected): `≤ 4εR + 2·(φ false + φ true)`.
* **`unlinkabilityNC`**: with one Anchor (`pk false = pk true`, `sk false = sk true`) and **any**
  index rule, `≤ 4εR`: the abort events of the two Clients have the same law, so no abort term.
* **`anonymityNC_vinegarRO`**: `φ` without any assumption on `Com`. When each Anchor's
  `derive_preimage` fails only if all 256 vinegars it draws for the target from a uniformly random
  table are bad (pqov's `D_sk` with its vinegar hash SHAKE256 as a random oracle,
  `security/uov-assumptions.md` §2 Lemma D), averaging over the tables gives
  `≤ 4εR + 2·(δ₀^256 + δ₁^256)`, `δ_c` the fraction of bad vinegars of Anchor `c`'s key
  (`pr_fail_vinegar`). pqov's `derive_preimage` is exhibited as a signer satisfying `hfail` with
  all 256 attempts; pqov itself uses only the first 255 (`Privacy/MoussakaPqov.lean`:
  `pqovRO`, `anonymityNC_pqov`, `δ^255`). `δ ≤ 1/255` holds on average over the key, not for a
  fixed key (`Privacy/PqovDelta.lean`).
* `anonymityNC_label_rows`, `anonymityNC_label_rows_shake`, `unlinkabilityNC_label_rows`: with the
  Lean prover for redemption (label rows), down to its tape hypothesis or to the hop hypotheses.

## Corrections to the note's Theorem 4(b)

* The note's `2·ε_ZK^joint|_{2 redemption proofs} + 2⁻¹⁹²` misses the abort term `2·(φ₀ + φ₁)`
  (honest `derive_preimage` fails on a fixed set of targets, and success is a function of
  `t = Com(nf, …, r)`, so conditioned on both issuances succeeding the nullifiers' laws can differ
  between two Anchors). It is `0` for unlinkability (one Anchor) and needs no Keccak assumption:
  with the vinegar hash as a random oracle it is at most `2·(δ₀^256 + δ₁^256)` for every `Com`.
* The `2⁻¹⁹²` term is not needed.
* The game needs the index rule to be the Client's lookup of its issuer's key (`IdxSound`; the
  note's "indices that the Client takes from `S` itself"). With an arbitrary rule pointing at a
  foreign key `P'`, the refusal reveals whether `P'(s_c) = t_c` for the Client's hidden `s_c`,
  which no assumption here bounds. `unlinkabilityNC` needs no such rule.
-/

open Finset

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The game -/

/-- **The non-colluding adversary** (the Moderator): contexts, the two issuing keys (Client
`false`, Client `true`), the Anchor Set and challenge digest per side (`false` = left), and the
guess from the two redemption requests (or `none`: refused). It sees no issuance. -/
structure AdversaryNC where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  choose : Bool → AnchorSet × Bytes
  guess : Option (Except Error Bytes × Except Error Bytes) → Prop

/-- The adversary as a colluding `Adversary` (for its contexts, keys and choices; the responses
and the guess are not used). -/
def AdversaryNC.base (A : AdversaryNC) : Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk, fun _ _ _ _ => 0, fun _ _ side => A.choose side, fun _ _ _ => True⟩

/-- **A sound index rule**: the index the Client takes from `S` for its issuer's key `pk` holds a
key with `pk`'s map, or is out of range (`moussaka.cpp:186-215` leaves the index to the caller;
the game of §6 has the Client take it from `S`). -/
def IdxSound (idx : AnchorSet → UOVKey → ℕ) : Prop :=
  ∀ S pk k, S.keys[idx S pk]? = some k → k.eval = pk.eval

/-- One Client's issuance tape: `(nf, r, ρ_iss)`. -/
abbrev IssT := Coins nfBytes × Coins rBytes × Coins proveSeedBytes

/-- The real game's tape: both Clients' issuance tapes and both redemption seeds. -/
abbrev TapeNC := (IssT × IssT) × (Coins proveSeedBytes × Coins proveSeedBytes)

section Game

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- The honest Anchor `c`'s answer to a request (`issue_response` with the label-row request
length; `none` when it refuses or throws). -/
def respNC (c : Bool) (q : Bytes) : Option Bytes :=
  match issueResponseLR PI (sk c) q A.base.ci with
  | .ok (some s) => some s
  | _ => none

/-- Client `c`'s token after `finalize_issue` on its Anchor's answer. -/
def tokNC (c : Bool) (i : PendingToken × Bytes) : Option Token :=
  (respNC A PI sk c i.2).bind (finalizeIssue (A.pk c) i.1)

/-- The token, or a well-formed dummy when issuance failed (then nothing is redeemed). -/
def tokDNC (c : Bool) (i : PendingToken × Bytes) : Token :=
  (tokNC A PI sk c i).getD ⟨List.replicate nfBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- Client `c` (issuance output `i`) can redeem at its own index in the set of side `side`. -/
def okNC (c side : Bool) (i : PendingToken × Bytes) : Bool :=
  redeemOk A.base.ci A.base.cr (tokDNC A PI sk c i) (A.choose side).1
    (idx (A.choose side).1 (A.pk c))

/-- Client `c`'s issuance succeeded and its token is redeemable at its index in both sets. -/
def goodNC (c : Bool) (i : PendingToken × Bytes) : Bool :=
  (tokNC A PI sk c i).isSome && okNC A idx PI sk c false i && okNC A idx PI sk c true i

/-- The redemption of side `side` in world `b`: Client `b ^^ side`'s token. -/
def ptNC (b : Bool) (i₀ i₁ : PendingToken × Bytes) (side : Bool) : RedeemPt :=
  ⟨tokDNC A PI sk (b ^^ side) (bif b ^^ side then i₁ else i₀), (A.choose side).1,
    idx (A.choose side).1 (A.pk (b ^^ side)), (A.choose side).2⟩

/-- The adversary's view in world `b`: the two redemption requests, or the refusal. -/
def viewNC (b : Bool) (i₀ i₁ : PendingToken × Bytes) (redL redR : RedeemPt → Except Error Bytes) :
    Prop :=
  A.guess (bif goodNC A idx PI sk false i₀ && goodNC A idx PI sk true i₁ then
    some (redL (ptNC A idx PI sk b i₀ i₁ false), redR (ptNC A idx PI sk b i₀ i₁ true)) else none)

/-- The game with real issuances and the redemption slots drawn by `gL`, `gR`. -/
def gameNC {TL TR : Type} (b : Bool) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (x : (IssT × IssT) × (TL × TR)) : Prop :=
  viewNC A idx PI sk b (issReal A.base PI x.1.1) (issReal A.base PI x.1.2) (gL x.2.1) (gR x.2.2)

/-- **The real game** in world `b`. -/
def realGameNC (PR : NIZK RedeemInstance) (b : Bool) :=
  gameNC A idx PI sk b (redReal A.base PR) (redReal A.base PR)

variable {CR : Type} (simR : RedeemInstance → CR → Bytes)

/-- The game with both redemption proofs simulated. -/
def simGameNC (b : Bool) :=
  gameNC A idx PI sk b (redSim A.base simR) (redSim A.base simR)

/-- **The abort probability** of Anchor `c`: its `derive_preimage` fails on
`Com(nf, ctx_iss, ctx_red, r)` for uniform `(nf, r)`. -/
noncomputable def phi (c : Bool) : ℝ :=
  pr (Coins nfBytes × Coins rBytes) fun y =>
    (sk c).derivePreimage (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2)) = none

end Game

/-! ## The honest Anchor on an honest request -/

section Honest

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- The Anchor accepts the request: right (label-row) length and a verifying issuance proof. -/
def accNC (q : Bytes) : Bool :=
  decide (q.length = issueRequestBytesLR) && PI.verify (q.drop uovM) ⟨q.take uovM, A.base.ci⟩

lemma length_ci : A.base.ci.length = ctxBytes := by simp [Adversary.ci]

lemma respNC_eq (c : Bool) (q : Bytes) :
    respNC A PI sk c q = if accNC A PI q then (sk c).derivePreimage (q.take uovM) else none := by
  unfold respNC issueResponseLR issueResponseN accNC
  by_cases hl : q.length = issueRequestBytesLR
  · simp only [hl, length_ci, ne_eq, not_true_eq_false, or_self, ↓reduceIte, decide_true,
      Bool.true_and]
    cases PI.verify (q.drop uovM) ⟨q.take uovM, A.base.ci⟩
    · simp
    · simp only [↓reduceIte]
      cases (sk c).derivePreimage (q.take uovM) <;> rfl
  · simp [hl]

/-- Client `c`'s commitment on tape `x`. -/
def tNC (x : IssT) : Bytes := com (List.ofFn x.1) A.base.ci A.base.cr (List.ofFn x.2.1)

lemma issReal_t (x : IssT) : (issReal A.base PI x).1.t = tNC A x := rfl

lemma issReal_take (x : IssT) : (issReal A.base PI x).2.take uovM = tNC A x := by
  simp only [issReal, issueRequestOf, tNC]
  exact List.take_left' (length_com _ _ _ _)

/-- **An honest issuance**: the token is `(nf, r, s)` for the Anchor's preimage `s`, if the Anchor
accepted and `derive_preimage` succeeded, and nothing otherwise. -/
lemma tokNC_issReal (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    tokNC A PI sk c (issReal A.base PI x) =
      if accNC A PI (issReal A.base PI x).2 then
        ((sk c).derivePreimage (tNC A x)).map fun s => ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩
      else none := by
  unfold tokNC
  rw [respNC_eq, issReal_take]
  split_ifs
  · cases hd : (sk c).derivePreimage (tNC A x) with
    | none => rfl
    | some s =>
      have hc := (hsk c (tNC A x) s (length_com _ _ _ _) hd).2
      simp only [Option.bind_some, Option.map_some, finalizeIssue, issReal_t, hc, ↓reduceIte]
      rfl
  · rfl

lemma tokDNC_wf (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    (tokDNC A PI sk c (issReal A.base PI x)).r.length = rBytes ∧
      (tokDNC A PI sk c (issReal A.base PI x)).s.length = uovN ∧
      (tokDNC A PI sk c (issReal A.base PI x)).nf.length = nfBytes := by
  unfold tokDNC
  rw [tokNC_issReal A PI sk hsk]
  split_ifs
  · cases hd : (sk c).derivePreimage (tNC A x) with
    | none => simp
    | some s =>
      have hs := (hsk c (tNC A x) s (length_com _ _ _ _) hd).1
      simp [hs]
  · simp

lemma tokDNC_wf' (hsk : ∀ c, (sk c).Correct (A.pk c)) (c d : Bool) (x₀ x₁ : IssT) :
    (tokDNC A PI sk c (bif d then issReal A.base PI x₁ else issReal A.base PI x₀)).r.length =
        rBytes ∧
      (tokDNC A PI sk c (bif d then issReal A.base PI x₁ else issReal A.base PI x₀)).s.length =
        uovN ∧
      (tokDNC A PI sk c (bif d then issReal A.base PI x₁ else issReal A.base PI x₀)).nf.length =
        nfBytes := by
  cases d
  · exact tokDNC_wf A PI sk hsk c x₀
  · exact tokDNC_wf A PI sk hsk c x₁

/-- Issuer `c`'s key is found (at the Client's index) in the set of side `side`. -/
def foundNC (c side : Bool) : Bool :=
  ((A.choose side).1.keys[idx (A.choose side).1 (A.pk c)]?).isSome

/-- The symmetric success predicate of the hybrid: the Anchor accepted, and both issuers' keys are
found in both sets. -/
def gSym (x : IssT) : Bool :=
  accNC A PI (issReal A.base PI x).2 &&
    ((foundNC A idx false false && foundNC A idx false true) &&
      (foundNC A idx true false && foundNC A idx true true))

/-- **Unless `derive_preimage` fails**, Client `c`'s success is "accepted, and its key is found in
both sets" (sound index rule). -/
lemma good_eq_of_derive (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) (c : Bool)
    (x : IssT) (hd : (sk c).derivePreimage (tNC A x) ≠ none) :
    goodNC A idx PI sk c (issReal A.base PI x) =
      (accNC A PI (issReal A.base PI x).2 && (foundNC A idx c false && foundNC A idx c true)) := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hd
  have hc := (hsk c (tNC A x) s (length_com _ _ _ _) hs).2
  have htok := tokNC_issReal A PI sk hsk c x
  rw [hs] at htok
  unfold goodNC okNC tokDNC
  cases ha : accNC A PI (issReal A.base PI x).2
  · rw [ha] at htok
    simp [htok]
  · rw [ha] at htok
    simp only [Option.map_some, ite_true] at htok
    simp only [htok, Option.isSome_some, Option.getD_some, Bool.true_and]
    have hok (side : Bool) : redeemOk A.base.ci A.base.cr ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩
        (A.choose side).1 (idx (A.choose side).1 (A.pk c)) = foundNC A idx c side := by
      unfold redeemOk foundNC
      cases hk : (A.choose side).1.keys[idx (A.choose side).1 (A.pk c)]? with
      | none => rfl
      | some k =>
        simp only [Option.isSome_some, decide_eq_true_eq]
        rw [hidx _ _ _ hk]
        exact hc
    rw [hok, hok]

end Honest

/-! ## Simulated redemptions: the view is a function of the refusal bit and the nullifiers -/

section Sim

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer) {CR : Type} (simR : RedeemInstance → CR → Bytes)

/-- A simulated redemption request of side `side` in world `b`: the nullifier `n_{b ^^ side}` and a
simulated proof. -/
def ySimNC (b : Bool) (n₀ n₁ : Bytes) (c : CR) (side : Bool) : Except Error Bytes :=
  .ok ((bif b ^^ side then n₁ else n₀) ++ simR ⟨(A.choose side).1.keys,
    bif b ^^ side then n₁ else n₀, A.base.ci, A.base.cr, (A.choose side).2⟩ c)

/-- The view with simulated redemptions, from the refusal bit `g`, the nullifiers and the simulator
coins. -/
def hviewNC (b g : Bool) (n₀ n₁ : Bytes) (cL cR : CR) : Prop :=
  A.guess (bif g then some (ySimNC A simR b n₀ n₁ cL false, ySimNC A simR b n₀ n₁ cR true)
    else none)

lemma tokNC_nf {c : Bool} {i : PendingToken × Bytes} {t : Token} (h : tokNC A PI sk c i = some t) :
    t.nf = i.1.nf := by
  unfold tokNC at h
  cases hr : respNC A PI sk c i.2 with
  | none => rw [hr] at h; cases h
  | some s =>
    rw [hr, Option.bind_some] at h
    unfold finalizeIssue at h
    split_ifs at h
    cases h
    rfl

lemma tokDNC_nf {c : Bool} {i : PendingToken × Bytes} (h : (tokNC A PI sk c i).isSome = true) :
    (tokDNC A PI sk c i).nf = i.1.nf := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h
  unfold tokDNC
  rw [ht, Option.getD_some]
  exact tokNC_nf A PI sk ht

theorem simNC_iff (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cL cR : CR) :
    viewNC A idx PI sk b i₀ i₁ (redSim A.base simR cL) (redSim A.base simR cR) ↔
      hviewNC A simR b (goodNC A idx PI sk false i₀ && goodNC A idx PI sk true i₁) i₀.1.nf i₁.1.nf
        cL cR := by
  unfold viewNC hviewNC
  cases hg : (goodNC A idx PI sk false i₀ && goodNC A idx PI sk true i₁)
  · rfl
  · refine iff_of_eq (congrArg _ ?_)
    simp only [Bool.and_eq_true, goodNC] at hg
    obtain ⟨⟨⟨t₀, o₀L⟩, o₀R⟩, ⟨⟨t₁, o₁L⟩, o₁R⟩⟩ := hg
    have n₀ := tokDNC_nf A PI sk t₀
    have n₁ := tokDNC_nf A PI sk t₁
    unfold okNC at o₀L o₀R o₁L o₁R
    cases b
    · simp only [Bool.cond_true, Option.some.injEq]
      rw [redSim_of_ok A.base simR _ _ o₀L, redSim_of_ok A.base simR _ _ o₁R]
      simp only [ptNC, ySimNC, Bool.false_xor, Bool.cond_false, Bool.cond_true, n₀, n₁]
    · simp only [Bool.cond_true, Option.some.injEq]
      rw [redSim_of_ok A.base simR _ _ o₁L, redSim_of_ok A.base simR _ _ o₀R]
      simp only [ptNC, ySimNC, Bool.true_xor, Bool.not_false, Bool.not_true, Bool.cond_false,
        Bool.cond_true, n₀, n₁]

/-- The hybrid: the view with the refusal bit `G x₀ && G x₁`. -/
def hybNC (G : IssT → Bool) (b : Bool) (x : (IssT × IssT) × (CR × CR)) : Prop :=
  hviewNC A simR b (G x.1.1 && G x.1.2) (List.ofFn x.1.1.1) (List.ofFn x.1.2.1) x.2.1 x.2.2

/-- Exchange the two Clients' tapes. -/
def swapC : (IssT × IssT) × (CR × CR) ≃ (IssT × IssT) × (CR × CR) where
  toFun x := ((x.1.2, x.1.1), x.2)
  invFun x := ((x.1.2, x.1.1), x.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma ySimNC_swap (n₀ n₁ : Bytes) (c : CR) (side : Bool) :
    ySimNC A simR false n₁ n₀ c side = ySimNC A simR true n₀ n₁ c side := by
  cases side <;> rfl

/-- **A symmetric refusal bit makes the worlds coincide**: the hybrid's two worlds are exchanged by
swapping the Clients' tapes. -/
theorem hybNC_eq [Fintype CR] (G : IssT → Bool) :
    pr _ (hybNC A simR G false) = pr _ (hybNC A simR G true) := by
  rw [← pr_equiv swapC]
  refine pr_congr fun x => ?_
  simp only [hybNC, hviewNC, swapC, Equiv.coe_fn_mk, Bool.and_comm (G x.1.2), ySimNC_swap]

end Sim

/-! ## The hops -/

section Hops

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

variable {TL TR TL' TR' : Type} [Fintype TL] [Fintype TR] [Fintype TL'] [Fintype TR']

theorem hopL_NC [Nonempty TR] (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) {ε : ℝ}
    {gL : TL → RedeemPt → Except Error Bytes} {gL' : TL' → RedeemPt → Except Error Bytes}
    (gR : TR → RedeemPt → Except Error Bytes)
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gL t p) (fun t => gL' t p)) :
    |pr _ (gameNC A idx PI sk b gL gR) - pr _ (gameNC A idx PI sk b gL' gR)| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le' _ _ fun xR =>
    h (ptNC A idx PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) false)
      (tokDNC_wf' A PI sk hsk _ _ _ _).1 (tokDNC_wf' A PI sk hsk _ _ _ _).2.1
      (tokDNC_wf' A PI sk hsk _ _ _ _).2.2
      (fun y => A.guess (bif goodNC A idx PI sk false (issReal A.base PI x.1) &&
        goodNC A idx PI sk true (issReal A.base PI x.2) then
          some (y, gR xR (ptNC A idx PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) true))
        else none))

theorem hopR_NC [Nonempty TL] (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) {ε : ℝ}
    (gL : TL → RedeemPt → Except Error Bytes) {gR : TR → RedeemPt → Except Error Bytes}
    {gR' : TR' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gR t p) (fun t => gR' t p)) :
    |pr _ (gameNC A idx PI sk b gL gR) - pr _ (gameNC A idx PI sk b gL gR')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le _ _ fun xL =>
    h (ptNC A idx PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) true)
      (tokDNC_wf' A PI sk hsk _ _ _ _).1 (tokDNC_wf' A PI sk hsk _ _ _ _).2.1
      (tokDNC_wf' A PI sk hsk _ _ _ _).2.2
      (fun y => A.guess (bif goodNC A idx PI sk false (issReal A.base PI x.1) &&
        goodNC A idx PI sk true (issReal A.base PI x.2) then
          some (gL xL (ptNC A idx PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) false), y)
        else none))

variable {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Both redemption proofs simulated**, `2εR` per world. -/
theorem real_sim_NC (PR : NIZK RedeemInstance) (hsk : ∀ c, (sk c).Correct (A.pk c)) {εR : ℝ}
    (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) (b : Bool) :
    |pr _ (realGameNC A idx PI sk PR b) - pr _ (simGameNC A idx PI sk simR b)| ≤ 2 * εR := by
  have hred := fun p hr hs hn => redeem_close A.base simR PR hεR hR p hr hs hn
  have h1 := hopL_NC A idx PI sk hsk b (redReal A.base PR) hred
  have h2 := hopR_NC A idx PI sk hsk b (redSim A.base simR) hred
  have := abs_sub_le (pr _ (realGameNC A idx PI sk PR b))
    (pr _ (gameNC A idx PI sk b (redSim A.base simR) (redReal A.base PR)))
    (pr _ (simGameNC A idx PI sk simR b))
  unfold realGameNC simGameNC at *
  linarith

lemma pr_fst_fst (P : IssT → Prop) :
    pr ((IssT × IssT) × (CR × CR)) (fun x => P x.1.1) = pr IssT P := by
  rw [pr_prod_fst (fun y : IssT × IssT => P y.1), pr_prod_fst]

lemma pr_fst_snd (P : IssT → Prop) :
    pr ((IssT × IssT) × (CR × CR)) (fun x => P x.1.2) = pr IssT P := by
  rw [pr_prod_fst (fun y : IssT × IssT => P y.2), pr_prod_snd]

lemma pr_derive_none (c : Bool) :
    pr IssT (fun x => (sk c).derivePreimage (tNC A x) = none) = phi A sk c := by
  rw [← pr_equiv (Equiv.prodAssoc (Coins nfBytes) (Coins rBytes) (Coins proveSeedBytes))]
  exact pr_prod_fst (fun y : Coins nfBytes × Coins rBytes =>
    (sk c).derivePreimage (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2)) = none)

/-- **The abort hop**: with simulated redemptions, replacing the refusal bit by the symmetric
`gSym x₀ && gSym x₁` costs at most `φ false + φ true` (identical until a `derive_preimage`
fails). -/
theorem sim_hyb_NC (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) (b : Bool) :
    |pr _ (simGameNC A idx PI sk simR b) - pr _ (hybNC A simR (gSym A idx PI) b)| ≤
      phi A sk false + phi A sk true := by
  have hb := abs_pr_sub_le_of_agree (simGameNC A idx PI sk simR b) (hybNC A simR (gSym A idx PI) b)
    (fun x => (sk false).derivePreimage (tNC A x.1.1) = none ∨
      (sk true).derivePreimage (tNC A x.1.2) = none) fun x hx => by
    simp only [not_or] at hx
    rw [simGameNC, gameNC, simNC_iff, good_eq_of_derive A idx PI sk hsk hidx false _ hx.1,
      good_eq_of_derive A idx PI sk hsk hidx true _ hx.2]
    unfold hybNC gSym
    have e : ∀ a₀ a₁ f₀ f₁ f₂ f₃ : Bool, ((a₀ && (f₀ && f₁)) && (a₁ && (f₂ && f₃))) =
        ((a₀ && ((f₀ && f₁) && (f₂ && f₃))) && (a₁ && ((f₀ && f₁) && (f₂ && f₃)))) := by decide
    rw [e]
    rfl
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  rw [pr_fst_fst (fun x => (sk false).derivePreimage (tNC A x) = none),
    pr_fst_snd (fun x => (sk true).derivePreimage (tNC A x) = none), pr_derive_none,
    pr_derive_none]

end Hops

/-! ## Theorem 4(b) -/

section Main

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer) {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem 4(b) (non-colluding mode), corrected.** For every Moderator that sees no issuance,
with any contexts, keys, Anchor Sets and digests, honest Anchors with signers correct for their
keys, a sound index rule, and any issuance proof system: if the redemption proofs are
`εR`-zero-knowledge, the acceptance probabilities in the two worlds differ by at most
`4εR + 2·(φ false + φ true)`, where `φ c` is the probability that Anchor `c`'s `derive_preimage`
fails on a uniform Client's commitment. No hiding or other assumption on `Com`. -/
theorem anonymityNC (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr _ (realGameNC A idx PI sk PR false) - pr _ (realGameNC A idx PI sk PR true)| ≤
      4 * εR + 2 * (phi A sk false + phi A sk true) := by
  have h0 := real_sim_NC A idx PI sk simR PR hsk hεR hR false
  have h1 := real_sim_NC A idx PI sk simR PR hsk hεR hR true
  have g0 := sim_hyb_NC A idx PI sk simR hsk hidx false
  have g1 := sim_hyb_NC A idx PI sk simR hsk hidx true
  have he := hybNC_eq A simR (gSym A idx PI)
  set p0 := pr _ (realGameNC A idx PI sk PR false)
  set p1 := pr _ (realGameNC A idx PI sk PR true)
  set s0 := pr _ (simGameNC A idx PI sk simR false)
  set s1 := pr _ (simGameNC A idx PI sk simR true)
  set y0 := pr _ (hybNC A simR (gSym A idx PI) false)
  set y1 := pr _ (hybNC A simR (gSym A idx PI) true)
  rw [abs_le] at h0 h1 g0 g1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, g0.1, g0.2, g1.1, g1.2]

/-- **Unlinkability against a non-colluding Moderator**: with one Anchor (equal keys and signers)
and **any** index rule, the two worlds differ by at most `4εR` (no abort term: both Clients'
success events have the same law). -/
theorem unlinkabilityNC (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true) (hs : sk false = sk true)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr _ (realGameNC A idx PI sk PR false) - pr _ (realGameNC A idx PI sk PR true)| ≤ 4 * εR := by
  have hg : goodNC A idx PI sk false = goodNC A idx PI sk true := by
    funext i
    simp only [goodNC, okNC, tokDNC, tokNC, respNC, hpk, hs]
  have hsim (b : Bool) : pr _ (simGameNC A idx PI sk simR b) =
      pr _ (hybNC A simR (fun x => goodNC A idx PI sk true (issReal A.base PI x)) b) :=
    pr_congr fun x => by
      rw [simGameNC, gameNC, simNC_iff, hg]
      rfl
  have h0 := real_sim_NC A idx PI sk simR PR hsk hεR hR false
  have h1 := real_sim_NC A idx PI sk simR PR hsk hεR hR true
  have he := hybNC_eq A simR (fun x => goodNC A idx PI sk true (issReal A.base PI x))
  rw [← hsim, ← hsim] at he
  rw [he] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (simGameNC A idx PI sk simR true)) _
    _ ≤ 2 * εR + 2 * εR := add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εR := by ring

end Main

/-! ## The abort term in the vinegar random-oracle model -/

section Vinegar

/-- A uniformly random function, evaluated at a point, is uniform. -/
lemma pr_eval {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [Nonempty V] (k : K)
    (P : V → Prop) : pr (K → V) (fun f => P (f k)) = pr V P := by
  rw [← pr_equiv (Equiv.funSplitAt k V).symm (fun f => P (f k))]
  have h (a : V × ({j // j ≠ k} → V)) : (Equiv.funSplitAt k V).symm a k = a.1 := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [h]
  exact pr_prod_fst P

/-- `n` independent uniform draws all satisfy `P` with probability `Pr[P]^n`. -/
lemma pr_forall_fin {V : Type*} [Fintype V] (n : ℕ) (P : V → Prop) :
    pr (Fin n → V) (fun v => ∀ i, P (v i)) = pr V P ^ n := by
  classical
  rw [pr_def, pr_def, div_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  congr 1
  have : (univ.filter fun v : Fin n → V => ∀ i, P (v i)) =
      Fintype.piFinset fun _ => univ.filter P := by
    ext v; simp
  rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, Nat.cast_pow]

/-- Bounds for every first coordinate average to a bound. -/
lemma abs_pr_prod_sub_le_avg {α β β' : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype β']
    (P : α × β → Prop) (Q : α × β' → Prop) (f : α → ℝ)
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ f a) :
    |pr (α × β) P - pr (α × β') Q| ≤ (∑ a, f a) / Fintype.card α := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => h a)

/-- The table key of a target: its first `M` bytes. -/
def tkey (t : Bytes) : Coins uovM := fun i => t.getD i 0

/-- **The Anchors' vinegar tables**: for each Anchor and target, the 256 vinegar candidates
`v_{y,0..255}` (pqov's `SHAKE256(y ‖ sk_seed ‖ "pqov-derive-preimage" ‖ ctr)`, as a random
oracle). -/
abbrev VTab (Vin : Type) := Bool → Coins uovM → Fin 256 → Vin

variable {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop)
  (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (skW : VTab Vin → Bool → Signer)

/-- **The vinegar-RO abort bound**: if Anchor `c`'s `derive_preimage` fails on a target only when
all 256 vinegars of its table at the target are bad, then averaged over the table it fails on a
uniform Client's commitment with probability at most `δ_c^256`, `δ_c` the fraction of bad
vinegars. Nothing about `Com` is used: the target is fixed before the table is read. -/
theorem pr_fail_vinegar
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    (c : Bool) :
    pr (VTab Vin × (Coins nfBytes × Coins rBytes)) (fun z =>
        (skW z.1 c).derivePreimage (com (List.ofFn z.2.1) A.base.ci A.base.cr (List.ofFn z.2.2)) =
          none) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
  rw [← pr_equiv (Equiv.prodComm _ _)]
  refine pr_le_of_forall_fst fun y => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  refine (pr_mono fun w hw => hfail w c _ hw).trans (le_of_eq ?_)
  rw [pr_eval c (fun g : Coins uovM → Fin 256 → Vin => ∀ i, ¬ Good c
      (g (tkey (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2))) i)),
    pr_eval (tkey (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2)))
      (fun g : Fin 256 → Vin => ∀ i, ¬ Good c (g i))]
  exact pr_forall_fin 256 (fun v => ¬ Good c v)

variable {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem 4(b) in the vinegar random-oracle model**: the Anchors' signers read independent
uniform vinegar tables and fail only when all 256 vinegars at the target are bad (`hfail`; pqov's
`D_sk`, `security/uov-assumptions.md` §2, with SHAKE256 as a random oracle and no adversary query
at the Anchors' secret seeds). Averaged over the tables, the two worlds differ by at most
`4εR + 2·(δ₀^256 + δ₁^256)`, with `δ_c` the fraction of bad vinegars of Anchor `c`'s key: no
assumption on `Com`. -/
theorem anonymityNC_vinegarRO (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ w c, (skW w c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr (VTab Vin × TapeNC) (fun z => realGameNC A idx PI (skW z.1) PR false z.2) -
        pr (VTab Vin × TapeNC) (fun z => realGameNC A idx PI (skW z.1) PR true z.2)| ≤
      4 * εR + 2 * (pr Vin (fun v => ¬ Good false v) ^ 256 +
        pr Vin (fun v => ¬ Good true v) ^ 256) := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  have hphi (c : Bool) : (∑ w, phi A (skW w) c) / Fintype.card (VTab Vin) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
    have := pr_fail_vinegar Good A skW hfail c
    rw [pr_prod] at this
    exact this
  have hw (w : VTab Vin) : |pr TapeNC (realGameNC A idx PI (skW w) PR false) -
      pr TapeNC (realGameNC A idx PI (skW w) PR true)| ≤
        4 * εR + 2 * (phi A (skW w) false + phi A (skW w) true) :=
    anonymityNC A idx PI (skW w) simR PR hεR (hsk w) hidx hR
  refine (abs_pr_prod_sub_le_avg (fun z : VTab Vin × TapeNC => realGameNC A idx PI (skW z.1) PR false z.2)
    (fun z : VTab Vin × TapeNC => realGameNC A idx PI (skW z.1) PR true z.2)
    (fun w => 4 * εR + 2 * (phi A (skW w) false + phi A (skW w) true)) hw).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hcard.ne', ← Finset.mul_sum, mul_div_assoc, Finset.sum_add_distrib,
    add_div]
  have := hphi false
  have := hphi true
  gcongr

end Vinegar

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- Zero knowledge of the Lean redemption prover (label rows) from its tape hypothesis. -/
theorem zkR_label_rows (Hs : Hashes) (hHs : HashesWF Hs) {εR : ℝ}
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR) :
    ZeroKnowledge RedeemRelW (proveR (leanNIZK Hs CrtGen.tables stR)) (leanSim pR) εR :=
  leanNIZK_zeroKnowledge Hs CrtGen.tables stR pR (fun _ => rfl) rfl RedeemRelW csR zkHypR hHs
    bavcComplete (fun _ _ _ rho => crtComplete Hs _ _ _ rho _ (hlab_of (show 16 ≤ 343 by decide)))
    htR

/-- **Theorem 4(b) with the Lean prover** for redemption (label rows; the issuance proof system
`PI` is arbitrary): `≤ 4εR + 2·(φ false + φ true)`, assuming only the redemption runs' tape
hypothesis and the hash record's output lengths. -/
theorem anonymityNC_label_rows (Hs : Hashes) (hHs : HashesWF Hs) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR) :
    |pr _ (realGameNC A idx PI sk (leanNIZK Hs CrtGen.tables stR) false) -
        pr _ (realGameNC A idx PI sk (leanNIZK Hs CrtGen.tables stR) true)| ≤
      4 * εR + 2 * (phi A sk false + phi A sk true) :=
  anonymityNC A idx PI sk (leanSim pR) _ hεR hsk hidx (zkR_label_rows Hs hHs htR)

/-- **Theorem 4(b) with the Lean prover and SHAKE**: the redemption error is the sum
`ε_rho + ε_grind + ε_bavc + ε_lab` of the hop hypotheses (`HopHyps`, `ZK/Hops.lean`). -/
theorem anonymityNC_label_rows_shake {εrhoR εgrindR εbavcR εlabR : ℝ}
    (hεR : 0 ≤ εrhoR + εgrindR + εbavcR + εlabR) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hidx : IdxSound idx)
    (htR : ∀ x w, RedeemRelW x w →
      HopHyps Hashes.shake CrtGen.tables (stR x) (toBA w) εrhoR εgrindR εbavcR εlabR) :
    |pr _ (realGameNC A idx PI sk (leanNIZK Hashes.shake CrtGen.tables stR) false) -
        pr _ (realGameNC A idx PI sk (leanNIZK Hashes.shake CrtGen.tables stR) true)| ≤
      4 * (εrhoR + εgrindR + εbavcR + εlabR) + 2 * (phi A sk false + phi A sk true) :=
  anonymityNC_label_rows A idx PI sk Hashes.shake hashesWF_shake hεR hsk hidx
    (fun x w h => tapeHyp_of_hops _ _ _ _ hashesWF_shake bavcComplete
      (hlab_of (show 16 ≤ 343 by decide)) (htR x w h))

/-- **Unlinkability against a non-colluding Moderator with the Lean prover**: one Anchor, any
index rule, `≤ 4εR`. -/
theorem unlinkabilityNC_label_rows (Hs : Hashes) (hHs : HashesWF Hs) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true) (hs : sk false = sk true)
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR) :
    |pr _ (realGameNC A idx PI sk (leanNIZK Hs CrtGen.tables stR) false) -
        pr _ (realGameNC A idx PI sk (leanNIZK Hs CrtGen.tables stR) true)| ≤ 4 * εR :=
  unlinkabilityNC A idx PI sk (leanSim pR) _ hεR hsk hpk hs (zkR_label_rows Hs hHs htR)

end Lean

end VoleMole.Privacy.Moussaka
