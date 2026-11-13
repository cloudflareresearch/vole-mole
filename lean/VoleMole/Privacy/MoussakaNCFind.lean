import VoleMole.Privacy.MoussakaFind
import VoleMole.Privacy.MoussakaNC

/-!
# Theorem 4(b) for `main`'s Client: the index from `find_issuer`

The non-colluding game of `Privacy/MoussakaNC.lean` (the Moderator alone, no issuance seen, honest
Anchors with correct signers, the label-row request length), with `main`'s Client: redemption
runs `Spec.Moussaka.redeemRequest`, which finds the issuer's index itself (`findIssuer`, the last
key that verifies the token) instead of taking it from an index rule. The refusal rule is the
same: both redemptions happen only if both tokens finalized and both are redeemable (`find_issuer`
succeeds) in both sets.

**The Anchor Sets must contain both issuers** (`Contains`: each set has a key with each issuer's
public map). The Moderator chooses the sets before anything is issued, so this is a restriction on
the adversary, which it can check itself. Then a finalized token is redeemable in both sets, and
the refusal bit is again a function of "the Anchor accepted" unless `derive_preimage` fails
(`good_eq_of_derive`); the proof is that of `Privacy/MoussakaNC.lean`. If a set lacks an issuer,
`main`'s Client still redeems whenever **some other key** of the set verifies its hidden preimage
`s`, so the refusal reveals whether `P'(s) = t` for keys `P'` the Moderator chose; no assumption
here bounds that (the index-taking game's `IdxSound` excluded it in the same way). With one Anchor
(`unlinkabilityNC`) the two Clients' refusal events have the same law, and no restriction is
needed.

## Results

* **`anonymityNC`**: `≤ 4εR + 2·(φ false + φ true)` for adversaries with `Contains`.
* **`unlinkabilityNC`**: one Anchor, any Anchor Sets, `≤ 4εR`.
* `anonymityNC_vinegarRO`: `≤ 4εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶)` over random-oracle vinegar tables.
* `anonymityNC_label_rows`, `anonymityNC_label_rows_shake`, `unlinkabilityNC_label_rows`: with the
  Lean redemption prover (label rows).
-/

open Finset

namespace VoleMole.Privacy.MoussakaFind

open VoleMole.Spec VoleMole.Spec.Moussaka
open VoleMole.Privacy.Moussaka (AdversaryNC IssT TapeNC respNC tokNC tokDNC accNC tNC tokNC_issReal
  tokDNC_wf' ySimNC hviewNC hybNC hybNC_eq tokDNC_nf phi pr_fst_fst pr_fst_snd pr_derive_none
  RedeemRelW proveR issReal VTab tkey pr_fail_vinegar abs_pr_prod_sub_le_avg zkR_label_rows)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The game -/

section Game

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- Both Anchor Sets contain a key with each issuer's public map. -/
def Contains : Prop :=
  ∀ c side, ∃ k ∈ (A.choose side).1.keys, k.eval = (A.pk c).eval

/-- Client `c` (issuance output `i`) can redeem in the set of side `side`. -/
def okNC (c side : Bool) (i : PendingToken × Bytes) : Bool :=
  redeemable A.base.ci A.base.cr (tokDNC A PI sk c i) (A.choose side).1

/-- Client `c`'s issuance succeeded and its token is redeemable in both sets. -/
def goodNC (c : Bool) (i : PendingToken × Bytes) : Bool :=
  (tokNC A PI sk c i).isSome && okNC A PI sk c false i && okNC A PI sk c true i

/-- The redemption of side `side` in world `b`: Client `b ^^ side`'s token. -/
def ptNC (b : Bool) (i₀ i₁ : PendingToken × Bytes) (side : Bool) : RedeemPt :=
  ⟨tokDNC A PI sk (b ^^ side) (bif b ^^ side then i₁ else i₀), (A.choose side).1,
    (A.choose side).2⟩

/-- The adversary's view in world `b`: the two redemption requests, or the refusal. -/
def viewNC (b : Bool) (i₀ i₁ : PendingToken × Bytes) (redL redR : RedeemPt → Except Error Bytes) :
    Prop :=
  A.guess (bif goodNC A PI sk false i₀ && goodNC A PI sk true i₁ then
    some (redL (ptNC A PI sk b i₀ i₁ false), redR (ptNC A PI sk b i₀ i₁ true)) else none)

/-- The game with real issuances and the redemption slots drawn by `gL`, `gR`. -/
def gameNC {TL TR : Type} (b : Bool) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (x : (IssT × IssT) × (TL × TR)) : Prop :=
  viewNC A PI sk b (issReal A.base PI x.1.1) (issReal A.base PI x.1.2) (gL x.2.1) (gR x.2.2)

/-- **The real game** in world `b`, with `main`'s Client. -/
def realGameNC (PR : NIZK RedeemInstance) (b : Bool) :=
  gameNC A PI sk b (redReal A.base PR) (redReal A.base PR)

variable {CR : Type} (simR : RedeemInstance → CR → Bytes)

/-- The game with both redemption proofs simulated. -/
def simGameNC (b : Bool) :=
  gameNC A PI sk b (redSim A.base simR) (redSim A.base simR)

end Game

/-! ## The refusal bit -/

section Honest

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- **Unless `derive_preimage` fails**, Client `c`'s success is "the Anchor accepted": its token
verifies under its issuer's key, which both sets contain. -/
lemma good_eq_of_derive (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A) (c : Bool)
    (x : IssT) (hd : (sk c).derivePreimage (tNC A x) ≠ none) :
    goodNC A PI sk c (issReal A.base PI x) = accNC A PI (issReal A.base PI x).2 := by
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
    have hok (side : Bool) : redeemable A.base.ci A.base.cr ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩
        (A.choose side).1 = true := by
      obtain ⟨k, hk, he⟩ := hK c side
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
      exact findIssuer_isSome.2 ⟨i, k, hi, by rw [he]; exact hc⟩
    rw [hok, hok]
    rfl

end Honest

/-! ## Simulated redemptions -/

section Sim

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {CR : Type}
  (simR : RedeemInstance → CR → Bytes)

theorem simNC_iff (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cL cR : CR) :
    viewNC A PI sk b i₀ i₁ (redSim A.base simR cL) (redSim A.base simR cR) ↔
      hviewNC A simR b (goodNC A PI sk false i₀ && goodNC A PI sk true i₁) i₀.1.nf i₁.1.nf
        cL cR := by
  unfold viewNC hviewNC
  cases hg : (goodNC A PI sk false i₀ && goodNC A PI sk true i₁)
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

end Sim

/-! ## The hops -/

section Hops

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

variable {TL TR TL' TR' : Type} [Fintype TL] [Fintype TR] [Fintype TL'] [Fintype TR']

theorem hopL_NC [Nonempty TR] (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) {ε : ℝ}
    {gL : TL → RedeemPt → Except Error Bytes} {gL' : TL' → RedeemPt → Except Error Bytes}
    (gR : TR → RedeemPt → Except Error Bytes)
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gL t p) (fun t => gL' t p)) :
    |pr _ (gameNC A PI sk b gL gR) - pr _ (gameNC A PI sk b gL' gR)| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le' _ _ fun xR =>
    h (ptNC A PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) false)
      (tokDNC_wf' A PI sk hsk _ _ _ _).1 (tokDNC_wf' A PI sk hsk _ _ _ _).2.1
      (tokDNC_wf' A PI sk hsk _ _ _ _).2.2
      (fun y => A.guess (bif goodNC A PI sk false (issReal A.base PI x.1) &&
        goodNC A PI sk true (issReal A.base PI x.2) then
          some (y, gR xR (ptNC A PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) true))
        else none))

theorem hopR_NC [Nonempty TL] (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) {ε : ℝ}
    (gL : TL → RedeemPt → Except Error Bytes) {gR : TR → RedeemPt → Except Error Bytes}
    {gR' : TR' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, p.tok.r.length = rBytes → p.tok.s.length = uovN →
      p.tok.nf.length = nfBytes → Close ε (fun t => gR t p) (fun t => gR' t p)) :
    |pr _ (gameNC A PI sk b gL gR) - pr _ (gameNC A PI sk b gL gR')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le _ _ fun xL =>
    h (ptNC A PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) true)
      (tokDNC_wf' A PI sk hsk _ _ _ _).1 (tokDNC_wf' A PI sk hsk _ _ _ _).2.1
      (tokDNC_wf' A PI sk hsk _ _ _ _).2.2
      (fun y => A.guess (bif goodNC A PI sk false (issReal A.base PI x.1) &&
        goodNC A PI sk true (issReal A.base PI x.2) then
          some (gL xL (ptNC A PI sk b (issReal A.base PI x.1) (issReal A.base PI x.2) false), y)
        else none))

variable {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Both redemption proofs simulated**, `2εR` per world. -/
theorem real_sim_NC (PR : NIZK RedeemInstance) (hsk : ∀ c, (sk c).Correct (A.pk c)) {εR : ℝ}
    (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) (b : Bool) :
    |pr _ (realGameNC A PI sk PR b) - pr _ (simGameNC A PI sk simR b)| ≤ 2 * εR := by
  have hred := fun p hr hs hn => redeem_close A.base simR PR hεR hR p hr hs hn
  have h1 := hopL_NC A PI sk hsk b (redReal A.base PR) hred
  have h2 := hopR_NC A PI sk hsk b (redSim A.base simR) hred
  have := abs_sub_le (pr _ (realGameNC A PI sk PR b))
    (pr _ (gameNC A PI sk b (redSim A.base simR) (redReal A.base PR)))
    (pr _ (simGameNC A PI sk simR b))
  unfold realGameNC simGameNC at *
  linarith

/-- The symmetric refusal bit of the hybrid: the Anchor accepted. -/
def gSym (x : IssT) : Bool := accNC A PI (issReal A.base PI x).2

/-- **The abort hop**: with simulated redemptions, replacing the refusal bit by the symmetric
`gSym x₀ && gSym x₁` costs at most `φ false + φ true`. -/
theorem sim_hyb_NC (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A) (b : Bool) :
    |pr _ (simGameNC A PI sk simR b) - pr _ (hybNC A simR (gSym A PI) b)| ≤
      phi A sk false + phi A sk true := by
  have hb := abs_pr_sub_le_of_agree (simGameNC A PI sk simR b) (hybNC A simR (gSym A PI) b)
    (fun x => (sk false).derivePreimage (tNC A x.1.1) = none ∨
      (sk true).derivePreimage (tNC A x.1.2) = none) fun x hx => by
    simp only [not_or] at hx
    rw [simGameNC, gameNC, simNC_iff, good_eq_of_derive A PI sk hsk hK false _ hx.1,
      good_eq_of_derive A PI sk hsk hK true _ hx.2]
    rfl
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  rw [pr_fst_fst (fun x => (sk false).derivePreimage (tNC A x) = none),
    pr_fst_snd (fun x => (sk true).derivePreimage (tNC A x) = none), pr_derive_none,
    pr_derive_none]

end Hops

/-! ## Theorem 4(b) -/

section Main

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {CR : Type} [Fintype CR]
  [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem 4(b) (non-colluding mode), corrected, for `main`'s Client.** For every Moderator
that sees no issuance and chooses Anchor Sets containing both issuers, with any contexts, keys and
digests, honest Anchors with signers correct for their keys, and any issuance proof system: if the
redemption proofs are `εR`-zero-knowledge, the two worlds differ by at most
`4εR + 2·(φ false + φ true)`. No assumption on `Com`. -/
theorem anonymityNC (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr _ (realGameNC A PI sk PR false) - pr _ (realGameNC A PI sk PR true)| ≤
      4 * εR + 2 * (phi A sk false + phi A sk true) := by
  have h0 := real_sim_NC A PI sk simR PR hsk hεR hR false
  have h1 := real_sim_NC A PI sk simR PR hsk hεR hR true
  have g0 := sim_hyb_NC A PI sk simR hsk hK false
  have g1 := sim_hyb_NC A PI sk simR hsk hK true
  have he := hybNC_eq A simR (gSym A PI)
  set p0 := pr _ (realGameNC A PI sk PR false)
  set p1 := pr _ (realGameNC A PI sk PR true)
  set s0 := pr _ (simGameNC A PI sk simR false)
  set s1 := pr _ (simGameNC A PI sk simR true)
  set y0 := pr _ (hybNC A simR (gSym A PI) false)
  set y1 := pr _ (hybNC A simR (gSym A PI) true)
  rw [abs_le] at h0 h1 g0 g1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, g0.1, g0.2, g1.1, g1.2]

/-- **Unlinkability against a non-colluding Moderator, `main`'s Client**: with one Anchor (equal
keys and signers) and any Anchor Sets, `≤ 4εR`. -/
theorem unlinkabilityNC (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true) (hs : sk false = sk true)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr _ (realGameNC A PI sk PR false) - pr _ (realGameNC A PI sk PR true)| ≤ 4 * εR := by
  have hg : goodNC A PI sk false = goodNC A PI sk true := by
    funext i
    simp only [goodNC, okNC, tokDNC, tokNC, respNC, hpk, hs]
  have hsim (b : Bool) : pr _ (simGameNC A PI sk simR b) =
      pr _ (hybNC A simR (fun x => goodNC A PI sk true (issReal A.base PI x)) b) :=
    pr_congr fun x => by
      rw [simGameNC, gameNC, simNC_iff, hg]
      rfl
  have h0 := real_sim_NC A PI sk simR PR hsk hεR hR false
  have h1 := real_sim_NC A PI sk simR PR hsk hεR hR true
  have he := hybNC_eq A simR (fun x => goodNC A PI sk true (issReal A.base PI x))
  rw [← hsim, ← hsim] at he
  rw [he] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (simGameNC A PI sk simR true)) _
    _ ≤ 2 * εR + 2 * εR := add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εR := by ring

end Main

/-! ## The abort term in the vinegar random-oracle model -/

section Vinegar

variable {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop)
  (A : AdversaryNC) (PI : NIZK IssueInstance) (skW : VTab Vin → Bool → Signer)
  {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem 4(b) in the vinegar random-oracle model, `main`'s Client** (as
`Privacy.Moussaka.anonymityNC_vinegarRO`): `≤ 4εR + 2·(δ₀^256 + δ₁^256)`. -/
theorem anonymityNC_vinegarRO (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ w c, (skW w c).Correct (A.pk c)) (hK : Contains A)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr (VTab Vin × TapeNC) (fun z => realGameNC A PI (skW z.1) PR false z.2) -
        pr (VTab Vin × TapeNC) (fun z => realGameNC A PI (skW z.1) PR true z.2)| ≤
      4 * εR + 2 * (pr Vin (fun v => ¬ Good false v) ^ 256 +
        pr Vin (fun v => ¬ Good true v) ^ 256) := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  have hphi (c : Bool) : (∑ w, phi A (skW w) c) / Fintype.card (VTab Vin) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
    have := pr_fail_vinegar Good A skW hfail c
    rw [pr_prod] at this
    exact this
  have hw (w : VTab Vin) : |pr TapeNC (realGameNC A PI (skW w) PR false) -
      pr TapeNC (realGameNC A PI (skW w) PR true)| ≤
        4 * εR + 2 * (phi A (skW w) false + phi A (skW w) true) :=
    anonymityNC A PI (skW w) simR PR hεR (hsk w) hK hR
  refine (abs_pr_prod_sub_le_avg (fun z : VTab Vin × TapeNC => realGameNC A PI (skW z.1) PR false z.2)
    (fun z : VTab Vin × TapeNC => realGameNC A PI (skW z.1) PR true z.2)
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
open VoleMole.Privacy.Moussaka (leanNIZK leanSim stR pR)

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- **Theorem 4(b) with the Lean prover**, `main`'s Client: `≤ 4εR + 2·(φ false + φ true)`,
assuming only the redemption runs' tape hypothesis and the hash record's output lengths. -/
theorem anonymityNC_label_rows (Hs : Hashes) (hHs : HashesWF Hs) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A)
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR) :
    |pr _ (realGameNC A PI sk (leanNIZK Hs CrtGen.tables stR) false) -
        pr _ (realGameNC A PI sk (leanNIZK Hs CrtGen.tables stR) true)| ≤
      4 * εR + 2 * (phi A sk false + phi A sk true) :=
  anonymityNC A PI sk (leanSim pR) _ hεR hsk hK (zkR_label_rows Hs hHs htR)

/-- **Theorem 4(b) with the Lean prover and SHAKE**, `main`'s Client. -/
theorem anonymityNC_label_rows_shake {εrhoR εgrindR εbavcR εlabR : ℝ}
    (hεR : 0 ≤ εrhoR + εgrindR + εbavcR + εlabR) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hK : Contains A)
    (htR : ∀ x w, RedeemRelW x w →
      HopHyps Hashes.shake CrtGen.tables (stR x) (toBA w) εrhoR εgrindR εbavcR εlabR) :
    |pr _ (realGameNC A PI sk (leanNIZK Hashes.shake CrtGen.tables stR) false) -
        pr _ (realGameNC A PI sk (leanNIZK Hashes.shake CrtGen.tables stR) true)| ≤
      4 * (εrhoR + εgrindR + εbavcR + εlabR) + 2 * (phi A sk false + phi A sk true) :=
  anonymityNC_label_rows A PI sk Hashes.shake hashesWF_shake hεR hsk hK
    (fun x w h => tapeHyp_of_hops _ _ _ _ hashesWF_shake bavcComplete
      (hlab_of (show 16 ≤ 343 by decide)) (htR x w h))

/-- **Unlinkability against a non-colluding Moderator with the Lean prover**, `main`'s Client:
one Anchor, any Anchor Sets, `≤ 4εR`. -/
theorem unlinkabilityNC_label_rows (Hs : Hashes) (hHs : HashesWF Hs) {εR : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true) (hs : sk false = sk true)
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR) :
    |pr _ (realGameNC A PI sk (leanNIZK Hs CrtGen.tables stR) false) -
        pr _ (realGameNC A PI sk (leanNIZK Hs CrtGen.tables stR) true)| ≤ 4 * εR :=
  unlinkabilityNC A PI sk (leanSim pR) _ hεR hsk hpk hs (zkR_label_rows Hs hHs htR)

end Lean

end VoleMole.Privacy.MoussakaFind
