import VoleMole.Privacy.MoussakaUnboundAd
import VoleMole.Privacy.MoussakaNC

/-!
# Unbound Moussaka: issuer hiding and unlinkability against a non-colluding Moderator (Thm U5(b))

Game ANON-U in the non-colluding mode of `lean/docs/security/moussaka-unbound.md` §6, on the
executable spec, with adaptive redemption queries. The adversary is the Moderator alone
(`AdversaryNC`): it chooses `ctx_iss` and the two issuing keys `pk false`, `pk true`, and **sees no
issuance**. Honest Anchors with signers `sk false`, `sk true` (any `Signer` correct for its key)
answer the Clients' requests with `issueResponse` (`unbound_issue_response`,
`src/ihat/ihat.cpp:369-380`: verify the issuance proof, then `derive_preimage`), and the Clients
run `finalizeIssue`. If either token does not finalize, the game ends (the guess sees `none`).
Otherwise the adversary makes `n` redemption queries `(i, w, S, ctx_red, cd)`, each chosen from the
history of earlier queries and answers, answered in world `b` by token `i ⊕ (b ∧ w)` under the
rule of the colluding game (`Privacy/MoussakaUnboundAd.lean`): both tokens redeemable in `S` and
the context rule.

**The Anchor Sets must contain both issuers** (`Contains`: every query's set has a key with each
issuer's public map), as in the base protocol's 4(b) with `find_issuer`
(`Privacy/MoussakaNCFind.lean`). The adversary can check this itself. Without it, whether the
Client's `find_issuer` succeeds in a foreign set depends on the hidden preimage `s`.

## The hops (per world)

1. All `n` redemption proofs simulated (`real_sim_NC`, from `interact_close`): `n·εR`. The issuance
   proofs are never shown, so they are not simulated.
2. With simulated redemptions, the view is a function of the bit "both issuances succeeded", the
   nullifier table `c, ctx ↦ Derive(k_c, ctx)` and the simulator coins (`simNC_iff`). The
   commitments `t_c` appear nowhere.
3. **The abort term** (`sim_hyb_NC`). Replacing the bit by `true` costs `ψ false + ψ true`
   (identical until an honest issuance fails), `ψ c` the probability that Anchor `c`'s
   `unbound_issue_response` returns nothing on a fresh honest request (`psi`).
4. **The PRF hop without the commitments** (`prf_hop_NC`): `Adv^prf_2` of the explicit reductions
   (`prfAdvNC`, `reductionNC`; the note's §3.2, an assumption on Keccak-p[800,12]).
5. The ideal worlds coincide (`idealNC_eq`, `pr_run_swap` of the colluding game).

## Results

* **`anonymityNC`**: `≤ 2n·εR + 2·(ψ false + ψ true) + 2εprf`.
* `psi_le`: `ψ c ≤ κ + φ c`, with `κ` the completeness error of the issuance proof system on honest
  requests (`kappa`) and `φ c` the probability that `derive_preimage` of Anchor `c` fails on
  `UCom(k, ctx_iss, r)` for uniform `(k, r)` (`phiU`); `kappa_eq_zero`: `κ = 0` for a complete
  proof system (`NIZK.Correct`). So **`anonymityNC_complete`**: `≤ 2n·εR + 2·(φ false + φ true) +
  2εprf`.
* **`anonymityNC_vinegarRO`**: `φ` without any assumption on `UCom`. When Anchor `c`'s
  `derive_preimage` fails only if all 256 vinegars it draws for the target from a uniformly random
  table are bad (pqov's `D_sk` with its vinegar hash as a random oracle, as in
  `Privacy/MoussakaNC.lean`), averaged over the tables: `≤ 2n·εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶) + 2εprf`.

## Correction to the note's Theorem U5(b)

The note's proof (b) takes the symmetric refusal bit to be `acc(x₀) ∧ acc(x₁) ∧ K₀ ∧ K₁` (the
Anchors accepted the issuance proofs) and then makes the PRF hop. But `acc(x_c)` is the verifier's
output on a real proof for the key `k_c`, so the PRF reduction, which does not know `k_c`, cannot
compute it. The hop is sound once `acc` is removed too: the abort term becomes `ψ c ≤ κ + φ c`, with
`κ = 0` for a perfectly complete issuance proof system (VOLEitH is).
-/

open Finset

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-- **`unbound_issue_response(sk, request, ctx_iss)`** (`src/ihat/ihat.cpp:369-380`): the Anchor
reads `t` from the request, verifies the issuance proof for `(t, ctx_iss)`, and returns
`derive_preimage(t)`; `none` is `std::nullopt` (invalid proof) or the exception of a failed
`derive_preimage`. The request is a fixed-size array in C++; here it is the Client's own request. -/
def issueResponse (PI : NIZK IssueInstance) (sk : Signer) (req ctxIss : Bytes) : Option Bytes :=
  if PI.verify (req.drop uovM) ⟨req.take uovM, ctxIss⟩ then sk.derivePreimage (req.take uovM)
  else none

/-! ## The game -/

/-- **The non-colluding adversary** (the Moderator): `ctx_iss`, the two issuing keys, each
redemption query from the history so far, and the guess from the history (`none`: a token did not
finalize). It sees no issuance. -/
structure AdversaryNC where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  next : Hist → Query
  guess : Option Hist → Prop

/-- The adversary's contexts and keys as a colluding `Adversary` (for `issReal`, `redReal`,
`redSim`, `ySim`; responses, queries and guess unused). -/
def AdversaryNC.base (A : AdversaryNC) : Adversary 0 :=
  ⟨A.ctxIss, A.pk, fun _ _ _ => 0, fun _ _ => Fin.elim0, fun _ _ _ => True⟩

/-- **Every queried Anchor Set contains both issuers** (a key with each issuer's public map). -/
def Contains (A : AdversaryNC) : Prop :=
  ∀ H c, ∃ k ∈ (A.next H).anchors.keys, k.eval = (A.pk c).eval

/-- One Client's issuance tape: `(nf_key, r, ρ_iss)`. -/
abbrev IssT := Coins nfKeyBytes × Coins rBytes × Coins proveSeedBytes

section Game

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {n : ℕ}

/-- The honest Anchor `c`'s answer to Client `c`'s request on tape `x`. -/
def respNC (c : Bool) (x : IssT) : Option Bytes :=
  issueResponse PI (sk c) (issReal A.base PI x).2 A.base.ci

/-- Client `c`'s token after `finalize_issue` on its Anchor's answer. -/
def tokNC (c : Bool) (x : IssT) : Option Token :=
  (respNC A PI sk c x).bind (finalizeIssue (A.pk c) (issReal A.base PI x).1)

/-- The token, or a well-formed dummy when issuance failed (then nothing is redeemed). -/
def tokDNC (c : Bool) (x : IssT) : Token :=
  (tokNC A PI sk c x).getD
    ⟨List.replicate nfKeyBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- The challenger's rule: both tokens redeemable in the query's set, and the context rule. -/
def validNC (x₀ x₁ : IssT) (H : Hist) (q : Query) : Bool :=
  redeemable A.base.ci (tokDNC A PI sk false x₀) q.anchors &&
    redeemable A.base.ci (tokDNC A PI sk true x₁) q.anchors && ctxOk H q

/-- Query `q` in world `b`. -/
def ptNC (b : Bool) (x₀ x₁ : IssT) (q : Query) : RedeemPt :=
  ⟨tokDNC A PI sk (who b q) (bif who b q then x₁ else x₀), q.anchors, List.ofFn q.ctxRed, q.cd⟩

/-- The game with real issuances and every redemption drawn by `g`. -/
def gameNC {T : Type} (b : Bool) (g : T → RedeemPt → Except Error Bytes)
    (x : (IssT × IssT) × (Fin n → T)) : Prop :=
  A.guess (bif (tokNC A PI sk false x.1.1).isSome && (tokNC A PI sk true x.1.2).isSome then
    some (interact A.next (validNC A PI sk x.1.1 x.1.2) refused
      (List.ofFn fun j q => g (x.2 j) (ptNC A PI sk b x.1.1 x.1.2 q)) [])
    else none)

/-- **The real non-colluding game** in world `b`, with `n` adaptive redemption queries. -/
def realGameNC (n : ℕ) (PR : NIZK RedeemInstance) (b : Bool) :=
  gameNC (n := n) A PI sk b (redReal A.base PR)

variable {CR : Type} (simR : RedeemInstance → CR → Bytes)

/-- The game with every redemption proof simulated. -/
def simGameNC (b : Bool) := gameNC (n := n) A PI sk b (redSim A.base simR)

/-- Honest issuance `c` fails: the Anchor's answer is empty. -/
def failNC (c : Bool) (x : IssT) : Bool := (respNC A PI sk c x).isNone

/-- **The abort probability** `ψ c` of Anchor `c` on a fresh honest request. -/
noncomputable def psi (c : Bool) : ℝ := pr IssT fun x => failNC A PI sk c x = true

end Game

/-! ## The honest Anchor on an honest request -/

section Honest

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- Client `c`'s commitment on tape `x`. -/
def tU (x : IssT) : Bytes := ucom (List.ofFn x.1) A.base.ci (List.ofFn x.2.1)

lemma issReal_take (x : IssT) : (issReal A.base PI x).2.take uovM = tU A x := by
  simp only [issReal, issueRequestOf, tU]
  exact List.take_left' (length_ucom _ _ _)

lemma issReal_drop (x : IssT) :
    (issReal A.base PI x).2.drop uovM =
      PI.prove (encodeIssueWitness (List.ofFn x.1) A.base.ci (List.ofFn x.2.1)) ⟨tU A x, A.base.ci⟩
        (List.ofFn x.2.2) := by
  simp only [issReal, issueRequestOf, tU]
  exact List.drop_left' (length_ucom _ _ _)

lemma issReal_fst (x : IssT) :
    (issReal A.base PI x).1 = ⟨List.ofFn x.1, List.ofFn x.2.1, A.base.ci, tU A x⟩ := rfl

lemma respNC_eq (c : Bool) (x : IssT) :
    respNC A PI sk c x = if PI.verify ((issReal A.base PI x).2.drop uovM) ⟨tU A x, A.base.ci⟩ then
      (sk c).derivePreimage (tU A x) else none := by
  unfold respNC issueResponse
  rw [issReal_take]

/-- **An honest issuance**: the token is `(nf_key, r, s)` for the Anchor's answer `s`. -/
lemma tokNC_eq (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    tokNC A PI sk c x = (respNC A PI sk c x).map fun s => ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩ := by
  unfold tokNC
  cases hr : respNC A PI sk c x with
  | none => rfl
  | some s =>
    have hd : (sk c).derivePreimage (tU A x) = some s := by
      rw [respNC_eq] at hr
      split_ifs at hr
      exact hr
    have hc := (hsk c (tU A x) s (length_ucom _ _ _) hd).2
    simp only [Option.bind_some, Option.map_some, finalizeIssue, issReal_fst, hc, ↓reduceIte]

lemma tokNC_isSome (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    (tokNC A PI sk c x).isSome = !failNC A PI sk c x := by
  rw [tokNC_eq A PI sk hsk]
  unfold failNC
  cases respNC A PI sk c x <;> simp

lemma tokDNC_wf (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    tokWF (tokDNC A PI sk c x) := by
  unfold tokDNC
  rw [tokNC_eq A PI sk hsk]
  cases hr : respNC A PI sk c x with
  | none => exact ⟨List.length_replicate, List.length_replicate, List.length_replicate⟩
  | some s =>
    have hd : (sk c).derivePreimage (tU A x) = some s := by
      rw [respNC_eq] at hr
      split_ifs at hr
      exact hr
    have hs := (hsk c (tU A x) s (length_ucom _ _ _) hd).1
    exact ⟨by simp [nfKeyBytes], by simp [rBytes], hs⟩

/-- A successful honest issuance gives a token that verifies under its issuer's key. -/
lemma tokDNC_of_resp (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) {s : Bytes}
    (hr : respNC A PI sk c x = some s) :
    tokDNC A PI sk c x = ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩ ∧ (A.pk c).eval s = tU A x := by
  refine ⟨?_, ?_⟩
  · unfold tokDNC
    rw [tokNC_eq A PI sk hsk, hr]
    rfl
  · rw [respNC_eq] at hr
    split_ifs at hr
    exact (hsk c (tU A x) s (length_ucom _ _ _) hr).2

/-- With both issuers in the set, a finalized token is redeemable. -/
lemma redeemable_of_contains (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT)
    {s : Bytes} (hr : respNC A PI sk c x = some s) (S : AnchorSet)
    (hS : ∃ k ∈ S.keys, k.eval = (A.pk c).eval) :
    redeemable A.base.ci (tokDNC A PI sk c x) S = true := by
  obtain ⟨ht, he⟩ := tokDNC_of_resp A PI sk hsk c x hr
  obtain ⟨k, hk, hke⟩ := hS
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
  unfold redeemable
  rw [ht]
  exact findIssuer_isSome.2 ⟨i, k, hi, by rw [hke]; exact he⟩

end Honest

/-! ## Simulated redemptions: the view reads the keys only through the nullifier table -/

section Sim

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {n : ℕ} {CR : Type}
  (simR : RedeemInstance → CR → Bytes)

/-- The view with every redemption simulated, from the success bit `g`, the nullifier table and
the simulator coins. -/
def hNC (b g : Bool) (O : Bool → Coins ctxBytes → Bytes) (cs : Fin n → CR) : Prop :=
  A.guess (bif g then
    some (interact A.next (fun H q => ctxOk H q) refused
      (List.ofFn fun j q => ySim A.base simR b O q (cs j)) [])
    else none)

/-- The nullifier table of the two Clients' keys. -/
def keyTab (x₀ x₁ : IssT) : Bool → Coins ctxBytes → Bytes :=
  fun c ctx => bif c then derive (List.ofFn x₁.1) (List.ofFn ctx)
    else derive (List.ofFn x₀.1) (List.ofFn ctx)

lemma redSim_ptNC (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) (x₀ x₁ : IssT) {s₀ s₁ : Bytes}
    (hr₀ : respNC A PI sk false x₀ = some s₀) (hr₁ : respNC A PI sk true x₁ = some s₁) (q : Query)
    (hq : ∀ c, ∃ k ∈ q.anchors.keys, k.eval = (A.pk c).eval) (c : CR) :
    redSim A.base simR c (ptNC A PI sk b x₀ x₁ q) = ySim A.base simR b (keyTab x₀ x₁) q c := by
  unfold redSim ySim ptNC
  cases hw : who b q
  · have h := redeemable_of_contains A PI sk hsk false x₀ hr₀ q.anchors (hq false)
    unfold redeemable at h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
    simp only [Bool.cond_false]
    rw [hi, (tokDNC_of_resp A PI sk hsk false x₀ hr₀).1]
    rfl
  · have h := redeemable_of_contains A PI sk hsk true x₁ hr₁ q.anchors (hq true)
    unfold redeemable at h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
    simp only [Bool.cond_true]
    rw [hi, (tokDNC_of_resp A PI sk hsk true x₁ hr₁).1]
    rfl

/-- **With simulated redemptions the view is a function of the success bit, the nullifier table and
the simulator coins**: the commitments, openings and preimages enter nothing else. -/
theorem simNC_iff (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A) (b : Bool)
    (x : (IssT × IssT) × (Fin n → CR)) :
    simGameNC A PI sk simR b x ↔
      hNC A simR b (!failNC A PI sk false x.1.1 && !failNC A PI sk true x.1.2)
        (keyTab x.1.1 x.1.2) x.2 := by
  unfold simGameNC gameNC hNC
  rw [tokNC_isSome A PI sk hsk, tokNC_isSome A PI sk hsk]
  refine iff_of_eq (congrArg _ ?_)
  cases hC : (!failNC A PI sk false x.1.1 && !failNC A PI sk true x.1.2)
  · simp only [Bool.cond_false]
  · simp only [Bool.and_eq_true, Bool.not_eq_true', failNC, Option.isNone_eq_false_iff,
      Option.isSome_iff_exists] at hC
    obtain ⟨⟨s₀, hr₀⟩, ⟨s₁, hr₁⟩⟩ := hC
    simp only [Bool.cond_true, Option.some.injEq]
    rw [interact_congr_valid A.next _ refused (valid' := fun H q => ctxOk H q) (fun H => by
      unfold validNC
      rw [redeemable_of_contains A PI sk hsk false _ hr₀ _ (hK H false),
        redeemable_of_contains A PI sk hsk true _ hr₁ _ (hK H true)]
      rfl)]
    exact interact_congr_of A.next _ refused
      (fun q => ∀ c, ∃ k ∈ q.anchors.keys, k.eval = (A.pk c).eval) _ _
      (fun j q hq => redSim_ptNC A PI sk simR hsk b x.1.1 x.1.2 hr₀ hr₁ q hq (x.2 j)) _
      fun H' _ _ _ => hK H'

end Sim

/-! ## The hops -/

section Hops

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {n : ℕ} {CR : Type}
  [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **All `n` adaptively chosen redemption proofs simulated**: `n·εR` per world. -/
theorem real_sim_NC (PR : NIZK RedeemInstance) (hsk : ∀ c, (sk c).Correct (A.pk c)) {εR : ℝ}
    (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) (b : Bool) :
    |pr _ (realGameNC A PI sk n PR b) - pr _ (simGameNC (n := n) A PI sk simR b)| ≤ n * εR :=
  abs_pr_prod_sub_le _ _ fun x =>
    interact_close A.next (validNC A PI sk x.1 x.2) refused
      (fun t q => redReal A.base PR t (ptNC A PI sk b x.1 x.2 q))
      (fun t q => redSim A.base simR t (ptNC A PI sk b x.1 x.2 q))
      (fun q => redeem_close A.base simR PR hεR hR _ (tokDNC_wf A PI sk hsk _ _)
        (by simp [ptNC, ctxBytes])) n []
      (fun Hs => A.guess (bif (tokNC A PI sk false x.1).isSome && (tokNC A PI sk true x.2).isSome
        then some Hs else none))

lemma pr_fst_fst (P : IssT → Prop) :
    pr ((IssT × IssT) × (Fin n → CR)) (fun x => P x.1.1) = pr IssT P := by
  rw [pr_prod_fst (fun y : IssT × IssT => P y.1), pr_prod_fst]

lemma pr_fst_snd (P : IssT → Prop) :
    pr ((IssT × IssT) × (Fin n → CR)) (fun x => P x.1.2) = pr IssT P := by
  rw [pr_prod_fst (fun y : IssT × IssT => P y.2), pr_prod_snd]

/-- The hybrid: both issuances counted as successful. -/
def hybNC (b : Bool) (x : (IssT × IssT) × (Fin n → CR)) : Prop :=
  hNC A simR b true (keyTab x.1.1 x.1.2) x.2

/-- **The abort hop**: replacing the success bit by `true` costs `ψ false + ψ true` (identical
until an honest issuance fails). -/
theorem sim_hyb_NC (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A) (b : Bool) :
    |pr _ (simGameNC (n := n) A PI sk simR b) - pr _ (hybNC (n := n) A simR b)| ≤
      psi A PI sk false + psi A PI sk true := by
  have hb := abs_pr_sub_le_of_agree (simGameNC (n := n) A PI sk simR b) (hybNC A simR b)
    (fun x => failNC A PI sk false x.1.1 = true ∨ failNC A PI sk true x.1.2 = true) fun x hx => by
      simp only [not_or, Bool.not_eq_true] at hx
      rw [simNC_iff A PI sk simR hsk hK, hx.1, hx.2]
      rfl
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  rw [pr_fst_fst (fun x => failNC A PI sk false x = true),
    pr_fst_snd (fun x => failNC A PI sk true x = true)]
  rfl

/-- The two Clients' keys. -/
abbrev KTape := Coins nfKeyBytes × Coins nfKeyBytes

/-- The rest of the tape: openings, issuance prover seeds, redemption simulator coins. -/
abbrev RestNC (n : ℕ) (CR : Type) :=
  ((Coins rBytes × Coins proveSeedBytes) × (Coins rBytes × Coins proveSeedBytes)) × (Fin n → CR)

/-- The table `c, ctx ↦ Derive(k_c, ctx)`. -/
def keyTable (k : KTape) : Bool → Coins ctxBytes → Bytes :=
  fun c ctx => bif c then derive (List.ofFn k.2) (List.ofFn ctx) else derive (List.ofFn k.1) (List.ofFn ctx)

/-- **The PRF advantage without the commitments** (`Adv^prf_2`, the note's §3.2): distinguish the
table `c, ctx ↦ Derive(k_c, ctx)` for uniform keys from a uniform table. -/
noncomputable def prfAdvNC (D : (Bool → Coins ctxBytes → Bytes) → Prop) : ℝ :=
  |pr KTape (fun k => D (keyTable k)) - pr Table (fun F => D (tbl F))|

/-- **The reduction to the PRF**: the adversary, with the simulator coins fixed, on the table it is
given (read adaptively). -/
def reductionNC (b : Bool) (cs : Fin n → CR) (O : Bool → Coins ctxBytes → Bytes) : Prop :=
  hNC A simR b true O cs

/-- The game after the PRF hop. -/
def idealNC (b : Bool) (y : Table × RestNC n CR) : Prop := reductionNC A simR b y.2.2 (tbl y.1)

/-- Split the tape into the keys and the rest. -/
def splitNC : (IssT × IssT) × (Fin n → CR) ≃ KTape × RestNC n CR where
  toFun x := ((x.1.1.1, x.1.2.1), ((x.1.1.2, x.1.2.2), x.2))
  invFun y := (((y.1.1, y.2.1.1), (y.1.2, y.2.1.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem prf_hop_NC (b : Bool) {εprf : ℝ}
    (hprf : ∀ cs : Fin n → CR, prfAdvNC (reductionNC A simR b cs) ≤ εprf) :
    |pr _ (hybNC (n := n) A simR b) - pr _ (idealNC (n := n) A simR b)| ≤ εprf := by
  have e : pr _ (hybNC (n := n) A simR b) =
      pr (KTape × RestNC n CR) (fun y => reductionNC A simR b y.2.2 (keyTable y.1)) := by
    rw [← pr_equiv splitNC.symm (hybNC A simR b)]
    rfl
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun r => hprf r.2

omit [Nonempty CR] in
/-- **After the PRF hop the worlds coincide.** -/
theorem idealNC_eq :
    pr _ (idealNC (n := n) A simR false) = pr _ (idealNC (n := n) A simR true) :=
  pr_run_swap simR A.base (fun _ => A.next) (fun _ H q => ctxOk H q) (fun _ _ _ h => h)
    (fun z : RestNC n CR => z.2) (fun _ Hs => A.guess (bif true then some Hs else none))

end Hops

/-! ## Theorem U5(b) -/

section Main

variable (A : AdversaryNC) (PI : NIZK IssueInstance) (sk : Bool → Signer) {n : ℕ} {CR : Type}
  [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem U5(b), corrected.** For every Moderator that sees no issuance and chooses its `n`
redemption queries adaptively, with Anchor Sets that contain both issuers, honest Anchors whose
signers are correct for their keys, and any issuance proof system: if the redemption proofs are
`εR`-zero-knowledge and every reduction `reductionNC A simR b cs` has PRF advantage (without the
commitments) at most `εprf`, the acceptance probabilities in the two worlds differ by at most
`2n·εR + 2·(ψ false + ψ true) + 2εprf`, `ψ c` the probability that Anchor `c`'s
`unbound_issue_response` fails on a fresh honest request. -/
theorem anonymityNC (PR : NIZK RedeemInstance) {εR εprf : ℝ} (hεR : 0 ≤ εR)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hprf : ∀ b (cs : Fin n → CR), prfAdvNC (reductionNC A simR b cs) ≤ εprf) :
    |pr _ (realGameNC A PI sk n PR false) - pr _ (realGameNC A PI sk n PR true)| ≤
      2 * n * εR + 2 * (psi A PI sk false + psi A PI sk true) + 2 * εprf := by
  have hw (b : Bool) : |pr _ (realGameNC A PI sk n PR b) - pr _ (idealNC (n := n) A simR b)| ≤
      n * εR + (psi A PI sk false + psi A PI sk true) + εprf := by
    have h1 := real_sim_NC (n := n) A PI sk simR PR hsk hεR hR b
    have h2 := sim_hyb_NC (n := n) A PI sk simR hsk hK b
    have h3 := prf_hop_NC A simR b (hprf b)
    have := abs_sub_le (pr _ (realGameNC A PI sk n PR b)) (pr _ (simGameNC (n := n) A PI sk simR b))
      (pr _ (idealNC (n := n) A simR b))
    have := abs_sub_le (pr _ (simGameNC (n := n) A PI sk simR b)) (pr _ (hybNC (n := n) A simR b))
      (pr _ (idealNC (n := n) A simR b))
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealNC_eq] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (idealNC (n := n) A simR true)) _
    _ ≤ (n * εR + (psi A PI sk false + psi A PI sk true) + εprf) +
        (n * εR + (psi A PI sk false + psi A PI sk true) + εprf) :=
        add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = _ := by ring

/-! ## The abort term -/

/-- **The completeness error** of the issuance proof system on honest requests. -/
noncomputable def kappa : ℝ :=
  pr IssT fun x => PI.verify ((issReal A.base PI x).2.drop uovM) ⟨tU A x, A.base.ci⟩ = false

/-- **The `derive_preimage` failure probability** `φ c` of Anchor `c` on `UCom(k, ctx_iss, r)` for
uniform `(k, r)`. -/
noncomputable def phiU (c : Bool) : ℝ :=
  pr (Coins nfKeyBytes × Coins rBytes) fun y =>
    (sk c).derivePreimage (ucom (List.ofFn y.1) A.base.ci (List.ofFn y.2)) = none

lemma pr_derive_none (c : Bool) :
    pr IssT (fun x => (sk c).derivePreimage (tU A x) = none) = phiU A sk c := by
  rw [← pr_equiv (Equiv.prodAssoc (Coins nfKeyBytes) (Coins rBytes) (Coins proveSeedBytes))]
  exact pr_prod_fst (fun y : Coins nfKeyBytes × Coins rBytes =>
    (sk c).derivePreimage (ucom (List.ofFn y.1) A.base.ci (List.ofFn y.2)) = none)

/-- `ψ c ≤ κ + φ c`: an honest issuance fails only if the proof is rejected or `derive_preimage`
fails. -/
theorem psi_le (c : Bool) : psi A PI sk c ≤ kappa A PI + phiU A sk c := by
  unfold psi
  refine (pr_mono fun x hx => ?_).trans ((pr_or_le
    (fun x => PI.verify ((issReal A.base PI x).2.drop uovM) ⟨tU A x, A.base.ci⟩ = false)
    (fun x => (sk c).derivePreimage (tU A x) = none)).trans (le_of_eq ?_))
  · show _ ∨ _
    simp only [failNC, Option.isNone_iff_eq_none] at hx
    rw [respNC_eq] at hx
    split_ifs at hx with h
    · exact Or.inr hx
    · exact Or.inl (by simpa using h)
  · rw [pr_derive_none]
    rfl

/-- **A complete issuance proof system has `κ = 0`.** -/
theorem kappa_eq_zero (hPI : PI.Correct IssueRel issueProofBytes) : kappa A PI = 0 := by
  unfold kappa
  rw [pr_congr (Q := fun _ => False) fun x => ?_, pr_const]
  · simp
  · rw [issReal_drop]
    have hrel : IssueRel ⟨tU A x, A.base.ci⟩
        (encodeIssueWitness (List.ofFn x.1) A.base.ci (List.ofFn x.2.1)) :=
      ⟨_, _, List.length_ofFn, List.length_ofFn, rfl, rfl⟩
    rw [(hPI _ _ _ hrel List.length_ofFn).2]
    simp

/-- **Theorem U5(b) with a complete issuance proof system**: the abort term is `derive_preimage`'s
failure probability only. -/
theorem anonymityNC_complete (PR : NIZK RedeemInstance) {εR εprf : ℝ} (hεR : 0 ≤ εR)
    (hPI : PI.Correct IssueRel issueProofBytes)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hprf : ∀ b (cs : Fin n → CR), prfAdvNC (reductionNC A simR b cs) ≤ εprf) :
    |pr _ (realGameNC A PI sk n PR false) - pr _ (realGameNC A PI sk n PR true)| ≤
      2 * n * εR + 2 * (phiU A sk false + phiU A sk true) + 2 * εprf := by
  have h := anonymityNC A PI sk simR PR hεR hsk hK hR hprf
  have h0 := psi_le A PI sk false
  have h1 := psi_le A PI sk true
  rw [kappa_eq_zero A PI hPI] at h0 h1
  linarith

end Main

/-! ## The abort term in the vinegar random-oracle model -/

section Vinegar

open VoleMole.Privacy.Moussaka (VTab tkey pr_eval pr_forall_fin abs_pr_prod_sub_le_avg)

variable {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop)
  (A : AdversaryNC) (PI : NIZK IssueInstance) (skW : VTab Vin → Bool → Signer)

/-- **The vinegar-RO abort bound for `UCom`**: if Anchor `c`'s `derive_preimage` fails on a target
only when all 256 vinegars of its table at the target are bad, then averaged over the table it fails
on `UCom(k, ctx_iss, r)` for uniform `(k, r)` with probability at most `δ_c^256`. Nothing about
`UCom` is used. -/
theorem pr_fail_vinegarU
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    (c : Bool) :
    pr (VTab Vin × (Coins nfKeyBytes × Coins rBytes)) (fun z =>
        (skW z.1 c).derivePreimage (ucom (List.ofFn z.2.1) A.base.ci (List.ofFn z.2.2)) = none) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
  rw [← pr_equiv (Equiv.prodComm _ _)]
  refine pr_le_of_forall_fst fun y => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  refine (pr_mono fun w hw => hfail w c _ hw).trans (le_of_eq ?_)
  rw [pr_eval c (fun g : Coins uovM → Fin 256 → Vin => ∀ i, ¬ Good c
      (g (tkey (ucom (List.ofFn y.1) A.base.ci (List.ofFn y.2))) i)),
    pr_eval (tkey (ucom (List.ofFn y.1) A.base.ci (List.ofFn y.2)))
      (fun g : Fin 256 → Vin => ∀ i, ¬ Good c (g i))]
  exact pr_forall_fin 256 (fun v => ¬ Good c v)

variable {n : ℕ} {CR : Type} [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes)

/-- **Theorem U5(b) in the vinegar random-oracle model**: the Anchors' signers read independent
uniform vinegar tables and fail only when all 256 vinegars at the target are bad (`hfail`). Averaged
over the tables, the two worlds differ by at most `2n·εR + 2·(δ₀^256 + δ₁^256) + 2εprf`, with `δ_c`
the fraction of bad vinegars of Anchor `c`'s key, for a complete issuance proof system. The PRF
hypothesis is for every table (the reductions do not depend on it: the Moderator never sees an
issuance). -/
theorem anonymityNC_vinegarRO (PR : NIZK RedeemInstance) {εR εprf : ℝ} (hεR : 0 ≤ εR)
    (hPI : PI.Correct IssueRel issueProofBytes)
    (hsk : ∀ w c, (skW w c).Correct (A.pk c)) (hK : Contains A)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hprf : ∀ b (cs : Fin n → CR), prfAdvNC (reductionNC A simR b cs) ≤ εprf) :
    |pr (VTab Vin × ((IssT × IssT) × (Fin n → Coins proveSeedBytes)))
          (fun z => realGameNC A PI (skW z.1) n PR false z.2) -
        pr (VTab Vin × ((IssT × IssT) × (Fin n → Coins proveSeedBytes)))
          (fun z => realGameNC A PI (skW z.1) n PR true z.2)| ≤
      2 * n * εR + 2 * (pr Vin (fun v => ¬ Good false v) ^ 256 +
        pr Vin (fun v => ¬ Good true v) ^ 256) + 2 * εprf := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  have hphi (c : Bool) : (∑ w, phiU A (skW w) c) / Fintype.card (VTab Vin) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
    have := pr_fail_vinegarU Good A skW hfail c
    rw [pr_prod] at this
    exact this
  have hw (w : VTab Vin) : |pr _ (realGameNC A PI (skW w) n PR false) -
      pr _ (realGameNC A PI (skW w) n PR true)| ≤
        2 * n * εR + 2 * (phiU A (skW w) false + phiU A (skW w) true) + 2 * εprf :=
    anonymityNC_complete A PI (skW w) simR PR hεR hPI (hsk w) hK hR hprf
  refine (abs_pr_prod_sub_le_avg
    (fun z : VTab Vin × ((IssT × IssT) × (Fin n → Coins proveSeedBytes)) =>
      realGameNC A PI (skW z.1) n PR false z.2)
    (fun z : VTab Vin × ((IssT × IssT) × (Fin n → Coins proveSeedBytes)) =>
      realGameNC A PI (skW z.1) n PR true z.2)
    (fun w => 2 * n * εR + 2 * (phiU A (skW w) false + phiU A (skW w) true) + 2 * εprf) hw).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, add_div, add_div,
    mul_div_cancel_left₀ _ hcard.ne', mul_div_cancel_left₀ _ hcard.ne', ← Finset.mul_sum,
    mul_div_assoc, Finset.sum_add_distrib, add_div]
  have := hphi false
  have := hphi true
  gcongr

end Vinegar

end VoleMole.Privacy.MoussakaUnbound
