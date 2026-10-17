import VoleMole.Audit.Nonvacuous

/-!
# Liveness of the privacy games: the honest path reaches the challenge-dependent outputs

`Audit/Nonvacuous.lean` shows that the headline theorems' hypotheses are satisfiable. That does not
rule out a different kind of vacuity: a game whose honest path never produces the
challenge-dependent outputs (a length check that rejects every honest message, a refusal rule that
always fires, a prover that always fails), so that its two worlds are trivially identical. This
happened to Moussaka's non-colluding games (`issueResponse` checked `main`'s request length against
the label-row prover's `7528`-byte proofs; fixed by `Spec.Moussaka.issueResponseLR`). Here, per
protocol, the honest path is shown to run.

## The audit (every privacy game)

Every game of `Privacy/` and `ROM/*Reads*.lean` was traced (the RO, Delta, RA, RAH, RAK, OC, Sh,
seed, NC, Many, P, PH/Lin, Adaptive, Interleave and InterleaveOC variants). Apart from the
non-colluding Moussaka games (already fixed), no honest step consumes the Lean prover's output with
a length or format check: in Moussaka 4(a), Ratatouille and PomFRIT the adversary plays every
Anchor, Issuer and Moderator, the honest Clients check only the adversary's responses
(`P(s) = t`, `Tag`, the 64-bit check), every Lean-prover game uses the label-row layout
(`Layout.labelRows`, `Sizes.labelRows`, `pomfritParams true`), and the further sessions of the
many-session games run the same honest functions. Each game therefore reduces to the two-session
paths below. One latent hazard: `Spec.Moussaka.finalizeRedeem` (the Moderator) checks `main`'s
redemption length `24 + 8751` and would reject every label-row redemption (`9007`-byte proofs,
`finalizeRedeem_leanPR_none`); no game runs an honest Moderator, and
`Spec.Moussaka.finalizeRedeemLR` is the one to use.

## Results

* **A trapdoor key whose signer never fails.** `keyI d`: the key of pqov's key generation with
  `O = 0` (`keyO0`, `P1 = 0`) whose `P2` part makes the system of the vinegar `e₀` the identity
  (`sysMat_keyI`). Its signer `skI d` returns a preimage for every target (`skI_some`,
  `eval_preI`) and is correct (`skI_correct`), so the abort term of the non-colluding games is `0`
  (`phi_skI`; `refused_ncL`: refusal `≤ 2·2⁻¹¹³`).
* **Moussaka 4(a).** With two trapdoor keys as the issuers, §6's rule allows the redemptions on
  every tape, for every issuance prover (`allOk_live`), and the guess sees both redemption
  requests, the left one `nf_b ‖ π` (`view_live`, `realGameRO_live`). The redemption proof has
  `0` or `9007` bytes (`leanPR_length`), and on the game's tables the label-row Moderator running
  the Lean verifier accepts each honest redemption, returning `nf_{b ^^ side}`, except with
  probability `≤ 2⁻¹¹³` (`leanR_complete`, `redeem_accepted_RO`).
* **Ratatouille.** With the trapdoor key's map as the Issuer's key, an honest issuance finalizes
  to a valid token and an honest spend of `0` to a valid change token (`iss_live`, `sp_live`, for
  any primitives, so also the random-oracle slots `issRealR`, `spRealR`); if the provers do not
  abort, both rounds run on every tape, round 1 revealing the nullifier of Client `b₁`'s token and
  round 2 that of Client `b₂`'s current token (`realGame_liveR`). The Lean provers of the
  random-oracle games abort with probability `≤ 2⁻¹¹³` per proof (`leanPIR_some`,
  `leanPSR_some`: their output has the label-row size, so `vecOf` keeps it).
* **PomFRIT.** With the trapdoor key, both sessions finalize on every tape, for every layout and
  prover, and the guess sees both signatures in message order (`realGame_liveP`,
  `realGameRO_liveP`).

Not shown: that the signature revealed in a PomFRIT game passes `pomfritVerify` (the step-2 proof
is the prover's output, non-empty unless grinding fails, but no lemma connects
`pomfritVerify_complete` to `realGameRO`), and a single game-level bound for Ratatouille's four
Lean proofs together (the per-proof bounds and the deterministic `realGame_liveR` are separate).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.Live

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Privacy VoleMole.Privacy.Moussaka

/-! ## The trapdoor key -/

/-- The `P2` part with `S₀ = 1` (`S k i j = P2 i j k`, `sysCoef_keyO0`). -/
def P2I : P2Part := fun i j k => if i.val = 0 ∧ j = k then 1 else 0

/-- **The trapdoor key** with digest `d`. -/
def keyI (d : Bytes) : UOVKey := ⟨d, (keyO0 (fun _ => 0) P2I).map⟩

theorem oilSpace_keyI (d : Bytes) : OilSpace (keyI d) 0 :=
  oilSpace_of_map_eq rfl 0 (oilSpace_keyO0 _ _)

/-- The system of the vinegar `e₀` is the identity. -/
theorem sysMat_keyI (d : Bytes) : sysMat (keyI d) 0 (unitVin 0) = 1 := by
  have e : sysMat (keyI d) 0 (unitVin 0) = sysMat (keyO0 (fun _ => 0) P2I) 0 (unitVin 0) := by
    ext k j
    simp only [sysMat, polar, Matrix.of_apply, keyI]
  rw [e, sysMat_eq_sum]
  ext k j
  simp only [Matrix.of_apply, sysCoef_keyO0, P2I, unitVin]
  rw [Finset.sum_eq_single (0 : Fin 74) (fun b _ hb => by simp [hb])
    (by simp)]
  by_cases h : j = k
  · subst h; simp
  · simp [h, Matrix.one_apply_ne' h]

theorem det_keyI (d : Bytes) : (sysMat (keyI d) 0 (unitVin 0)).det ≠ 0 := by
  rw [sysMat_keyI, Matrix.det_one]; exact one_ne_zero

/-- **The preimage** of `t` under `keyI d` (pqov's attempt with the vinegar `e₀`). -/
noncomputable def preI (d t : Bytes) : Bytes := toBytes (preimageVec (keyI d) 0 (unitVin 0) t)

theorem attempt_keyI (d t : Bytes) : attempt (keyI d) 0 t (unitVin 0) = some (preI d t) := by
  unfold attempt preI
  simp [det_keyI d]

theorem preI_length (d t : Bytes) : (preI d t).length = uovN := toBytes_length _

/-- **`P(preI d t) = t`** for every `45`-byte target. -/
theorem eval_preI (d t : Bytes) (ht : t.length = uovM) : (keyI d).eval (preI d t) = t :=
  (attempt_correct (keyI d) 0 (oilSpace_keyI d) t ht _ _ (attempt_keyI d t)).2

/-- **The trapdoor signer**: one attempt with the vinegar `e₀`. -/
noncomputable def skI (d : Bytes) : Signer := ⟨fun t => attempt (keyI d) 0 t (unitVin 0)⟩

theorem skI_some (d t : Bytes) : (skI d).derivePreimage t = some (preI d t) := attempt_keyI d t

theorem skI_correct (d : Bytes) : (skI d).Correct (keyI d) := fun t s ht h =>
  attempt_correct (keyI d) 0 (oilSpace_keyI d) t ht _ s h

/-- The bytes of a list as coins (`List.ofFn` inverts it at the right length). -/
def coinsOf (n : ℕ) (l : Bytes) : Coins n := fun i => l.getD i 0

theorem ofFn_coinsOf {n : ℕ} {l : Bytes} (h : l.length = n) : List.ofFn (coinsOf n l) = l := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp [coinsOf, List.getElem?_eq_getElem h2]

/-! ## Moussaka 4(a): the redemptions happen and reveal the nullifiers

A colluding adversary with two trapdoor keys (digests `[0]`, `[1]`), answering each Client with the
preimage of the commitment `t` it reads off the request, and choosing the Anchor Set of both keys:
§6's rule allows the redemptions on **every** tape and for **every** issuance prover
(`allOk_live`), and the guess sees the two redemption requests, the left one carrying Client `b`'s
nullifier (`view_live`, `realGameRO_live`). -/

section Moussaka

open VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.ZK.Sim

attribute [local irreducible] com UOVKey.eval preI

/-- The digests of the two Anchors' keys. -/
def digL (c : Bool) : Bytes := [bif c then 1 else 0]

/-- The two issuers' keys. -/
def pkL (c : Bool) : UOVKey := keyI (digL c)

/-- The Anchor Set of both keys. -/
def SL : AnchorSet :=
  ⟨[pkL false, pkL true], ⟨by simp, by simp [maxAnchors], by simp [pkL, keyI, digL]⟩⟩

/-- The response: the preimage of the first `45` bytes of Client `c`'s request. -/
noncomputable def respL (q₀ q₁ : Bytes) (c : Bool) : Coins uovN :=
  coinsOf uovN (preI (digL c) ((bif c then q₁ else q₀).take uovM))

/-- **The live colluding adversary**, with any contexts, digest and guess. -/
noncomputable def mLive (ci cr : Coins ctxBytes) (cd : Bytes)
    (G : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Prop) : Adversary :=
  ⟨ci, cr, pkL, respL, fun _ _ _ => (SL, cd), G⟩

/-- `idxEval` finds a key with the issuer's map, and the Client's check then passes. -/
theorem redeemOk_idxEval (ci cr : Bytes) (t : Token) (S : AnchorSet) (pk : UOVKey)
    (hex : ∃ (i : ℕ) (k : UOVKey), S.keys[i]? = some k ∧ k.eval = pk.eval)
    (ht : pk.eval t.s = com t.nf ci cr t.r) : redeemOk ci cr t S (idxEval S pk) = true := by
  have hs := foundNC_idxEval ⟨fun _ => 0, fun _ => 0, fun _ => pk, fun _ => (S, []), fun _ => True⟩
    false false hex
  unfold foundNC at hs
  simp only at hs
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
  have he := idxEval_sound S pk k hk
  unfold redeemOk
  rw [hk]
  simp only [decide_eq_true_eq]
  rw [he]; exact ht

theorem SL_found (c : Bool) : ∃ (i : ℕ) (k : UOVKey), SL.keys[i]? = some k ∧ k.eval = (pkL c).eval :=
  ⟨bif c then 1 else 0, pkL c, by cases c <;> rfl, rfl⟩

variable {ci cr : Coins ctxBytes} {cd : Bytes}
  {G : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Prop}

/-- `finalize_issue` accepts the trapdoor preimage. -/
theorem finalize_preI (d : Bytes) (p : PendingToken) (ht : p.t.length = uovM) :
    finalizeIssue (keyI d) p (preI d p.t) = some ⟨p.nf, p.r, preI d p.t⟩ := by
  unfold finalizeIssue
  simp [eval_preI d _ ht]

/-- An honest issuance output (any prover). -/
def honI (PI : NIZK IssueInstance) (ci cr : Coins ctxBytes) (x : Coins nfBytes × Coins rBytes)
    (rho : Bytes) : PendingToken × Bytes :=
  issueRequestOf PI (List.ofFn ci) (List.ofFn cr) (List.ofFn x.1) (List.ofFn x.2) rho

/-- The token Client `c` finalizes: its pending token's `(nf, r)` and the preimage. -/
theorem tok_live (PI₀ PI₁ : NIZK IssueInstance) (x₀ x₁ : Coins nfBytes × Coins rBytes)
    (ρ₀ ρ₁ : Bytes) (c : Bool) :
    tok (mLive ci cr cd G) (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) c =
      some ⟨List.ofFn (bif c then x₁ else x₀).1, List.ofFn (bif c then x₁ else x₀).2,
        preI (digL c) (com (List.ofFn (bif c then x₁ else x₀).1) (List.ofFn ci) (List.ofFn cr)
          (List.ofFn (bif c then x₁ else x₀).2))⟩ := by
  have hl : ∀ x : Coins nfBytes × Coins rBytes,
      (com (List.ofFn x.1) (List.ofFn ci) (List.ofFn cr) (List.ofFn x.2)).length = uovM :=
    fun _ => length_com _ _ _ _
  unfold tok
  simp only [mLive, respL]
  cases c <;>
  · simp only [honI, issueRequestOf, Bool.cond_true, Bool.cond_false]
    rw [take_append_eq (hl _), ofFn_coinsOf (preI_length _ _)]
    exact finalize_preI _ _ (hl _)

/-- **§6's rule allows the redemptions** on every tape, for every issuance prover. -/
theorem allOk_live (PI₀ PI₁ : NIZK IssueInstance) (x₀ x₁ : Coins nfBytes × Coins rBytes)
    (ρ₀ ρ₁ : Bytes) :
    allOk (mLive ci cr cd G) idxEval (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) = true := by
  have hok : ∀ c side, okAt (mLive ci cr cd G) idxEval (honI PI₀ ci cr x₀ ρ₀)
      (honI PI₁ ci cr x₁ ρ₁) c side = true := by
    intro c side
    unfold okAt tokD
    rw [tok_live]
    simp only [Option.getD_some, mLive]
    refine redeemOk_idxEval _ _ _ _ _ (SL_found c) ?_
    exact eval_preI _ _ (length_com _ _ _ _)
  unfold allOk
  simp only [tok_live, Option.isSome_some, hok, Bool.and_self]

/-- The nullifier of Client `c`'s token. -/
theorem tokD_nf_live (PI₀ PI₁ : NIZK IssueInstance) (x₀ x₁ : Coins nfBytes × Coins rBytes)
    (ρ₀ ρ₁ : Bytes) (c : Bool) :
    (tokD (mLive ci cr cd G) (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) c).nf =
      List.ofFn (bif c then x₁ else x₀).1 := by
  unfold tokD; rw [tok_live]; rfl

/-- **The redemption requests are `nf ‖ π`**, the nullifier of Client `b ^^ side`. -/
theorem redeem_live (PI₀ PI₁ : NIZK IssueInstance) (PR : NIZK RedeemInstance)
    (x₀ x₁ : Coins nfBytes × Coins rBytes) (ρ₀ ρ₁ ρ : Bytes) (b side : Bool) :
    ∃ π, redeemRequestOf PR (pt (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀)
        (honI PI₁ ci cr x₁ ρ₁) side).tok
      (pt (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) side).anchors
      (pt (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) side).i
      (List.ofFn ci) (List.ofFn cr)
      (pt (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) side).cd ρ =
      .ok (List.ofFn (bif b ^^ side then x₁ else x₀).1 ++ π) := by
  have h := redeemOk_pt_of_allOk idxEval (mLive ci cr cd G) (allOk_live PI₀ PI₁ x₀ x₁ ρ₀ ρ₁) b side
  have hnf := tokD_nf_live (ci := ci) (cr := cr) (cd := cd) (G := G) PI₀ PI₁ x₀ x₁ ρ₀ ρ₁ (b ^^ side)
  set p := pt (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁) side
  have hpn : p.tok.nf = List.ofFn (bif b ^^ side then x₁ else x₀).1 := hnf
  unfold redeemOk at h
  unfold redeemRequestOf
  revert h
  rcases p.anchors.keys[p.i]? with _ | pk
  · intro h; simp at h
  · intro h
    simp only [decide_eq_true_eq] at h
    simp only [mLive, Adversary.ci, Adversary.cr] at h
    simp only [h, ↓reduceIte, hpn]
    exact ⟨_, rfl⟩

/-- **The base game reveals the redemptions** (`Privacy/Moussaka.lean`): with the live adversary,
on every tape, the guess sees both redemption requests, the left one carrying Client `b`'s
nullifier and the right one Client `¬b`'s. -/
theorem view_live (PI₀ PI₁ : NIZK IssueInstance) (PR : NIZK RedeemInstance)
    (x₀ x₁ : Coins nfBytes × Coins rBytes) (ρ₀ ρ₁ : Bytes) (ρL ρR : Coins proveSeedBytes)
    (b : Bool) :
    ∃ πL πR, (view (mLive ci cr cd G) idxEval b (honI PI₀ ci cr x₀ ρ₀) (honI PI₁ ci cr x₁ ρ₁)
        (redReal (mLive ci cr cd G) PR ρL) (redReal (mLive ci cr cd G) PR ρR) ↔
      G (honI PI₀ ci cr x₀ ρ₀).2 (honI PI₁ ci cr x₁ ρ₁).2
        (some (.ok (List.ofFn (bif b then x₁ else x₀).1 ++ πL),
          .ok (List.ofFn (bif b then x₀ else x₁).1 ++ πR)))) := by
  obtain ⟨πL, hL⟩ := redeem_live (ci := ci) (cr := cr) (cd := cd) (G := G) PI₀ PI₁ PR x₀ x₁ ρ₀ ρ₁
    (List.ofFn ρL) b false
  obtain ⟨πR, hR⟩ := redeem_live (ci := ci) (cr := cr) (cd := cd) (G := G) PI₀ PI₁ PR x₀ x₁ ρ₀ ρ₁
    (List.ofFn ρR) b true
  refine ⟨πL, πR, ?_⟩
  unfold view post redReal
  rw [allOk_live]
  simp only [Bool.xor_false, Bool.xor_true, Bool.cond_true] at hL hR ⊢
  simp only [mLive, Adversary.ci, Adversary.cr] at hL hR ⊢
  rw [hL, hR]
  cases b <;> rfl

/-- The live adversary in the random-oracle model, with a guess that also sees the tables. -/
noncomputable def mLiveRO {R : Type} (ci cr : Coins ctxBytes) (cd : Bytes)
    (G : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop) :
    AdversaryRO R :=
  ⟨ci, cr, pkL, respL, fun _ _ _ => (SL, cd), G⟩

/-- **The random-oracle game reveals the redemptions** (`realGameRO`, the game of
`anonymityRO_lean_num` and, through the table-reading, shared-`H₃` and seed reductions, of the
other two-session 4(a) games): for every issuance and redemption prover on the tables (the Lean
provers `leanPI`, `leanPR` included) and every tape, the guess sees both redemption requests, the
left one `nf_b ‖ π_L`. -/
theorem realGameRO_live {R : Type} [Fintype R] [Nonempty R]
    (G : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop)
    (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance) (b : Bool)
    (z : ((TIr × TIr) × (TRr × TRr)) × ShM R) :
    ∃ πL πR, (realGameRO (mLiveRO ci cr cd G) idxEval PI PR b z ↔
      G (honI (nizkAt PI z.1.1.1.2.2 z.2) ci cr z.1.1.1.1 (List.ofFn z.1.1.1.2.1)).2
        (honI (nizkAt PI z.1.1.2.2.2 z.2) ci cr z.1.1.2.1 (List.ofFn z.1.1.2.2.1)).2
        (some (.ok (List.ofFn (bif b then z.1.1.2.1 else z.1.1.1.1).1 ++ πL),
          .ok (List.ofFn (bif b then z.1.1.1.1 else z.1.1.2.1).1 ++ πR)))
        ((z.1.1.1.2.2, z.1.1.2.2.2), (z.1.2.1.2, z.1.2.2.2)) z.2) := by
  obtain ⟨⟨⟨⟨x₀, ρ₀, g₀⟩, ⟨x₁, ρ₁, g₁⟩⟩, ⟨⟨ρL, gL⟩, ⟨ρR, gR⟩⟩⟩, v⟩ := z
  have hb : (mLiveRO (R := R) ci cr cd G).base = mLive ci cr cd (fun _ _ _ => True) := rfl
  obtain ⟨πL, hL⟩ := redeem_live (ci := ci) (cr := cr) (cd := cd) (G := fun _ _ _ => True)
    (nizkAt PI g₀ v) (nizkAt PI g₁ v) (nizkAt PR gL v) x₀ x₁ (List.ofFn ρ₀) (List.ofFn ρ₁)
    (List.ofFn ρL) b false
  obtain ⟨πR, hR⟩ := redeem_live (ci := ci) (cr := cr) (cd := cd) (G := fun _ _ _ => True)
    (nizkAt PI g₀ v) (nizkAt PI g₁ v) (nizkAt PR gR v) x₀ x₁ (List.ofFn ρ₀) (List.ofFn ρ₁)
    (List.ofFn ρR) b true
  refine ⟨πL, πR, ?_⟩
  simp only [Bool.xor_false, Bool.xor_true] at hL hR
  unfold realGameRO gameRO viewRO postRO
  simp only [issRealRO, redRealRO, hb]
  rw [show issueRequestOf (nizkAt PI g₀ v) (mLive ci cr cd (fun _ _ _ => True)).ci
      (mLive ci cr cd (fun _ _ _ => True)).cr (List.ofFn x₀.1) (List.ofFn x₀.2) (List.ofFn ρ₀) =
      honI (nizkAt PI g₀ v) ci cr x₀ (List.ofFn ρ₀) from rfl,
    show issueRequestOf (nizkAt PI g₁ v) (mLive ci cr cd (fun _ _ _ => True)).ci
      (mLive ci cr cd (fun _ _ _ => True)).cr (List.ofFn x₁.1) (List.ofFn x₁.2) (List.ofFn ρ₁) =
      honI (nizkAt PI g₁ v) ci cr x₁ (List.ofFn ρ₁) from rfl]
  rw [allOk_live]
  simp only [mLive, Adversary.ci, Adversary.cr] at hL hR ⊢
  rw [hL, hR]
  simp only [mLiveRO, Bool.cond_true]
  cases b <;> rfl

/-! ### The redemption proofs: their length, `main`'s Moderator, completeness -/

open VoleMole.Verifier VoleMole.Verifier.Bridge

/-- The label-row redemption parameters' proof size. -/
theorem pR_proofBytes : pR.proofBytes = redeemProofBytesLR := by decide

variable {R : Type} [CipherRow R]

/-- **The Lean redemption prover's output has `0` or `9007` bytes.** -/
theorem leanPR_length (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) (s : ShM R) :
    (leanPR w x rho g s).length = 0 ∨ (leanPR w x rho g s).length = redeemProofBytesLR := by
  unfold leanPR
  cases h : realROb pR Hashes.shake (stR x) (toBA w) (toBA rho) g s with
  | error e => left; simp [Except.toOption, length_toL, ByteArray.size]
  | ok b =>
    right
    simp only [Except.toOption, Option.getD_some, length_toL]
    exact (@Verifier.prove_ok_size (icPrg (rowFn s.2.2)) _ _ _ _ _ _ _ h).trans pR_proofBytes

/-- **`main`'s Moderator would reject every label-row redemption request** (`24 + 0` or
`24 + 9007` bytes, never `24 + 8751`): the latent counterpart of `issueResponse_leanPI_malformed`.
No game runs an honest Moderator (in 4(a) and 4(b) the adversary is the Moderator), so no game is
vacuous through it; `finalizeRedeemLR` is the Moderator to use. -/
theorem finalizeRedeem_leanPR_none (VR : NIZK RedeemInstance) (A : AnchorSet) (nf w : Bytes)
    (x : RedeemInstance) (rho : Bytes) (g : Tab3) (s : ShM R) (ci cr cd : Bytes)
    (hnf : nf.length = nfBytes) :
    finalizeRedeem VR A (nf ++ leanPR w x rho g s) ci cr cd = none := by
  have hl : (nf ++ leanPR w x rho g s).length ≠ redeemRequestBytes := by
    rw [List.length_append, hnf]
    rcases leanPR_length w x rho g s with h | h <;> rw [h] <;> decide
  unfold finalizeRedeem
  simp only [hl, ne_eq, not_false_eq_true, ↓reduceIte]

/-- The honest Moderator's Lean verifier of redemptions on the shared tables. -/
noncomputable def leanVR : RedeemInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pR Hashes.shake (stR x) (toBA pf) s).accept

variable [Fintype R] [Nonempty R]

/-- The coins of one redemption proof and the shared tables, rearranged as in `complete_rom`. -/
def cplEquivR : ((VoleMole.ZK.Sim.Bytes 16 × Tab2G pR) × (Tab3 × Tab5F)) × (Blk → R) ≃
    (Coins proveSeedBytes × Tab3) × ShM R where
  toFun z := ((z.1.1.1, z.1.2.1), (z.1.1.2, z.1.2.2, z.2))
  invFun z := (((z.1.1, z.2.1), (z.1.2, z.2.2.1)), z.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Completeness of the Lean redemption proofs** on the shared tables: for every redemption
instance and witness in the relation, the proof has `9007` bytes and the Lean verifier accepts it,
except with probability `≤ 2⁻¹¹³`. -/
theorem leanR_complete (x : RedeemInstance) (w : Bytes) (hw : RedeemRelW x w) :
    pr ((Coins proveSeedBytes × Tab3) × ShM R) (fun z =>
      ¬ ((leanPR w x (List.ofFn z.1.1) z.1.2 z.2).length = redeemProofBytesLR ∧
        leanVR x (leanPR w x (List.ofFn z.1.1) z.1.2 z.2) z.2 = true)) ≤ 1 / 2 ^ 113 := by
  rw [← pr_equiv cplEquivR]
  refine pr_le_of_snd fun E => ?_
  have h := @moussakaRedeem_complete_rom (icPrg (rowFn E)) Hashes.shake hashesWF_shake x w hw
  refine (Privacy.pr_mono fun c hc => ?_).trans h
  intro hex
  obtain ⟨proof, hp, hv⟩ := hex
  apply hc
  have hpf : leanPR w x (List.ofFn (cplEquivR (c, E)).1.1) (cplEquivR (c, E)).1.2
      (cplEquivR (c, E)).2 = toL proof := by
    simp only [leanPR, realROb, toBA_ofFn]
    exact congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty)) hp
  rw [hpf, length_toL]
  refine ⟨(@Verifier.prove_ok_size (icPrg (rowFn E)) _ _ _ _ _ _ _ hp).trans pR_proofBytes, ?_⟩
  have hv' := hv
  rw [@verify_agreeOff_h3 (icPrg (rowFn E)) _ _ (recH_agreeOff_recV Hashes.shake (stR x)
    (toBA w) c.2.1 c.1.2 c.2.2)] at hv'
  unfold leanVR verRO
  rw [Verifier.toBA_toL]
  exact hv'

/-- **The label-row Moderator accepts** a redemption request whose proof has the label-row length
and passes the verifier, returning its nullifier. -/
theorem finalizeRedeemLR_ok (VR : NIZK RedeemInstance) (A : AnchorSet) (nf pf ci cr cd : Bytes)
    (hnf : nf.length = nfBytes) (hl : pf.length = redeemProofBytesLR)
    (hv : VR.verify pf ⟨A.keys, nf, ci, cr, cd⟩ = true) :
    finalizeRedeemLR VR A (nf ++ pf) ci cr cd = some nf := by
  show finalizeRedeemN _ _ _ _ _ _ _ = _
  unfold finalizeRedeemN
  rw [take_append_eq hnf, drop_append_eq hnf]
  simp [hnf, hl, hv]

/-- **The honest redemptions of the 4(a) random-oracle game are accepted** by the label-row
Moderator running the Lean verifier on the same tables, except with probability `≤ 2⁻¹¹³` (over
the redemption's randomness, its `H₃` slice and the shared tables), returning the nullifier of
Client `b ^^ side`. (The redemption point `pt` does not depend on the issuance provers.) -/
theorem redeem_accepted_RO
    (G : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop)
    (PI₀ PI₁ : NIZK IssueInstance) (x₀ x₁ : Coins nfBytes × Coins rBytes) (ρ₀ ρ₁ : Bytes)
    (b side : Bool) :
    pr (TRr × ShM R) (fun z => ¬ ∃ req,
      (redRealRO (mLiveRO ci cr cd G) leanPR z.1).out
          (pt (mLive ci cr cd fun _ _ _ => True) idxEval b (honI PI₀ ci cr x₀ ρ₀)
            (honI PI₁ ci cr x₁ ρ₁) side) z.2 = .ok req ∧
      finalizeRedeemLR ⟨fun _ _ _ => [], fun pf x => leanVR x pf z.2⟩ SL req (List.ofFn ci)
        (List.ofFn cr) cd = some (List.ofFn (bif b ^^ side then x₁ else x₀).1)) ≤ 1 / 2 ^ 113 := by
  set A := mLiveRO (R := R) ci cr cd G
  have hb : A.base = mLive ci cr cd (fun _ _ _ => True) := rfl
  set p := pt (mLive ci cr cd fun _ _ _ => True) idxEval b (honI PI₀ ci cr x₀ ρ₀)
    (honI PI₁ ci cr x₁ ρ₁) side
  have hok := redeemOk_pt_of_allOk idxEval (mLive ci cr cd fun _ _ _ => True)
    (allOk_live PI₀ PI₁ x₀ x₁ ρ₀ ρ₁) b side
  have hnf : p.tok.nf = List.ofFn (bif b ^^ side then x₁ else x₀).1 :=
    tokD_nf_live PI₀ PI₁ x₀ x₁ ρ₀ ρ₁ (b ^^ side)
  have htok : p.tok = ⟨List.ofFn (bif b ^^ side then x₁ else x₀).1,
      List.ofFn (bif b ^^ side then x₁ else x₀).2, preI (digL (b ^^ side))
        (com (List.ofFn (bif b ^^ side then x₁ else x₀).1) (List.ofFn ci) (List.ofFn cr)
          (List.ofFn (bif b ^^ side then x₁ else x₀).2))⟩ := by
    show tokD _ _ _ _ = _
    unfold tokD; rw [tok_live]; rfl
  obtain ⟨hrel, hout, -⟩ := redeem_facts A (PR := leanPR) (simR := fun _ (_ : Unit) => ([] : Bytes)) p
    (by rw [htok]; simp) (by rw [htok]; exact preI_length _ _) (by rw [htok]; simp)
    (by rw [hb]; exact hok)
  refine (Privacy.pr_mono fun z hz => ?_).trans (leanR_complete (R := R) _ _ hrel)
  rintro ⟨hl, hv⟩
  apply hz
  refine ⟨_, hout z.1 z.2, ?_⟩
  rw [← hnf]
  exact finalizeRedeemLR_ok _ _ _ _ _ _ _ (by rw [htok]; simp) hl hv

/-! ### Moussaka 4(b): a signer with abort term `0` -/

/-- **The trapdoor signers never abort**: `φ = 0`. -/
theorem phi_skI (A : AdversaryNC) (c : Bool) : phi A (fun c => skI (digL c)) c = 0 := by
  unfold phi; simp [skI_some, pr_const]

/-- The non-colluding Moderator with both trapdoor keys in its sets. -/
def ncL (ci cr : Coins ctxBytes) (cd : Bytes)
    (G : Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop) :
    AdversaryNCRO R :=
  ⟨ci, cr, pkL, fun _ => (SL, cd), G⟩

omit [CipherRow R] [Fintype R] [Nonempty R] in
theorem found_ncL (G : Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop)
    (c side : Bool) : foundNC (ncL ci cr cd G).nc idxEval c side = true :=
  foundNC_idxEval _ c side (SL_found c)

/-- **With the trapdoor signers the non-colluding game refuses the redemptions with probability
`≤ 2·2⁻¹¹³`** (the game of `anonymityNCRO_lean_num`; its abort term is `0`). -/
theorem refused_ncL (G : Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM R) (fun x =>
      (goodNC (ncL ci cr cd G).nc idxEval (nizkC leanPI leanVI x false) (fun c => skI (digL c)) false
          (issC (ncL ci cr cd G) leanPI leanVI x false) &&
        goodNC (ncL ci cr cd G).nc idxEval (nizkC leanPI leanVI x true) (fun c => skI (digL c)) true
          (issC (ncL ci cr cd G) leanPI leanVI x true)) = false) ≤ 2 / 2 ^ 113 := by
  have h := pr_refused_NCRO_le (ncL ci cr cd G) idxEval (fun c => skI (digL c))
    (fun c => skI_correct (digL c)) idxEval_sound (found_ncL G)
  rw [phi_skI, phi_skI] at h
  linarith

end Moussaka

/-! ## Ratatouille: both rounds run and reveal the challenge nullifiers

A malicious Issuer with the trapdoor key's map, answering each issuance with the preimage of
`Tag(c, 0)` and each spend with refund `0` and the preimage of `Tag(c', 0)`, spending `0` in both
rounds. If the provers do not abort, both rounds run on every tape (`view_liveR`), round 1's
request carrying the nullifier of Client `b₁`'s token; the Lean provers abort with probability
`≤ 2⁻¹¹³` per proof (`leanPIR_some`, `leanPSR_some`). -/

section Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

attribute [local irreducible] preI

/-- The trapdoor key as Ratatouille's public key (its map). -/
def pkR : PublicKey := (keyI []).map

/-- The preimage of a target under `pkR`. -/
noncomputable def preV (y : Target) : Preimage := Vector.ofFn fun i => (preI [] y.toList).getD i 0

lemma preV_toList (y : Target) : (preV y).toList = preI [] y.toList := by
  refine List.ext_getElem (by simp [preI_length]) fun i h1 h2 => ?_
  simp [preV, List.getElem?_eq_getElem h2]

lemma fn_eq_getD (s : Preimage) (i : ℕ) : s.fn i = s.toList.toArray.getD i 0 := by
  unfold Spec.Ratatouille.Bytes.fn
  split_ifs with h
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- `uovEval` is `UOVKey.eval` of the key with that map. -/
theorem uovEval_toList (pk : PublicKey) (s : Preimage) :
    (uovEval pk s).toList = (⟨[], pk⟩ : UOVKey).eval s.toList := by
  unfold uovEval UOVKey.eval
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  have hk : k < 45 := by simpa using h1
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map, List.getElem_finRange]
  congr 2
  funext i
  rw [fn_eq_getD]

/-- **`P(preV y) = y`.** -/
theorem uovEval_preV (y : Target) : uovEval pkR (preV y) = y := by
  apply Vector.toList_inj.1
  rw [uovEval_toList, preV_toList]
  exact eval_preI [] _ (by simp)

/-- The issuance response: the preimage of `Tag(c, 0)` for the request's commitment. -/
noncomputable def rIss {Z : Sizes} (tr : IssTr Z) (c : Bool) : Preimage :=
  match bif c then tr.2 else tr.1 with
  | .ok q => preV (tag (issueReqC q) 0)
  | .error _ => preV (tag (Vector.ofFn fun _ => 0) 0)

/-- The spend response: refund `0` and the preimage of `Tag(c', 0)`. -/
noncomputable def rSp {Z : Sizes} (rq : Except Error (SpendRequest Z)) : SpendResponse :=
  match rq with
  | .ok q => spendResponseBytes 0 (preV (tag (SpendReq.parse q).cNext 0))
  | .error _ => spendResponseBytes 0 (preV (tag (Vector.ofFn fun _ => 0) 0))

/-- **The live Issuer**, with any context, initial balance and guess. -/
noncomputable def rLive {Z : Sizes} (ctx : Context) (tInit : Credits)
    (G : IssTr Z → Option (Except Error (SpendRequest Z) × Option (Except Error (SpendRequest Z))) →
      Prop) : Adversary Z :=
  ⟨pkR, ctx, tInit, rIss, fun _ => 0, fun _ rq => rSp rq, fun _ _ => 0, G⟩

variable {Z : Sizes} {SK : Type} {ctx : Context} {tInit : Credits}
  {G : IssTr Z → Option (Except Error (SpendRequest Z) × Option (Except Error (SpendRequest Z))) →
    Prop}

lemma clientCheck_zero (t : Credits) : clientCheck t 0 0 = some t := by
  simp [clientCheck]

/-- **An honest issuance finalizes** under the live Issuer's response: the token
`(nf, T_init, r, 0, s)`, valid and affording `0`. -/
theorem iss_live (P : Prim Z SK) (ht : tInit ≠ 0) (nf : Nullifier) (r : Opening) (ρ : Rho)
    (π : IssueProof Z) (hπ : P.proveIssue ⟨com nf ctx tInit r, tInit, ctx⟩ ⟨nf, r⟩ ρ = some π) :
    (issOutOf (rLive ctx tInit G) (issueOf P tInit ctx nf r ρ)).req =
        .ok (issueReqBytes (com nf ctx tInit r) π) ∧
      (issOutOf (rLive ctx tInit G) (issueOf P tInit ctx nf r ρ)).fin
        (preV (tag (com nf ctx tInit r) 0)) =
        some ⟨nf, tInit, r, 0, preV (tag (com nf ctx tInit r) 0)⟩ ∧
      (tokIface (rLive ctx tInit G)).ok ⟨nf, tInit, r, 0, preV (tag (com nf ctx tInit r) 0)⟩ 0 =
        true := by
  have hq : issueOf P tInit ctx nf r ρ =
      .ok (⟨nf, r, tInit, com nf ctx tInit r⟩, issueReqBytes (com nf ctx tInit r) π) := by
    simp [issueOf, ht, hπ]
  rw [hq]
  refine ⟨rfl, ?_, ?_⟩
  · simp only [issOutOf, finalizeIssue, rLive, uovEval_preV, ↓reduceIte]
  · simp [tokIface, rLive, TokenS.Valid, uovEval_preV, clientCheck_zero]

/-- **An honest spend of `0` from a valid token** produces the request `nf ‖ 0 ‖ c' ‖ π` and,
under the live Issuer's response, a valid change token. -/
theorem sp_live (P : Prim Z SK) (τ : TokenS) (hτ : (tokIface (rLive ctx tInit G)).ok τ 0 = true)
    (nf' : Nullifier) (r' : Opening) (ρ : Rho) (π : SpendProof Z)
    (hπ : P.proveSpend ⟨pkR, τ.nf, 0, com nf' ctx (τ.t + τ.x) r', ctx⟩
      ⟨τ.t, τ.r, τ.x, τ.s, nf', τ.t + τ.x, r'⟩ ρ = some π) :
    (spOutOf (rLive ctx tInit G) (spendOf P pkR (some τ) 0 ctx nf' r' ρ).2).req =
        .ok (SpendReq.toBytes ⟨τ.nf, 0, com nf' ctx (τ.t + τ.x) r', π⟩) ∧
      ∃ τ', (spOutOf (rLive ctx tInit G) (spendOf P pkR (some τ) 0 ctx nf' r' ρ).2).fin
          (rSp (spOutOf (rLive ctx tInit G) (spendOf P pkR (some τ) 0 ctx nf' r' ρ).2).req) =
          some τ' ∧ τ'.nf = nf' ∧ (tokIface (rLive ctx tInit G)).ok τ' 0 = true := by
  simp only [tokIface, rLive, Bool.and_eq_true, Option.isSome_iff_exists] at hτ
  obtain ⟨hv, t', ht'⟩ := hτ
  have hv := of_decide_eq_true hv
  have ht'' : t' = τ.t + τ.x - 0 := by
    have := ht'; simp only [clientCheck] at this
    split_ifs at this; simp_all
  rw [show τ.t + τ.x - 0 = τ.t + τ.x by simp] at ht''
  subst ht''
  have hq : spendOf P pkR (some τ) 0 ctx nf' r' ρ = (none, .ok (⟨nf', τ.t + τ.x, r',
      com nf' ctx (τ.t + τ.x) r'⟩, SpendReq.toBytes ⟨τ.nf, 0, com nf' ctx (τ.t + τ.x) r', π⟩)) := by
    simp [spendOf, hv, ht', hπ]
  rw [hq]
  refine ⟨rfl, ⟨nf', τ.t + τ.x, r', 0, preV (tag (com nf' ctx (τ.t + τ.x) r') 0)⟩, ?_, rfl, ?_⟩
  · simp only [spOutOf, rSp, parse_toBytes, finalizeSpend, respRefund_mk, respSig_mk, rLive,
      uovEval_preV, ↓reduceIte]
  · show (decide (TokenS.Valid pkR ctx _) && (clientCheck _ _ _).isSome) = true
    simp [TokenS.Valid, uovEval_preV, clientCheck_zero]

/-- **The base game runs both rounds** (`Privacy/Ratatouille.lean`'s `realGame`): with the live
Issuer and provers that do not abort, on every tape the guess sees both spend requests; round 1's
reveals the nullifier of Client `b₁`'s issued token, round 2's that of Client `b₂`'s current token
(its round-1 change token if `b₂ = b₁`, else Client `¬b₁`'s issued token). -/
theorem realGame_liveR (P : Prim Z SK) (ht : tInit ≠ 0)
    (hPI : ∀ u w ρ, (P.proveIssue u w ρ).isSome) (hPS : ∀ u w ρ, (P.proveSpend u w ρ).isSome)
    (b₁ b₂ : Bool) (x : ((Coins 24 × Coins 16 × Coins 16) × (Coins 24 × Coins 16 × Coins 16)) ×
      ((Coins 24 × Coins 16 × Coins 16) × (Coins 24 × Coins 16 × Coins 16))) :
    ∃ tr rq₁ rq₂, (Ratatouille.realGame (rLive ctx tInit G) P b₁ b₂ x ↔ G tr (some (.ok rq₁, some (.ok rq₂)))) ∧
      (SpendReq.parse rq₁).nf = vec (bif b₁ then x.1.2 else x.1.1).1 ∧
      (SpendReq.parse rq₂).nf =
        bif b₂ == b₁ then vec x.2.1.1 else vec (bif b₁ then x.1.1 else x.1.2).1 := by
  obtain ⟨⟨⟨n₀, r₀, ρ₀⟩, ⟨n₁, r₁, ρ₁⟩⟩, ⟨⟨m₁, s₁, σ₁⟩, ⟨m₂, s₂, σ₂⟩⟩⟩ := x
  set A := rLive (Z := Z) ctx tInit G
  obtain ⟨π₀, hπ₀⟩ := Option.isSome_iff_exists.1 (hPI ⟨com (vec n₀) ctx tInit (vec r₀), tInit, ctx⟩
    ⟨vec n₀, vec r₀⟩ (vec ρ₀))
  obtain ⟨π₁, hπ₁⟩ := Option.isSome_iff_exists.1 (hPI ⟨com (vec n₁) ctx tInit (vec r₁), tInit, ctx⟩
    ⟨vec n₁, vec r₁⟩ (vec ρ₁))
  obtain ⟨e₀, f₀, k₀⟩ := iss_live (G := G) P ht (vec n₀) (vec r₀) (vec ρ₀) π₀ hπ₀
  obtain ⟨e₁, f₁, k₁⟩ := iss_live (G := G) P ht (vec n₁) (vec r₁) (vec ρ₁) π₁ hπ₁
  set τ₀ : TokenS := ⟨vec n₀, tInit, vec r₀, 0, preV (tag (com (vec n₀) ctx tInit (vec r₀)) 0)⟩
  set τ₁ : TokenS := ⟨vec n₁, tInit, vec r₁, 0, preV (tag (com (vec n₁) ctx tInit (vec r₁)) 0)⟩
  set tr : IssTr Z := (.ok (issueReqBytes (com (vec n₀) ctx tInit (vec r₀)) π₀),
    .ok (issueReqBytes (com (vec n₁) ctx tInit (vec r₁)) π₁))
  have hr0 : A.respondIss tr false = preV (tag (com (vec n₀) ctx tInit (vec r₀)) 0) := by
    simp only [A, rLive, rIss, tr, Bool.cond_false, issueReqC_mk]
  have hr1 : A.respondIss tr true = preV (tag (com (vec n₁) ctx tInit (vec r₁)) 0) := by
    simp only [A, rLive, rIss, tr, Bool.cond_true, issueReqC_mk]
  -- the spend from a valid token
  have hsp : ∀ (τ : TokenS) (m : Coins 24) (s : Coins 16) (σ : Coins 16),
      (tokIface A).ok τ 0 = true → ∃ π τ',
        (spReal A P (m, s, σ) τ 0).req = .ok (SpendReq.toBytes ⟨τ.nf, 0,
          com (vec m) ctx (τ.t + τ.x) (vec s), π⟩) ∧
        (spReal A P (m, s, σ) τ 0).fin (rSp (spReal A P (m, s, σ) τ 0).req) = some τ' ∧
        τ'.nf = vec m ∧ (tokIface A).ok τ' 0 = true := by
    intro τ m s σ hτ
    obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 (hPS ⟨pkR, τ.nf, 0,
      com (vec m) ctx (τ.t + τ.x) (vec s), ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, vec m, τ.t + τ.x, vec s⟩ (vec σ))
    obtain ⟨hreq, τ', hfin, hnf, hok⟩ := sp_live P τ hτ (vec m) (vec s) (vec σ) π hπ
    exact ⟨π, τ', hreq, hfin, hnf, hok⟩
  have htk : ∀ c, tokD (tokIface A) (some τ₀) (some τ₁) c = bif c then τ₁ else τ₀ := by
    intro c; cases c <;> rfl
  have hokc : ∀ c, (tokIface A).ok (bif c then τ₁ else τ₀) 0 = true := by
    intro c; cases c
    · exact k₀
    · exact k₁
  obtain ⟨π₁', τ', hq₁, hf₁, hn', hk'⟩ := hsp _ m₁ s₁ σ₁ (hokc b₁)
  have hcur : (tokIface A).ok (cur₂ (tokIface A) b₁ b₂ (some τ₀) (some τ₁) (some τ')) 0 = true := by
    unfold cur₂
    cases b₂ == b₁
    · simp only [Bool.cond_false]; rw [htk]; exact hokc _
    · exact hk'
  obtain ⟨π₂', -, hq₂, -, -, -⟩ := hsp _ m₂ s₂ σ₂ hcur
  refine ⟨tr, SpendReq.toBytes ⟨(bif b₁ then τ₁ else τ₀).nf, 0,
      com (vec m₁) ctx ((bif b₁ then τ₁ else τ₀).t + (bif b₁ then τ₁ else τ₀).x) (vec s₁), π₁'⟩,
    SpendReq.toBytes ⟨(cur₂ (tokIface A) b₁ b₂ (some τ₀) (some τ₁) (some τ')).nf, 0,
      com (vec m₂) ctx ((cur₂ (tokIface A) b₁ b₂ (some τ₀) (some τ₁) (some τ')).t +
        (cur₂ (tokIface A) b₁ b₂ (some τ₀) (some τ₁) (some τ')).x) (vec s₂), π₂'⟩, ?_, ?_, ?_⟩
  · unfold Ratatouille.realGame Ratatouille.game Ratatouille.view stage₁ stage₂ stage₃
    have e₀' : (Ratatouille.issReal A P (n₀, r₀, ρ₀)).req = tr.1 := e₀
    have e₁' : (Ratatouille.issReal A P (n₁, r₁, ρ₁)).req = tr.2 := e₁
    rw [e₀', e₁']
    rw [show (Ratatouille.issReal A P (n₀, r₀, ρ₀)).fin (A.respondIss (tr.1, tr.2) false) = some τ₀
        by rw [hr0]; exact f₀,
      show (Ratatouille.issReal A P (n₁, r₁, ρ₁)).fin (A.respondIss (tr.1, tr.2) true) = some τ₁
        by rw [hr1]; exact f₁]
    rw [htk]
    have hd₁ : A.d₁ tr = 0 := rfl
    rw [hd₁, hq₁]
    have hres : A.respond₁ tr (Except.ok (SpendReq.toBytes ⟨(bif b₁ then τ₁ else τ₀).nf, 0,
        com (vec m₁) ctx ((bif b₁ then τ₁ else τ₀).t + (bif b₁ then τ₁ else τ₀).x) (vec s₁), π₁'⟩)) =
        rSp (spReal A P (m₁, s₁, σ₁) (bif b₁ then τ₁ else τ₀) 0).req := by rw [hq₁]; rfl
    rw [hres, hf₁]
    have hd₂ : ∀ rq, A.d₂ tr rq = 0 := fun _ => rfl
    rw [hd₂, hq₂]
    have h1 : ok₁ A (tokIface A) tr (some τ₀) (some τ₁) = true := by
      unfold ok₁; rw [htk, htk, hd₁, hokc false, hokc true]; rfl
    have h2 : ok₂ A (tokIface A) b₁ tr (some τ₀) (some τ₁) (Except.ok (SpendReq.toBytes
        ⟨(bif b₁ then τ₁ else τ₀).nf, 0, com (vec m₁) ctx ((bif b₁ then τ₁ else τ₀).t +
          (bif b₁ then τ₁ else τ₀).x) (vec s₁), π₁'⟩)) (some τ') = true := by
      unfold ok₂; rw [htk, hd₂]; simp only [Option.isSome_some, Option.getD_some, hk', hokc,
        Bool.and_self]
    rw [h1, h2]
    rfl
  · rw [parse_toBytes]; cases b₁ <;> rfl
  · rw [parse_toBytes]
    unfold cur₂
    cases hb : b₂ == b₁
    · simp only [Bool.cond_false]; rw [htk]; cases b₁ <;> rfl
    · simp only [Bool.cond_true, Option.getD_some]; exact hn'

/-! ### The Lean provers of the random-oracle games abort with probability `≤ 2⁻¹¹³` -/

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

/-- A proof the prover returns has the spec's label-row size, so `vecOf` keeps it. -/
lemma vecOf_ok {n : ℕ} {b : ByteArray} (h : b.size = n) : (vecOf n (.ok b)).isSome := by
  simp [vecOf, h]

theorem pI_proofBytes_R : Ratatouille.pI.proofBytes = Sizes.labelRows.issue := by decide
theorem pS_proofBytes_R : Ratatouille.pS.proofBytes = Sizes.labelRows.spend := by decide

variable {R : Type} [CipherRow R] [Fintype R] [Nonempty R]

/-- The coins of one proof and the shared tables, rearranged as in `complete_rom`. -/
def cplEquivRI : ((VoleMole.ZK.Sim.Bytes 16 × Tab2G Ratatouille.pI) × (Tab3 × Tab5F)) × (Blk → R) ≃
    (Coins 16 × Tab3) × ShR R where
  toFun z := ((z.1.1.1, z.1.2.1), (z.1.1.2, z.1.2.2, z.2))
  invFun z := (((z.1.1, z.2.1), (z.1.2, z.2.2.1)), z.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def cplEquivRS : ((VoleMole.ZK.Sim.Bytes 16 × Tab2G Ratatouille.pS) × (Tab3 × Tab5F)) × (Blk → R) ≃
    (Coins 16 × Tab3) × ShR R where
  toFun z := ((z.1.1.1, z.1.2.1), (z.1.1.2, z.1.2.2, z.2))
  invFun z := (((z.1.1, z.2.1), (z.1.2, z.2.2.1)), z.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The Lean issuance prover of the Ratatouille games returns a proof** (the label-row size,
so not `none`) except with probability `≤ 2⁻¹¹³`, for every instance and witness in the
relation. -/
theorem leanPIR_some (x : IssueInstance) (w : IssueWitness) (h : IssueRel x w) :
    pr ((Coins 16 × Tab3) × ShR R) (fun z => leanPIR x w (vec z.1.1) z.1.2 z.2 = none) ≤
      1 / 2 ^ 113 := by
  rw [← pr_equiv cplEquivRI]
  refine pr_le_of_snd fun E => ?_
  have hc := @ratatouilleIssue_complete_rom (icPrg (rowFn E)) Hashes.shake hashesWF_shake x w h
  refine (Privacy.pr_mono fun c hc' => ?_).trans hc
  rintro ⟨proof, hp, -⟩
  have e : leanPIR x w (vec (cplEquivRI (c, E)).1.1) (cplEquivRI (c, E)).1.2 (cplEquivRI (c, E)).2 =
      vecOf _ (.ok proof) := by
    simp only [leanPIR, bOf_vec, realROb]
    exact congrArg (vecOf _) hp
  rw [e] at hc'
  have := vecOf_ok (n := Sizes.labelRows.issue)
    ((@Verifier.prove_ok_size (icPrg (rowFn E)) _ _ _ _ _ _ _ hp).trans pI_proofBytes_R)
  rw [hc'] at this
  exact absurd this (by simp)

/-- **The Lean spend prover returns a proof** except with probability `≤ 2⁻¹¹³`. -/
theorem leanPSR_some (x : SpendInstance) (w : SpendWitness) (h : SpendRel x w) :
    pr ((Coins 16 × Tab3) × ShR R) (fun z => leanPSR x w (vec z.1.1) z.1.2 z.2 = none) ≤
      1 / 2 ^ 113 := by
  rw [← pr_equiv cplEquivRS]
  refine pr_le_of_snd fun E => ?_
  have hc := @ratatouilleSpend_complete_rom (icPrg (rowFn E)) Hashes.shake hashesWF_shake x w h
  refine (Privacy.pr_mono fun c hc' => ?_).trans hc
  rintro ⟨proof, hp, -⟩
  have e : leanPSR x w (vec (cplEquivRS (c, E)).1.1) (cplEquivRS (c, E)).1.2 (cplEquivRS (c, E)).2 =
      vecOf _ (.ok proof) := by
    simp only [leanPSR, bOf_vec, realROb]
    exact congrArg (vecOf _) hp
  rw [e] at hc'
  have := vecOf_ok (n := Sizes.labelRows.spend)
    ((@Verifier.prove_ok_size (icPrg (rowFn E)) _ _ _ _ _ _ _ hp).trans pS_proofBytes_R)
  rw [hc'] at this
  exact absurd this (by simp)

end Ratatouille

/-! ## PomFRIT: both sessions complete and the signatures are revealed

A malicious Issuer with the trapdoor key, answering each request `t` with its preimage: on every
tape, for every proof layout and every two-phase prover, both Clients' `finalize_issue` accept and
the guess sees both signatures, in message order (`realGame_liveP`); in the random-oracle games
(`realGameRO`) the same holds, since their sessions are `realSession Layout.labelRows` with the
Lean prover (`realSession_eq`). -/

section PomFRIT

open VoleMole.Spec.PomFRIT VoleMole.Privacy.PomFRIT

attribute [local irreducible] preI UOVKey.eval

/-- **The live Issuer**: the trapdoor key, any messages and guess, the preimage of each request. -/
noncomputable def pLive (msg : Bool → Bytes) (G : Bytes → Bytes → Option (Bytes × Bytes) → Prop) :
    PomFRIT.Adversary :=
  ⟨keyI [], msg, fun q₀ q₁ c => preI [] (bif c then q₁ else q₀), G⟩

variable {St : Type}

lemma issueRequestOf_fields (L : Layout) (P : Prover St) (pk : UOVKey) (m a b c : Bytes) :
    (PomFRIT.issueRequestOf L P pk m a b c).1.pkDigest = pk.digest ∧
      (PomFRIT.issueRequestOf L P pk m a b c).1.t = (PomFRIT.issueRequestOf L P pk m a b c).2 :=
  ⟨rfl, rfl⟩

/-- A request has `45` bytes. -/
lemma issueRequestOf_length (L : Layout) (P : Prover St) (pk : UOVKey) (m : Bytes)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) :
    (PomFRIT.issueRequestOf L P pk m (List.ofFn x.1) (List.ofFn x.2.1)
      (List.ofFn x.2.2)).2.length = uovM := by
  simp only [PomFRIT.issueRequestOf, length_xorBytes, Layout.length_hashToTarget, List.length_ofFn]
  rfl

/-- **An honest session finalizes** with the trapdoor preimage of its request. -/
theorem session_live (L : Layout) (P : Prover St) (m : Bytes)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) :
    ∃ σ, (realSession L P (keyI []) m x).2 (preI [] (realSession L P (keyI []) m x).1) =
      .ok (some σ) := by
  have hl := issueRequestOf_length L P (keyI []) m x
  obtain ⟨hd, ht⟩ := issueRequestOf_fields L P (keyI []) m (List.ofFn x.1) (List.ofFn x.2.1)
    (List.ofFn x.2.2)
  have he := eval_preI [] _ hl
  rw [← ht] at he
  unfold realSession
  simp only
  unfold Layout.finalizeIssue
  rw [← ht] at hl ⊢
  simp only [preI_length, hd, he, ne_eq, not_true_eq_false, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **The base game reveals both signatures** (`Privacy/PomFRIT.lean`'s `realGame`, any layout and
prover): on every tape the guess sees both requests and `some` pair of signatures, the pair being
the sessions' signatures in message order. -/
theorem realGame_liveP (L : Layout) (P : Prover St) (msg : Bool → Bytes)
    (G : Bytes → Bytes → Option (Bytes × Bytes) → Prop) (b : Bool)
    (x : (Coins proveSeedBytes × Coins refresherBytes × Coins uovM) ×
      (Coins proveSeedBytes × Coins refresherBytes × Coins uovM)) :
    ∃ σ₀ σ₁, (PomFRIT.realGame L (pLive msg G) P b x ↔
      G (realSession L P (keyI []) (msg b) x.1).1 (realSession L P (keyI []) (msg !b) x.2).1
        (some (bif b then (σ₁, σ₀) else (σ₀, σ₁)))) := by
  obtain ⟨σ₀, h₀⟩ := session_live L P (msg b) x.1
  obtain ⟨σ₁, h₁⟩ := session_live L P (msg !b) x.2
  refine ⟨σ₀, σ₁, ?_⟩
  unfold PomFRIT.realGame PomFRIT.game PomFRIT.view
  simp only [pLive, Bool.cond_false, Bool.cond_true]
  rw [h₀, h₁]
  rfl

/-- The live Issuer in the random-oracle model. -/
noncomputable def pLiveRO {R : Type} (msg : Bool → Bytes)
    (G : Bytes → Bytes → Option (Bytes × Bytes) → SlP → ShP R → Prop) : PomFRIT.AdversaryRO R :=
  ⟨keyI [], msg, fun q₀ q₁ c => preI [] (bif c then q₁ else q₀), G⟩

/-- **The random-oracle game reveals both signatures** (`realGameRO`, the game of
`blindnessRO_lean_num` and, through `realGameRA`, `realGameSh`, the many-session and seed
reductions, of the other PomFRIT games): on every tape. -/
theorem realGameRO_liveP {R : Type} [Fintype R] [Nonempty R] [ZK.Sim.CipherRow R] (Hb : Verifier.Hashes)
    (msg : Bool → Bytes) (G : Bytes → Bytes → Option (Bytes × Bytes) → SlP → ShP R → Prop)
    (b : Bool) (z : (XR × XR) × ShP R) :
    ∃ σ₀ σ₁, (PomFRIT.realGameRO Hb (pLiveRO msg G) b z ↔
      G (realSession Layout.labelRows (leanProverRO Hb z.1.1.2 z.2) (keyI []) (msg b) z.1.1.1).1
        (realSession Layout.labelRows (leanProverRO Hb z.1.2.2 z.2) (keyI []) (msg !b) z.1.2.1).1
        (some (bif b then (σ₁, σ₀) else (σ₀, σ₁))) (z.1.1.2, z.1.2.2) z.2) := by
  obtain ⟨σ₀, h₀⟩ := session_live Layout.labelRows (leanProverRO Hb z.1.1.2 z.2) (msg b) z.1.1.1
  obtain ⟨σ₁, h₁⟩ := session_live Layout.labelRows (leanProverRO Hb z.1.2.2 z.2) (msg !b) z.1.2.1
  refine ⟨σ₀, σ₁, ?_⟩
  unfold PomFRIT.realGameRO viewS
  simp only [pLiveRO, Bool.cond_false, Bool.cond_true]
  rw [h₀, h₁]
  rfl

end PomFRIT

end VoleMole.Audit.Live
