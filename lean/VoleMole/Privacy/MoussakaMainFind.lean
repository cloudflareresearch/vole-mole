import VoleMole.Privacy.MoussakaNCMain
import VoleMole.Privacy.MoussakaNCFind

/-!
# Moussaka 4(a) and 4(b') on `main` for `main`'s Client (`find_issuer`)

The `main` games (`Privacy/MoussakaMain*.lean`, `Privacy/MoussakaNCMain.lean`) are stated for an
index rule that may read the token (`Rule`, `Privacy/MoussakaRule.lean`). `main`'s Client finds
its issuer's index itself (`Spec.Moussaka.redeemRequest`, `find_issuer`: the last key of the set
that verifies `(s, t)`); that is the rule `findIdx`. This file instantiates the theorems at it.

## `findIdx` is `main`'s Client in the `main` games

The `main` games model a redemption by `redOut` (the request) and `redStmt` (the statement and
witness the prover gets). At a point whose index is `findIdx` (`ptM`, `ptNM` with `findIdx`):

* `redOut_findIdx`: the request is `find_issuer`'s: `invalidToken` if no key of the set verifies
  the token, and `nf ‖ π` otherwise (`MoussakaFind.redeemRequestOf`);
* `redStmt_findIdx`: the witness is the one `redeemRequest` proves, at the index `find_issuer`
  returns.

So `realH A findIdx` and `realNCM A findIdx PI sk` are the games of `main`'s Client, as
`Spec.Moussaka.redeemRequest_eq_at` and `redeemRequest_eq_findIdx` relate the spec's two steps.

## Results

* **`anonymity_main_sharedAll_find`**: Theorem 4(a) on `main`, all tables shared, with `main`'s
  Client: the bound of `anonymity_main_sharedAll`, unchanged. The (PU) predictors are those of
  `anonymity_main_sharedAll` at `findIdx`: they compute the simulated view, and hence the rule's
  index, from the commitments, as the rule reads the opening only through `t`.
* **`anonymityNC_main_find`**: Theorem 4(b') on `main`, all tables shared, with `main`'s Client,
  for Moderators whose Anchor Sets contain both issuers' maps (`MoussakaFind.Contains`, as in
  `MoussakaFind.anonymityNC`): the bound of `anonymityNC_main`. Without that restriction the
  refusal bit can reveal whether a foreign key of the Moderator's choice verifies a Client's hidden
  preimage (`Privacy/MoussakaNCFind.lean`).
* **`unlinkabilityNC_main_find`**: one Anchor, any Anchor Sets, no abort term.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## `findIdx` in the `main` games is `main`'s Client -/

section Bridge

variable (B : AdversaryM)

/-- The first key of a validated set. -/
lemma keys_zero (S : AnchorSet) : ∃ k, S.keys[0]? = some k := by
  obtain ⟨k, ks, hk⟩ := List.exists_cons_of_ne_nil S.valid.1
  exact ⟨k, by rw [hk]; rfl⟩

/-- If `find_issuer` fails, the key at index `0` does not verify the token. -/
lemma eval_zero_ne {S : AnchorSet} {t s : Bytes} (h : findIssuer S t s = none) {k : UOVKey}
    (hk : S.keys[0]? = some k) : k.eval s ≠ t := fun he => by
  have := findIssuer_isSome.2 ⟨0, k, hk, he⟩
  rw [h] at this
  exact Bool.false_ne_true this

/-- **A redemption request at `findIdx` is `find_issuer`'s**: `invalidToken` if no key verifies
the token, otherwise the nullifier and the proof. -/
theorem redOut_findIdx (P : RedeemPt) (o : Option Out) (pk : UOVKey)
    (hi : P.i = findIdx P.anchors pk (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s) :
    redOut B P o =
      match findIssuer P.anchors (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s with
      | none => .error .invalidToken
      | some _ => .ok (P.tok.nf ++ pf o) := by
  unfold redOut
  rw [hi]
  unfold findIdx
  cases h : findIssuer P.anchors (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s with
  | some i =>
    obtain ⟨k, hk, he⟩ := findIssuer_some h
    simp only [Option.getD_some, hk]
    simp only [he, ↓reduceIte]
  | none =>
    obtain ⟨k, hk⟩ := keys_zero P.anchors
    simp only [Option.getD_none, hk]
    simp only [eval_zero_ne h hk, ↓reduceIte]

/-- **A redemption statement at `findIdx` is the one `redeemRequest` proves**: the witness at
the index `find_issuer` returns, and none if it fails. -/
theorem redStmt_findIdx (P : RedeemPt) (pk : UOVKey)
    (hi : P.i = findIdx P.anchors pk (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s) :
    redStmt B P =
      (findIssuer P.anchors (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s).map fun i =>
        (stR (xRM B P), toBA (encodeRedeemWitness P.tok.nf B.int.ci B.int.cr P.tok.r P.tok.s i)) := by
  unfold redStmt
  rw [hi]
  unfold findIdx
  cases h : findIssuer P.anchors (com P.tok.nf B.int.ci B.int.cr P.tok.r) P.tok.s with
  | some i =>
    obtain ⟨k, hk, he⟩ := findIssuer_some h
    simp only [Option.getD_some, hk, Option.map_some]
    simp only [he, ↓reduceIte]
  | none =>
    obtain ⟨k, hk⟩ := keys_zero P.anchors
    simp only [Option.getD_none, hk, Option.map_none]
    simp only [eval_zero_ne h hk, ↓reduceIte]

/-- The colluding game's redemption points with `findIdx` have `find_issuer`'s index. -/
theorem ptM_findIdx (b : Bool) (s : SecM) (o₁ o₂ : Option Out) (side : Bool) :
    (ptM B findIdx b s o₁ o₂ side).i =
      findIdx (ptM B findIdx b s o₁ o₂ side).anchors (B.int.pk (b ^^ side))
        (com (ptM B findIdx b s o₁ o₂ side).tok.nf B.int.ci B.int.cr
          (ptM B findIdx b s o₁ o₂ side).tok.r) (ptM B findIdx b s o₁ o₂ side).tok.s := rfl

end Bridge

/-- The non-colluding game's redemption points with `findIdx` have `find_issuer`'s index. -/
theorem ptNM_findIdx (A : AdversaryNCM) (PI : NIZK IssueInstance) (sk : Bool → Signer) (b : Bool)
    (s : SecNC) (side : Bool) :
    (ptNM A findIdx PI sk b s side).i =
      findIdx (ptNM A findIdx PI sk b s side).anchors (A.m.int.pk (b ^^ side))
        (com (ptNM A findIdx PI sk b s side).tok.nf A.m.int.ci A.m.int.cr
          (ptNM A findIdx PI sk b s side).tok.r) (ptNM A findIdx PI sk b s side).tok.s := rfl

/-! ## Theorem 4(a) on `main` for `main`'s Client -/

/-- **Theorem 4(a) on `main` (no label rows), all tables shared, for `main`'s Client**
(`find_issuer`, the rule `findIdx`). For the colluding adversary whose guess reads the one `H₃` at
`q3` points, the cipher at `qE` keys and `H₅` at a consistent read set (`AdversaryH.ConsH`),

    |Pr[world 0] − Pr[world 1]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
      + 15·(Σ_{b, c} puAdv Com (predH_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide + 2·2⁻¹²⁸,

the bound of `anonymity_main_sharedAll`, with the predictors and the hiding reductions at
`findIdx`. -/
theorem anonymity_main_sharedAll_find (A : AdversaryH) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    {εhide : ℝ}
    (hhide : ∀ T b a, hidingAdv A.base.toM.int.ci A.base.toM.int.cr
      (redS23 (A.withH T) findIdx b a) ≤ εhide) :
    |realH A findIdx false - realH A findIdx true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (puAdv (comM A.base.toM) (predH₀ A findIdx false) +
          puAdv (comM A.base.toM) (predH₁ A findIdx false) +
          puAdv (comM A.base.toM) (predH₀ A findIdx true) +
          puAdv (comM A.base.toM) (predH₁ A findIdx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide + 2 / 2 ^ 128 :=
  anonymity_main_sharedAll A findIdx hC hhide

/-! ## Theorem 4(b') on `main` for `main`'s Client -/

/-- **`find_issuer` is a sound rule for sets that contain both issuers' maps**: an honest token
is always redeemable. -/
theorem ruleNC_findIdx (A : AdversaryNC) (hK : MoussakaFind.Contains A) :
    RuleNC A findIdx (fun _ _ => true) := by
  intro c side tk hc
  rw [show tokT A.base tk = com tk.nf A.base.ci A.base.cr tk.r from rfl, redeemOk_findIdx]
  obtain ⟨k, hk, he⟩ := hK c side
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
  exact findIssuer_isSome.2 ⟨i, k, hi, by rw [he]; exact hc⟩

/-- **Theorem 4(b') on `main` (no label rows), all tables shared, for `main`'s Client.** For
every non-colluding Moderator whose two Anchor Sets contain a key with each issuer's map
(`MoussakaFind.Contains`), honest Anchors with signers correct for their keys answering with
`main`'s `issue_response`, any issuance proof system, and the executable prover for the two
redemptions on the shared tables: if the guess reads `H₃` at `q3` points, the cipher at `qE` keys
and `H₅` at a consistent read set of at most `q5` keys,

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
        + 15·(8·noHitProb + (4·(q5 + 625) + 626)·2⁻¹²⁸) + 2·2⁻¹²⁸ + 2·(φ false + φ true),

the bound of `anonymityNC_main`. No assumption on `Com`. -/
theorem anonymityNC_main_find (A : AdversaryNCM) (PI : NIZK IssueInstance) (sk : Bool → Signer)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : MoussakaFind.Contains A.nc) {q3 qE q5 : ℕ}
    (hC : A.ConsH q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A findIdx PI sk false - realNCM A findIdx PI sk true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 +
        2 * (phi A.nc sk false + phi A.nc sk true) :=
  anonymityNC_main A findIdx PI sk hsk (ruleNC_findIdx A.nc hK) hC h5

/-- **Unlinkability against a non-colluding Moderator on `main` for `main`'s Client**: one Anchor
(equal keys and signers), any Anchor Sets, no abort term. -/
theorem unlinkabilityNC_main_find (A : AdversaryNCM) (PI : NIZK IssueInstance) (sk : Bool → Signer)
    (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true) (hs : sk false = sk true)
    {q3 qE q5 : ℕ} (hC : A.ConsH q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A findIdx PI sk false - realNCM A findIdx PI sk true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 :=
  unlinkabilityNC_main A findIdx PI sk hsk hpk hs hC h5

end VoleMole.Privacy.Moussaka
