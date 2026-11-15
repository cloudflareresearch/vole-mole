import VoleMole.Privacy.Moussaka

/-!
# Moussaka's colluding game with an index rule that reads the token

`Privacy/Moussaka.lean` states the colluding game for a Client that takes its issuer's index from
`S` by a rule `idx S pk` of the Anchor Set and the issuer's key: the index-taking API before
`21be618` (`Spec.Moussaka.redeemRequestAt`). `main`'s Client finds the index from its token
(`find_issuer`: the last key of `S` that verifies `(s, t)`), which is no such rule.

Here the game is restated for a **token-reading rule** (`Rule`): the index is `ix S pk t s`, a
function of the set, the issuer's key, the token's commitment `t = Com(nf, ctx_iss, ctx_red, r)`
and its preimage `s`, but not of `nf` or `r` on their own. Both Clients are covered:

* `Rule.ofIdx idx` is the index-taking Client (`ptG_ofIdx`, `allOkG_ofIdx`, ...: the definitions
  here agree with those of `Privacy/Moussaka.lean` definitionally);
* `findIdx` is `main`'s Client: `redeemRequest` is `redeemRequestAt` at `findIdx`
  (`redeemRequest_eq_findIdx`; outside the set's range `find_issuer` and the index-taking step
  refuse alike, since a validated set is nonempty), and redeemability at `findIdx` is
  `find_issuer`'s success (`redeemOk_findIdx`).

The definitions and lemmas are those of `Privacy/Moussaka.lean` with the suffix `G`; with
simulated proofs the view is again a function of the commitments and the nullifiers
(`post_redSimG`), because the rule reads `r` only through `t`. The `main` games
(`Privacy/MoussakaMain*.lean`) are stated for a `Rule`, so their theorems hold for both Clients.
-/

open Finset

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## Rules -/

/-- **An index rule that may read the token**: the Client's index in `S`, from the issuer's key,
the token's commitment `t` and its preimage `s`. -/
abbrev Rule := AnchorSet → UOVKey → Bytes → Bytes → ℕ

/-- The index-taking Client's rule (`Privacy/Moussaka.lean`), not reading the token. -/
def Rule.ofIdx (idx : AnchorSet → UOVKey → ℕ) : Rule := fun S pk _ _ => idx S pk

/-- **`main`'s Client** (`find_issuer`): the last index whose key verifies `(s, t)`, and `0` if
there is none (then no key of `S` verifies the token, and the index-taking step refuses at `0`
with the error `find_issuer` gives). -/
def findIdx : Rule := fun S _ t s => (findIssuer S t s).getD 0

/-- **`main`'s redemption step is the index-taking step at `findIdx`**, for every token, set,
contexts, digest and seed. -/
theorem redeemRequest_eq_findIdx (PR : NIZK RedeemInstance) (tok : Token) (S : AnchorSet)
    (pk : UOVKey) (ctxIss ctxRed cd seed : Bytes) :
    redeemRequest PR tok S ctxIss ctxRed cd seed =
      redeemRequestAt PR tok S (findIdx S pk (com tok.nf ctxIss ctxRed tok.r) tok.s) ctxIss ctxRed
        cd seed := by
  unfold findIdx
  cases h : findIssuer S (com tok.nf ctxIss ctxRed tok.r) tok.s with
  | some i => exact redeemRequest_eq_at PR tok S i ctxIss ctxRed cd seed h
  | none =>
    obtain ⟨k, ks, hk⟩ := List.exists_cons_of_ne_nil S.valid.1
    have h0 : S.keys[0]? = some k := by rw [hk]; rfl
    have hne : k.eval tok.s ≠ com tok.nf ctxIss ctxRed tok.r := fun he => by
      have := findIssuer_isSome.2 ⟨0, k, h0, he⟩
      rw [h] at this
      exact Bool.false_ne_true this
    simp [redeemRequest, redeemRequestAt, h, h0, hne]

/-- **Redeemability at `findIdx` is `find_issuer`'s success.** -/
theorem redeemOk_findIdx (ci cr : Bytes) (t : Token) (S : AnchorSet) (pk : UOVKey) :
    redeemOk ci cr t S (findIdx S pk (com t.nf ci cr t.r) t.s) =
      (findIssuer S (com t.nf ci cr t.r) t.s).isSome := by
  unfold findIdx redeemOk
  cases h : findIssuer S (com t.nf ci cr t.r) t.s with
  | some i =>
    obtain ⟨k, hk, he⟩ := findIssuer_some h
    simp [hk, he]
  | none =>
    obtain ⟨k, ks, hk⟩ := List.exists_cons_of_ne_nil S.valid.1
    have h0 : S.keys[0]? = some k := by rw [hk]; rfl
    have hne : k.eval t.s ≠ com t.nf ci cr t.r := fun he => by
      have := findIssuer_isSome.2 ⟨0, k, h0, he⟩
      rw [h] at this
      exact Bool.false_ne_true this
    simp [h0, hne]

/-! ## The game with a rule -/

variable (A : Adversary) (ix : Rule)

/-- The commitment a token opens to. -/
def tokT (t : Token) : Bytes := com t.nf A.ci A.cr t.r

/-- Client `c` can redeem at the rule's index in the set of side `side`. -/
def okAtG (i₀ i₁ : PendingToken × Bytes) (c side : Bool) : Bool :=
  redeemOk A.ci A.cr (tokD A i₀ i₁ c) (A.choose i₀.2 i₁.2 side).1
    (ix (A.choose i₀.2 i₁.2 side).1 (A.pk c) (tokT A (tokD A i₀ i₁ c)) (tokD A i₀ i₁ c).s)

/-- §6's rule: both tokens finalized, and each is redeemable at its index in both sets. -/
def allOkG (i₀ i₁ : PendingToken × Bytes) : Bool :=
  (tok A i₀ i₁ false).isSome && (tok A i₀ i₁ true).isSome &&
    okAtG A ix i₀ i₁ false false && okAtG A ix i₀ i₁ false true &&
    okAtG A ix i₀ i₁ true false && okAtG A ix i₀ i₁ true true

/-- The redemption of side `side` in world `b`: Client `b ^^ side`'s token at the rule's index. -/
def ptG (b : Bool) (i₀ i₁ : PendingToken × Bytes) (side : Bool) : RedeemPt :=
  ⟨tokD A i₀ i₁ (b ^^ side), (A.choose i₀.2 i₁.2 side).1,
    ix (A.choose i₀.2 i₁.2 side).1 (A.pk (b ^^ side)) (tokT A (tokD A i₀ i₁ (b ^^ side)))
      (tokD A i₀ i₁ (b ^^ side)).s, (A.choose i₀.2 i₁.2 side).2⟩

/-- The adversary's guess from the issuance outputs and the two redemption requests. -/
def postG (i₀ i₁ : PendingToken × Bytes) (yL yR : Except Error Bytes) : Prop :=
  A.guess i₀.2 i₁.2 (bif allOkG A ix i₀ i₁ then some (yL, yR) else none)

/-- The view in world `b`. -/
def viewG (b : Bool) (i₀ i₁ : PendingToken × Bytes) (redL redR : RedeemPt → Except Error Bytes) :
    Prop :=
  postG A ix i₀ i₁ (redL (ptG A ix b i₀ i₁ false)) (redR (ptG A ix b i₀ i₁ true))

/-- The game with the four slots drawn by `g₀ g₁ gL gR`. -/
def gameG {T₀ T₁ TL TR : Type} (b : Bool) (g₀ : T₀ → PendingToken × Bytes)
    (g₁ : T₁ → PendingToken × Bytes) (gL : TL → RedeemPt → Except Error Bytes)
    (gR : TR → RedeemPt → Except Error Bytes) (x : (T₀ × T₁) × (TL × TR)) : Prop :=
  viewG A ix b (g₀ x.1.1) (g₁ x.1.2) (gL x.2.1) (gR x.2.2)

/-! ### The index-taking Client is a rule -/

theorem okAtG_ofIdx (idx : AnchorSet → UOVKey → ℕ) : okAtG A (Rule.ofIdx idx) = okAt A idx := rfl
theorem allOkG_ofIdx (idx : AnchorSet → UOVKey → ℕ) : allOkG A (Rule.ofIdx idx) = allOk A idx :=
  rfl
theorem ptG_ofIdx (idx : AnchorSet → UOVKey → ℕ) : ptG A (Rule.ofIdx idx) = pt A idx := rfl
theorem gameG_ofIdx (idx : AnchorSet → UOVKey → ℕ) {T₀ T₁ TL TR : Type} :
    gameG (T₀ := T₀) (T₁ := T₁) (TL := TL) (TR := TR) A (Rule.ofIdx idx) = game A idx := rfl

/-! ### `main`'s Client is `findIdx` -/

/-- **With `findIdx`, the rule's check is `find_issuer`'s success** (`MoussakaFind.okAt`). -/
theorem okAtG_findIdx (i₀ i₁ : PendingToken × Bytes) (c side : Bool) :
    okAtG A findIdx i₀ i₁ c side = (findIssuer (A.choose i₀.2 i₁.2 side).1
      (com (tokD A i₀ i₁ c).nf A.ci A.cr (tokD A i₀ i₁ c).r) (tokD A i₀ i₁ c).s).isSome :=
  redeemOk_findIdx _ _ _ _ _

/-- **With `findIdx`, a real redemption at the game's point is `main`'s `redeemRequest`.** -/
theorem redeemRequest_ptG_findIdx (PR : NIZK RedeemInstance) (b : Bool) (i₀ i₁ : PendingToken × Bytes)
    (side : Bool) (seed : Bytes) :
    redeemRequest PR (ptG A findIdx b i₀ i₁ side).tok (ptG A findIdx b i₀ i₁ side).anchors A.ci A.cr
        (ptG A findIdx b i₀ i₁ side).cd seed =
      redeemRequestAt PR (ptG A findIdx b i₀ i₁ side).tok (ptG A findIdx b i₀ i₁ side).anchors
        (ptG A findIdx b i₀ i₁ side).i A.ci A.cr (ptG A findIdx b i₀ i₁ side).cd seed :=
  redeemRequest_eq_findIdx PR _ _ (A.pk (b ^^ side)) _ _ _ _

/-! ## All proofs simulated -/

/-- Client `c` is redeemable at the rule's index in the set of side `side`, checked against
`t_c`. -/
def okTG (q₀ q₁ t₀ t₁ : Bytes) (c side : Bool) : Bool :=
  match (A.choose q₀ q₁ side).1.keys[ix (A.choose q₀ q₁ side).1 (A.pk c) (bif c then t₁ else t₀)
      (resp A q₀ q₁ c)]? with
  | none => false
  | some pk => decide (pk.eval (resp A q₀ q₁ c) = bif c then t₁ else t₀)

/-- §6's rule, as a function of the requests and the commitments. -/
def allOkTG (q₀ q₁ t₀ t₁ : Bytes) : Bool :=
  finT A q₀ q₁ t₀ t₁ false && finT A q₀ q₁ t₀ t₁ true && okTG A ix q₀ q₁ t₀ t₁ false false &&
    okTG A ix q₀ q₁ t₀ t₁ false true && okTG A ix q₀ q₁ t₀ t₁ true false &&
    okTG A ix q₀ q₁ t₀ t₁ true true

lemma okAtG_of_allOkG {i₀ i₁ : PendingToken × Bytes} (h : allOkG A ix i₀ i₁ = true)
    (c side : Bool) : okAtG A ix i₀ i₁ c side = true := by
  unfold allOkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  cases c <;> cases side <;> assumption

/-- With the redemptions allowed, the Client's check passes at both redemption points. -/
lemma redeemOk_ptG_of_allOkG {i₀ i₁ : PendingToken × Bytes} (h : allOkG A ix i₀ i₁ = true)
    (b side : Bool) :
    redeemOk A.ci A.cr (ptG A ix b i₀ i₁ side).tok (ptG A ix b i₀ i₁ side).anchors
      (ptG A ix b i₀ i₁ side).i = true :=
  okAtG_of_allOkG A ix h _ _

/-- **`allOkG` is `allOkTG`** for honest pending tokens (`t = Com(nf, ·, r)`). -/
lemma allOkG_eq_allOkTG (i₀ i₁ : PendingToken × Bytes)
    (h₀ : i₀.1.t = com i₀.1.nf A.ci A.cr i₀.1.r) (h₁ : i₁.1.t = com i₁.1.nf A.ci A.cr i₁.1.r) :
    allOkG A ix i₀ i₁ = allOkTG A ix i₀.2 i₁.2 i₀.1.t i₁.1.t := by
  have htok (c : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD A i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hok (c side : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      okAtG A ix i₀ i₁ c side = okTG A ix i₀.2 i₁.2 i₀.1.t i₁.1.t c side := by
    unfold okAtG okTG redeemOk tokT
    rw [htok c hc]
    cases c <;> simp only [Bool.cond_false, Bool.cond_true, ← h₀, ← h₁] <;> rfl
  unfold allOkG allOkTG
  rw [tok_of_fin A i₀ i₁ false, tok_of_fin A i₀ i₁ true]
  cases e₀ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t false
  · simp
  · cases e₁ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t true
    · simp
    · simp [hok _ _ e₀, hok _ _ e₁]

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)

/-- **With simulated redemptions, the view reads the issuance outputs only through the requests,
the commitments and the nullifiers.** -/
theorem post_redSimG (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cL cR : CR)
    (h₀ : i₀.1.t = com i₀.1.nf A.ci A.cr i₀.1.r) (h₁ : i₁.1.t = com i₁.1.nf A.ci A.cr i₁.1.r) :
    postG A ix i₀ i₁ (redSim A simR cL (ptG A ix b i₀ i₁ false))
        (redSim A simR cR (ptG A ix b i₀ i₁ true)) ↔
      A.guess i₀.2 i₁.2 (bif allOkTG A ix i₀.2 i₁.2 i₀.1.t i₁.1.t then
        some (ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cL false,
          ySim A simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf cR true) else none) := by
  have htok (c : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD A i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hall := allOkG_eq_allOkTG A ix i₀ i₁ h₀ h₁
  unfold postG
  rw [hall]
  refine iff_of_eq (congrArg _ ?_)
  cases hC : allOkTG A ix i₀.2 i₁.2 i₀.1.t i₁.1.t
  · rfl
  · have hA : allOkG A ix i₀ i₁ = true := hall.trans hC
    have f₀ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t false = true := by
      unfold allOkTG at hC; simp only [Bool.and_eq_true] at hC; exact hC.1.1.1.1.1
    have f₁ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t true = true := by
      unfold allOkTG at hC; simp only [Bool.and_eq_true] at hC; exact hC.1.1.1.1.2
    rw [redSim_of_ok A simR _ _ (redeemOk_ptG_of_allOkG A ix hA b false),
      redSim_of_ok A simR _ _ (redeemOk_ptG_of_allOkG A ix hA b true)]
    cases b
    · simp only [ptG, htok false f₀, htok true f₁, ySim, Bool.false_xor, Bool.cond_false,
        Bool.cond_true]
    · simp only [ptG, htok false f₀, htok true f₁, ySim, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.cond_false, Bool.cond_true]

/-- The game with all four proofs simulated. -/
def simGameG (b : Bool) :=
  gameG A ix b (issSim A simI) (issSim A simI) (redSim A simR) (redSim A simR)

/-- The view with all four proofs simulated, as a function of the commitments, the nullifiers and
the simulator coins. -/
def hviewG (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (cI₀ cI₁ : CI) (cL cR : CR) : Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.ci⟩ cI₁
  A.guess q₀ q₁ (bif allOkTG A ix q₀ q₁ t₀ t₁ then
    some (ySim A simR b q₀ q₁ n₀ n₁ cL false, ySim A simR b q₀ q₁ n₀ n₁ cR true) else none)

theorem simGame_iffG (b : Bool)
    (x : ((Coins nfBytes × Coins rBytes × CI) × (Coins nfBytes × Coins rBytes × CI)) × (CR × CR)) :
    simGameG A ix simI simR b x ↔
      hviewG A ix simI simR b (com (List.ofFn x.1.1.1) A.ci A.cr (List.ofFn x.1.1.2.1))
        (com (List.ofFn x.1.2.1) A.ci A.cr (List.ofFn x.1.2.2.1)) (List.ofFn x.1.1.1)
        (List.ofFn x.1.2.1) x.1.1.2.2 x.1.2.2.2 x.2.1 x.2.2 :=
  post_redSimG A ix simR b _ _ _ _ rfl rfl

/-- **The reduction to hiding**: the adversary, with the simulator coins `c` fixed. -/
def reductionG (b : Bool) (c : (CI × CI) × (CR × CR)) (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hviewG A ix simI simR b z.1 z.2.1 z.2.2.1 z.2.2.2 c.1.1 c.1.2 c.2.1 c.2.2

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
def idealGameG (b : Bool)
    (x : (HTape × (Coins nfBytes × Coins nfBytes)) × ((CI × CI) × (CR × CR))) : Prop :=
  reductionG A ix simI simR b x.2 (hideIdeal A.ci A.cr x.1)

theorem hiding_hopG [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv A.ci A.cr (reductionG A ix simI simR b c) ≤ εhide) :
    |pr _ (simGameG A ix simI simR b) - pr _ (idealGameG A ix simI simR b)| ≤ εhide := by
  rw [← pr_equiv regroup.symm (simGameG A ix simI simR b),
    pr_congr fun y => simGame_iffG A ix simI simR b (regroup.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- **After the hiding hop the worlds coincide** (swap of the fresh nullifiers). -/
theorem idealGame_eqG [Fintype CI] [Fintype CR] :
    pr _ (idealGameG A ix simI simR false) = pr _ (idealGameG A ix simI simR true) := by
  rw [← pr_equiv swapN]
  exact pr_congr fun x => Iff.rfl

end VoleMole.Privacy.Moussaka
