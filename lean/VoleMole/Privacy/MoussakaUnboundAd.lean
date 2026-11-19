import VoleMole.Privacy.MoussakaUnbound

/-!
# Unbound Moussaka: issuer hiding and unlinkability with adaptive redemption queries

Theorem U5(a) of `lean/docs/security/moussaka-unbound.md` on the executable spec, as in
`Privacy/MoussakaUnbound.lean`, but the adversary chooses **each redemption query after seeing the
answers to the earlier ones**.

**Game.** The adversary plays every Anchor and the Moderator. It chooses `ctx_iss` and the two
issuing keys, sees both Clients' issuance requests and answers them (`AdversaryAd`). If either
`finalize_issue` fails the game ends (the guess sees `none`). Otherwise it makes `n` redemption
queries one after the other: query `j` is `next q₀ q₁ H`, a function of the two issuance requests
and of the history `H` of earlier queries and answers. Query `(i, w, S, ctx_red, cd)` is answered,
in world `b`, by a redemption of token `i ⊕ (b ∧ w)` (`who`) under `(S, ctx_red, cd)`, **if** both
tokens are redeemable in `S` (`find_issuer` succeeds) and every earlier query with the same
`ctx_red` carried the same swap flag `w` (`ctxOk`, the context rule); otherwise it is refused
(`refused`). Both conditions are functions of what the adversary has seen (it knows `t₀, t₁`, its
own responses and its earlier queries), so a refusal reveals nothing. The guess sees the issuance
requests and the whole history.

## The hops (per world)

1. Both issuance proofs simulated (`gameAd_hop₀`, `gameAd_hop₁`): `2εI`.
2. **All `n` adaptively chosen redemption proofs simulated** (`gameAd_hopRed`, from the generic
   `interact_close`): the `j`-th hop fixes every other proof's randomness; the point at which proof
   `j` is made is then a function of the earlier (fixed) answers. `n·εR`.
3. With every proof simulated the run reads the keys only through the nullifier table
   `c, ctx ↦ Derive(k_c, ctx)` (`post_redSimAd`), so the PRF hop applies (`prf_hopAd`, the same
   `prfAdv` as the non-adaptive game, for the reductions `reductionAd`, which query the table
   adaptively). `εprf`.
4. **The ideal worlds coincide** (`idealGameAd_eq`). The swap pattern `W` (the flag of the first
   query in each context, `firstFlag`) now depends on the table through the earlier answers. The
   map `F ↦ swapF W_F F`, with `W_F` read off the run in world 1 on `F`, sends the run in world 1
   to the run in world 0 (`runI_swap`, from `interact_congr_of` and `firstFlag_of_prefix`), and the
   run in world 0 on the image has the same pattern, so the map with the pattern of world 0 is its
   inverse (`swapE`). This is the eager form of the lazy-sampling argument of the note: when a
   fresh context is first queried, its flag is fixed and the pair `(F₀(ctx), F₁(ctx))` is drawn
   fresh, and exchanging it is a bijection of the remaining randomness.

## Results

* `interact`, `interact_close`: an adaptive interaction with `n` oracles, and the `n`-step hybrid
  over independent oracle tapes (each oracle `ε`-close at every point: `n·ε`).
* **`anonymityAd`**: `|Pr[A accepts in world 0] − Pr[A accepts in world 1]| ≤ 4εI + 2n·εR + 2εprf`,
  for adaptive redemption queries.

The hypotheses are those of `Privacy/MoussakaUnbound.lean`'s `anonymity`: per-proof zero knowledge
of both unbound relations (`ZeroKnowledge` for `IssueRelW`, `RedeemRelW`; with the CRT masks from
the witness, as on `main`, no efficient simulator meets it, see the note's §3.1 and §10), and the
PRF advantage of the explicit reductions (Keccak-p[800,12], an assumption).
-/

open Finset

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## Adaptive interactions -/

section Interact

variable {Q Y : Type*} (next : List (Q × Y) → Q) (valid : List (Q × Y) → Q → Bool) (refuse : Y)

/-- **An adaptive interaction**: each oracle in turn answers the query `next H` chosen from the
history `H` so far, if `valid H (next H)`; otherwise the answer is `refuse`. -/
def interact : List (Q → Y) → List (Q × Y) → List (Q × Y)
  | [], H => H
  | o :: os, H =>
    interact os (H ++ [(next H, if valid H (next H) then o (next H) else refuse)])

theorem interact_prefix : ∀ (os : List (Q → Y)) (H : List (Q × Y)),
    H <+: interact next valid refuse os H
  | [], H => List.prefix_refl H
  | _ :: os, H => (List.prefix_append H _).trans (interact_prefix os _)

theorem interact_ofFn_succ {n : ℕ} (f : Fin (n + 1) → Q → Y) (H : List (Q × Y)) :
    interact next valid refuse (List.ofFn f) H =
      interact next valid refuse (List.ofFn fun j => f j.succ)
        (H ++ [(next H, if valid H (next H) then f 0 (next H) else refuse)]) := by
  rw [List.ofFn_succ]
  rfl

/-- **Validity is read only at the queries asked.** -/
theorem interact_congr_valid {valid' : List (Q × Y) → Q → Bool}
    (h : ∀ H, valid H (next H) = valid' H (next H)) :
    ∀ (os : List (Q → Y)) (H : List (Q × Y)),
      interact next valid refuse os H = interact next valid' refuse os H
  | [], _ => rfl
  | o :: os, H => by
    simp only [interact, h H]
    exact interact_congr_valid h os _

/-- **Oracles that agree on the valid queries asked give the same run.** If `f j` and `f' j` agree
on every query with `P`, and every valid query of the run with `f` has `P`, the runs coincide. -/
theorem interact_congr_of (P : Q → Prop) :
    ∀ {n : ℕ} (f f' : Fin n → Q → Y), (∀ j q, P q → f j q = f' j q) → ∀ H : List (Q × Y),
      (∀ H' y, H' ++ [(next H', y)] <+: interact next valid refuse (List.ofFn f) H →
        valid H' (next H') = true → P (next H')) →
      interact next valid refuse (List.ofFn f) H = interact next valid refuse (List.ofFn f') H
  | 0, f, f', _, H, _ => by simp [interact]
  | n + 1, f, f', hf, H, hP => by
    rw [interact_ofFn_succ, interact_ofFn_succ]
    have hstep : (if valid H (next H) then f 0 (next H) else refuse) =
        (if valid H (next H) then f' 0 (next H) else refuse) := by
      cases hv : valid H (next H)
      · rfl
      · simp only [↓reduceIte]
        refine hf 0 _ (hP H (f 0 (next H)) ?_ hv)
        rw [interact_ofFn_succ, hv]
        exact interact_prefix next valid refuse _ _
    rw [← hstep]
    refine interact_congr_of P (fun j => f j.succ) (fun j => f' j.succ) (fun j q => hf j.succ q) _
      fun H' y h hv => hP H' y ?_ hv
    rwa [interact_ofFn_succ]

/-- The two halves of a tape `Fin (n+1) → T`, as in `close_pi`. -/
lemma interact_consE {T : Type*} {n : ℕ} (o : T → Q → Y) (H : List (Q × Y))
    (p : T × (Fin n → T)) :
    interact next valid refuse (List.ofFn fun j => o (consE T n p j)) H =
      interact next valid refuse (List.ofFn fun j => o (p.2 j))
        (H ++ [(next H, if valid H (next H) then o p.1 (next H) else refuse)]) := by
  rw [interact_ofFn_succ]
  simp [consE]

/-- **The `n`-step hybrid for an adaptive interaction.** If the oracles with tapes `T` and `T'` are
`ε`-close at every query, the runs with `n` independent oracle tapes are `n·ε`-close, for any start
history. The `j`-th step fixes every other tape; the query of oracle `j` is then fixed by the earlier
answers. -/
theorem interact_close {T T' : Type*} [Fintype T] [Nonempty T] [Fintype T'] [Nonempty T'] {ε : ℝ}
    (o : T → Q → Y) (o' : T' → Q → Y) (h : ∀ q, Close ε (fun t => o t q) (fun t => o' t q)) :
    ∀ (n : ℕ) (H : List (Q × Y)), Close (n * ε)
      (fun τ : Fin n → T => interact next valid refuse (List.ofFn fun j => o (τ j)) H)
      (fun τ : Fin n → T' => interact next valid refuse (List.ofFn fun j => o' (τ j)) H)
  | 0, H => by
    refine (close_const (α := Fin 0 → T) (β := Fin 0 → T') (le_of_eq (by simp)) H).congr
      (fun τ => ?_) fun τ => ?_ <;> simp [interact]
  | n + 1, H => by
    let st : Y → List (Q × Y) := fun y =>
      H ++ [(next H, if valid H (next H) then y else refuse)]
    let F : T × (Fin n → T) → List (Q × Y) := fun p =>
      interact next valid refuse (List.ofFn fun j => o (p.2 j)) (st (o p.1 (next H)))
    let G : T' × (Fin n → T) → List (Q × Y) := fun p =>
      interact next valid refuse (List.ofFn fun j => o (p.2 j)) (st (o' p.1 (next H)))
    let K : T' × (Fin n → T') → List (Q × Y) := fun p =>
      interact next valid refuse (List.ofFn fun j => o' (p.2 j)) (st (o' p.1 (next H)))
    have a : Close 0 F
        (fun τ : Fin (n + 1) → T => interact next valid refuse (List.ofFn fun j => o (τ j)) H) :=
      (close_equiv (consE T n)
        (fun τ : Fin (n + 1) → T => interact next valid refuse (List.ofFn fun j => o (τ j)) H)).congr
        (fun p => (interact_consE next valid refuse o H p).symm) fun _ => rfl
    have b : Close ε F G := fun D =>
      abs_pr_prod_sub_le' (fun p : T × (Fin n → T) => D (F p)) (fun p : T' × (Fin n → T) => D (G p))
        fun v => h (next H) (fun y => D (interact next valid refuse
          (List.ofFn fun j => o (v j)) (st y)))
    have c : Close (n * ε) G K := fun D =>
      abs_pr_prod_sub_le (fun p : T' × (Fin n → T) => D (G p)) (fun p : T' × (Fin n → T') => D (K p))
        fun a => interact_close o o' h n (st (o' a (next H))) D
    have d : Close 0 K
        (fun τ : Fin (n + 1) → T' => interact next valid refuse (List.ofFn fun j => o' (τ j)) H) :=
      (close_equiv (consE T' n)
        (fun τ : Fin (n + 1) → T' => interact next valid refuse (List.ofFn fun j => o' (τ j)) H)).congr
        (fun p => (interact_consE next valid refuse o' H p).symm) fun _ => rfl
    refine (a.symm.trans (b.trans (c.trans d))).mono (le_of_eq ?_)
    push_cast; ring

end Interact

/-! ## The context rule and the swap pattern of a history -/

/-- What the adversary has seen of the redemptions: each query and its answer. -/
abbrev Hist := List (Query × Except Error Bytes)

/-- The answer to a refused query. -/
def refused : Except Error Bytes := .error .invalidToken

/-- **The context rule** for query `q` after history `H`: every earlier query in `q`'s context
carried `q`'s swap flag. -/
def ctxOk (H : Hist) (q : Query) : Bool :=
  H.all fun e => !decide (e.1.ctxRed = q.ctxRed) || e.1.w == q.w

/-- **The swap pattern of a history**: the flag of the first query in each context (`false` for
contexts never queried). -/
def firstFlag (H : Hist) (ctx : Coins ctxBytes) : Bool :=
  ((H.find? fun e => decide (e.1.ctxRed = ctx)).map fun e => e.1.w).getD false

/-- A query that satisfies the context rule has the flag of the first query in its context, in
every history that extends it. -/
theorem firstFlag_of_prefix {H Hf : Hist} {q : Query} {y : Except Error Bytes}
    (hp : H ++ [(q, y)] <+: Hf) (hc : ctxOk H q = true) : firstFlag Hf q.ctxRed = q.w := by
  obtain ⟨L, rfl⟩ := hp
  unfold firstFlag
  rw [List.append_assoc, List.find?_append]
  cases hf : H.find? fun e => decide (e.1.ctxRed = q.ctxRed) with
  | none => simp
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hpe := List.find?_some hf
    have := List.all_eq_true.1 hc e he
    simp only [decide_eq_true_eq] at hpe
    simp only [hpe, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    simp [this]

/-! ## The adaptive game -/

/-- **The colluding adversary with adaptive redemption queries**: `ctx_iss`, the two issuing keys,
the responses to the two issuance requests, each redemption query from the requests and the history
so far, and the guess from the requests and the history (`none`: a token did not finalize). -/
structure AdversaryAd where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  next : Bytes → Bytes → Hist → Query
  guess : Bytes → Bytes → Option Hist → Prop

/-- The adversary's issuance stage as a non-adaptive adversary (for `tok`, `tokD`, `issReal`,
`issSim`, `redReal`, `redSim`, `ySim`; its queries and guess are not used). -/
def AdversaryAd.base (A : AdversaryAd) : Adversary 0 :=
  ⟨A.ctxIss, A.pk, A.respond, fun _ _ => Fin.elim0, fun _ _ _ => True⟩

variable (A : AdversaryAd) {n : ℕ}

/-- The challenger's rule for query `q` after `H`: both tokens redeemable in `q`'s Anchor Set, and
the context rule. -/
def validR (i₀ i₁ : PendingToken × Bytes) (H : Hist) (q : Query) : Bool :=
  redeemable A.base.ci (tokD A.base i₀ i₁ false) q.anchors &&
    redeemable A.base.ci (tokD A.base i₀ i₁ true) q.anchors && ctxOk H q

/-- Query `q` in world `b`: the answering token, the Anchor Set, the context and the digest. -/
def ptQ (b : Bool) (i₀ i₁ : PendingToken × Bytes) (q : Query) : RedeemPt :=
  ⟨tokD A.base i₀ i₁ (who b q), q.anchors, List.ofFn q.ctxRed, q.cd⟩

/-- Both tokens finalized. -/
def finBoth (i₀ i₁ : PendingToken × Bytes) : Bool :=
  (tok A.base i₀ i₁ false).isSome && (tok A.base i₀ i₁ true).isSome

/-- The view in world `b`, given the issuance outputs and the `n` redemption provers. -/
def viewAd (b : Bool) (i₀ i₁ : PendingToken × Bytes)
    (reds : Fin n → RedeemPt → Except Error Bytes) : Prop :=
  A.guess i₀.2 i₁.2 (bif finBoth A i₀ i₁ then
    some (interact (A.next i₀.2 i₁.2) (validR A i₀ i₁) refused
      (List.ofFn fun j q => reds j (ptQ A b i₀ i₁ q)) [])
    else none)

/-- The adaptive game with the issuance slots drawn by `g₀ g₁` and every redemption by `g`. -/
def gameAd {T₀ T₁ T : Type} (b : Bool) (g₀ : T₀ → PendingToken × Bytes)
    (g₁ : T₁ → PendingToken × Bytes) (g : T → RedeemPt → Except Error Bytes)
    (x : (T₀ × T₁) × (Fin n → T)) : Prop :=
  viewAd A b (g₀ x.1.1) (g₁ x.1.2) fun j => g (x.2 j)

/-- **The real adaptive game** in world `b`, with `n` redemption queries. -/
def realGameAd (n : ℕ) (PI : NIZK IssueInstance) (PR : NIZK RedeemInstance) (b : Bool) :=
  gameAd (n := n) A b (issReal A.base PI) (issReal A.base PI) (redReal A.base PR)

/-! ## The proof hops -/

variable {T₀ T₁ T T₀' T₁' T' : Type} [Fintype T₀] [Fintype T₁] [Fintype T] [Fintype T₀']
  [Fintype T₁'] [Fintype T']

theorem gameAd_hop₀ [Nonempty T₁] [Nonempty T] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₀' : T₀' → PendingToken × Bytes}
    (g₁ : T₁ → PendingToken × Bytes) (g : T → RedeemPt → Except Error Bytes)
    (h : Close ε g₀ g₀') :
    |pr _ (gameAd (n := n) A b g₀ g₁ g) - pr _ (gameAd (n := n) A b g₀' g₁ g)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le' _ _ fun x₁ =>
    h (fun o => viewAd A b o (g₁ x₁) fun j => g (y j))

theorem gameAd_hop₁ [Nonempty T₀] [Nonempty T] (b : Bool) {ε : ℝ}
    (g₀ : T₀ → PendingToken × Bytes) {g₁ : T₁ → PendingToken × Bytes}
    {g₁' : T₁' → PendingToken × Bytes} (g : T → RedeemPt → Except Error Bytes)
    (h : Close ε g₁ g₁') :
    |pr _ (gameAd (n := n) A b g₀ g₁ g) - pr _ (gameAd (n := n) A b g₀ g₁' g)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le _ _ fun x₀ =>
    h (fun o => viewAd A b (g₀ x₀) o fun j => g (y j))

/-- **All `n` adaptively chosen redemption proofs at once**: `n` hops. -/
theorem gameAd_hopRed [Nonempty T₀] [Nonempty T₁] [Nonempty T] [Nonempty T'] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes}
    (h₀ : WellFormed g₀) (h₁ : WellFormed g₁) {g : T → RedeemPt → Except Error Bytes}
    {g' : T' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, tokWF p.tok → p.ctxRed.length = ctxBytes →
      Close ε (fun t => g t p) (fun t => g' t p)) :
    |pr _ (gameAd (n := n) A b g₀ g₁ g) - pr _ (gameAd (n := n) A b g₀ g₁ g')| ≤ n * ε :=
  abs_pr_prod_sub_le _ _ fun x =>
    interact_close (A.next (g₀ x.1).2 (g₁ x.2).2) (validR A (g₀ x.1) (g₁ x.2)) refused
      (fun t q => g t (ptQ A b (g₀ x.1) (g₁ x.2) q)) (fun t q => g' t (ptQ A b (g₀ x.1) (g₁ x.2) q))
      (fun q => h _ (tokD_wf A.base (h₀ _) (h₁ _) _) (by simp [ptQ, ctxBytes])) n []
      (fun Hs => A.guess (g₀ x.1).2 (g₁ x.2).2
        (bif finBoth A (g₀ x.1) (g₁ x.2) then some Hs else none))

/-! ## All proofs simulated: the run reads the keys only through the nullifier table -/

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)

/-- The challenger's rule as a function of the requests and the commitments. -/
def validT (q₀ q₁ t₀ t₁ : Bytes) (H : Hist) (q : Query) : Bool :=
  okT A.base q₀ q₁ t₀ t₁ false q.anchors && okT A.base q₀ q₁ t₀ t₁ true q.anchors && ctxOk H q

/-- The run with all proofs simulated, from the requests, the commitments, the nullifier table and
the redemption simulator's coins. -/
def runT (b : Bool) (q₀ q₁ t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes) (cs : Fin n → CR) :
    Hist :=
  interact (A.next q₀ q₁) (validT A q₀ q₁ t₀ t₁) refused
    (List.ofFn fun j q => ySim A.base simR b O q (cs j)) []

/-- The view with all proofs simulated. -/
def hviewAd (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes) (cI₀ cI₁ : CI)
    (cs : Fin n → CR) : Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.base.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.base.ci⟩ cI₁
  A.guess q₀ q₁ (bif finT A.base q₀ q₁ t₀ t₁ false && finT A.base q₀ q₁ t₀ t₁ true then
    some (runT A simR b q₀ q₁ t₀ t₁ O cs) else none)

/-- A finalized token is the pending token's key and opening with the adversary's response. -/
lemma tokD_of_finT (i₀ i₁ : PendingToken × Bytes) (c : Bool)
    (hc : finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
    tokD A.base i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.k, (bif c then i₁ else i₀).1.r, resp A.base i₀.2 i₁.2 c⟩ := by
  unfold tokD
  rw [tok_of_fin A.base i₀ i₁ c]
  simp only [hc, ↓reduceIte, Option.getD_some]

lemma finBoth_eq (i₀ i₁ : PendingToken × Bytes) :
    finBoth A i₀ i₁ =
      (finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t false && finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t true) := by
  unfold finBoth
  rw [tok_of_fin A.base i₀ i₁ false, tok_of_fin A.base i₀ i₁ true]
  cases finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t false <;>
    cases finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t true <;> simp

/-- With both tokens finalized, a simulated redemption that the Client's `find_issuer` accepts is
the table's nullifier with a simulated proof. -/
lemma redSim_ptQ (b : Bool) (i₀ i₁ : PendingToken × Bytes)
    (h₀ : i₀.1.t = ucom i₀.1.k A.base.ci i₀.1.r) (h₁ : i₁.1.t = ucom i₁.1.k A.base.ci i₁.1.r)
    (hf : ∀ c, finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) (q : Query)
    (hq : okT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t (who b q) q.anchors = true) (c : CR) :
    redSim A.base simR c (ptQ A b i₀ i₁ q) = ySim A.base simR b
      (fun c ctx => bif c then derive i₁.1.k (List.ofFn ctx) else derive i₀.1.k (List.ofFn ctx))
      q c := by
  unfold okT at hq
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hq
  unfold redSim ySim ptQ
  rw [tokD_of_finT A i₀ i₁ _ (hf _)]
  cases hw : who b q
  · rw [hw] at hi
    simp only [Bool.cond_false] at hi ⊢
    rw [← h₀, hi]
  · rw [hw] at hi
    simp only [Bool.cond_true] at hi ⊢
    rw [← h₁, hi]

/-- **With simulated redemptions, the adaptive view reads the issuance outputs only through the
requests, the commitments and the nullifier table** (for honest pending tokens). -/
theorem viewAd_redSim (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cs : Fin n → CR)
    (h₀ : i₀.1.t = ucom i₀.1.k A.base.ci i₀.1.r) (h₁ : i₁.1.t = ucom i₁.1.k A.base.ci i₁.1.r) :
    viewAd A b i₀ i₁ (fun j => redSim A.base simR (cs j)) ↔
      A.guess i₀.2 i₁.2 (bif finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t false &&
          finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t true then
        some (runT A simR b i₀.2 i₁.2 i₀.1.t i₁.1.t
          (fun c ctx => bif c then derive i₁.1.k (List.ofFn ctx) else derive i₀.1.k (List.ofFn ctx))
          cs) else none) := by
  unfold viewAd
  rw [finBoth_eq]
  refine iff_of_eq (congrArg _ ?_)
  cases hC : (finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t false && finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t true)
  · simp only [Bool.cond_false]
  · simp only [Bool.and_eq_true] at hC
    have hf (c : Bool) : finT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t c = true := by
      cases c
      · exact hC.1
      · exact hC.2
    have hcom (c : Bool) : ucom (bif c then i₁ else i₀).1.k A.base.ci (bif c then i₁ else i₀).1.r =
        bif c then i₁.1.t else i₀.1.t := by
      cases c
      · exact h₀.symm
      · exact h₁.symm
    have hv : validR A i₀ i₁ = validT A i₀.2 i₁.2 i₀.1.t i₁.1.t := by
      funext H q
      unfold validR validT redeemable okT
      rw [tokD_of_finT A i₀ i₁ false (hf false), tokD_of_finT A i₀ i₁ true (hf true)]
      simp only [hcom]
    simp only [Bool.cond_true, Option.some.injEq]
    unfold runT
    rw [hv]
    refine interact_congr_of _ _ _
      (fun q => okT A.base i₀.2 i₁.2 i₀.1.t i₁.1.t (who b q) q.anchors = true) _ _
      (fun j q hq => redSim_ptQ A simR b i₀ i₁ h₀ h₁ hf q hq (cs j)) _ fun H' _ _ hval => ?_
    unfold validT at hval
    simp only [Bool.and_eq_true] at hval
    cases who b (A.next i₀.2 i₁.2 H')
    · exact hval.1.1
    · exact hval.1.2

/-- The adaptive game with every proof simulated. -/
def simGameAd (b : Bool) := gameAd (n := n) A b (issSim A.base simI) (issSim A.base simI)
  (redSim A.base simR)

/-! ## The PRF hop -/

/-- **The reduction to the PRF**: the adversary, with the simulator coins fixed, run on the
commitments and the table it is given (read adaptively, at the queried contexts). -/
def reductionAd (b : Bool) (cc : (CI × CI) × (Fin n → CR))
    (z : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes)) : Prop :=
  hviewAd A simI simR b z.1 z.2.1 z.2.2 cc.1.1 cc.1.2 cc.2

theorem simGameAd_iff (b : Bool)
    (x : ((Coins nfKeyBytes × Coins rBytes × CI) × (Coins nfKeyBytes × Coins rBytes × CI)) ×
      (Fin n → CR)) :
    simGameAd A simI simR b x ↔
      reductionAd A simI simR b (regroup x).2 (prfReal A.base.ci (regroup x).1) := by
  unfold simGameAd gameAd
  rw [viewAd_redSim A simR b _ _ _ rfl rfl]
  unfold reductionAd hviewAd prfReal regroup issSim
  simp only [Equiv.coe_fn_mk]

theorem prf_hopAd [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εprf : ℝ}
    (hprf : ∀ cc, prfAdv A.base.ci (reductionAd (n := n) A simI simR b cc) ≤ εprf) :
    |pr _ (simGameAd (n := n) A simI simR b) -
        pr ((PTape × Table) × ((CI × CI) × (Fin n → CR)))
          (fun x => reductionAd A simI simR b x.2 (prfIdeal A.base.ci x.1))| ≤ εprf := by
  have e : pr _ (simGameAd (n := n) A simI simR b) = pr (PTape × ((CI × CI) × (Fin n → CR)))
      (fun y => reductionAd A simI simR b y.2 (prfReal A.base.ci y.1)) := by
    rw [← pr_equiv regroup.symm (simGameAd A simI simR b)]
    exact pr_congr fun y =>
      (simGameAd_iff A simI simR b (regroup.symm y)).trans (by rw [Equiv.apply_symm_apply])
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun cc => hprf cc

/-! ## The ideal worlds coincide: a table-dependent involution -/

/-- A uniform nullifier table as byte lists. -/
def tbl (F : Table) : Bool → Coins ctxBytes → Bytes := fun c ctx => List.ofFn (F c ctx)

/-- **One simulated answer under the swapped table**: if the swap pattern `W` has `q`'s flag at
`q`'s context, world `¬b` on `swapF W F` answers `q` as world `b` on `F`. -/
theorem ySim_swapF (B : Adversary 0) (b : Bool) (W : Coins ctxBytes → Bool) (F : Table) (q : Query)
    (hW : W q.ctxRed = q.w) (c : CR) :
    ySim B simR (!b) (tbl (swapF W F)) q c = ySim B simR b (tbl F) q c := by
  unfold ySim tbl swapF who
  rw [hW]
  cases b <;> cases q.i <;> cases q.w <;> rfl

/-- **The swap of a whole adaptive run.** For any queries `nx` and any rule `vd` that implies the
context rule, the run in world `b` on table `F` and the run in world `¬b` on `swapF W F`, with `W`
the swap pattern of the first run, coincide. -/
theorem run_swapF (B : Adversary 0) (nx : Hist → Query) (vd : Hist → Query → Bool)
    (hvd : ∀ H q, vd H q = true → ctxOk H q = true) (b : Bool) (F : Table) (cs : Fin n → CR) :
    interact nx vd refused (List.ofFn fun j q => ySim B simR (!b)
        (tbl (swapF (firstFlag (interact nx vd refused
          (List.ofFn fun j q => ySim B simR b (tbl F) q (cs j)) [])) F)) q (cs j)) [] =
      interact nx vd refused (List.ofFn fun j q => ySim B simR b (tbl F) q (cs j)) [] := by
  symm
  refine interact_congr_of nx vd refused
    (fun q => firstFlag (interact nx vd refused
      (List.ofFn fun j q => ySim B simR b (tbl F) q (cs j)) []) q.ctxRed = q.w) _ _
    (fun j q hq => (ySim_swapF simR B b _ F q hq (cs j)).symm) _ fun H' y hp hv =>
      firstFlag_of_prefix hp (hvd _ _ hv)

/-- **The two ideal worlds have the same law**, for any adaptive run on the uniform table: the
experiment `G z (run_b)` on `Table × Z`, where the run reads the table only through the simulated
answers and its rule implies the context rule. -/
theorem pr_run_swap {Z : Type} [Fintype Z] (B : Adversary 0) (nx : Z → Hist → Query)
    (vd : Z → Hist → Query → Bool) (hvd : ∀ z H q, vd z H q = true → ctxOk H q = true)
    (cs : Z → Fin n → CR) (G : Z → Hist → Prop) :
    pr (Table × Z) (fun y => G y.2 (interact (nx y.2) (vd y.2) refused
        (List.ofFn fun j q => ySim B simR false (tbl y.1) q (cs y.2 j)) [])) =
      pr (Table × Z) (fun y => G y.2 (interact (nx y.2) (vd y.2) refused
        (List.ofFn fun j q => ySim B simR true (tbl y.1) q (cs y.2 j)) [])) := by
  let run : Bool → Table × Z → Hist := fun b y => interact (nx y.2) (vd y.2) refused
    (List.ofFn fun j q => ySim B simR b (tbl y.1) q (cs y.2 j)) []
  let sw : Bool → Table × Z → Table × Z := fun b y => (swapF (firstFlag (run b y)) y.1, y.2)
  have hrun (b : Bool) (y : Table × Z) : run (!b) (sw b y) = run b y :=
    run_swapF simR B (nx y.2) (vd y.2) (hvd y.2) b y.1 (cs y.2)
  have hinv (b : Bool) (y : Table × Z) : sw (!b) (sw b y) = y := by
    have h1 : firstFlag (run (!b) (sw b y)) = firstFlag (run b y) := by rw [hrun]
    show (swapF (firstFlag (run (!b) (sw b y))) (swapF (firstFlag (run b y)) y.1), y.2) = y
    rw [h1, swapF_swapF]
  let e : Table × Z ≃ Table × Z := ⟨sw true, sw false, hinv true, hinv false⟩
  rw [← pr_equiv e]
  exact pr_congr fun y => by
    show G y.2 (run false (sw true y)) ↔ G y.2 (run true y)
    rw [← hrun true y]
    rfl

/-- The ideal game, with the table as the first coordinate. -/
def idealGameAd (b : Bool) (y : Table × (PTape × ((CI × CI) × (Fin n → CR)))) : Prop :=
  reductionAd A simI simR b y.2.2 (prfIdeal A.base.ci (y.2.1, y.1))

theorem pr_idealGameAd [Fintype CI] [Fintype CR] (b : Bool) :
    pr ((PTape × Table) × ((CI × CI) × (Fin n → CR)))
        (fun x => reductionAd A simI simR b x.2 (prfIdeal A.base.ci x.1)) =
      pr _ (idealGameAd (n := n) A simI simR b) := by
  let e : Table × (PTape × ((CI × CI) × (Fin n → CR))) ≃
      (PTape × Table) × ((CI × CI) × (Fin n → CR)) :=
    { toFun := fun y => ((y.2.1, y.1), y.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-- **After the PRF hop the worlds coincide**, for adaptive queries. -/
theorem idealGameAd_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGameAd (n := n) A simI simR false) = pr _ (idealGameAd (n := n) A simI simR true) := by
  let t₀ : PTape → Bytes := fun p => ucom (List.ofFn p.1.1) A.base.ci (List.ofFn p.1.2)
  let t₁ : PTape → Bytes := fun p => ucom (List.ofFn p.2.1) A.base.ci (List.ofFn p.2.2)
  let q₀ : PTape × ((CI × CI) × (Fin n → CR)) → Bytes := fun z =>
    t₀ z.1 ++ simI ⟨t₀ z.1, A.base.ci⟩ z.2.1.1
  let q₁ : PTape × ((CI × CI) × (Fin n → CR)) → Bytes := fun z =>
    t₁ z.1 ++ simI ⟨t₁ z.1, A.base.ci⟩ z.2.1.2
  have hv (z : PTape × ((CI × CI) × (Fin n → CR))) (H : Hist) (q : Query)
      (h : validT A (q₀ z) (q₁ z) (t₀ z.1) (t₁ z.1) H q = true) : ctxOk H q = true := by
    unfold validT at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  exact pr_run_swap simR A.base (fun z => A.next (q₀ z) (q₁ z))
    (fun z => validT A (q₀ z) (q₁ z) (t₀ z.1) (t₁ z.1)) hv (fun z => z.2.2)
    (fun z Hs => A.guess (q₀ z) (q₁ z) (bif finT A.base (q₀ z) (q₁ z) (t₀ z.1) (t₁ z.1) false &&
      finT A.base (q₀ z) (q₁ z) (t₀ z.1) (t₁ z.1) true then some Hs else none))

/-! ## Issuer hiding and unlinkability with adaptive redemption queries -/

/-- **Theorem U5(a) with adaptive redemption queries.** If the unbound issuance and redemption
proofs are `εI`- and `εR`-zero-knowledge and every reduction `reductionAd A simI simR b cc` has PRF
advantage at most `εprf`, then for every adversary playing all Anchors and the Moderator, choosing
each of its `n` redemption queries (token, swap flag, Anchor Set, context, digest) after seeing the
answers to the earlier ones, the acceptance probabilities in the two worlds differ by at most
`4εI + 2n·εR + 2εprf`. -/
theorem anonymityAd [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (PI : NIZK IssueInstance)
    (PR : NIZK RedeemInstance) {εI εR εprf : ℝ} (hεR : 0 ≤ εR)
    (hI : ZeroKnowledge IssueRelW (proveR PI) simI εI)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hprf : ∀ b cc, prfAdv A.base.ci (reductionAd (n := n) A simI simR b cc) ≤ εprf) :
    |pr _ (realGameAd A n PI PR false) - pr _ (realGameAd A n PI PR true)| ≤
      4 * εI + 2 * n * εR + 2 * εprf := by
  have hiss := issue_close A.base simI PI hI
  have hred := fun p hp hc => redeem_close A.base simR PR hεR hR p hp hc
  have hw (b : Bool) : |pr _ (realGameAd A n PI PR b) - pr _ (idealGameAd (n := n) A simI simR b)| ≤
      2 * εI + n * εR + εprf := by
    set p0 := pr _ (realGameAd A n PI PR b)
    set p1 := pr _ (gameAd (n := n) A b (issSim A.base simI) (issReal A.base PI) (redReal A.base PR))
    set p2 := pr _ (gameAd (n := n) A b (issSim A.base simI) (issSim A.base simI) (redReal A.base PR))
    set p3 := pr _ (simGameAd (n := n) A simI simR b)
    set p4 := pr _ (idealGameAd (n := n) A simI simR b)
    have h1 : |p0 - p1| ≤ εI := gameAd_hop₀ A b (issReal A.base PI) (redReal A.base PR) hiss
    have h2 : |p1 - p2| ≤ εI := gameAd_hop₁ A b (issSim A.base simI) (redReal A.base PR) hiss
    have h3 : |p2 - p3| ≤ n * εR :=
      gameAd_hopRed A b (issSim_wf A.base simI) (issSim_wf A.base simI) hred
    have h4 : |p3 - p4| ≤ εprf := by
      have := prf_hopAd A simI simR b (hprf b)
      rwa [pr_idealGameAd] at this
    have := abs_sub_le p0 p1 p4
    have := abs_sub_le p1 p2 p4
    have := abs_sub_le p2 p3 p4
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGameAd_eq] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (idealGameAd (n := n) A simI simR true)) _
    _ ≤ (2 * εI + n * εR + εprf) + (2 * εI + n * εR + εprf) :=
        add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εI + 2 * n * εR + 2 * εprf := by ring

end VoleMole.Privacy.MoussakaUnbound
