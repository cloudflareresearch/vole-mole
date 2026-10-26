import VoleMole.Privacy.Basic
import VoleMole.Spec.MoussakaUnbound

/-!
# Unbound Moussaka: issuer hiding and unlinkability on the executable spec

Theorem U5(a) of `lean/docs/security/moussaka-unbound.md` as a game on `Spec/MoussakaUnbound.lean`
(`issueRequest`, `finalizeIssue`, `redeemRequest` with the C++ `find_issuer`), with the seed
expansions' outputs `(nf_key, r, ρ_iss)` and each `ρ_red` uniform.

**Game.** The adversary plays every Anchor and the Moderator. It chooses `ctx_iss` and the two
issuing keys `pk false`, `pk true` (arbitrary; equal keys give unlinkability, different keys issuer
hiding), sees both Clients' issuance requests and answers them. Then, from the two requests, it
chooses `n` redemption queries `(i, w, S, ctx_red, cd)`: query `j` is answered by token
`i ⊕ (b ∧ w)` in world `b`, redeemed under Anchor Set `S`, context `ctx_red` and digest `cd`. The
swap flag `w = false` asks for token `i` in both worlds; `w = true` asks for token `i` in world 0
and for the other token in world 1. So a `w = true` query tests issuance–redemption unlinkability
and issuer hiding, and a `w = false` query in one context with a `w = true` query in another tests
unlinkability of redemptions across contexts. All redemptions happen only if:

* both tokens finalized, and both are redeemable (`find_issuer` succeeds) in every queried Anchor
  Set (otherwise a refusal could depend on the token, as in the base note §6);
* **the context rule**: queries with the same `ctx_red` carry the same swap flag. Two redemptions
  of one token in one context reveal the same nullifier, so without the rule the worlds are
  trivially distinguishable (the note's §0, last row).

Otherwise every query is refused. The adversary's guess sees the issuance requests and all `n`
redemption requests. The queries are chosen after issuance and before any redemption; adaptive
redemption queries are not modelled (the note covers them by lazy sampling, on paper).

**Assumptions.**
* Zero knowledge of both unbound proof systems (`ZeroKnowledge` for `IssueRelW` and `RedeemRelW`,
  errors `εI`, `εR`), against distinguishers that may know the witness. As for the bound relations,
  on `main` (CRT masks from the witness) no efficient simulator satisfies this; with dedicated label
  rows it is `lean/docs/zk.md`'s theorem (the note's UF6).
* `Derive` is a PRF with the commitments leaked, in the two-key form of the note's §3.2
  (`prfAdv`): given `t₀ = UCom(k₀, ctx_iss, r₀)`, `t₁ = UCom(k₁, ctx_iss, r₁)`, distinguish the
  table `c, ctx ↦ Derive(k_c, ctx)` from a uniformly random table. It is a computational assumption
  on Keccak-p[800], so it is stated for the explicit reductions `reduction A simI simR b cc` (the
  adversary with the simulator coins fixed), which read the table only at the queried contexts.

## Results

* `issue_close`, `redeem_close`: one real and one simulated proof are close as protocol messages.
* `close_pi`: `n` independent hops of `ε` each are `n·ε`-close (all redemption proofs at once).
* `simGame_iff`: with all proofs simulated, the view is a function `hview` of the commitments, the
  table of nullifiers and the simulator coins: the openings and keys enter nothing else.
* `idealGame_eq`: after the PRF hop (a uniform table), the worlds coincide exactly: the involution
  `swapF` that exchanges the two rows of the table on the contexts with swap flag `true` maps one
  world to the other.
* **`anonymity`**: `|Pr[A accepts in world 0] − Pr[A accepts in world 1]| ≤ 4εI + 2n·εR + 2εprf`.
-/

open Finset

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## `n` hops at once -/

/-- The two halves of a tape `Fin (n+1) → T`. -/
def consE (T : Type*) (n : ℕ) : T × (Fin n → T) ≃ (Fin (n + 1) → T) where
  toFun p := Fin.cons p.1 p.2
  invFun τ := (τ 0, Fin.tail τ)
  left_inv p := by simp
  right_inv τ := by simp

theorem vec_consE {T γ : Type*} {n : ℕ} (X : Fin (n + 1) → T → γ) (p : T × (Fin n → T)) :
    (fun j => X j (consE T n p j)) =
      Fin.cons (α := fun _ => γ) (X 0 p.1) (fun j => X j.succ (p.2 j)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [consE]

/-- **`n` hops of `ε` each**: if the `j`-th components are `ε`-close for every `j`, the vectors of
independent components are `n·ε`-close. -/
theorem close_pi {T T' γ : Type*} [Fintype T] [Nonempty T] [Fintype T'] [Nonempty T'] {ε : ℝ}
    (n : ℕ) :
    ∀ (X : Fin n → T → γ) (Y : Fin n → T' → γ), (∀ j, Close ε (X j) (Y j)) →
      Close (n * ε) (fun τ : Fin n → T => fun j => X j (τ j))
        (fun τ : Fin n → T' => fun j => Y j (τ j)) := by
  induction n with
  | zero =>
    intro X Y _
    have h1 : ∀ τ : Fin 0 → T, (fun j => X j (τ j)) = Fin.elim0 := fun τ => funext fun j => j.elim0
    have h2 : ∀ τ : Fin 0 → T', (fun j => Y j (τ j)) = Fin.elim0 := fun τ => funext fun j => j.elim0
    exact (close_const (le_of_eq (by simp)) _).congr h1 h2
  | succ n ih =>
    intro X Y h
    have ih' := ih (fun j => X j.succ) (fun j => Y j.succ) fun j => h j.succ
    let F : T × (Fin n → T) → (Fin (n+1) → γ) := fun p =>
      Fin.cons (α := fun _ => γ) (X 0 p.1) (fun j => X j.succ (p.2 j))
    let G : T' × (Fin n → T) → (Fin (n+1) → γ) := fun p =>
      Fin.cons (α := fun _ => γ) (Y 0 p.1) (fun j => X j.succ (p.2 j))
    let H : T' × (Fin n → T') → (Fin (n+1) → γ) := fun p =>
      Fin.cons (α := fun _ => γ) (Y 0 p.1) (fun j => Y j.succ (p.2 j))
    have a0 := close_equiv (γ := Fin (n+1) → γ) (consE T n) (fun τ : Fin (n + 1) → T => fun j => X j (τ j))
    have a : Close 0 F (fun τ : Fin (n + 1) → T => fun j => X j (τ j)) := by
      refine Close.congr a0 (fun p => ?_) (fun _ => rfl)
      exact (vec_consE X p).symm
    have b : Close ε F G := fun D =>
      abs_pr_prod_sub_le' (fun p : T × (Fin n → T) => D (F p)) (fun p : T' × (Fin n → T) => D (G p))
        fun v => h 0 (fun o => D (Fin.cons (α := fun _ => γ) o (fun j => X j.succ (v j))))
    have c : Close (n * ε) G H := fun D =>
      abs_pr_prod_sub_le (fun p : T' × (Fin n → T) => D (G p)) (fun p : T' × (Fin n → T') => D (H p))
        fun a => ih' (fun v => D (Fin.cons (α := fun _ => γ) (Y 0 a) v))
    have d0 := close_equiv (γ := Fin (n+1) → γ) (consE T' n) (fun τ : Fin (n + 1) → T' => fun j => Y j (τ j))
    have d : Close 0 H (fun τ : Fin (n + 1) → T' => fun j => Y j (τ j)) := by
      refine Close.congr d0 (fun p => ?_) (fun _ => rfl)
      exact (vec_consE Y p).symm
    refine (a.symm.trans (b.trans (c.trans d))).mono (le_of_eq ?_)
    push_cast; ring

/-! ## The spec with the seed expansions' outputs given -/

/-- `issueRequest` with the output `(nf_key, r, ρ_iss)` of the seed expansion as arguments. -/
def issueRequestOf (PI : NIZK IssueInstance) (ctxIss k r rho : Bytes) : PendingToken × Bytes :=
  let t := ucom k ctxIss r
  (⟨k, r, ctxIss, t⟩, t ++ PI.prove (encodeIssueWitness k ctxIss r) ⟨t, ctxIss⟩ rho)

theorem issueRequest_eq (PI : NIZK IssueInstance) (ctxIss seed : Bytes) :
    issueRequest PI ctxIss seed =
      issueRequestOf PI ctxIss (expandIssueSeed seed).1 (expandIssueSeed seed).2.1
        (expandIssueSeed seed).2.2 := rfl

/-- `redeemRequest` with `ρ_red` as an argument. -/
def redeemRequestOf (PR : NIZK RedeemInstance) (tok : Token) (S : AnchorSet)
    (ctxIss ctxRed cd rho : Bytes) : Except Error Bytes :=
  match findIssuer S (ucom tok.k ctxIss tok.r) tok.s with
  | none => .error .invalidToken
  | some i =>
    .ok (derive tok.k ctxRed ++ PR.prove (encodeRedeemWitness tok.k ctxIss ctxRed tok.r tok.s i)
      ⟨S.keys, derive tok.k ctxRed, ctxIss, ctxRed, cd⟩ rho)

theorem redeemRequest_eq (PR : NIZK RedeemInstance) (tok : Token) (S : AnchorSet)
    (ctxIss ctxRed cd seed : Bytes) :
    redeemRequest PR tok S ctxIss ctxRed cd seed =
      redeemRequestOf PR tok S ctxIss ctxRed cd (expandRedeemSeed seed) := rfl

/-- The prover of a `NIZK` with its randomness `ρ` uniform (16 bytes). -/
def proveR {I : Type} (Z : NIZK I) (x : I) (w : Bytes) (ρ : Coins proveSeedBytes) : Bytes :=
  Z.prove w x (List.ofFn ρ)

/-! ## The game -/

/-- A redemption query: token `i` (in world 0), swap flag `w`, Anchor Set, context, digest. -/
structure Query where
  i : Bool
  w : Bool
  anchors : AnchorSet
  ctxRed : Coins ctxBytes
  cd : Bytes

/-- The colluding adversary with `n` redemption queries. -/
structure Adversary (n : ℕ) where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  queries : Bytes → Bytes → Fin n → Query
  guess : Bytes → Bytes → Option (Fin n → Except Error Bytes) → Prop

/-- The token that answers query `q` in world `b`. -/
def who (b : Bool) (q : Query) : Bool := xor q.i (b && q.w)

/-- The context rule: queries in the same context carry the same swap flag. -/
def ctxRule {n : ℕ} (qs : Fin n → Query) : Bool :=
  decide (∀ j j', (qs j).ctxRed = (qs j').ctxRed → (qs j).w = (qs j').w)

variable {n : ℕ} (A : Adversary n)

def Adversary.ci : Bytes := List.ofFn A.ctxIss

/-- Client `c`'s token after `finalize_issue` on the adversary's response. -/
def tok (i₀ i₁ : PendingToken × Bytes) (c : Bool) : Option Token :=
  finalizeIssue (A.pk c) (bif c then i₁ else i₀).1 (List.ofFn (A.respond i₀.2 i₁.2 c))

/-- The token, or a well-formed dummy when finalization failed (then nothing is redeemed). -/
def tokD (i₀ i₁ : PendingToken × Bytes) (c : Bool) : Token :=
  (tok A i₀ i₁ c).getD
    ⟨List.replicate nfKeyBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- The Client's `find_issuer` succeeds for token `t` in `S`. -/
def redeemable (ci : Bytes) (t : Token) (S : AnchorSet) : Bool :=
  (findIssuer S (ucom t.k ci t.r) t.s).isSome

/-- The game's rule: both tokens finalized, both redeemable in every queried set, and the context
rule. -/
def allOk (i₀ i₁ : PendingToken × Bytes) : Bool :=
  (tok A i₀ i₁ false).isSome && (tok A i₀ i₁ true).isSome &&
    decide (∀ j c, redeemable A.ci (tokD A i₀ i₁ c) (A.queries i₀.2 i₁.2 j).anchors = true) &&
    ctxRule (A.queries i₀.2 i₁.2)

/-- Where a redemption is asked: the token, the Anchor Set, the context and the digest. -/
structure RedeemPt where
  tok : Token
  anchors : AnchorSet
  ctxRed : Bytes
  cd : Bytes

/-- Query `j` in world `b`. -/
def pt (b : Bool) (i₀ i₁ : PendingToken × Bytes) (j : Fin n) : RedeemPt :=
  let q := A.queries i₀.2 i₁.2 j
  ⟨tokD A i₀ i₁ (who b q), q.anchors, List.ofFn q.ctxRed, q.cd⟩

/-- The adversary's guess from the issuance outputs and the redemption requests. -/
def post (i₀ i₁ : PendingToken × Bytes) (ys : Fin n → Except Error Bytes) : Prop :=
  A.guess i₀.2 i₁.2 (bif allOk A i₀ i₁ then some ys else none)

/-- The view in world `b`, given the issuance outputs and the redemption provers. -/
def view (b : Bool) (i₀ i₁ : PendingToken × Bytes) (reds : Fin n → RedeemPt → Except Error Bytes) :
    Prop :=
  post A i₀ i₁ fun j => reds j (pt A b i₀ i₁ j)

/-- The game with the issuance slots drawn by `g₀ g₁` and every redemption by `g`. -/
def game {T₀ T₁ T : Type} (b : Bool) (g₀ : T₀ → PendingToken × Bytes)
    (g₁ : T₁ → PendingToken × Bytes) (g : T → RedeemPt → Except Error Bytes)
    (x : (T₀ × T₁) × (Fin n → T)) : Prop :=
  view A b (g₀ x.1.1) (g₁ x.1.2) fun j => g (x.2 j)

/-- A real issuance from `(nf_key, r, ρ_iss)`. -/
def issReal (PI : NIZK IssueInstance)
    (x : Coins nfKeyBytes × Coins rBytes × Coins proveSeedBytes) : PendingToken × Bytes :=
  issueRequestOf PI A.ci (List.ofFn x.1) (List.ofFn x.2.1) (List.ofFn x.2.2)

/-- A real redemption from `ρ_red`. -/
def redReal (PR : NIZK RedeemInstance) (ρ : Coins proveSeedBytes) (p : RedeemPt) :
    Except Error Bytes :=
  redeemRequestOf PR p.tok p.anchors A.ci p.ctxRed p.cd (List.ofFn ρ)

/-- **The real game** in world `b`. -/
def realGame (PI : NIZK IssueInstance) (PR : NIZK RedeemInstance) (b : Bool) :=
  game A b (issReal A PI) (issReal A PI) (redReal A PR)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)

/-- A simulated issuance from `(nf_key, r)` and simulator coins. -/
def issSim (x : Coins nfKeyBytes × Coins rBytes × CI) : PendingToken × Bytes :=
  let t := ucom (List.ofFn x.1) A.ci (List.ofFn x.2.1)
  (⟨List.ofFn x.1, List.ofFn x.2.1, A.ci, t⟩, t ++ simI ⟨t, A.ci⟩ x.2.2)

/-- A simulated redemption, with the Client's `find_issuer` unchanged. -/
def redSim (c : CR) (p : RedeemPt) : Except Error Bytes :=
  match findIssuer p.anchors (ucom p.tok.k A.ci p.tok.r) p.tok.s with
  | none => .error .invalidToken
  | some _ =>
    .ok (derive p.tok.k p.ctxRed ++
      simR ⟨p.anchors.keys, derive p.tok.k p.ctxRed, A.ci, p.ctxRed, p.cd⟩ c)

/-! ## One proof at a time -/

variable {T₀ T₁ T T₀' T₁' T' : Type} [Fintype T₀] [Fintype T₁] [Fintype T] [Fintype T₀']
  [Fintype T₁'] [Fintype T']

theorem game_hop₀ [Nonempty T₁] [Nonempty T] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₀' : T₀' → PendingToken × Bytes}
    (g₁ : T₁ → PendingToken × Bytes) (g : T → RedeemPt → Except Error Bytes)
    (h : Close ε g₀ g₀') :
    |pr _ (game A b g₀ g₁ g) - pr _ (game A b g₀' g₁ g)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le' _ _ fun x₁ =>
    h (fun o => view A b o (g₁ x₁) fun j => g (y j))

theorem game_hop₁ [Nonempty T₀] [Nonempty T] (b : Bool) {ε : ℝ}
    (g₀ : T₀ → PendingToken × Bytes) {g₁ : T₁ → PendingToken × Bytes}
    {g₁' : T₁' → PendingToken × Bytes} (g : T → RedeemPt → Except Error Bytes)
    (h : Close ε g₁ g₁') :
    |pr _ (game A b g₀ g₁ g) - pr _ (game A b g₀ g₁' g)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le _ _ fun x₀ =>
    h (fun o => view A b (g₀ x₀) o fun j => g (y j))

/-- Issuance outputs whose pending tokens have a 16-byte key and opening. -/
def WellFormed {T : Type} (g : T → PendingToken × Bytes) : Prop :=
  ∀ x, (g x).1.k.length = nfKeyBytes ∧ (g x).1.r.length = rBytes

/-- A well-formed token: the lengths of the C++ `std::array` types. -/
def tokWF (t : Token) : Prop :=
  t.k.length = nfKeyBytes ∧ t.r.length = rBytes ∧ t.s.length = uovN

theorem tokD_wf {i₀ i₁ : PendingToken × Bytes}
    (h₀ : i₀.1.k.length = nfKeyBytes ∧ i₀.1.r.length = rBytes)
    (h₁ : i₁.1.k.length = nfKeyBytes ∧ i₁.1.r.length = rBytes) (c : Bool) :
    tokWF (tokD A i₀ i₁ c) := by
  unfold tokD tok finalizeIssue
  split_ifs
  · exact ⟨by cases c <;> exact (by assumption : _ ∧ _).1, by cases c <;>
      exact (by assumption : _ ∧ _).2, List.length_ofFn⟩
  · exact ⟨List.length_replicate, List.length_replicate, List.length_replicate⟩

/-- **All redemption proofs at once**: `n` hops. -/
theorem game_hopRed [Nonempty T₀] [Nonempty T₁] [Nonempty T] [Nonempty T'] (b : Bool) {ε : ℝ}
    {g₀ : T₀ → PendingToken × Bytes} {g₁ : T₁ → PendingToken × Bytes}
    (h₀ : WellFormed g₀) (h₁ : WellFormed g₁) {g : T → RedeemPt → Except Error Bytes}
    {g' : T' → RedeemPt → Except Error Bytes}
    (h : ∀ p : RedeemPt, tokWF p.tok → p.ctxRed.length = ctxBytes →
      Close ε (fun t => g t p) (fun t => g' t p)) :
    |pr _ (game A b g₀ g₁ g) - pr _ (game A b g₀ g₁ g')| ≤ n * ε :=
  abs_pr_prod_sub_le _ _ fun x =>
    close_pi n (fun j t => g t (pt A b (g₀ x.1) (g₁ x.2) j))
      (fun j t => g' t (pt A b (g₀ x.1) (g₁ x.2) j))
      (fun j => h _ (tokD_wf A (h₀ _) (h₁ _) _) (by simp [pt, ctxBytes]))
      (fun ys => post A (g₀ x.1) (g₁ x.2) ys)

theorem issReal_wf (PI : NIZK IssueInstance) : WellFormed (issReal A PI) := fun x => by
  simp [issReal, issueRequestOf, rBytes, nfKeyBytes]

theorem issSim_wf : WellFormed (issSim A simI) := fun x => by simp [issSim, rBytes, nfKeyBytes]

/-- The issuance relation on well-formed instances (`ctx_iss` of 16 bytes). -/
def IssueRelW (x : IssueInstance) (w : Bytes) : Prop := IssueRel x w ∧ x.ctxIss.length = ctxBytes

/-- The redemption relation on well-formed instances: a validated Anchor Set (at most 64 keys),
`nf` of 24 bytes, contexts of 16. -/
def RedeemRelW (x : RedeemInstance) (w : Bytes) : Prop :=
  RedeemRel x w ∧ x.anchors.length ≤ maxAnchors ∧ x.nf.length = nfBytes ∧
    x.ctxIss.length = ctxBytes ∧ x.ctxRed.length = ctxBytes

/-- **One issuance proof.** -/
theorem issue_close [Fintype CI] (PI : NIZK IssueInstance) {εI : ℝ}
    (hI : ZeroKnowledge IssueRelW (proveR PI) simI εI) :
    Close εI (issReal A PI) (issSim A simI) := by
  refine Close.congr (Close.prod_right (X := fun k y => issReal A PI (k, y))
    (Y := fun k y => issSim A simI (k, y)) fun k => Close.congr
      (Close.prod_right (X := fun r ρ => issReal A PI (k, r, ρ))
        (Y := fun r c => issSim A simI (k, r, c)) fun r => ?_) (fun _ => rfl) (fun _ => rfl))
    (fun _ => rfl) (fun _ => rfl)
  have hrel : IssueRelW ⟨ucom (List.ofFn k) A.ci (List.ofFn r), A.ci⟩
      (encodeIssueWitness (List.ofFn k) A.ci (List.ofFn r)) :=
    ⟨⟨_, _, List.length_ofFn, List.length_ofFn, rfl, rfl⟩, by simp [Adversary.ci, ctxBytes]⟩
  exact (hI _ _ hrel).map fun π =>
    ((⟨List.ofFn k, List.ofFn r, A.ci, ucom (List.ofFn k) A.ci (List.ofFn r)⟩ : PendingToken),
      ucom (List.ofFn k) A.ci (List.ofFn r) ++ π)

/-- **One redemption proof.** At every redemption point with a well-formed token and a 16-byte
context, a real and a simulated redemption are `εR`-close. -/
theorem redeem_close [Fintype CR] [Nonempty CR] (PR : NIZK RedeemInstance) {εR : ℝ} (hε : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) (p : RedeemPt) (hp : tokWF p.tok)
    (hc : p.ctxRed.length = ctxBytes) :
    Close εR (fun ρ => redReal A PR ρ p) (fun c => redSim A simR c p) := by
  intro D
  unfold redReal redSim redeemRequestOf
  cases hf : findIssuer p.anchors (ucom p.tok.k A.ci p.tok.r) p.tok.s with
  | none => exact close_const hε _ D
  | some i =>
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    have hrel : RedeemRelW ⟨p.anchors.keys, derive p.tok.k p.ctxRed, A.ci, p.ctxRed, p.cd⟩
        (encodeRedeemWitness p.tok.k A.ci p.ctxRed p.tok.r p.tok.s i) :=
      ⟨⟨_, _, _, i, pk, hp.1, hp.2.1, hp.2.2, hk, rfl, he, rfl⟩, p.anchors.valid.2.1,
        length_derive _ _, by simp [Adversary.ci, ctxBytes], hc⟩
    exact (hR _ _ hrel).map
      (fun π => (Except.ok (derive p.tok.k p.ctxRed ++ π) : Except Error Bytes)) D

/-! ## All proofs simulated: the view reads the nullifiers only through a table -/

/-- The adversary's response to Client `c`. -/
def resp (q₀ q₁ : Bytes) (c : Bool) : Bytes := List.ofFn (A.respond q₀ q₁ c)

/-- `finalize_issue` succeeds for Client `c`, checked against `t_c`. -/
def finT (q₀ q₁ t₀ t₁ : Bytes) (c : Bool) : Bool :=
  decide ((A.pk c).eval (resp A q₀ q₁ c) = bif c then t₁ else t₀)

/-- Client `c`'s `find_issuer` succeeds in `S`, checked against `t_c`. -/
def okT (q₀ q₁ t₀ t₁ : Bytes) (c : Bool) (S : AnchorSet) : Bool :=
  (findIssuer S (bif c then t₁ else t₀) (resp A q₀ q₁ c)).isSome

/-- The game's rule, as a function of the requests and the commitments. -/
def allOkT (q₀ q₁ t₀ t₁ : Bytes) : Bool :=
  finT A q₀ q₁ t₀ t₁ false && finT A q₀ q₁ t₀ t₁ true &&
    decide (∀ j c, okT A q₀ q₁ t₀ t₁ c (A.queries q₀ q₁ j).anchors = true) &&
    ctxRule (A.queries q₀ q₁)

/-- A simulated redemption request for query `q` in world `b`, with the nullifier read from the
table `O` at the answering token and the query's context. -/
def ySim (b : Bool) (O : Bool → Coins ctxBytes → Bytes) (q : Query) (c : CR) : Except Error Bytes :=
  .ok (O (who b q) q.ctxRed ++
    simR ⟨q.anchors.keys, O (who b q) q.ctxRed, A.ci, List.ofFn q.ctxRed, q.cd⟩ c)

/-- The view with all proofs simulated, as a function of the commitments, the nullifier table and
the simulator coins. -/
def hview (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes) (cI₀ cI₁ : CI)
    (cs : Fin n → CR) : Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.ci⟩ cI₁
  A.guess q₀ q₁ (bif allOkT A q₀ q₁ t₀ t₁ then
    some (fun j => ySim A simR b O (A.queries q₀ q₁ j) (cs j)) else none)

theorem tok_of_fin (i₀ i₁ : PendingToken × Bytes) (c : Bool) :
    tok A i₀ i₁ c = if finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c then
      some ⟨(bif c then i₁ else i₀).1.k, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩
    else none := by
  have ht : (bif c then i₁ else i₀).1.t = bif c then i₁.1.t else i₀.1.t := by cases c <;> rfl
  unfold tok finT finalizeIssue resp
  rw [ht]
  by_cases h : (A.pk c).eval (List.ofFn (A.respond i₀.2 i₁.2 c)) = bif c then i₁.1.t else i₀.1.t
  · simp only [h, decide_true, ↓reduceIte]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **With simulated redemptions, the view reads the issuance outputs only through the requests,
the commitments and the nullifier table `c, ctx ↦ Derive(k_c, ctx)`** (for honest pending tokens,
`t = UCom(k, ctx_iss, r)`). -/
theorem post_redSim (b : Bool) (i₀ i₁ : PendingToken × Bytes) (cs : Fin n → CR)
    (h₀ : i₀.1.t = ucom i₀.1.k A.ci i₀.1.r) (h₁ : i₁.1.t = ucom i₁.1.k A.ci i₁.1.r) :
    post A i₀ i₁ (fun j => redSim A simR (cs j) (pt A b i₀ i₁ j)) ↔
      A.guess i₀.2 i₁.2 (bif allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t then
        some (fun j => ySim A simR b
          (fun c ctx => bif c then derive i₁.1.k (List.ofFn ctx) else derive i₀.1.k (List.ofFn ctx))
          (A.queries i₀.2 i₁.2 j) (cs j)) else none) := by
  have htok (c : Bool) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD A i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.k, (bif c then i₁ else i₀).1.r, resp A i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hcom (c : Bool) : ucom (bif c then i₁ else i₀).1.k A.ci (bif c then i₁ else i₀).1.r =
      bif c then i₁.1.t else i₀.1.t := by
    cases c
    · exact h₀.symm
    · exact h₁.symm
  have hred (c : Bool) (S : AnchorSet) (hc : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      redeemable A.ci (tokD A i₀ i₁ c) S = okT A i₀.2 i₁.2 i₀.1.t i₁.1.t c S := by
    unfold redeemable okT
    rw [htok c hc]
    simp only [hcom]
  have hall : allOk A i₀ i₁ = allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t := by
    unfold allOk allOkT
    rw [tok_of_fin A i₀ i₁ false, tok_of_fin A i₀ i₁ true]
    cases e₀ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t false
    · simp
    · cases e₁ : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t true
      · simp
      · have : ∀ j c, redeemable A.ci (tokD A i₀ i₁ c) (A.queries i₀.2 i₁.2 j).anchors =
            okT A i₀.2 i₁.2 i₀.1.t i₁.1.t c (A.queries i₀.2 i₁.2 j).anchors := fun j c => by
          cases c
          · exact hred false _ e₀
          · exact hred true _ e₁
        simp only [this, Option.isSome_some, ↓reduceIte, Bool.true_and]
  unfold post
  rw [hall]
  refine iff_of_eq (congrArg _ ?_)
  cases hC : allOkT A i₀.2 i₁.2 i₀.1.t i₁.1.t
  · rfl
  · unfold allOkT at hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    obtain ⟨⟨⟨f₀, f₁⟩, hok⟩, -⟩ := hC
    have hf (c : Bool) : finT A i₀.2 i₁.2 i₀.1.t i₁.1.t c = true := by cases c <;> assumption
    simp only [Bool.cond_true, Option.some.injEq]
    funext j
    have hr : redeemable A.ci (tokD A i₀ i₁ (who b (A.queries i₀.2 i₁.2 j)))
        (A.queries i₀.2 i₁.2 j).anchors = true := by
      rw [hred _ _ (hf _)]; exact hok j _
    unfold redeemable at hr
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hr
    unfold redSim ySim
    simp only [pt]
    rw [hi]
    simp only [htok _ (hf _)]
    cases who b (A.queries i₀.2 i₁.2 j) <;> rfl

/-- The game with every proof simulated. -/
def simGame (b : Bool) := game A b (issSim A simI) (issSim A simI) (redSim A simR)

/-! ## The PRF hop -/

/-- The keys and openings of the two tokens. -/
abbrev PTape := (Coins nfKeyBytes × Coins rBytes) × (Coins nfKeyBytes × Coins rBytes)

/-- A nullifier table: one uniform 24-byte value per token and context. -/
abbrev Table := Bool → Coins ctxBytes → Coins nfBytes

/-- The real PRF experiment: both commitments and the table `c, ctx ↦ Derive(k_c, ctx)`. -/
def prfReal (ci : Bytes) (x : PTape) : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes) :=
  (ucom (List.ofFn x.1.1) ci (List.ofFn x.1.2), ucom (List.ofFn x.2.1) ci (List.ofFn x.2.2),
    fun c ctx => bif c then derive (List.ofFn x.2.1) (List.ofFn ctx)
      else derive (List.ofFn x.1.1) (List.ofFn ctx))

/-- The ideal PRF experiment: both commitments and a uniform table. -/
def prfIdeal (ci : Bytes) (x : PTape × Table) : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes) :=
  (ucom (List.ofFn x.1.1.1) ci (List.ofFn x.1.1.2), ucom (List.ofFn x.1.2.1) ci (List.ofFn x.1.2.2),
    fun c ctx => List.ofFn (x.2 c ctx))

/-- **The PRF advantage** of `D` (`security/moussaka-unbound.md` §3.2, `Adv^prf-t_2`). -/
noncomputable def prfAdv (ci : Bytes) (D : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes) → Prop) :
    ℝ :=
  |pr PTape (fun x => D (prfReal ci x)) - pr (PTape × Table) (fun x => D (prfIdeal ci x))|

/-- **The reduction to the PRF**: the adversary, with the simulator coins fixed, run on the
commitments and the table it is given. -/
def reduction (b : Bool) (cc : (CI × CI) × (Fin n → CR))
    (z : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes)) : Prop :=
  hview A simI simR b z.1 z.2.1 z.2.2 cc.1.1 cc.1.2 cc.2

/-- The game after the PRF hop: the nullifiers are read from a uniform table. -/
def idealGame (b : Bool) (x : (PTape × Table) × ((CI × CI) × (Fin n → CR))) : Prop :=
  reduction A simI simR b x.2 (prfIdeal A.ci x.1)

/-- Regroup the simulated game's tape as the PRF tape and the simulator coins. -/
def regroup :
    ((Coins nfKeyBytes × Coins rBytes × CI) × (Coins nfKeyBytes × Coins rBytes × CI)) ×
        (Fin n → CR) ≃ PTape × ((CI × CI) × (Fin n → CR)) where
  toFun x := (((x.1.1.1, x.1.1.2.1), (x.1.2.1, x.1.2.2.1)), ((x.1.1.2.2, x.1.2.2.2), x.2))
  invFun y := (((y.1.1.1, y.1.1.2, y.2.1.1), (y.1.2.1, y.1.2.2, y.2.1.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem simGame_iff (b : Bool)
    (x : ((Coins nfKeyBytes × Coins rBytes × CI) × (Coins nfKeyBytes × Coins rBytes × CI)) ×
      (Fin n → CR)) :
    simGame A simI simR b x ↔ reduction A simI simR b (regroup x).2 (prfReal A.ci (regroup x).1) := by
  unfold simGame game view
  rw [post_redSim A simR b _ _ _ rfl rfl]
  unfold reduction hview prfReal regroup issSim
  simp only [Equiv.coe_fn_mk]

theorem prf_hop [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εprf : ℝ}
    (hprf : ∀ cc, prfAdv A.ci (reduction A simI simR b cc) ≤ εprf) :
    |pr _ (simGame A simI simR b) - pr _ (idealGame A simI simR b)| ≤ εprf := by
  have e : pr _ (simGame A simI simR b) = pr (PTape × ((CI × CI) × (Fin n → CR)))
      (fun y => reduction A simI simR b y.2 (prfReal A.ci y.1)) := by
    rw [← pr_equiv regroup.symm (simGame A simI simR b)]
    exact pr_congr fun y =>
      (simGame_iff A simI simR b (regroup.symm y)).trans (by rw [Equiv.apply_symm_apply])
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun cc => hprf cc

/-! ## The ideal worlds coincide -/

/-- The swap pattern of a query list: context `ctx` is swapped iff some query in it has flag
`true` (under the context rule, all of them do). -/
def swapOf (qs : Fin n → Query) (ctx : Coins ctxBytes) : Bool :=
  decide (∃ j, (qs j).ctxRed = ctx ∧ (qs j).w = true)

/-- Exchange the two rows of the table on the swapped contexts. -/
def swapF (W : Coins ctxBytes → Bool) (F : Table) : Table := fun c ctx => F (xor c (W ctx)) ctx

theorem swapF_swapF (W : Coins ctxBytes → Bool) (F : Table) : swapF W (swapF W F) = F := by
  funext c ctx; simp [swapF]

/-- The swap pattern of the ideal game at tape `x`; it does not read the table. -/
def patOf (x : (PTape × Table) × ((CI × CI) × (Fin n → CR))) : Coins ctxBytes → Bool :=
  let t₀ := ucom (List.ofFn x.1.1.1.1) A.ci (List.ofFn x.1.1.1.2)
  let t₁ := ucom (List.ofFn x.1.1.2.1) A.ci (List.ofFn x.1.1.2.2)
  swapOf (A.queries (t₀ ++ simI ⟨t₀, A.ci⟩ x.2.1.1) (t₁ ++ simI ⟨t₁, A.ci⟩ x.2.1.2))

/-- The swap, as an involution of the ideal game's tape. -/
def swapT : (PTape × Table) × ((CI × CI) × (Fin n → CR)) ≃
    (PTape × Table) × ((CI × CI) × (Fin n → CR)) where
  toFun x := ((x.1.1, swapF (patOf A simI x) x.1.2), x.2)
  invFun x := ((x.1.1, swapF (patOf A simI x) x.1.2), x.2)
  left_inv x := by
    have : patOf A simI ((x.1.1, swapF (patOf A simI x) x.1.2), x.2) = patOf A simI x := rfl
    simp only [this, swapF_swapF]
  right_inv x := by
    have : patOf A simI ((x.1.1, swapF (patOf A simI x) x.1.2), x.2) = patOf A simI x := rfl
    simp only [this, swapF_swapF]

theorem swapOf_eq {qs : Fin n → Query} (h : ctxRule qs = true) (j : Fin n) :
    swapOf qs (qs j).ctxRed = (qs j).w := by
  unfold ctxRule at h
  simp only [decide_eq_true_eq] at h
  unfold swapOf
  cases hw : (qs j).w
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro j' hj' hw'
    rw [h j' j hj', hw] at hw'
    cases hw'
  · simp only [decide_eq_true_eq]
    exact ⟨j, rfl, hw⟩

/-- **After the PRF hop the worlds coincide**: world 1 at table `F` is world 0 at `swapF W F`, for
the swap pattern `W` of the queries, and `swapF W` is a bijection. -/
theorem idealGame_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGame A simI simR false) = pr _ (idealGame A simI simR true) := by
  rw [← pr_equiv (swapT A simI)]
  refine pr_congr fun x => ?_
  unfold idealGame reduction hview prfIdeal
  simp only [swapT, Equiv.coe_fn_mk]
  refine iff_of_eq (congrArg _ ?_)
  set t₀ := ucom (List.ofFn x.1.1.1.1) A.ci (List.ofFn x.1.1.1.2)
  set t₁ := ucom (List.ofFn x.1.1.2.1) A.ci (List.ofFn x.1.1.2.2)
  set q₀ := t₀ ++ simI ⟨t₀, A.ci⟩ x.2.1.1
  set q₁ := t₁ ++ simI ⟨t₁, A.ci⟩ x.2.1.2
  cases hC : allOkT A q₀ q₁ t₀ t₁
  · rfl
  · have hr : ctxRule (A.queries q₀ q₁) = true := by
      unfold allOkT at hC
      simp only [Bool.and_eq_true] at hC
      exact hC.2
    simp only [Bool.cond_true, Option.some.injEq]
    funext j
    have hW : patOf A simI x (A.queries q₀ q₁ j).ctxRed = (A.queries q₀ q₁ j).w :=
      swapOf_eq hr j
    unfold ySim swapF who
    beta_reduce
    rw [hW]
    simp

/-! ## Issuer hiding and unlinkability -/

/-- **Theorem U5(a), from uniform seed expansions.** If the unbound issuance and redemption proofs
are `εI`- and `εR`-zero-knowledge and every reduction `reduction A simI simR b cc` has PRF advantage
at most `εprf`, then for every adversary playing all Anchors and the Moderator, with any keys,
Anchor Sets, contexts, digests and `n` redemption queries, the acceptance probabilities in the two
worlds differ by at most `4εI + 2n·εR + 2εprf`. The adversary's queries must have 16-byte contexts,
which `Coins ctxBytes` enforces. -/
theorem anonymity [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (PI : NIZK IssueInstance)
    (PR : NIZK RedeemInstance) {εI εR εprf : ℝ} (hεR : 0 ≤ εR)
    (hI : ZeroKnowledge IssueRelW (proveR PI) simI εI)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR)
    (hprf : ∀ b cc, prfAdv A.ci (reduction A simI simR b cc) ≤ εprf) :
    |pr _ (realGame A PI PR false) - pr _ (realGame A PI PR true)| ≤
      4 * εI + 2 * n * εR + 2 * εprf := by
  have hiss := issue_close A simI PI hI
  have hred := fun p hp hc => redeem_close A simR PR hεR hR p hp hc
  have hw (b : Bool) : |pr _ (realGame A PI PR b) - pr _ (idealGame A simI simR b)| ≤
      2 * εI + n * εR + εprf := by
    set p0 := pr _ (realGame A PI PR b)
    set p1 := pr _ (game A b (issSim A simI) (issReal A PI) (redReal A PR))
    set p2 := pr _ (game A b (issSim A simI) (issSim A simI) (redReal A PR))
    set p3 := pr _ (simGame A simI simR b)
    set p4 := pr _ (idealGame A simI simR b)
    have h1 : |p0 - p1| ≤ εI := game_hop₀ A b (issReal A PI) (redReal A PR) hiss
    have h2 : |p1 - p2| ≤ εI := game_hop₁ A b (issSim A simI) (redReal A PR) hiss
    have h3 : |p2 - p3| ≤ n * εR :=
      game_hopRed A b (issSim_wf A simI) (issSim_wf A simI) hred
    have h4 : |p3 - p4| ≤ εprf := prf_hop A simI simR b (hprf b)
    have := abs_sub_le p0 p1 p4
    have := abs_sub_le p1 p2 p4
    have := abs_sub_le p2 p3 p4
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGame_eq] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (idealGame A simI simR true)) _
    _ ≤ (2 * εI + n * εR + εprf) + (2 * εI + n * εR + εprf) :=
        add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * εI + 2 * n * εR + 2 * εprf := by ring

end VoleMole.Privacy.MoussakaUnbound
