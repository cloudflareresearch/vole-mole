import VoleMole.Theft.Many
import VoleMole.Theft.MoussakaUnbound

/-!
# Unbound Moussaka: Proposition U3 and Theorem U4 for `U` honest tokens and `M` honest redemptions
(`security/moussaka-unbound.md` §5.2, §5.3)

`Theft/MoussakaUnbound.lean` proves the two theorems for one honest token with one redemption.
This file proves them for `U` honest tokens and `M` honest redemptions in total, of tokens and in
an order the adversary chooses (so up to `M` redemptions of each token), on the generic game of
`Theft/Many.lean`.

**The game NM-U^{U,M}.** `U` honest Clients with independent coins `ω h = (nf_key_h, r_h)` each
request an unbound token for the adversary's `ctx_iss h` (slots `0 … U − 1`, the spec's
`issueRequestOf`, `specI_eqN`). The adversary (`ThiefN`: every Anchor and Moderator) answers
token `h` with a signature it chooses from all `U` requests (`respond`), and then makes `M`
redemption queries, one after the other: from the issuance requests and the redemption requests
it has seen so far it chooses a token `h`, an Anchor Set, a **redemption context** and a digest
(`choose`), and the Client of token `h` answers as the spec does (`finalizeIssue`,
`redeemRequestOf` with the C++ `find_issuer`; `specR_eqN`). These choices do not read the tables.
At the end the adversary reads the tables and outputs one operation (`UOp`).

**The event** (`BadN`): the operation is accepted (`AccOp`), its statement differs from every
honest statement of the same relation (`FreshOpN`), and the extracted witness is not a witness,
or it **hits some honest token** `h` (`HitOp`): it opens `t_h`, or it is a redemption carrying
`Derive(nf_key_h, ctx_red*)` for its own context.

**`nmUN`**:

    Pr[BadN] ≤ U·ε_I + M·ε_R + Σ_i δ_i + ε_SE
                 + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)),

with `ε_I`, `ε_R` zero knowledge of the two unbound proof systems (at the hops' distinguishers),
`δ_i` the collision term of hop `i` (`deltaN`; `δ_0 = 0`), `ε_SE` weak simulation-extractability
with `U + M` simulated proofs (`WeakSEN`, **a hypothesis**, L8 on paper), `ε_prf` the PRF
advantage with the commitment leaked (`prf1Adv`, **a hypothesis** on Keccak-p[800]) of the
explicit distinguishers `owkDN`, and `Adv^bind`, `Adv^spr-k` the advantages of explicit
adversaries per honest token. The sum over `h` is the note's factor `U`: a union bound over the
token that is hit, each term a one-token game in which the other tokens' coins are fixed.

**Key recovery with many nullifiers** (`owkAdvN_le`): the key-recovery adversary of token `h`
sees `t_h` and `Derive(nf_key_h, ·)` at up to `M` contexts it chooses adaptively (`ReadsO`,
proved for the reduction: `viewN_reads`). The PRF distinguisher checks its key at `M + 1` fixed
distinct contexts (`pts`); with a uniform table one of them was not queried, so the check passes
with probability at most `(M+1)·2⁻¹⁹²` (`pr_guess_unread_le`).

`noSquatN` (Proposition U3) and `noRedirectUN` (Theorem U4) restrict the event.
-/

open Finset

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

variable {G S : Type} {U M : ℕ}

/-! ## The adversary and the honest Clients -/

/-- An instance of one of the two unbound relations. -/
abbrev UI := IssueInstance ⊕ RedeemInstance

/-- The log of the honest Clients' statements and proofs, one entry per slot (`none`: the Client
refused). -/
abbrev Log := List (Option (UI × Bytes))

/-- The coins of the `U` honest Clients. -/
abbrev SecN (U : ℕ) := Fin U → Sec

/-- **The adversary**: every Anchor and Moderator, against `U` honest tokens and `M` honest
redemptions. `respond h reqs` is the signature for token `h`, from all issuance requests;
`choose reqs reds` is the next redemption query, from the issuance requests and the redemption
requests so far: the token, the Anchor Set, the redemption context and the digest. -/
structure ThiefN (U M : ℕ) (G S : Type) where
  ctxIss : Fin U → Coins ctxBytes
  pk : Fin U → UOVKey
  respond : Fin U → List Bytes → Coins uovN
  choose : List Bytes → List (Except Error Bytes) → Fin U × AnchorSet × Coins ctxBytes × Bytes
  out : List Bytes → List (Except Error Bytes) → (Fin (U + M) → G) → S → UOp

variable (A : ThiefN U M G S)

def ThiefN.ci (h : Fin U) : Bytes := List.ofFn (A.ctxIss h)

/-- The issuance request of a log entry: `t ‖ π`. -/
def msgI : Option (UI × Bytes) → Bytes
  | some (.inl x, π) => x.t ++ π
  | _ => []

/-- The redemption request of a log entry: `nf ‖ π`, or the Client's refusal. -/
def msgR : Option (UI × Bytes) → Except Error Bytes
  | some (.inr x, π) => .ok (x.nf ++ π)
  | _ => .error .invalidToken

/-- The issuance requests and the redemption requests of a log. -/
def reqsOf (U : ℕ) (l : Log) : List Bytes := (l.take U).map msgI
def redsOf (U : ℕ) (l : Log) : List (Except Error Bytes) := (l.drop U).map msgR

/-- The redemption query after the log `l`: token, Anchor Set, context, digest, and the token's
signature. -/
def ThiefN.tok (l : Log) : Fin U := (A.choose (reqsOf U l) (redsOf U l)).1
def ThiefN.set (l : Log) : AnchorSet := (A.choose (reqsOf U l) (redsOf U l)).2.1
def ThiefN.crC (l : Log) : Coins ctxBytes := (A.choose (reqsOf U l) (redsOf U l)).2.2.1
def ThiefN.cd (l : Log) : Bytes := (A.choose (reqsOf U l) (redsOf U l)).2.2.2
def ThiefN.sig (l : Log) : Bytes := List.ofFn (A.respond (A.tok l) (reqsOf U l))

/-- **The public form of the honest secrets**: the commitments `t_h` and the nullifier tables
`ctx ↦ Derive(nf_key_h, ctx)`. -/
abbrev Pub (U : ℕ) := (Fin U → Bytes) × (Fin U → Coins ctxBytes → Bytes)

/-- The commitment of token `h`. -/
def tOfN (ω : SecN U) (h : Fin U) : Bytes := ucom (List.ofFn (ω h).1) (A.ci h) (List.ofFn (ω h).2)

/-- The public form of the coins. -/
def pubOf (ω : SecN U) : Pub U :=
  (tOfN A ω, fun h c => derive (List.ofFn (ω h).1) (List.ofFn c))

/-- **The statement of the next slot**, from the public form: slot `h < U` is the issuance of
token `h`; a later slot is the redemption the adversary asks for, if the token finalized and
some key of the set verifies it. -/
def xN (p : Pub U) (l : Log) : Option UI :=
  if h : l.length < U then some (.inl ⟨p.1 ⟨l.length, h⟩, A.ci ⟨l.length, h⟩⟩)
  else if (A.pk (A.tok l)).eval (A.sig l) = p.1 (A.tok l) then
    match findIssuer (A.set l) (p.1 (A.tok l)) (A.sig l) with
    | none => none
    | some _ => some (.inr ⟨(A.set l).keys, p.2 (A.tok l) (A.crC l), A.ci (A.tok l),
        List.ofFn (A.crC l), A.cd l⟩)
  else none

/-- **The statement and witness of the next slot.** -/
def xwN (ω : SecN U) (l : Log) : Option (UI × Bytes) :=
  if h : l.length < U then
    some (.inl ⟨tOfN A ω ⟨l.length, h⟩, A.ci ⟨l.length, h⟩⟩,
      encodeIssueWitness (List.ofFn (ω ⟨l.length, h⟩).1) (A.ci ⟨l.length, h⟩)
        (List.ofFn (ω ⟨l.length, h⟩).2))
  else if (A.pk (A.tok l)).eval (A.sig l) = tOfN A ω (A.tok l) then
    match findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) with
    | none => none
    | some i => some (.inr ⟨(A.set l).keys,
          derive (List.ofFn (ω (A.tok l)).1) (List.ofFn (A.crC l)), A.ci (A.tok l),
          List.ofFn (A.crC l), A.cd l⟩,
        encodeRedeemWitness (List.ofFn (ω (A.tok l)).1) (A.ci (A.tok l)) (List.ofFn (A.crC l))
          (List.ofFn (ω (A.tok l)).2) (A.sig l) i)
  else none

theorem xwN_fst (ω : SecN U) (l : Log) : (xwN A ω l).map Prod.fst = xN A (pubOf A ω) l := by
  unfold xwN xN
  have ht : (pubOf A ω).1 = tOfN A ω := rfl
  rw [ht]
  split_ifs with h hv
  · rfl
  · cases findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) <;> rfl
  · rfl

/-- The issuance relation, on the sum of the instance types. -/
def RelUI (x : UI) (w : Bytes) : Prop :=
  match x with
  | .inl x => IssueRelW x w
  | .inr _ => False

/-- The redemption relation, on the sum of the instance types. -/
def RelUR (x : UI) (w : Bytes) : Prop :=
  match x with
  | .inl _ => False
  | .inr x => RedeemRelW x w

theorem xwN_relI (ω : SecN U) (l : Log) (hl : l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelUI x w := by
  intro x w h
  unfold xwN at h
  simp only [hl, ↓reduceDIte] at h
  cases h
  exact ⟨⟨List.ofFn (ω ⟨l.length, hl⟩).1, List.ofFn (ω ⟨l.length, hl⟩).2, List.length_ofFn,
    List.length_ofFn, rfl, rfl⟩, List.length_ofFn⟩

theorem xwN_relR (ω : SecN U) (l : Log) (hl : ¬ l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelUR x w := by
  intro x w h
  unfold xwN at h
  simp only [hl, ↓reduceDIte] at h
  split_ifs at h with hv
  cases hf : findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf] at h
    cases h
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    exact ⟨⟨List.ofFn (ω (A.tok l)).1, List.ofFn (ω (A.tok l)).2, A.sig l, i, pk, List.length_ofFn,
      List.length_ofFn, List.length_ofFn, hk, rfl, he, rfl⟩,
      (A.set l).valid.2.1, length_derive _ _, List.length_ofFn, List.length_ofFn⟩

/-! ## The provers and simulators on the sum of the instance types -/

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- The two provers as one, with uniform randomness and an optional output. -/
def PU (x : UI) (w : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Option Bytes :=
  match x with
  | .inl x => some (PI w x (List.ofFn ρ) g s)
  | .inr x => some (PR w x (List.ofFn ρ) g s)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)

/-- The two simulators as one, with coins for both. -/
def simU (x : UI) (c : CI × CR) : Option Bytes :=
  match x with
  | .inl x => some (simI x c.1)
  | .inr x => some (simR x c.2)

/-- The two programmings as one. -/
def progU (x : UI) (c : CI × CR) (s : S) : S :=
  match x with
  | .inl x => progI x c.1 s
  | .inr x => progR x c.2 s

/-- **The real slot**: the log entry of the next honest proof. -/
def PN (ω : SecN U) (l : Log) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Option (UI × Bytes) :=
  pairO (xN A (pubOf A ω) l) (proveO (PU PI PR) (xwN A ω l) ρ g s)

/-- **The simulated slot**, from the public form of the secrets. -/
def SmP (p : Pub U) (l : Log) (c : CI × CR) : Option (UI × Bytes) :=
  pairO (xN A p l) (simO (simU simI simR) (xN A p l) c)

/-- The simulated slot's programming. -/
def pgP (p : Pub U) (l : Log) (c : CI × CR) (s : S) : S :=
  progO (progU progI progR) (xN A p l) c s

/-! ## The game runs the spec -/

/-- **Slot `h < U` is `unbound_issue_request`** of Client `h`. -/
theorem specI_eqN (ω : SecN U) (l : Log) (hl : l.length < U) (ρ : Coins proveSeedBytes) (g : G)
    (s : S) :
    msgI (PN A PI PR ω l ρ g s) =
      (issueRequestOf (nizkG PI g s) (A.ci ⟨l.length, hl⟩) (List.ofFn (ω ⟨l.length, hl⟩).1)
        (List.ofFn (ω ⟨l.length, hl⟩).2) (List.ofFn ρ)).2 := by
  simp only [PN, xN, xwN, hl, ↓reduceDIte]
  rfl

/-- **A slot `≥ U` is `finalize_issue` and `UnboundToken::redeem_request`** of the Client the
adversary chose, under its Anchor Set, redemption context and digest. -/
theorem specR_eqN (ω : SecN U) (l : Log) (hl : ¬ l.length < U) (ρ : Coins proveSeedBytes) (g : G)
    (s : S) :
    msgR (PN A PI PR ω l ρ g s) =
      match finalizeIssue (A.pk (A.tok l))
          ⟨List.ofFn (ω (A.tok l)).1, List.ofFn (ω (A.tok l)).2, A.ci (A.tok l),
            tOfN A ω (A.tok l)⟩ (A.sig l) with
      | none => .error .invalidToken
      | some tok => redeemRequestOf (nizkG PR g s) tok (A.set l) (A.ci (A.tok l))
          (List.ofFn (A.crC l)) (A.cd l) (List.ofFn ρ) := by
  simp only [PN, xN, xwN, hl, ↓reduceDIte, finalizeIssue]
  have hp : (pubOf A ω).1 = tOfN A ω := rfl
  rw [hp]
  by_cases hv : (A.pk (A.tok l)).eval (A.sig l) = tOfN A ω (A.tok l)
  · simp only [hv, ite_true]
    unfold redeemRequestOf
    have ht : ucom (List.ofFn (ω (A.tok l)).1) (A.ci (A.tok l)) (List.ofFn (ω (A.tok l)).2) =
        tOfN A ω (A.tok l) := rfl
    simp only [ht]
    cases findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) <;> rfl
  · simp only [hv, ite_false]
    rfl

/-! ## The event -/

/-- The adversary's operation, from the log. -/
def opN (l : Log) (g : Fin (U + M) → G) (s : S) : UOp := A.out (reqsOf U l) (redsOf U l) g s

/-- **Its statement is fresh**: it differs from every honest statement of the same relation. -/
def FreshOpN (l : Log) (op : UOp) : Prop :=
  match op with
  | .issue req ci => ∀ x π, some (Sum.inl x, π) ∈ l → stOfI req ci ≠ x
  | .redeem S' req ci cr cd => ∀ x π, some (Sum.inr x, π) ∈ l → stOfR S' req ci cr cd ≠ x

/-- **The extractor**: the log, the adversary's last stage, the tables. -/
abbrev ExtN (U M : ℕ) (G S : Type) :=
  Log → ((Fin (U + M) → G) → S → UOp) → (Fin (U + M) → G) → S → Bytes

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : ExtN U M G S)

def accN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  AccOp verI verR (opN A l g s) s

def freshN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  FreshOpN l (opN A l g s)

def relN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  RelOp (opN A l g s) (ext l (opN A l) g s)

/-- The witness hits the honest token `h`. -/
def hitH (h : Fin U) (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  HitOp (tOfN A ω h) (List.ofFn (ω h).1) (opN A l g s) (ext l (opN A l) g s)

/-- The witness hits some honest token. -/
def hitN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  ∃ h, hitH A ext h ω l g s

/-- **The bad event.** -/
def BadN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧ (¬ relN A ext ω l g s ∨ hitN A ext ω l g s)

/-- **The squatting event (Proposition U3)**: an accepted redemption with a fresh statement that
carries the nullifier of some honest token for its own context. -/
def SquatN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧ ∃ h : Fin U,
    match opN A l g s with
    | .issue _ _ => False
    | .redeem _ req _ cr _ => req.take nfBytes = derive (List.ofFn (ω h).1) cr

/-- **The redirect event (Theorem U4)**: an accepted operation with a fresh statement whose
extracted witness is not a witness or opens the commitment of some honest token. -/
def RedirectN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧
    (¬ relN A ext ω l g s ∨ ∃ h : Fin U,
      ucom (keyOf (ext l (opN A l) g s)) (ciOf (opN A l g s)) (rOf (ext l (opN A l) g s)) =
        tOfN A ω h)

/-- The tape of the game: the Clients' coins, the slots, the shared tables. -/
abbrev TapeN (U M : ℕ) (CI CR G S : Type) :=
  (SecN U × (Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G)) × S

/-- **The real game NM-U^{U,M}** for an event. -/
def nmRealNE (Ev : SecN U → Log → (Fin (U + M) → G) → S → Prop) [Nonempty G]
    (z : TapeN U M CI CR G S) : Prop :=
  realGN (PN A PI PR) Ev z

/-- **The simulated game.** -/
def nmSimN (Ev : SecN U → Log → (Fin (U + M) → G) → S → Prop) [Nonempty CI] [Nonempty CR]
    (z : TapeN U M CI CR G S) : Prop :=
  simGN (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω)) Ev z

/-- **The collision term of hop `i`.** -/
def deltaNU [Nonempty CI] [Nonempty CR] [Nonempty G] (i : Fin (U + M))
    (z : TapeN U M CI CR G S) : Prop :=
  deltaN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) i z

/-- **The distinguisher of hop `i`**, as a function of the proof of slot `i`. -/
def distPN [Nonempty CI] [Nonempty CR] [Nonempty G] (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G) (p : Bytes) (g : G) (u : S) :
    Prop :=
  distN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) (BadN A verI verR ext) i ω τ
    (pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω)) ω
        (tapeC τ) i).1) (some p)) g u

/-! ## Zero knowledge on the sum of the instance types -/

section ZK

variable [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] [Fintype G] [Fintype S]

omit [Nonempty CI] in
theorem zkU_I {AdmI : (Bytes → G → S → Prop) → Prop} {εI : ℝ}
    (hzk : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI) :
    ZeroKnowledgeRO RelUI (PU PI PR) (simU simI simR) (progU progI progR)
      (fun D => AdmI (fun o g s => D (some o) g s)) εI := by
  intro x w hxw D hD
  rcases x with x | x
  · have h := hzk x w hxw _ hD
    let e : ((CI × CR) × G) × S ≃ CR × ((CI × G) × S) :=
      { toFun := fun a => (a.1.1.2, ((a.1.1.1, a.1.2), a.2))
        invFun := fun y => (((y.2.1.1, y.1), y.2.1.2), y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 := pr_equiv e (fun y : CR × ((CI × G) × S) =>
      D (some (simI x y.2.1.1)) y.2.1.2 (progI x y.2.1.1 y.2.2))
    rw [pr_prod_snd (α := CR) (fun y : (CI × G) × S =>
      D (some (simI x y.1.1)) y.1.2 (progI x y.1.1 y.2))] at e1
    simp only [PU, simU, progU]
    rw [← e1] at h
    exact h
  · exact hxw.elim

omit [Nonempty CR] in
theorem zkU_R {AdmR : (Bytes → G → S → Prop) → Prop} {εR : ℝ}
    (hzk : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR) :
    ZeroKnowledgeRO RelUR (PU PI PR) (simU simI simR) (progU progI progR)
      (fun D => AdmR (fun o g s => D (some o) g s)) εR := by
  intro x w hxw D hD
  rcases x with x | x
  · exact hxw.elim
  · have h := hzk x w hxw _ hD
    let e : ((CI × CR) × G) × S ≃ CI × ((CR × G) × S) :=
      { toFun := fun a => (a.1.1.1, ((a.1.1.2, a.1.2), a.2))
        invFun := fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 := pr_equiv e (fun y : CI × ((CR × G) × S) =>
      D (some (simR x y.2.1.1)) y.2.1.2 (progR x y.2.1.1 y.2.2))
    rw [pr_prod_snd (α := CI) (fun y : (CR × G) × S =>
      D (some (simR x y.1.1)) y.1.2 (progR x y.1.1 y.2))] at e1
    simp only [PU, simU, progU]
    rw [← e1] at h
    exact h

end ZK

/-! ## Key recovery with many nullifiers reduces to the PRF -/

/-- **An adversary with oracle access to the nullifiers**: from the commitment `t`, the table
`ctx ↦ Derive(k, ctx)` and its coins it outputs a result. Its queries are bounded by `ReadsO`. -/
abbrev OAdvN (β X : Type) := Bytes → (Coins ctxBytes → Bytes) → β → X

/-- The adversary's output on the key and opening `x.1` and its coins `x.2`. -/
def OAdvN.run {β X : Type} (B : OAdvN β X) (ci : Bytes) (x : Sec × β) : X :=
  B (ucom (List.ofFn x.1.1) ci (List.ofFn x.1.2))
    (fun c => derive (List.ofFn x.1.1) (List.ofFn c)) x.2

/-- **`f` reads its table at most at `q` points**, chosen adaptively: outside `Q F` the table can
change. -/
def ReadsO {K R X : Type} (f : (K → R) → X) (q : ℕ) : Prop :=
  ∃ Q : (K → R) → Finset K, (∀ F, (Q F).card ≤ q) ∧
    ∀ F F', (∀ k ∈ Q F, F k = F' k) → f F' = f F

/-- **Key recovery with many nullifiers** (`Adv^ow-k`). -/
noncomputable def owkAdvN {β : Type} [Fintype β] (ci : Bytes) (B : OAdvN β Bytes) : ℝ :=
  pr (Sec × β) fun x => B.run ci x = List.ofFn x.1.1

/-- **Second preimages of `Derive` in the key, with many nullifiers** (`Adv^spr-k`). -/
noncomputable def sprAdvN {β : Type} [Fintype β] (ci : Bytes) (B : OAdvN β (Bytes × Bytes)) : ℝ :=
  pr (Sec × β) fun x => SprWin (List.ofFn x.1.1) (B.run ci x)

/-- **Guessing a table at a point that was not read.** If `g` depends on the uniform table `F`
only through the points `Q F`, the probability that `c` was not read and `g F` is (the encoding
of) `F c` is at most `1/|R|`. -/
theorem pr_guess_unread_le {K R Y : Type} [Fintype K] [DecidableEq K] [Fintype R] [Nonempty R]
    (c : K) (Q : (K → R) → Finset K) (g : (K → R) → Y) (enc : R → Y)
    (henc : Function.Injective enc)
    (hg : ∀ F F', (∀ k ∈ Q F, F k = F' k) → g F' = g F) :
    pr (K → R) (fun F => c ∉ Q F ∧ enc (F c) = g F) ≤ 1 / Fintype.card R := by
  classical
  rw [← pr_equiv (Equiv.funSplitAt c R).symm]
  refine pr_le_of_snd fun rest => ?_
  rw [pr_def, div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)]
  have hcard : (Finset.univ.filter fun y : R =>
      c ∉ Q ((Equiv.funSplitAt c R).symm (y, rest)) ∧
        enc ((Equiv.funSplitAt c R).symm (y, rest) c) =
          g ((Equiv.funSplitAt c R).symm (y, rest))).card ≤ 1 := by
    refine Finset.card_le_one.2 fun y₁ h₁ y₂ h₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    have hv : ∀ y : R, (Equiv.funSplitAt c R).symm (y, rest) c = y := fun y => by
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    have hag : ∀ k ∈ Q ((Equiv.funSplitAt c R).symm (y₁, rest)),
        (Equiv.funSplitAt c R).symm (y₁, rest) k = (Equiv.funSplitAt c R).symm (y₂, rest) k := by
      intro k hk
      have hkc : k ≠ c := fun e => h₁.1 (e ▸ hk)
      simp [Equiv.funSplitAt, Equiv.piSplitAt, hkc]
    have e := hg _ _ hag
    rw [hv] at h₁ h₂
    exact henc (h₁.2.trans (e ▸ h₂.2.symm ▸ rfl))
  exact_mod_cast hcard

/-- **The PRF distinguisher of a key-recovery adversary** (coins `b` fixed): it runs the
adversary on `t` and the table, and checks the output key at the `M + 1` contexts `pts`. -/
def owkDN {β : Type} {q : ℕ} (B : OAdvN β Bytes) (pts : Fin (q + 1) → Coins ctxBytes) (b : β)
    (z : Bytes × (Coins ctxBytes → Bytes)) : Prop :=
  ∀ i, derive (B z.1 z.2 b) (List.ofFn (pts i)) = z.2 (pts i)

/-- **The ideal experiment**: one of the `q + 1` contexts was not queried, and the table there is
independent of the adversary's view: the check passes with probability at most
`(q + 1)·2⁻¹⁹²`. -/
theorem owkDN_ideal {β : Type} {q : ℕ} (ci : Bytes) (B : OAdvN β Bytes)
    (pts : Fin (q + 1) → Coins ctxBytes) (hpts : Function.Injective pts) (b : β)
    (hB : ∀ t, ReadsO (fun F => B t F b) q) :
    pr (Sec × Tab1) (fun x => owkDN B pts b (prf1Ideal ci x)) ≤ (q + 1) / 2 ^ 192 := by
  classical
  rw [← pr_equiv (Equiv.prodComm Tab1 Sec)]
  refine pr_le_of_snd fun x => ?_
  set t := ucom (List.ofFn x.1) ci (List.ofFn x.2)
  obtain ⟨Q, hQ, hf⟩ := hB t
  -- the adversary on a uniform table of nullifiers
  let Q' : Tab1 → Finset (Coins ctxBytes) := fun F => Q fun c => List.ofFn (F c)
  have hstep : ∀ i : Fin (q + 1), pr Tab1 (fun F => pts i ∉ Q' F ∧
      List.ofFn (F (pts i)) = derive (B t (fun c => List.ofFn (F c)) b) (List.ofFn (pts i))) ≤
      1 / 2 ^ 192 := by
    intro i
    have h := pr_guess_unread_le (K := Coins ctxBytes) (R := Coins nfBytes) (pts i) Q'
      (fun F => derive (B t (fun c => List.ofFn (F c)) b) (List.ofFn (pts i))) List.ofFn
      List.ofFn_injective (fun F F' hag => by
        have := hf (fun c => List.ofFn (F c)) (fun c => List.ofFn (F' c))
          fun k hk => congrArg List.ofFn (hag k hk)
        simp only [this])
    rw [card_coins24] at h
    exact_mod_cast h
  have hex : ∀ F : Tab1, owkDN B pts b (prf1Ideal ci (x, F)) →
      ∃ i : Fin (q + 1), pts i ∉ Q' F ∧
        List.ofFn (F (pts i)) = derive (B t (fun c => List.ofFn (F c)) b) (List.ofFn (pts i)) := by
    intro F hF
    have hne : ∃ i : Fin (q + 1), pts i ∉ Q' F := by
      by_contra hall
      have hall : ∀ i, pts i ∈ Q' F := fun i => by_contra fun hi => hall ⟨i, hi⟩
      have hsub : Finset.image pts Finset.univ ⊆ Q' F := by
        intro c hc
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
        exact hall i
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hpts, Finset.card_univ, Fintype.card_fin] at this
      have hq : (Q' F).card ≤ q := hQ _
      omega
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi, (hF i).symm⟩
  refine (pr_mono hex).trans ((pr_exists_le_sum _).trans ?_)
  calc ∑ i : Fin (q + 1), pr Tab1 (fun F => pts i ∉ Q' F ∧
        List.ofFn (F (pts i)) = derive (B t (fun c => List.ofFn (F c)) b) (List.ofFn (pts i)))
      ≤ ∑ _i : Fin (q + 1), (1 : ℝ) / 2 ^ 192 := Finset.sum_le_sum fun i _ => hstep i
    _ = (q + 1) / 2 ^ 192 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- **Key recovery with `q` adaptive nullifier queries is bounded by the PRF assumption**:
`Adv^ow-k(B) ≤ ε_prf + (q + 1)·2⁻¹⁹²` if every `owkDN B pts b` has PRF advantage at most
`ε_prf`. -/
theorem owkAdvN_le {β : Type} [Fintype β] [Nonempty β] {q : ℕ} (ci : Bytes) (B : OAdvN β Bytes)
    (pts : Fin (q + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hB : ∀ t b, ReadsO (fun F => B t F b) q) {εprf : ℝ}
    (hprf : ∀ b, prf1Adv ci (owkDN B pts b) ≤ εprf) :
    owkAdvN ci B ≤ εprf + (q + 1) / 2 ^ 192 := by
  unfold owkAdvN
  refine pr_le_of_snd fun b => ?_
  have hreal : pr Sec (fun a => B.run ci (a, b) = List.ofFn a.1) ≤
      pr Sec (fun x => owkDN B pts b (prf1Real ci x)) := pr_mono fun a ha => by
    simp only [OAdvN.run] at ha
    intro i
    simp only [prf1Real, ha]
  have h := hprf b
  unfold prf1Adv at h
  have := (abs_le.1 h).2
  linarith [owkDN_ideal ci B pts hpts b fun t => hB t b]

/-! ## The simulated world and the reductions, per honest token -/

/-- The coins of the reduction for token `h`: the other Clients' coins, the slots, the tables. -/
abbrev RedC (U M : ℕ) (CI CR G S : Type) (h : Fin U) :=
  ({j : Fin U // j ≠ h} → Sec) × ((Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G) × S)

/-- The Clients' coins from token `h`'s and the others'. -/
def insSec (h : Fin U) (x : Sec) (o : {j : Fin U // j ≠ h} → Sec) : SecN U :=
  fun j => if e : j = h then x else o ⟨j, e⟩

/-- **The public form with token `h` given by its commitment and nullifier table**, the other
tokens by their coins. -/
def pubH (h : Fin U) (t : Bytes) (F : Coins ctxBytes → Bytes) (o : {j : Fin U // j ≠ h} → Sec) :
    Pub U :=
  (fun j => if e : j = h then t
      else ucom (List.ofFn (o ⟨j, e⟩).1) (A.ci j) (List.ofFn (o ⟨j, e⟩).2),
    fun j c => if e : j = h then F c else derive (List.ofFn (o ⟨j, e⟩).1) (List.ofFn c))

theorem pubOf_insSec (h : Fin U) (x : Sec) (o : {j : Fin U // j ≠ h} → Sec) :
    pubOf A (insSec h x o) =
      pubH A h (ucom (List.ofFn x.1) (A.ci h) (List.ofFn x.2))
        (fun c => derive (List.ofFn x.1) (List.ofFn c)) o := by
  unfold pubOf pubH tOfN insSec
  refine Prod.ext (funext fun j => ?_) (funext fun j => funext fun c => ?_)
  · by_cases e : j = h
    · subst e; simp
    · simp [e]
  · by_cases e : j = h
    · subst e; simp
    · simp [e]

/-- The regrouping of the simulated game's tape around token `h`. -/
def regroupH (h : Fin U) : Sec × RedC U M CI CR G S h ≃ TapeN U M CI CR G S where
  toFun y := ((insSec h y.1 y.2.1, y.2.2.1), y.2.2.2)
  invFun z := (z.1.1 h, (fun j => z.1.1 j.1, (z.1.2, z.2)))
  left_inv y := by
    refine Prod.ext (by simp [insSec]) (Prod.ext (funext fun j => ?_) rfl)
    simp [insSec, j.2]
  right_inv z := by
    refine Prod.ext (Prod.ext (funext fun j => ?_) rfl) rfl
    by_cases e : j = h
    · subst e; simp [insSec]
    · simp [insSec, e]

variable [Nonempty CI] [Nonempty CR]

/-- **The simulated world as a function of `t_h` and the nullifier table of token `h`**: the
adversary's operation and the extracted witness. -/
noncomputable def viewN (h : Fin U) : OAdvN (RedC U M CI CR G S h) (UOp × Bytes) := fun t F b =>
  (opN A (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) (U + M)).1
      (tapeG b.2.1)
      ((simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) (U + M)).2
        b.2.2),
    ext (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) (U + M)).1
      (opN A
        (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) (U + M)).1)
      (tapeG b.2.1)
      ((simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) (U + M)).2
        b.2.2))

/-- **`B_k h`, key recovery**: the simulated world's extracted key. -/
noncomputable def keyBN (h : Fin U) : OAdvN (RedC U M CI CR G S h) Bytes := fun t F b =>
  keyOf (viewN A simI progI simR progR ext h t F b).2

/-- **`B₁ h`, binding**: the honest opening of token `h` and the extracted one. -/
noncomputable def bindBN (h : Fin U) (z : Sec × RedC U M CI CR G S h) : UOpening × UOpening :=
  ((List.ofFn z.1.1, A.ci h, List.ofFn z.1.2),
    (keyOf ((viewN A simI progI simR progR ext h).run (A.ci h) z).2,
      ciOf ((viewN A simI progI simR progR ext h).run (A.ci h) z).1,
      rOf ((viewN A simI progI simR progR ext h).run (A.ci h) z).2))

/-- **`B₂ h`, key second preimage**: the extracted key and the operation's redemption context. -/
noncomputable def sprBN (h : Fin U) : OAdvN (RedC U M CI CR G S h) (Bytes × Bytes) := fun t F b =>
  (keyOf (viewN A simI progI simR progR ext h t F b).2,
    crOf (viewN A simI progI simR progR ext h t F b).1)

omit [Nonempty CI] [Nonempty CR] in
/-- The statement of a slot depends on the nullifier tables only at the query's token and
context. -/
theorem xN_congr {p p' : Pub U} (l : Log) (h1 : p.1 = p'.1)
    (h2 : ¬ l.length < U → p.2 (A.tok l) (A.crC l) = p'.2 (A.tok l) (A.crC l)) :
    xN A p l = xN A p' l := by
  unfold xN
  split_ifs with hl hv hv' hv'
  · rw [h1]
  · rw [← h1, h2 hl]
  · exact absurd (h1 ▸ hv) hv'
  · exact absurd (h1 ▸ hv') hv
  · rfl

/-- **The simulated world reads the nullifier table of token `h` at most at `M` contexts**: those
of the redemption queries. -/
theorem viewN_reads (h : Fin U) (t : Bytes) (b : RedC U M CI CR G S h) :
    ReadsO (fun F => viewN A simI progI simR progR ext h t F b) M := by
  classical
  refine ⟨fun F => Finset.image (fun j : Fin M => A.crC
      (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1)
        (U + j.val)).1) Finset.univ,
    fun F => (Finset.card_image_le).trans (by simp), fun F F' hag => ?_⟩
  have key : ∀ j, j ≤ U + M →
      simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F' b.1) (tapeC b.2.1) j =
        simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hx : xN A (pubH A h t F' b.1)
            (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) j).1 =
          xN A (pubH A h t F b.1)
            (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) j).1 := by
        refine xN_congr A _ rfl fun hl => ?_
        rw [simPre_length] at hl
        have hp : ∀ (F₁ : Coins ctxBytes → Bytes) (j : Fin U) (c : Coins ctxBytes),
            (pubH A h t F₁ b.1).2 j c =
              if e : j = h then F₁ c else derive (List.ofFn (b.1 ⟨j, e⟩).1) (List.ofFn c) :=
          fun _ _ _ => rfl
        rw [hp, hp]
        split_ifs with e
        · refine (hag _ (Finset.mem_image.2 ⟨⟨j - U, by omega⟩, Finset.mem_univ _, ?_⟩)).symm
          simp only [show U + (j - U) = j by omega]
        · rfl
      have hpg : pgP A progI progR (pubH A h t F' b.1)
            (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) j).1 =
          pgP A progI progR (pubH A h t F b.1)
            (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h t F b.1) (tapeC b.2.1) j).1 := by
        funext c s
        simp only [pgP, hx]
      simp only [simPre, ihj, SmP, hx, hpg]
  simp only [viewN, key (U + M) le_rfl]

/-- The simulated game with the hit of token `h`, on the regrouped tape, is the view. -/
theorem nmSimN_hitH (h : Fin U) (y : Sec × RedC U M CI CR G S h) :
    nmSimN A simI progI simR progR (hitH A ext h) (regroupH h y) ↔
      HitOp (ucom (List.ofFn y.1.1) (A.ci h) (List.ofFn y.1.2)) (List.ofFn y.1.1)
        ((viewN A simI progI simR progR ext h).run (A.ci h) y).1
        ((viewN A simI progI simR progR ext h).run (A.ci h) y).2 := by
  have hm := simPre_map (pubOf A) (SmP A simI simR) (pgP (S := S) A progI progR)
    (insSec h y.1 y.2.1) (tapeC y.2.2.1) (U + M)
  have hp := pubOf_insSec A h y.1 y.2.1
  have ht : tOfN A (insSec h y.1 y.2.1) h = ucom (List.ofFn y.1.1) (A.ci h) (List.ofFn y.1.2) := by
    simp [tOfN, insSec]
  have hk : (insSec h y.1 y.2.1 h).1 = y.1.1 := by simp [insSec]
  simp only [nmSimN, simGN, hitH, regroupH, Equiv.coe_fn_mk, hm, hp, ht, hk, OAdvN.run, viewN]

omit [Nonempty CI] [Nonempty CR] in
/-- The squatting event is in the bad event. -/
theorem squatN_bad {ω : SecN U} {l : Log} {g : Fin (U + M) → G} {s : S}
    (hz : SquatN A verI verR ω l g s) : BadN A verI verR ext ω l g s := by
  obtain ⟨ha, hf, h, hn⟩ := hz
  exact ⟨ha, hf, or_iff_not_imp_left.2 fun hr => ⟨h, Or.inr ⟨not_not.1 hr, hn⟩⟩⟩

omit [Nonempty CI] [Nonempty CR] in
/-- The redirect event is in the bad event (the 16-byte `ctx_iss` of `OpensOp` is implied by
acceptance). -/
theorem redirectN_bad {ω : SecN U} {l : Log} {g : Fin (U + M) → G} {s : S}
    (hz : RedirectN A verI verR ext ω l g s) : BadN A verI verR ext ω l g s := by
  obtain ⟨ha, hf, ho⟩ := hz
  refine ⟨ha, hf, ?_⟩
  rcases ho with hr | ⟨h, ho⟩
  · exact Or.inl hr
  · by_cases hr : relN A ext ω l g s
    · refine Or.inr ⟨h, Or.inl ⟨hr, ?_, ho⟩⟩
      have ha' : AccOp verI verR (opN A l g s) s := ha
      revert ha'
      generalize opN A l g s = op
      cases op <;> simp only [ciOf, AccOp] <;> tauto
    · exact Or.inl hr

section Red

variable [Fintype CI] [Fintype CR] [Fintype G] [Fintype S] [Nonempty G]

omit [Nonempty G] in
/-- **The hit step.** In the simulated world, a hit of some honest token `h` is a key recovery
(`B_k h`), a binding break (`B₁ h`) or a key second preimage (`B₂ h`) for that token. -/
theorem sim_hit_leN :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (hitN A ext)) ≤
      ∑ h : Fin U, (owkAdvN (A.ci h) (keyBN A simI progI simR progR ext h) +
        bindAdv (bindBN A simI progI simR progR ext h) +
        sprAdvN (A.ci h) (sprBN A simI progI simR progR ext h)) := by
  have hex : ∀ z : TapeN U M CI CR G S, nmSimN A simI progI simR progR (hitN A ext) z →
      ∃ h, nmSimN A simI progI simR progR (hitH A ext h) z := fun z hz => hz
  refine (pr_mono hex).trans ((pr_exists_le_sum _).trans (Finset.sum_le_sum fun h _ => ?_))
  rw [← pr_equiv (regroupH h)]
  unfold owkAdvN sprAdvN bindAdv
  refine (pr_mono fun y hy => hit_cases (ci := A.ci h) List.length_ofFn List.length_ofFn
    List.length_ofFn ((nmSimN_hitH A simI progI simR progR ext h y).1 hy)).trans ?_
  refine (pr_or_le _ _).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (pr_or_le _ _)

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
def seEvN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s

/-- **Weak simulation-extractability step.** -/
theorem sim_se_leN {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εSE : ℝ} [Nonempty (SecN U)]
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤ εSE :=
  simGN_le_of_weakSEN (ρ := Coins proveSeedBytes) hse (fun ω l => xN A (pubOf A ω) l)
    (fun _ l => opN A l) fun _ l => hAE l

/-- **Unbound redemption non-malleability and no squatting for `U` honest tokens and `M` honest
redemptions (Theorems U4 and U3 together).** For every adversary, with zero knowledge of both
unbound proof systems at the hops' distinguishers, weak simulation-extractability with `U + M`
simulated proofs, and the PRF assumption for the key-recovery distinguishers:

    Pr[BadN] ≤ U·ε_I + M·ε_R + Σ_i δ_i + ε_SE
                 + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)). -/
theorem nmUN [Nonempty S] [Nonempty (SecN U)]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ,
      AdmI (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hAR : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ,
      AdmR (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A simI progI simR progR ext h) pts b) ≤ εprf) :
    pr (TapeN U M CI CR G S) (nmRealNE A PI PR (BadN A verI verR ext)) ≤
      U * εI + M * εR + ∑ i, pr (TapeN U M CI CR G S) (deltaNU A PI PR simI progI simR progR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A simI progI simR progR ext h) +
          sprAdvN (A.ci h) (sprBN A simI progI simR progR ext h)) := by
  have hzkI' := zkU_I PI PR simI progI simR progR hzkI
  have hzkR' := zkU_R PI PR simI progI simR progR hzkR
  have h := theftN_le (Ω := SecN U) (ρ := Coins proveSeedBytes) (C := CI × CR) (G := G) (S := S)
    (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω))
    (accN A verI verR) (freshN A) (relN A ext) (hitN A ext)
    (fun i => if i.val < U then εI else εR)
    (fun i ω τ => by
      have hlen := simPre_length (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP (S := S) A progI progR (pubOf A ω)) ω (tapeC τ) i
      by_cases hi : i.val < U
      · have := zk_step hzkI' hεI
          (xwN A ω (simPre (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP (S := S) A progI progR (pubOf A ω)) ω (tapeC τ) i).1)
          (xwN_relI A ω _ (by rw [hlen]; exact hi))
          (pairO ((xwN A ω (simPre (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP (S := S) A progI progR (pubOf A ω)) ω (tapeC τ) i).1).map Prod.fst))
          (distN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP A progI progR (pubOf A ω)) (BadN A verI verR ext) i ω τ)
          (fun _ _ _ => by
            have := hAI i hi ω τ
            unfold distPN at this
            rw [← xwN_fst] at this
            exact this)
        simp only [hi, ↓reduceIte]
        rw [xwN_fst] at this
        exact this
      · have := zk_step hzkR' hεR
          (xwN A ω (simPre (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP (S := S) A progI progR (pubOf A ω)) ω (tapeC τ) i).1)
          (xwN_relR A ω _ (by rw [hlen]; exact hi))
          (pairO ((xwN A ω (simPre (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP (S := S) A progI progR (pubOf A ω)) ω (tapeC τ) i).1).map Prod.fst))
          (distN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
            (fun ω => pgP A progI progR (pubOf A ω)) (BadN A verI verR ext) i ω τ)
          (fun _ _ _ => by
            have := hAR i (not_lt.1 hi) ω τ
            unfold distPN at this
            rw [← xwN_fst] at this
            exact this)
        simp only [hi, ↓reduceIte]
        rw [xwN_fst] at this
        exact this)
  have hse' := sim_se_leN A simI progI simR progR verI verR ext hse hAE
  have hhit := sim_hit_leN A simI progI simR progR ext
  have hkey : ∀ hh : Fin U, owkAdvN (A.ci hh) (keyBN A simI progI simR progR ext hh) ≤
      εprf + (M + 1) / 2 ^ 192 := fun hh =>
    owkAdvN_le (A.ci hh) _ pts hpts (fun t b => by
      obtain ⟨Q, hQ, hf⟩ := viewN_reads A simI progI simR progR ext hh t b
      exact ⟨Q, hQ, fun F F' hag => by simp only [keyBN, hf F F' hag]⟩) (hprf hh)
  have hsum : ∑ hh : Fin U, (owkAdvN (A.ci hh) (keyBN A simI progI simR progR ext hh) +
        bindAdv (bindBN A simI progI simR progR ext hh) +
        sprAdvN (A.ci hh) (sprBN A simI progI simR progR ext hh)) ≤
      ∑ hh : Fin U, (εprf + (M + 1) / 2 ^ 192 +
        bindAdv (bindBN A simI progI simR progR ext hh) +
        sprAdvN (A.ci hh) (sprBN A simI progI simR progR ext hh)) :=
    Finset.sum_le_sum fun hh _ => by linarith [hkey hh]
  have hε : ∑ i : Fin (U + M), (if i.val < U then εI else εR) = U * εI + M * εR := by
    rw [Fin.sum_univ_add]
    simp
  have hsplit : ∑ i : Fin (U + M), ((if i.val < U then εI else εR) +
        pr (TapeN U M CI CR G S) (deltaN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
          (fun ω => pgP A progI progR (pubOf A ω)) i)) =
      U * εI + M * εR +
        ∑ i, pr (TapeN U M CI CR G S) (deltaNU A PI PR simI progI simR progR i) := by
    rw [Finset.sum_add_distrib, hε]
    rfl
  rw [hsplit] at h
  have e1 : pr (TapeN U M CI CR G S) (nmRealNE A PI PR (BadN A verI verR ext)) =
      pr (TapeN U M CI CR G S) (realGN (PN A PI PR) (fun ω l g s =>
        accN A verI verR ω l g s ∧ freshN A ω l g s ∧
          (¬ relN A ext ω l g s ∨ hitN A ext ω l g s))) := rfl
  have e2 : pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) =
      pr (TapeN U M CI CR G S) (simGN (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) (fun ω l g s =>
          accN A verI verR ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s)) := rfl
  have e3 : pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (hitN A ext)) =
      pr (TapeN U M CI CR G S) (simGN (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) (hitN A ext)) := rfl
  rw [e1]
  rw [e2] at hse'
  rw [e3] at hhit
  linarith

/-- **Proposition U3 (no nullifier squatting) for `U` honest tokens and `M` honest redemptions**:
the probability that an accepted redemption with a fresh statement carries the nullifier of some
honest token for its context is at most the bound of `nmUN`. -/
theorem noSquatN [Nonempty S] [Nonempty (SecN U)]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ,
      AdmI (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hAR : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ,
      AdmR (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A simI progI simR progR ext h) pts b) ≤ εprf) :
    pr (TapeN U M CI CR G S) (nmRealNE A PI PR (SquatN A verI verR)) ≤
      U * εI + M * εR + ∑ i, pr (TapeN U M CI CR G S) (deltaNU A PI PR simI progI simR progR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A simI progI simR progR ext h) +
          sprAdvN (A.ci h) (sprBN A simI progI simR progR ext h)) := by
  refine (pr_mono fun z hz => ?_).trans
    (nmUN A PI PR simI progI simR progR verI verR ext hzkI hεI hzkR hεR hAI hAR hse hAE pts hpts
      hprf)
  exact squatN_bad A verI verR ext hz

/-- **Theorem U4 (redemption non-malleability, no redirect to another digest, Anchor Set or
redemption context) for `U` honest tokens and `M` honest redemptions**: the probability of
`RedirectN` is at most the bound of `nmUN`. -/
theorem noRedirectUN [Nonempty S] [Nonempty (SecN U)]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ,
      AdmI (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hAR : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ,
      AdmR (distPN A PI PR simI progI simR progR verI verR ext i ω τ))
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A simI progI simR progR ext h) pts b) ≤ εprf) :
    pr (TapeN U M CI CR G S) (nmRealNE A PI PR (RedirectN A verI verR ext)) ≤
      U * εI + M * εR + ∑ i, pr (TapeN U M CI CR G S) (deltaNU A PI PR simI progI simR progR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A simI progI simR progR ext h) +
          sprAdvN (A.ci h) (sprBN A simI progI simR progR ext h)) := by
  refine (pr_mono fun z hz => ?_).trans
    (nmUN A PI PR simI progI simR progR verI verR ext hzkI hεI hzkR hεR hAI hAR hse hAE pts hpts
      hprf)
  exact redirectN_bad A verI verR ext hz

end Red

end VoleMole.Theft.MoussakaUnbound
