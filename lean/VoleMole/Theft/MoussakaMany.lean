import VoleMole.Theft.Many
import VoleMole.Theft.Moussaka

/-!
# Moussaka: redemption non-malleability for `U` honest tokens and `M` honest redemptions
(`security/moussaka.md` §5.3, Theorem 3)

`Theft/Moussaka.lean` proves Theorem 3 for one honest token with one redemption. This file proves
it for `U` honest tokens and `M` honest redemptions in total, on the generic game of
`Theft/Many.lean`, built as the unbound `Theft/MoussakaUnboundMany.lean`.

**The game NM^{U,M}.** `U` honest Clients with independent coins `ω h = (nf_h, r_h)` each request
a token for the adversary's contexts `ctx_iss h`, `ctx_red h` (slots `0 … U − 1`, the spec's
`issueRequestOf`, `specI_eqN`). The adversary (`ThiefN`: every Anchor and the Moderator) answers
token `h` with a signature it chooses from all `U` requests, and then makes `M` redemption
queries, one after the other: from the issuance requests and the redemption requests seen so far
it chooses a token, an Anchor Set and a challenge digest, and the Client of that token answers
as the spec does (`finalizeIssue`, `redeemOf` with the C++ `find_issuer`; `specR_eqN`). So a token
may be redeemed several times, under different sets and digests. These choices do not read the
tables. At the end the adversary reads the tables and outputs one operation (`MOp`).

**The event** (`BadN`): the operation is accepted (`AccOp`), its statement differs from every
honest statement of the same relation (`FreshOpN`), and the extracted witness is not a witness
or opens the commitment `t_h` of **some** honest token.

**`noRedirectN`**:

    Pr[BadN] ≤ U·ε_I + M·ε_R + Σ_i δ_i + ε_SE + Σ_h Adv^ow(inverter h),

with `ε_I`, `ε_R` zero knowledge of the two proof systems at the hops' distinguishers, `δ_i` the
collision term of hop `i`, `ε_SE` weak simulation-extractability with `U + M` simulated proofs
(`WeakSEN`, **a hypothesis**, L8 on paper), and `Adv^ow(inverter h)` the chance of the explicit
inverter of token `h` (the simulated world with the other Clients' coins as its own) of finding
an opening of `t_h` from `nf_h` and `t_h` alone (`owAdv`). The sum over `h` is the factor `U` of
the note's `U·Adv^ow-r`.
-/

open Finset

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {G S : Type} {U M : ℕ}

/-! ## The adversary and the honest Clients -/

/-- An instance of one of the two relations. -/
abbrev MI := IssueInstance ⊕ RedeemInstance

/-- The log of the honest Clients' statements and proofs, one entry per slot (`none`: the Client
refused). -/
abbrev Log := List (Option (MI × Bytes))

/-- The coins of the `U` honest Clients. -/
abbrev SecN (U : ℕ) := Fin U → Sec

/-- **The adversary**: every Anchor and the Moderator, against `U` honest tokens and `M` honest
redemptions. `respond h reqs` is the signature for token `h`, from all issuance requests;
`choose reqs reds` is the next redemption query, from the issuance requests and the redemption
requests so far: the token, the Anchor Set and the digest. -/
structure ThiefN (U M : ℕ) (G S : Type) where
  ctxIss : Fin U → Coins ctxBytes
  ctxRed : Fin U → Coins ctxBytes
  pk : Fin U → UOVKey
  respond : Fin U → List Bytes → Coins uovN
  choose : List Bytes → List (Except Error Bytes) → Fin U × AnchorSet × Bytes
  out : List Bytes → List (Except Error Bytes) → (Fin (U + M) → G) → S → MOp

variable (A : ThiefN U M G S)

def ThiefN.ci (h : Fin U) : Bytes := List.ofFn (A.ctxIss h)
def ThiefN.cr (h : Fin U) : Bytes := List.ofFn (A.ctxRed h)

/-- The issuance request of a log entry: `t ‖ π`. -/
def msgI : Option (MI × Bytes) → Bytes
  | some (.inl x, π) => x.t ++ π
  | _ => []

/-- The redemption request of a log entry: `nf ‖ π`, or the Client's refusal. -/
def msgR : Option (MI × Bytes) → Except Error Bytes
  | some (.inr x, π) => .ok (x.nf ++ π)
  | _ => .error .invalidToken

/-- The issuance requests and the redemption requests of a log. -/
def reqsOf (U : ℕ) (l : Log) : List Bytes := (l.take U).map msgI
def redsOf (U : ℕ) (l : Log) : List (Except Error Bytes) := (l.drop U).map msgR

/-- The redemption query after the log `l`: token, Anchor Set, digest, and the token's
signature. -/
def ThiefN.tok (l : Log) : Fin U := (A.choose (reqsOf U l) (redsOf U l)).1
def ThiefN.set (l : Log) : AnchorSet := (A.choose (reqsOf U l) (redsOf U l)).2.1
def ThiefN.cd (l : Log) : Bytes := (A.choose (reqsOf U l) (redsOf U l)).2.2
def ThiefN.sig (l : Log) : Bytes := List.ofFn (A.respond (A.tok l) (reqsOf U l))

/-- **The public form of the honest secrets**: the nullifiers `nf_h` and the commitments `t_h`. -/
abbrev Pub (U : ℕ) := (Fin U → Bytes) × (Fin U → Bytes)

/-- The commitment of token `h`. -/
def tOfN (ω : SecN U) (h : Fin U) : Bytes :=
  com (List.ofFn (ω h).1) (A.ci h) (A.cr h) (List.ofFn (ω h).2)

/-- The public form of the coins. -/
def pubOf (ω : SecN U) : Pub U := (fun h => List.ofFn (ω h).1, tOfN A ω)

/-- **The statement of the next slot**, from the public form: slot `h < U` is the issuance of
token `h`; a later slot is the redemption the adversary asks for, if the token finalized and
some key of the set verifies it. -/
def xN (p : Pub U) (l : Log) : Option MI :=
  if h : l.length < U then some (.inl ⟨p.2 ⟨l.length, h⟩, A.ci ⟨l.length, h⟩⟩)
  else if (A.pk (A.tok l)).eval (A.sig l) = p.2 (A.tok l) then
    match findIssuer (A.set l) (p.2 (A.tok l)) (A.sig l) with
    | none => none
    | some _ => some (.inr ⟨(A.set l).keys, p.1 (A.tok l), A.ci (A.tok l), A.cr (A.tok l),
        A.cd l⟩)
  else none

/-- **The statement and witness of the next slot.** -/
def xwN (ω : SecN U) (l : Log) : Option (MI × Bytes) :=
  if h : l.length < U then
    some (.inl ⟨tOfN A ω ⟨l.length, h⟩, A.ci ⟨l.length, h⟩⟩,
      encodeIssueWitness (List.ofFn (ω ⟨l.length, h⟩).1) (A.ci ⟨l.length, h⟩)
        (A.cr ⟨l.length, h⟩) (List.ofFn (ω ⟨l.length, h⟩).2))
  else if (A.pk (A.tok l)).eval (A.sig l) = tOfN A ω (A.tok l) then
    match findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) with
    | none => none
    | some i => some (.inr ⟨(A.set l).keys, List.ofFn (ω (A.tok l)).1, A.ci (A.tok l),
          A.cr (A.tok l), A.cd l⟩,
        encodeRedeemWitness (List.ofFn (ω (A.tok l)).1) (A.ci (A.tok l)) (A.cr (A.tok l))
          (List.ofFn (ω (A.tok l)).2) (A.sig l) i)
  else none

theorem xwN_fst (ω : SecN U) (l : Log) : (xwN A ω l).map Prod.fst = xN A (pubOf A ω) l := by
  unfold xwN xN
  have ht : (pubOf A ω).2 = tOfN A ω := rfl
  rw [ht]
  split_ifs with h hv
  · rfl
  · cases findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) <;> rfl
  · rfl

/-- The two relations, on the sum of the instance types. -/
abbrev RelMI : MI → Bytes → Prop := RelInl IssueRelW
abbrev RelMR : MI → Bytes → Prop := RelInr RedeemRelW

theorem xwN_relI (ω : SecN U) (l : Log) (hl : l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelMI x w := by
  intro x w h
  unfold xwN at h
  simp only [hl, ↓reduceDIte] at h
  cases h
  exact ⟨⟨List.ofFn (ω ⟨l.length, hl⟩).1, List.ofFn (ω ⟨l.length, hl⟩).2, A.cr ⟨l.length, hl⟩,
    List.length_ofFn, List.length_ofFn, List.length_ofFn, rfl, rfl⟩, List.length_ofFn⟩

theorem xwN_relR (ω : SecN U) (l : Log) (hl : ¬ l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelMR x w := by
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
    exact ⟨⟨List.ofFn (ω (A.tok l)).2, A.sig l, i, pk, List.length_ofFn, List.length_ofFn, hk, rfl,
      he⟩, (A.set l).valid.2.1, List.length_ofFn, List.length_ofFn, List.length_ofFn⟩

/-! ## The provers and simulators on the sum of the instance types -/

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- The two provers as one, with uniform randomness and an optional output. -/
abbrev PM : MI → Bytes → Coins proveSeedBytes → G → S → Option Bytes :=
  sumProve (fun x w ρ g s => PI w x (List.ofFn ρ) g s) (fun x w ρ g s => PR w x (List.ofFn ρ) g s)

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)

/-- The two simulators as one, with coins for both. -/
abbrev simM : MI → CI × CR → Option Bytes := sumSim simI simR

/-- The two programmings as one. -/
abbrev progM : MI → CI × CR → S → S := sumProg progI progR

/-- **The real slot**: the log entry of the next honest proof. -/
def PN (ω : SecN U) (l : Log) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Option (MI × Bytes) :=
  pairO (xN A (pubOf A ω) l) (proveO (PM PI PR) (xwN A ω l) ρ g s)

/-- **The simulated slot**, from the public form of the secrets. -/
def SmP (p : Pub U) (l : Log) (c : CI × CR) : Option (MI × Bytes) :=
  pairO (xN A p l) (simO (simM simI simR) (xN A p l) c)

/-- The simulated slot's programming. -/
def pgP (p : Pub U) (l : Log) (c : CI × CR) (s : S) : S :=
  progO (progM progI progR) (xN A p l) c s

/-! ## The game runs the spec -/

/-- **Slot `h < U` is `issue_request`** of Client `h`. -/
theorem specI_eqN (ω : SecN U) (l : Log) (hl : l.length < U) (ρ : Coins proveSeedBytes) (g : G)
    (s : S) :
    msgI (PN A PI PR ω l ρ g s) =
      (issueRequestOf (nizkG PI g s) (A.ci ⟨l.length, hl⟩) (A.cr ⟨l.length, hl⟩)
        (List.ofFn (ω ⟨l.length, hl⟩).1) (List.ofFn (ω ⟨l.length, hl⟩).2) (List.ofFn ρ)).2 := by
  simp only [PN, xN, xwN, hl, ↓reduceDIte]
  rfl

/-- **A slot `≥ U` is `finalize_issue` and `redeem_request`** of the Client the adversary chose,
under its Anchor Set and digest. -/
theorem specR_eqN (ω : SecN U) (l : Log) (hl : ¬ l.length < U) (ρ : Coins proveSeedBytes) (g : G)
    (s : S) :
    msgR (PN A PI PR ω l ρ g s) =
      match finalizeIssue (A.pk (A.tok l))
          ⟨List.ofFn (ω (A.tok l)).1, List.ofFn (ω (A.tok l)).2, A.ci (A.tok l), A.cr (A.tok l),
            tOfN A ω (A.tok l)⟩ (A.sig l) with
      | none => .error .invalidToken
      | some tok => redeemOf (nizkG PR g s) tok (A.set l) (A.ci (A.tok l)) (A.cr (A.tok l))
          (A.cd l) (List.ofFn ρ) := by
  simp only [PN, xN, xwN, hl, ↓reduceDIte, finalizeIssue]
  have hp : (pubOf A ω).2 = tOfN A ω := rfl
  rw [hp]
  by_cases hv : (A.pk (A.tok l)).eval (A.sig l) = tOfN A ω (A.tok l)
  · simp only [hv, ite_true]
    unfold redeemOf
    have ht : com (List.ofFn (ω (A.tok l)).1) (A.ci (A.tok l)) (A.cr (A.tok l))
        (List.ofFn (ω (A.tok l)).2) = tOfN A ω (A.tok l) := rfl
    simp only [ht]
    cases findIssuer (A.set l) (tOfN A ω (A.tok l)) (A.sig l) <;> rfl
  · simp only [hv, ite_false]
    rfl

/-! ## The event -/

/-- The adversary's operation, from the log. -/
def opN (l : Log) (g : Fin (U + M) → G) (s : S) : MOp := A.out (reqsOf U l) (redsOf U l) g s

/-- **Its statement is fresh**: it differs from every honest statement of the same relation. -/
def FreshOpN (l : Log) (op : MOp) : Prop :=
  match op with
  | .issue req ci => ∀ x π, some (Sum.inl x, π) ∈ l → stOfI req ci ≠ x
  | .redeem S' req ci cr cd => ∀ x π, some (Sum.inr x, π) ∈ l → stOfR S' req ci cr cd ≠ x

/-- **The extractor**: the log, the adversary's last stage, the tables. -/
abbrev ExtN (U M : ℕ) (G S : Type) :=
  Log → ((Fin (U + M) → G) → S → MOp) → (Fin (U + M) → G) → S → Bytes

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : ExtN U M G S)

def accN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  AccOp verI verR (opN A l g s) s

def freshN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  FreshOpN l (opN A l g s)

def relN (_ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  RelOp (opN A l g s) (ext l (opN A l) g s)

/-- The witness opens the commitment of the honest token `h`. -/
def opensH (h : Fin U) (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  OpensOp (tOfN A ω h) (opN A l g s) (ext l (opN A l) g s)

/-- The witness opens the commitment of some honest token. -/
def opensN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  ∃ h, opensH A ext h ω l g s

/-- **The bad event.** -/
def BadN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧ (¬ relN A ext ω l g s ∨ opensN A ext ω l g s)

/-- The tape of the game: the Clients' coins, the slots, the shared tables. -/
abbrev TapeN (U M : ℕ) (CI CR G S : Type) :=
  (SecN U × (Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G)) × S

/-- **The real game NM^{U,M}.** -/
def nmRealN [Nonempty G] (z : TapeN U M CI CR G S) : Prop :=
  realGN (PN A PI PR) (BadN A verI verR ext) z

/-- **The simulated game** for an event. -/
def nmSimN (Ev : SecN U → Log → (Fin (U + M) → G) → S → Prop) [Nonempty CI] [Nonempty CR]
    (z : TapeN U M CI CR G S) : Prop :=
  simGN (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω)) Ev z

/-- **The collision term of hop `i`.** -/
def deltaNM [Nonempty CI] [Nonempty CR] [Nonempty G] (i : Fin (U + M))
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

/-- **No redirect off the bad event.** An accepted redemption whose statement differs from every
honest one has a witness, and its commitment `Com(nf*, ctx_iss*, ctx_red*, r)` is not the
commitment of any honest token. -/
theorem not_redirectN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) (S' : AnchorSet)
    (req ci cr cd : Bytes) (hq : opN A l g s = .redeem S' req ci cr cd)
    (hA : accN A verI verR ω l g s) (hF : freshN A ω l g s)
    (hB : ¬ BadN A verI verR ext ω l g s) :
    RedeemRel (stOfR S' req ci cr cd) (ext l (opN A l) g s) ∧
      ∀ h, com (req.take nfBytes) ci cr ((ext l (opN A l) g s).take rBytes) ≠ tOfN A ω h := by
  have h : relN A ext ω l g s ∧ ¬ opensN A ext ω l g s := by
    unfold BadN at hB; tauto
  obtain ⟨hR, hO⟩ := h
  simp only [relN, hq, RelOp] at hR
  refine ⟨hR, fun h hc => hO ⟨h, ?_⟩⟩
  simp only [opensH, hq, OpensOp, opensOf, List.mem_cons, List.not_mem_nil, or_false, comOf,
    exists_eq_left]
  exact hc

/-! ## The simulated world and the inverters, per honest token -/

/-- The coins of the reduction for token `h`: the other Clients' coins, the slots, the tables. -/
abbrev RedC (U M : ℕ) (CI CR G S : Type) (h : Fin U) :=
  ({j : Fin U // j ≠ h} → Sec) × ((Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G) × S)

/-- The Clients' coins from token `h`'s and the others'. -/
def insSec (h : Fin U) (x : Sec) (o : {j : Fin U // j ≠ h} → Sec) : SecN U :=
  fun j => if e : j = h then x else o ⟨j, e⟩

/-- **The public form with token `h` given by its nullifier and commitment**, the other tokens by
their coins. -/
def pubH (h : Fin U) (nf t : Bytes) (o : {j : Fin U // j ≠ h} → Sec) : Pub U :=
  (fun j => if e : j = h then nf else List.ofFn (o ⟨j, e⟩).1,
    fun j => if e : j = h then t
      else com (List.ofFn (o ⟨j, e⟩).1) (A.ci j) (A.cr j) (List.ofFn (o ⟨j, e⟩).2))

theorem pubOf_insSec (h : Fin U) (x : Sec) (o : {j : Fin U // j ≠ h} → Sec) :
    pubOf A (insSec h x o) =
      pubH A h (List.ofFn x.1) (com (List.ofFn x.1) (A.ci h) (A.cr h) (List.ofFn x.2)) o := by
  unfold pubOf pubH tOfN insSec
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
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

/-- **The inverter of token `h`**: the simulated world from `nf_h` and `t_h` alone (the other
Clients' coins, the slots and the tables as its coins), the adversary, the extractor; it outputs
the first extracted opening of `t_h`. -/
noncomputable def inverterN (h : Fin U) (nf t : Bytes) (b : RedC U M CI CR G S h) : Open4 :=
  pick t (opensOf
    (opN A (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h nf t b.1) (tapeC b.2.1)
        (U + M)).1 (tapeG b.2.1)
      ((simPre (SmP A simI simR) (pgP A progI progR) (pubH A h nf t b.1) (tapeC b.2.1)
        (U + M)).2 b.2.2))
    (ext (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h nf t b.1) (tapeC b.2.1)
        (U + M)).1
      (opN A (simPre (SmP A simI simR) (pgP A progI progR) (pubH A h nf t b.1) (tapeC b.2.1)
        (U + M)).1) (tapeG b.2.1)
      ((simPre (SmP A simI simR) (pgP A progI progR) (pubH A h nf t b.1) (tapeC b.2.1)
        (U + M)).2 b.2.2)))

/-- The simulated game with the opening of `t_h`, on the regrouped tape, is the inverter's
input. -/
theorem nmSimN_opensH (h : Fin U) (y : Sec × RedC U M CI CR G S h) :
    nmSimN A simI progI simR progR (opensH A ext h) (regroupH h y) →
      comOf (inverterN A simI progI simR progR ext h (List.ofFn y.1.1)
        (com (List.ofFn y.1.1) (A.ci h) (A.cr h) (List.ofFn y.1.2)) y.2) =
        com (List.ofFn y.1.1) (A.ci h) (A.cr h) (List.ofFn y.1.2) := by
  have hm := simPre_map (pubOf A) (SmP A simI simR) (pgP (S := S) A progI progR)
    (insSec h y.1 y.2.1) (tapeC y.2.2.1) (U + M)
  have hp := pubOf_insSec A h y.1 y.2.1
  have ht : tOfN A (insSec h y.1 y.2.1) h =
      com (List.ofFn y.1.1) (A.ci h) (A.cr h) (List.ofFn y.1.2) := by
    simp [tOfN, insSec]
  intro hz
  simp only [nmSimN, simGN, opensH, regroupH, Equiv.coe_fn_mk, hm, hp, ht] at hz
  exact pick_win _ _ hz

section Red

variable [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **One-wayness step.** In the simulated world, an opening of some honest `t_h` is found by
the inverter of token `h`. -/
theorem sim_opens_leN :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (opensN A ext)) ≤
      ∑ h : Fin U, owAdv (A.ci h) (A.cr h) (inverterN A simI progI simR progR ext h) := by
  have hex : ∀ z : TapeN U M CI CR G S, nmSimN A simI progI simR progR (opensN A ext) z →
      ∃ h, nmSimN A simI progI simR progR (opensH A ext h) z := fun z hz => hz
  refine (pr_mono hex).trans ((pr_exists_le_sum _).trans (Finset.sum_le_sum fun h _ => ?_))
  rw [← pr_equiv (regroupH h)]
  unfold owAdv
  exact pr_mono fun y hy => nmSimN_opensH A simI progI simR progR ext h y hy

variable [Nonempty G]

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
def seEvN (ω : SecN U) (l : Log) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verR ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s

/-- **Weak simulation-extractability step.** -/
theorem sim_se_leN {AdmE : ((Fin (U + M) → G) → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simR) (progM progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤ εSE :=
  simGN_le_of_weakSEN (ρ := Coins proveSeedBytes) hse (fun ω l => xN A (pubOf A ω) l)
    (fun _ l => opN A l) fun _ l => hAE l

/-- **Redemption non-malleability for `U` honest tokens and `M` honest redemptions (Theorem 3).**
For every adversary, with zero knowledge of both proof systems at the hops' distinguishers and
weak simulation-extractability with `U + M` simulated proofs:

    Pr[BadN] ≤ U·ε_I + M·ε_R + Σ_i δ_i + ε_SE + Σ_h Adv^ow(inverter h). -/
theorem noRedirectN [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : ((Fin (U + M) → G) → S → MOp) → Prop} {εI εR εSE : ℝ}
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
    (hse : WeakSEN (U + M) (simM simI simR) (progM progI progR) (AccOp verI verR) FreshOpN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmRealN A PI PR verI verR ext) ≤
      U * εI + M * εR + ∑ i, pr (TapeN U M CI CR G S) (deltaNM A PI PR simI progI simR progR i) +
        εSE + ∑ h : Fin U, owAdv (A.ci h) (A.cr h) (inverterN A simI progI simR progR ext h) := by
  have hzkI' : ZeroKnowledgeRO RelMI (PM PI PR) (simM simI simR) (progM progI progR)
      (fun D => AdmI (fun o g s => D (some o) g s)) εI := zk_sum_inl hzkI
  have hzkR' : ZeroKnowledgeRO RelMR (PM PI PR) (simM simI simR) (progM progI progR)
      (fun D => AdmR (fun o g s => D (some o) g s)) εR := zk_sum_inr hzkR
  have h := theftN_le (Ω := SecN U) (ρ := Coins proveSeedBytes) (C := CI × CR) (G := G) (S := S)
    (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω))
    (accN A verI verR) (freshN A) (relN A ext) (opensN A ext)
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
  have hop := sim_opens_leN A simI progI simR progR ext
  have hε : ∑ i : Fin (U + M), (if i.val < U then εI else εR) = U * εI + M * εR := by
    rw [Fin.sum_univ_add]
    simp
  have hsplit : ∑ i : Fin (U + M), ((if i.val < U then εI else εR) +
        pr (TapeN U M CI CR G S) (deltaN (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
          (fun ω => pgP A progI progR (pubOf A ω)) i)) =
      U * εI + M * εR +
        ∑ i, pr (TapeN U M CI CR G S) (deltaNM A PI PR simI progI simR progR i) := by
    rw [Finset.sum_add_distrib, hε]
    rfl
  rw [hsplit] at h
  have e1 : pr (TapeN U M CI CR G S) (nmRealN A PI PR verI verR ext) =
      pr (TapeN U M CI CR G S) (realGN (PN A PI PR) (fun ω l g s =>
        accN A verI verR ω l g s ∧ freshN A ω l g s ∧
          (¬ relN A ext ω l g s ∨ opensN A ext ω l g s))) := rfl
  have e2 : pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) =
      pr (TapeN U M CI CR G S) (simGN (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) (fun ω l g s =>
          accN A verI verR ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s)) := rfl
  have e3 : pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (opensN A ext)) =
      pr (TapeN U M CI CR G S) (simGN (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) (opensN A ext)) := rfl
  rw [e1]
  rw [e2] at hse'
  rw [e3] at hop
  linarith

end Red

end VoleMole.Theft.Moussaka
