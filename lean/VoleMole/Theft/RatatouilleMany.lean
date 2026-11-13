import VoleMole.Theft.ManyPlain
import VoleMole.Theft.Ratatouille

/-!
# Ratatouille: no theft for `U` honest Clients and `M` honest spends
(`security/ratatouille.md` §5, Theorem 3, N2a in its extraction form)

`Theft/Ratatouille.lean` proves Theorem 3 for one honest Client with one issuance and one spend.
This file proves it for `U` honest Clients and `M` honest spends in total, with the change tokens
chained, on the generic game of `Theft/Many.lean`.

**The game THEFT^{U,M}.** Slot `j < U + M` has its own secret coins `(nf_j, r_j)`.

* Slots `0 … U − 1`: Client `h` requests a token worth `T_init h` under `ctx h` with the coins of
  slot `h` (the spec's `issueOf`, `specI_eqN`). The adversary (`ThiefN`: the Issuer, with one key
  `pk`) answers Client `h` with a signature it chooses from all `U` requests, and the Client
  finalizes (`finalizeIssue`, `fin_issue`).
* Slots `U … U + M − 1`: the adversary chooses, from every request seen so far, a Client and an
  amount `d`. That Client spends `d` from its **current** token (its issued token, or the change
  token of its last spend), with the coins of the slot for the change commitment (the spec's
  `spendOf`, `specS_eqN`). The adversary then answers with a refund and a signature chosen from
  the requests including this one, and the Client finalizes its change token (`finalizeSpend`,
  `fin_spend`). A spend the Client refuses (`std::invalid_argument`) keeps the token; a prover
  abort consumes it, as in the C++.

  These choices do not read the tables. At the end the adversary reads the tables and outputs one
  Issuer operation (`Op`).

The Clients' state is kept in public form (`St`, `PTok`: which slot's coins made the token's
commitment, and `t`, `x`, `s`), as a function of the log of honest statements and proofs
(`stOf`), so that the simulated world needs the secrets only through the nullifiers and the
commitment functions `(ctx, t) ↦ Com(nf_j, ctx, t, r_j)` (`Pub`).

**The event** (`BadN`): the operation is accepted with the key `pk` (`AccOp`), its statement
differs from every honest statement of the same relation in the log (`FreshOpN`), and the
extracted witness is not a witness or opens the commitment of **some** honest slot (`comAt`: the
commitment `Com(nf_j, ctx, t, r_j)` in the statement slot `j` proves; an issued state or a change
state). Off this event an accepted fresh spend has a witness whose parent commitment and change
commitment are no honest commitment (`not_theftN_spend`): it spends a separately certified state,
also when its nullifier is an honest one (nullifier squatting, the correction to N2a).

**`noTheftN`**:

    Pr[BadN] ≤ U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(inverter j),

with `ε_I`, `ε_S` zero knowledge of the two proof systems at the hops' distinguishers, `δ_i` the
collision term of hop `i`, `ε_SE` weak simulation-extractability with `U + M` simulated proofs
(`WeakSEN`, **a hypothesis**), and `Adv^ow(inverter j)` (`owAdvK`) the chance of the explicit
inverter of slot `j` (the simulated world with the other slots' coins as its own) of opening a
commitment `Com(nf_j, ctx, t, r_j)` at a context and credit value of its choice, from `nf_j` and
the commitment function alone. The sum has `U + M` terms: one per honest commitment.
-/

open Finset

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {Z : Sizes} {G S : Type} {U M : ℕ}

/-! ## The adversary and the public form of the secrets -/

/-- An instance of one of the two relations. -/
abbrev RI := IssueInstance ⊕ SpendInstance

/-- A proof of one of the two relations. -/
abbrev RP (Z : Sizes) := IssueProof Z ⊕ SpendProof Z

/-- A log entry: the statement and proof of one honest slot (`none`: no request was sent). -/
abbrev Ent (Z : Sizes) := Option (RI × RP Z)

/-- The log of the honest slots. -/
abbrev LogR (Z : Sizes) := List (Ent Z)

/-- **The adversary**: the Issuer, against `U` honest Clients and `M` honest spends.
`respond h reqs` is the signature for Client `h`, from all issuance requests; `choose reqs sps` is
the next spend query (a Client and an amount), from the issuance requests and the spend requests
so far; `respondS reqs sps` is the response (refund and signature) to the last spend request of
`sps`. -/
structure ThiefN (Z : Sizes) (U M : ℕ) (G S : Type) where
  pk : PublicKey
  ctx : Fin U → Context
  tInit : Fin U → Credits
  respond : Fin U → List (Except Error (IssueRequest Z)) → Preimage
  choose : List (Except Error (IssueRequest Z)) → List (Except Error (SpendRequest Z)) →
    Fin U × Credits
  respondS : List (Except Error (IssueRequest Z)) → List (Except Error (SpendRequest Z)) →
    SpendResponse
  out : List (Except Error (IssueRequest Z)) → List (Except Error (SpendRequest Z)) →
    (Fin (U + M) → G) → S → Op Z

variable (A : ThiefN Z U M G S)

/-- The one-Client adversary record with the same key. The parts `AccOp`, `RelOp`, `opXS` of the
event (`Theft/Ratatouille.lean`) read only its key. -/
def ThiefN.base : Thief Z G S :=
  ⟨A.pk, Vector.replicate 16 0, 0, fun _ => Vector.replicate 119 0, fun _ => 0,
    fun _ _ _ _ _ => .issue (Vector.replicate _ 0) 0 (Vector.replicate 16 0)⟩

/-- The coins of one slot: `(nf, r)`. -/
abbrev SecC := Coins 24 × Coins 16

/-- The coins of the `U + M` slots. -/
abbrev SecN (U M : ℕ) := Fin (U + M) → SecC

/-- The public form of a slot's coins: the nullifier and the commitment function
`(ctx, t) ↦ Com(nf, ctx, t, r)`. -/
abbrev PubC := Nullifier × (Context → Credits → Commitment)

/-- The public form of the secrets, by slot. -/
abbrev Pub := ℕ → PubC

def pubC (x : SecC) : PubC := (vec x.1, fun c t => com (vec x.1) c t (vec x.2))

/-- The coins of slot `i` (arbitrary beyond the last slot; never used). -/
noncomputable def secAt (ω : SecN U M) (i : ℕ) : SecC := extN ω i

/-- **The public form of the coins.** -/
noncomputable def pubOf (ω : SecN U M) : Pub := fun i => pubC (secAt ω i)

/-! ## The Clients' state, in public form -/

/-- **A token in public form**: the slot whose coins made its commitment, `t`, `x` and `s`. -/
structure PTok where
  src : ℕ
  t : Credits
  x : Credits
  s : Preimage

/-- **The state of the game** after some slots: their number, the issuance requests and the spend
requests so far (as the adversary sees them), and each Client's current token. -/
structure St (Z : Sizes) (U : ℕ) where
  n : ℕ
  iss : List (Except Error (IssueRequest Z))
  sp : List (Except Error (SpendRequest Z))
  cur : Fin U → Option PTok

def St.init : St Z U := ⟨0, [], [], fun _ => none⟩

/-- The Client and the amount of the next spend query. -/
def ThiefN.who (σ : St Z U) : Fin U := (A.choose σ.iss σ.sp).1
def ThiefN.amt (σ : St Z U) : Credits := (A.choose σ.iss σ.sp).2

/-- **The statement of the next slot and the credit value its commitment commits to**, or the
exception the Client throws before proving. A slot `< U` is the issuance of Client `n`
(`std::invalid_argument` if `T_init = 0`). A later slot is the spend the adversary asks for:
`std::logic_error` if the Client has no token, `std::invalid_argument` if the token is not valid
for `pk` or does not afford `d` (`spend_request_with_seed`'s checks). -/
def xtE (p : Pub) (σ : St Z U) : Except Error (RI × Credits) :=
  if h : σ.n < U then
    if A.tInit ⟨σ.n, h⟩ = 0 then .error .invalidArgument
    else .ok (.inl ⟨(p σ.n).2 (A.ctx ⟨σ.n, h⟩) (A.tInit ⟨σ.n, h⟩), A.tInit ⟨σ.n, h⟩,
      A.ctx ⟨σ.n, h⟩⟩, A.tInit ⟨σ.n, h⟩)
  else
    match σ.cur (A.who σ) with
    | none => .error .logic
    | some τ =>
      if uovEval A.pk τ.s = tag ((p τ.src).2 (A.ctx (A.who σ)) τ.t) τ.x then
        match clientCheck τ.t τ.x (A.amt σ) with
        | none => .error .invalidArgument
        | some t' => .ok (.inr ⟨A.pk, (p τ.src).1, A.amt σ, (p σ.n).2 (A.ctx (A.who σ)) t',
            A.ctx (A.who σ)⟩, t')
      else .error .invalidArgument

/-- The commitment and the context of a statement. -/
def cOf : RI → Commitment
  | .inl x => x.c
  | .inr x => x.cNext

def ctxOf : RI → Context
  | .inl x => x.ctx
  | .inr x => x.ctx

/-- **The commitment of a slot's statement is the slot's commitment function** at the statement's
context and the committed credit value. -/
theorem xtE_com {p : Pub} {σ : St Z U} {xt : RI × Credits} (h : xtE A p σ = .ok xt) :
    cOf xt.1 = (p σ.n).2 (ctxOf xt.1) xt.2 := by
  unfold xtE at h
  split_ifs at h with h1 h2
  · cases h; rfl
  · cases hc : σ.cur (A.who σ) with
    | none => rw [hc] at h; cases h
    | some τ =>
      rw [hc] at h
      simp only at h
      split_ifs at h
      cases hk : clientCheck τ.t τ.x (A.amt σ) with
      | none => rw [hk] at h; cases h
      | some t' => rw [hk] at h; cases h; rfl

/-- The issuance request of Client `h`, from its log entry: the request, or the exception. -/
def entI (h : Fin U) (e : Ent Z) : Except Error (IssueRequest Z) :=
  match e with
  | some (.inl x, .inl π) => .ok (issueReqBytes x.c π)
  | _ => if A.tInit h = 0 then .error .invalidArgument else .error .runtime

/-- The exception of a spend slot with no request: the Client's, or `std::runtime_error` (the
prover aborted). -/
def errS (p : Pub) (σ : St Z U) : Error :=
  match xtE A p σ with
  | .error er => er
  | .ok _ => .runtime

/-- The spend request of a slot, from its log entry: the request, or the exception. -/
def entS (p : Pub) (σ : St Z U) (e : Ent Z) : Except Error (SpendRequest Z) :=
  match e with
  | some (.inr x, .inr π) => .ok (SpendReq.toBytes ⟨x.nf, x.d, x.cNext, π⟩)
  | _ => .error (errS A p σ)

/-- **Client `i`'s token after `finalize_issue`** on the adversary's response, if its request was
sent. -/
def tok0 (p : Pub) (iss : List (Except Error (IssueRequest Z))) (i : Fin U) : Option PTok :=
  match iss[i.val]? with
  | some (.ok _) =>
    if uovEval A.pk (A.respond i iss) = tag ((p i).2 (A.ctx i) (A.tInit i)) 0 then
      some ⟨i, A.tInit i, 0, A.respond i iss⟩
    else none
  | _ => none

/-- **The spending Client's token after a spend slot**: unchanged if the Client refused; consumed
if the prover aborted; otherwise the change token after `finalize_spend` on the adversary's
response (`sp'`: the spend requests including this one). -/
def curS (p : Pub) (σ : St Z U) (e : Ent Z) (sp' : List (Except Error (SpendRequest Z))) :
    Option PTok :=
  match xtE A p σ with
  | .error _ => σ.cur (A.who σ)
  | .ok xt =>
    match e with
    | some (.inr _, .inr _) =>
      if uovEval A.pk (respSig (A.respondS σ.iss sp')) =
          tag (cOf xt.1) (respRefund (A.respondS σ.iss sp')) then
        some ⟨σ.n, xt.2, respRefund (A.respondS σ.iss sp'), respSig (A.respondS σ.iss sp')⟩
      else none
    | _ => none

/-- **One slot.** An issuance slot records the request; after the last one every Client finalizes.
A spend slot records the request and updates the spending Client's token. -/
def step (p : Pub) (σ : St Z U) (e : Ent Z) : St Z U :=
  if h : σ.n < U then
    ⟨σ.n + 1, σ.iss ++ [entI A ⟨σ.n, h⟩ e], [],
      if σ.n + 1 = U then tok0 A p (σ.iss ++ [entI A ⟨σ.n, h⟩ e]) else fun _ => none⟩
  else
    ⟨σ.n + 1, σ.iss, σ.sp ++ [entS A p σ e],
      Function.update σ.cur (A.who σ) (curS A p σ e (σ.sp ++ [entS A p σ e]))⟩

/-- **The state after a log.** -/
def stOf (p : Pub) (l : LogR Z) : St Z U := l.foldl (step A p) St.init

theorem stOf_snoc (p : Pub) (l : LogR Z) (e : Ent Z) :
    stOf A p (l ++ [e]) = step A p (stOf A p l) e := by
  simp [stOf, List.foldl_append]

theorem step_n (p : Pub) (σ : St Z U) (e : Ent Z) : (step A p σ e).n = σ.n + 1 := by
  unfold step; split <;> rfl

theorem foldl_step_n (p : Pub) (l : LogR Z) :
    ∀ σ : St Z U, (l.foldl (step A p) σ).n = σ.n + l.length := by
  induction l with
  | nil => intro σ; rfl
  | cons e l ih =>
    intro σ
    rw [List.foldl_cons, ih, step_n, List.length_cons]
    omega

/-- The state after a log has seen as many slots as the log has entries. -/
theorem stOf_n (p : Pub) (l : LogR Z) : (stOf A p l).n = l.length := by
  rw [stOf, foldl_step_n]; simp [St.init]

/-- **The statement of the next slot**, from the public form and the log. -/
def xN (p : Pub) (l : LogR Z) : Option RI :=
  match xtE A p (stOf A p l) with
  | .ok xt => some xt.1
  | .error _ => none

/-- The witness of a slot's statement: the slot's coins, and for a spend the current token. -/
noncomputable def witE (ω : SecN U M) (σ : St Z U) (t' : Credits) : Wit :=
  (⟨vec (secAt ω σ.n).1, vec (secAt ω σ.n).2⟩,
    match σ.cur (A.who σ) with
    | some τ => ⟨τ.t, vec (secAt ω τ.src).2, τ.x, τ.s, vec (secAt ω σ.n).1, t',
        vec (secAt ω σ.n).2⟩
    | none => ⟨0, vec (secAt ω σ.n).2, 0, Vector.replicate 119 0, vec (secAt ω σ.n).1, t',
        vec (secAt ω σ.n).2⟩)

/-- **The statement and witness of the next slot.** -/
noncomputable def xwN (ω : SecN U M) (l : LogR Z) : Option (RI × Wit) :=
  match xtE A (pubOf ω) (stOf A (pubOf ω) l) with
  | .ok xt => some (xt.1, witE A ω (stOf A (pubOf ω) l) xt.2)
  | .error _ => none

theorem xwN_fst (ω : SecN U M) (l : LogR Z) :
    (xwN A ω l).map Prod.fst = xN A (pubOf ω) l := by
  unfold xwN xN
  cases xtE A (pubOf ω) (stOf A (pubOf ω) l) <;> rfl

/-- The two relations, on the sum of the instance types. -/
abbrev RelRI : RI → Wit → Prop := RelOInl IssueRel
abbrev RelRS : RI → Wit → Prop := RelOInr SpendRel

theorem xwN_relI (ω : SecN U M) (l : LogR Z) (hl : l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelRI x w := by
  intro x w h
  have hn : (stOf A (pubOf ω) l).n < U := by rw [stOf_n]; exact hl
  unfold xwN at h
  cases hx : xtE A (pubOf ω) (stOf A (pubOf ω) l) with
  | error er => rw [hx] at h; cases h
  | ok xt =>
    rw [hx] at h
    cases h
    unfold xtE at hx
    simp only [hn, ↓reduceDIte] at hx
    split_ifs at hx
    cases hx
    rfl

theorem xwN_relS (ω : SecN U M) (l : LogR Z) (hl : ¬ l.length < U) :
    ∀ x w, xwN A ω l = some (x, w) → RelRS x w := by
  intro x w h
  have hn : ¬ (stOf A (pubOf ω) l).n < U := by rw [stOf_n]; exact hl
  unfold xwN at h
  cases hx : xtE A (pubOf ω) (stOf A (pubOf ω) l) with
  | error er => rw [hx] at h; cases h
  | ok xt =>
    rw [hx] at h
    cases h
    unfold xtE at hx
    simp only [hn, ↓reduceDIte] at hx
    cases hc : (stOf A (pubOf ω) l).cur (A.who (stOf A (pubOf ω) l)) with
    | none => rw [hc] at hx; cases hx
    | some τ =>
      rw [hc] at hx
      simp only at hx
      split_ifs at hx with hv
      cases hk : clientCheck τ.t τ.x (A.amt (stOf A (pubOf ω) l)) with
      | none => rw [hk] at hx; cases hx
      | some t' =>
        rw [hk] at hx
        cases hx
        simp only [RelRS, RelOInr, witE, hc]
        refine ⟨hv, rfl, ?_⟩
        have := clientCheck_eq hk
        simp only
        omega

/-! ## The provers and simulators on the sum of the instance types -/

variable (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
  (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))

/-- The two provers as one, with uniform randomness. -/
abbrev PM : RI → Wit → Coins 16 → G → S → Option (RP Z) := sumProveO (PI' PI) (PS' PS)

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → S → S) (simS : SpendInstance → CS → Option (SpendProof Z))
  (progS : SpendInstance → CS → S → S)

/-- The two simulators as one, with coins for both. -/
abbrev simM : RI → CI × CS → Option (RP Z) := sumSimO simI simS

/-- The two programmings as one. -/
abbrev progM : RI → CI × CS → S → S := sumProg progI progS

/-- **The real slot**: the log entry of the next honest proof. -/
noncomputable def PN (ω : SecN U M) (l : LogR Z) (ρ : Coins 16) (g : G) (s : S) : Ent Z :=
  pairO (xN A (pubOf ω) l) (proveO (PM PI PS) (xwN A ω l) ρ g s)

/-- **The simulated slot**, from the public form of the secrets. -/
def SmP (p : Pub) (l : LogR Z) (c : CI × CS) : Ent Z :=
  pairO (xN A p l) (simO (simM simI simS) (xN A p l) c)

/-- The simulated slot's programming. -/
def pgP (p : Pub) (l : LogR Z) (c : CI × CS) (s : S) : S :=
  progO (progM progI progS) (xN A p l) c s

/-! ## The game runs the spec -/

/-- A token of the state, with its opening. -/
noncomputable def toTok (ω : SecN U M) (τ : PTok) : TokenS :=
  ⟨vec (secAt ω τ.src).1, τ.t, vec (secAt ω τ.src).2, τ.x, τ.s⟩

/-- Client `h`'s token (`Token::Impl`) in a state. -/
noncomputable def tokC (ω : SecN U M) (σ : St Z U) (h : Fin U) : Option TokenS :=
  (σ.cur h).map (toTok ω)

/-- **A slot `< U` is `issue_request_with_seed`** of Client `n`, at the coins of slot `n`. -/
theorem specI_eqN (ω : SecN U M) (l : LogR Z) (hn : (stOf A (pubOf ω) l).n < U) (ρ : Coins 16)
    (g : G) (s : S) :
    entI A ⟨(stOf A (pubOf ω) l).n, hn⟩ (PN A PI PS ω l ρ g s) =
      (issueOf (primT PI PS g s) (A.tInit ⟨(stOf A (pubOf ω) l).n, hn⟩)
        (A.ctx ⟨(stOf A (pubOf ω) l).n, hn⟩) (vec (secAt ω (stOf A (pubOf ω) l).n).1)
        (vec (secAt ω (stOf A (pubOf ω) l).n).2) (vec ρ)).map Prod.snd := by
  unfold PN xN xwN xtE issueOf
  simp only [hn, ↓reduceDIte]
  by_cases h0 : A.tInit ⟨(stOf A (pubOf ω) l).n, hn⟩ = 0
  · simp [h0, entI, pairO, Except.map]
  · simp only [h0, ↓reduceIte, proveO, PM, sumProveO, PI', primT, witE, pubOf, pubC]
    cases PI _ _ (vec ρ) g s <;> simp [entI, pairO, Except.map, h0]

/-- **A slot `≥ U` is `spend_request_with_seed`** of the Client the adversary chose, from its
current token, for the amount the adversary chose, at the coins of the slot. -/
theorem specS_eqN (ω : SecN U M) (l : LogR Z) (hn : ¬ (stOf A (pubOf ω) l).n < U) (ρ : Coins 16)
    (g : G) (s : S) :
    entS A (pubOf ω) (stOf A (pubOf ω) l) (PN A PI PS ω l ρ g s) =
      ((spendOf (primT PI PS g s) A.pk
        (tokC ω (stOf A (pubOf ω) l) (A.who (stOf A (pubOf ω) l)))
        (A.amt (stOf A (pubOf ω) l)) (A.ctx (A.who (stOf A (pubOf ω) l)))
        (vec (secAt ω (stOf A (pubOf ω) l).n).1) (vec (secAt ω (stOf A (pubOf ω) l).n).2)
        (vec ρ)).2).map Prod.snd := by
  unfold PN xN xwN
  generalize stOf A (pubOf ω) l = σ at hn ⊢
  cases hc : σ.cur (A.who σ) with
  | none =>
    have hx : xtE A (pubOf ω) σ = .error .logic := by
      unfold xtE; simp only [hn, ↓reduceDIte, hc]
    simp [hx, entS, errS, pairO, tokC, hc, spendOf, Except.map]
  | some τ =>
    by_cases hv : uovEval A.pk τ.s = tag ((pubOf ω τ.src).2 (A.ctx (A.who σ)) τ.t) τ.x
    · have hval : TokenS.Valid A.pk (A.ctx (A.who σ))
          ⟨vec (secAt ω τ.src).1, τ.t, vec (secAt ω τ.src).2, τ.x, τ.s⟩ := hv
      cases hk : clientCheck τ.t τ.x (A.amt σ) with
      | none =>
        have hx : xtE A (pubOf ω) σ = .error .invalidArgument := by
          unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte, hk]
        simp [hx, entS, errS, pairO, tokC, hc, spendOf, Except.map, hval, toTok, hk]
      | some t' =>
        have hx : xtE A (pubOf ω) σ = .ok (.inr ⟨A.pk, (pubOf ω τ.src).1, A.amt σ,
            (pubOf ω σ.n).2 (A.ctx (A.who σ)) t', A.ctx (A.who σ)⟩, t') := by
          unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte, hk]
        simp only [hx, tokC, hc, Option.map_some, spendOf, toTok, hk, proveO, PM, sumProveO, PS',
          primT, witE, pubOf, pubC]
        cases PS _ _ (vec ρ) g s <;> simp [entS, errS, pairO, Except.map, hx, hval]
    · have hval : ¬ TokenS.Valid A.pk (A.ctx (A.who σ))
          ⟨vec (secAt ω τ.src).1, τ.t, vec (secAt ω τ.src).2, τ.x, τ.s⟩ := hv
      have hx : xtE A (pubOf ω) σ = .error .invalidArgument := by
        unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte]
      simp [hx, entS, errS, pairO, tokC, hc, spendOf, Except.map, toTok, hval]

/-- **After the last issuance slot every Client finalizes**: its token is `tok0` of all `U`
requests. -/
theorem step_cur_issue (p : Pub) (σ : St Z U) (e : Ent Z) (hn : σ.n < U) :
    (step A p σ e).cur =
      if σ.n + 1 = U then tok0 A p (step A p σ e).iss else fun _ => none := by
  unfold step
  simp only [hn, ↓reduceDIte]

/-- **`tok0` is `finalize_issue`** of the Client's pending token on the adversary's response, if
its request was sent. -/
theorem fin_issue (ω : SecN U M) (iss : List (Except Error (IssueRequest Z))) (i : Fin U) :
    (tok0 A (pubOf ω) iss i).map (toTok ω) =
      match iss[i.val]? with
      | some (.ok _) =>
        match (finalizeIssue A.pk (some ⟨vec (secAt ω i).1, vec (secAt ω i).2, A.tInit i,
            com (vec (secAt ω i).1) (A.ctx i) (A.tInit i) (vec (secAt ω i).2)⟩)
            (A.respond i iss)).2 with
        | .ok o => o
        | .error _ => none
      | _ => none := by
  unfold tok0
  cases h : iss[i.val]? with
  | none => rfl
  | some r =>
    cases r with
    | error er => rfl
    | ok q =>
      simp only [finalizeIssue, pubOf, pubC]
      split_ifs with h1 <;> simp [h1, toTok]

/-- **A spend slot updates the spending Client's token as the spec does**: the token
`spend_request_with_seed` leaves if it throws, and otherwise the change token of
`finalize_spend` on the adversary's response to this request. -/
theorem fin_spend (ω : SecN U M) (l : LogR Z) (hn : ¬ (stOf A (pubOf ω) l).n < U) (ρ : Coins 16)
    (g : G) (s : S) :
    tokC ω (stOf A (pubOf ω) (l ++ [PN A PI PS ω l ρ g s])) (A.who (stOf A (pubOf ω) l)) =
      match spendOf (primT PI PS g s) A.pk
          (tokC ω (stOf A (pubOf ω) l) (A.who (stOf A (pubOf ω) l)))
          (A.amt (stOf A (pubOf ω) l)) (A.ctx (A.who (stOf A (pubOf ω) l)))
          (vec (secAt ω (stOf A (pubOf ω) l).n).1) (vec (secAt ω (stOf A (pubOf ω) l).n).2)
          (vec ρ) with
      | (_, .ok q) =>
        match (finalizeSpend A.pk (some q.1) (A.respondS (stOf A (pubOf ω) l).iss
            (stOf A (pubOf ω) (l ++ [PN A PI PS ω l ρ g s])).sp)).2 with
        | .ok o => o
        | .error _ => none
      | (τo, .error _) => τo := by
  rw [stOf_snoc]
  unfold PN xN xwN
  generalize stOf A (pubOf ω) l = σ at hn ⊢
  unfold step
  simp only [hn, ↓reduceDIte, tokC, Function.update_self]
  cases hc : σ.cur (A.who σ) with
  | none =>
    have hx : xtE A (pubOf ω) σ = .error .logic := by
      unfold xtE; simp only [hn, ↓reduceDIte, hc]
    simp [hx, curS, hc, spendOf]
  | some τ =>
    by_cases hv : uovEval A.pk τ.s = tag ((pubOf ω τ.src).2 (A.ctx (A.who σ)) τ.t) τ.x
    · have hval : TokenS.Valid A.pk (A.ctx (A.who σ))
          ⟨vec (secAt ω τ.src).1, τ.t, vec (secAt ω τ.src).2, τ.x, τ.s⟩ := hv
      cases hk : clientCheck τ.t τ.x (A.amt σ) with
      | none =>
        have hx : xtE A (pubOf ω) σ = .error .invalidArgument := by
          unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte, hk]
        simp [hx, curS, hc, spendOf, hval, toTok, hk]
      | some t' =>
        have hx : xtE A (pubOf ω) σ = .ok (.inr ⟨A.pk, (pubOf ω τ.src).1, A.amt σ,
            (pubOf ω σ.n).2 (A.ctx (A.who σ)) t', A.ctx (A.who σ)⟩, t') := by
          unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte, hk]
        simp only [hx, hc, Option.map_some, spendOf, toTok, hk, proveO, PM, sumProveO, PS',
          primT, witE, pubOf, pubC, curS, cOf]
        cases PS _ _ (vec ρ) g s with
        | none => simp [pairO, hval]
        | some pf =>
          simp only [pairO, Option.map_some, hval, not_true_eq_false, ↓reduceIte, finalizeSpend]
          split_ifs with h1 <;> simp [h1, toTok]
    · have hval : ¬ TokenS.Valid A.pk (A.ctx (A.who σ))
          ⟨vec (secAt ω τ.src).1, τ.t, vec (secAt ω τ.src).2, τ.x, τ.s⟩ := hv
      have hx : xtE A (pubOf ω) σ = .error .invalidArgument := by
        unfold xtE; simp only [hn, ↓reduceDIte, hc, hv, ↓reduceIte]
      simp [hx, curS, hc, spendOf, toTok, hval]

/-- A spend slot leaves the other Clients' tokens alone. -/
theorem fin_other (ω : SecN U M) (l : LogR Z) (hn : ¬ (stOf A (pubOf ω) l).n < U) (e : Ent Z)
    (h : Fin U) (hne : h ≠ A.who (stOf A (pubOf ω) l)) :
    tokC ω (stOf A (pubOf ω) (l ++ [e])) h = tokC ω (stOf A (pubOf ω) l) h := by
  rw [stOf_snoc]
  unfold step
  simp only [hn, ↓reduceDIte, tokC, Function.update_of_ne hne]

/-! ## The event -/

/-- The adversary's operation, from the requests of the log. -/
def opN (p : Pub) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Op Z :=
  A.out (stOf A p l).iss (stOf A p l).sp g s

/-- **Its statement is fresh**: it differs from every honest statement of the same relation in
the log (weak non-malleability; a verbatim copy is allowed, F2). -/
def FreshOpN (l : LogR Z) (op : Op Z) : Prop :=
  match op with
  | .issue q t c => ∀ x π, some (Sum.inl x, π) ∈ l → opXI q t c ≠ x
  | .spend q c _ => ∀ x π, some (Sum.inr x, π) ∈ l → opXS A.base q c ≠ x

/-- **The extractor**: the log, the adversary's last stage, the tables. -/
abbrev ExtN (Z : Sizes) (U M : ℕ) (G S : Type) :=
  LogR Z → ((Fin (U + M) → G) → S → Op Z) → (Fin (U + M) → G) → S → Wit

variable (verI : IssueInstance → IssueProof Z → S → Bool)
  (verS : SpendInstance → SpendProof Z → S → Bool) (ext : ExtN Z U M G S)

noncomputable def accN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  AccOp A.base verI verS (opN A (pubOf ω) l g s) s

noncomputable def freshN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  FreshOpN A l (opN A (pubOf ω) l g s)

noncomputable def relN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  RelOp A.base (opN A (pubOf ω) l g s) (ext l (opN A (pubOf ω) l) g s)

/-- **The commitment of slot `j`**: the commitment in the statement the slot proves after the
first `j` entries of the log (an issued state `Com(nf_j, ctx, T_init, r_j)` or a change state
`Com(nf_j, ctx, t', r_j)`), if the Client makes a statement. -/
def comAt (p : Pub) (l : LogR Z) (j : ℕ) : Option Commitment := (xN A p (l.take j)).map cOf

/-- The witness opens the commitment of the honest slot `j`. -/
noncomputable def opensJ (j : Fin (U + M)) (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G)
    (s : S) : Prop :=
  ∃ c, comAt A (pubOf ω) l j = some c ∧
    ∃ o ∈ opensOf (opN A (pubOf ω) l g s) (ext l (opN A (pubOf ω) l) g s), comOf o = c

/-- The witness opens the commitment of some honest slot. -/
noncomputable def opensN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  ∃ j, opensJ A ext j ω l g s

/-- **The bad event**: an accepted operation with a fresh statement whose extracted witness is
not a witness or opens the commitment of an honest slot. -/
noncomputable def BadN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verS ω l g s ∧ freshN A ω l g s ∧ (¬ relN A ext ω l g s ∨ opensN A ext ω l g s)

/-- The tape of the game: the slots' coins, the slots, the shared tables. -/
abbrev TapeN (U M : ℕ) (CI CS G S : Type) :=
  (SecN U M × (Fin (U + M) → Slot (Coins 16) (CI × CS) G)) × S

/-- **The real game THEFT^{U,M}.** -/
noncomputable def theftRealN [Nonempty G] (z : TapeN U M CI CS G S) : Prop :=
  realGN (PN A PI PS) (BadN A verI verS ext) z

/-- **The simulated game** for an event. -/
noncomputable def theftSimN (Ev : SecN U M → LogR Z → (Fin (U + M) → G) → S → Prop)
    [Nonempty CI] [Nonempty CS] (z : TapeN U M CI CS G S) : Prop :=
  simGN (fun ω => SmP A simI simS (pubOf ω)) (fun ω => pgP A progI progS (pubOf ω)) Ev z

/-- **The collision term of hop `i`.** -/
noncomputable def deltaNR [Nonempty CI] [Nonempty CS] [Nonempty G] (i : Fin (U + M))
    (z : TapeN U M CI CS G S) : Prop :=
  deltaN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
    (fun ω => pgP A progI progS (pubOf ω)) i z

/-- **The distinguisher of an issuance hop `i`**, as a function of the issuance proof. -/
noncomputable def distPI [Nonempty CI] [Nonempty CS] [Nonempty G] (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) (p : Option (IssueProof Z))
    (g : G) (u : S) : Prop :=
  distN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
    (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext) i ω τ
    (pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A simI simS (pubOf ω)) (fun ω => pgP A progI progS (pubOf ω)) ω
        (tapeC τ) i).1) (p.map Sum.inl)) g u

/-- **The distinguisher of a spend hop `i`**, as a function of the spend proof. -/
noncomputable def distPS [Nonempty CI] [Nonempty CS] [Nonempty G] (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) (p : Option (SpendProof Z))
    (g : G) (u : S) : Prop :=
  distN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
    (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext) i ω τ
    (pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A simI simS (pubOf ω)) (fun ω => pgP A progI progS (pubOf ω)) ω
        (tapeC τ) i).1) (p.map Sum.inr)) g u

/-- **Off the bad event there is no theft.** An accepted spend whose statement differs from every
honest one has a witness; its parent `Com(nf*, ctx*, t, r)` is not the commitment of any honest
slot (issued or change), so the spend consumes a separately certified state, even if `nf*` is an
honest nullifier (nullifier squatting); and its change commitment is not an honest commitment. -/
theorem not_theftN_spend (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S)
    (q : SpendRequest Z) (c : Context) (x : Credits)
    (hq : opN A (pubOf ω) l g s = .spend q c x) (hA : accN A verI verS ω l g s)
    (hF : freshN A ω l g s) (hB : ¬ BadN A verI verS ext ω l g s) :
    SpendRel (opXS A.base q c) (ext l (opN A (pubOf ω) l) g s).2 ∧
      ∀ (j : Fin (U + M)) (cj : Commitment), comAt A (pubOf ω) l j = some cj →
        com (SpendReq.parse q).nf c (ext l (opN A (pubOf ω) l) g s).2.t
            (ext l (opN A (pubOf ω) l) g s).2.r ≠ cj ∧
          (SpendReq.parse q).cNext ≠ cj := by
  have h : relN A ext ω l g s ∧ ¬ opensN A ext ω l g s := by
    unfold BadN at hB; tauto
  obtain ⟨hR, hO⟩ := h
  simp only [relN, hq, RelOp] at hR
  refine ⟨hR, fun j cj hj => ⟨fun hc => hO ⟨j, cj, hj, ?_⟩, fun hc => hO ⟨j, cj, hj, ?_⟩⟩⟩
  · rw [hq]
    exact ⟨_, List.mem_cons_self, hc⟩
  · rw [hq]
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [← hc]
    exact hR.2.1.symm

/-! ## One-wayness, per honest slot -/

/-- **One-wayness of `Com` in the opening, for one slot's coins.** The inverter `B` sees the
nullifier `nf`, the commitment function `(ctx, t) ↦ Com(nf, ctx, t, r)` (it may evaluate it at
contexts and credit values of its choice; `r` stays hidden) and auxiliary coins `β`. It wins with
a context, a credit value and an opening of `Com(nf, ctx, t, r)` (any opening: a different one is
a collision). -/
noncomputable def owAdvK {β : Type} [Fintype β]
    (B : Nullifier → (Context → Credits → Commitment) → β → Context × Credits × Open4) : ℝ :=
  pr (SecC × β) fun z =>
    comOf (B (pubC z.1).1 (pubC z.1).2 z.2).2.2 =
      (pubC z.1).2 (B (pubC z.1).1 (pubC z.1).2 z.2).1 (B (pubC z.1).1 (pubC z.1).2 z.2).2.1

/-- The first opening of `c` in a list. -/
def pickC (c : Commitment) : List Open4 → Open4
  | [] => open0
  | o :: os => if comOf o = c then o else pickC c os

theorem pickC_win (c : Commitment) (l : List Open4) (h : ∃ o ∈ l, comOf o = c) :
    comOf (pickC c l) = c := by
  induction l with
  | nil => obtain ⟨o, ho, _⟩ := h; cases ho
  | cons a l ih =>
    simp only [pickC]
    split_ifs with ha
    · exact ha
    · obtain ⟨o, ho, ho'⟩ := h
      rcases List.mem_cons.1 ho with rfl | ho
      · exact absurd ho' ha
      · exact ih ⟨o, ho, ho'⟩

/-- The coins of the reduction for slot `j`: the other slots' coins, the slots, the tables. -/
abbrev RedC (U M : ℕ) (CI CS G S : Type) (j : Fin (U + M)) :=
  ({i : Fin (U + M) // i ≠ j} → SecC) × ((Fin (U + M) → Slot (Coins 16) (CI × CS) G) × S)

/-- The slots' coins from slot `j`'s and the others'. -/
def insSec (j : Fin (U + M)) (x : SecC) (o : {i : Fin (U + M) // i ≠ j} → SecC) : SecN U M :=
  fun i => if e : i = j then x else o ⟨i, e⟩

/-- **The public form with slot `j` given by its nullifier and commitment function**, the other
slots by their coins. -/
noncomputable def pubH (j : Fin (U + M)) (nf : Nullifier) (K : Context → Credits → Commitment)
    (o : {i : Fin (U + M) // i ≠ j} → SecC) : Pub :=
  fun i => if i = j.val then (nf, K) else pubC (extN (insSec j (Classical.arbitrary SecC) o) i)

theorem pubOf_insSec (j : Fin (U + M)) (x : SecC) (o : {i : Fin (U + M) // i ≠ j} → SecC) :
    pubOf (insSec j x o) = pubH j (pubC x).1 (pubC x).2 o := by
  funext i
  unfold pubOf pubH secAt
  by_cases e : i = j.val
  · subst e
    rw [extN_val]
    simp [insSec]
  · simp only [e, ↓reduceIte]
    congr 1
    unfold extN
    split_ifs with hi
    · have hne : (⟨i, hi⟩ : Fin (U + M)) ≠ j := fun h => e (congrArg Fin.val h)
      simp [insSec, hne]
    · rfl

/-- The regrouping of the simulated game's tape around slot `j`. -/
def regroupJ (j : Fin (U + M)) : SecC × RedC U M CI CS G S j ≃ TapeN U M CI CS G S where
  toFun y := ((insSec j y.1 y.2.1, y.2.2.1), y.2.2.2)
  invFun z := (z.1.1 j, (fun i => z.1.1 i.1, (z.1.2, z.2)))
  left_inv y := by
    refine Prod.ext (by simp [insSec]) (Prod.ext (funext fun i => ?_) rfl)
    simp [insSec, i.2]
  right_inv z := by
    refine Prod.ext (Prod.ext (funext fun i => ?_) rfl) rfl
    by_cases e : i = j
    · subst e; simp [insSec]
    · simp [insSec, e]

variable [Nonempty CI] [Nonempty CS]

/-- The simulated log and programming, from the public form. -/
noncomputable def simLog (p : Pub) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) :
    LogR Z × (S → S) :=
  simPre (SmP A simI simS) (pgP A progI progS) p (tapeC τ) (U + M)

/-- The openings the extractor's witness carries, in the simulated world. -/
noncomputable def simOpens (p : Pub) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) (s : S) :
    List Open4 :=
  opensOf (opN A p (simLog A simI progI simS progS p τ).1 (tapeG τ)
      ((simLog A simI progI simS progS p τ).2 s))
    (ext (simLog A simI progI simS progS p τ).1
      (opN A p (simLog A simI progI simS progS p τ).1) (tapeG τ)
      ((simLog A simI progI simS progS p τ).2 s))

/-- **The inverter of slot `j`**: the simulated world from `nf_j` and the commitment function
alone (the other slots' coins, the slots and the tables as its coins), the adversary, the
extractor; it outputs the context and credit value of slot `j`'s statement and the first
extracted opening of its commitment. -/
noncomputable def inverterN (j : Fin (U + M)) (nf : Nullifier)
    (K : Context → Credits → Commitment) (b : RedC U M CI CS G S j) : Context × Credits × Open4 :=
  match xtE A (pubH j nf K b.1) (stOf A (pubH j nf K b.1)
      ((simLog A simI progI simS progS (pubH j nf K b.1) b.2.1).1.take j)) with
  | .ok xt => (ctxOf xt.1, xt.2,
      pickC (cOf xt.1) (simOpens A simI progI simS progS ext (pubH j nf K b.1) b.2.1 b.2.2))
  | .error _ => (Vector.replicate 16 0, 0, open0)

/-- The simulated game with an opening of slot `j`'s commitment, on the regrouped tape, is a win
of the inverter. -/
theorem theftSimN_opensJ (j : Fin (U + M)) (y : SecC × RedC U M CI CS G S j) :
    theftSimN A simI progI simS progS (opensJ A ext j) (regroupJ j y) →
      comOf (inverterN A simI progI simS progS ext j (pubC y.1).1 (pubC y.1).2 y.2).2.2 =
        (pubC y.1).2 (inverterN A simI progI simS progS ext j (pubC y.1).1 (pubC y.1).2 y.2).1
          (inverterN A simI progI simS progS ext j (pubC y.1).1 (pubC y.1).2 y.2).2.1 := by
  have hm := simPre_map pubOf (SmP A simI simS) (pgP (S := S) A progI progS)
    (insSec j y.1 y.2.1) (tapeC y.2.2.1) (U + M)
  have hp := pubOf_insSec j y.1 y.2.1
  intro hz
  simp only [theftSimN, simGN, opensJ, comAt, regroupJ, Equiv.coe_fn_mk, hm, hp] at hz
  obtain ⟨c, hc, o, ho, hoc⟩ := hz
  unfold xN at hc
  unfold inverterN simOpens simLog
  cases hx : xtE A (pubH j (pubC y.1).1 (pubC y.1).2 y.2.1)
      (stOf A (pubH j (pubC y.1).1 (pubC y.1).2 y.2.1)
        ((simPre (SmP A simI simS) (pgP A progI progS) (pubH j (pubC y.1).1 (pubC y.1).2 y.2.1)
          (tapeC y.2.2.1) (U + M)).1.take j)) with
  | error er => rw [hx] at hc; cases hc
  | ok xt =>
    rw [hx] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    simp only
    rw [pickC_win (cOf xt.1) _ ⟨o, ho, hoc.trans hc.symm⟩, xtE_com A hx, stOf_n, List.length_take,
      simPre_length, min_eq_left (le_of_lt j.isLt)]
    simp [pubH]

section Red

variable [Fintype CI] [Fintype CS] [Fintype G] [Fintype S]

/-- **One-wayness step.** In the simulated world, an opening of the commitment of some honest
slot is found by the inverter of that slot. -/
theorem sim_opens_leN :
    pr (TapeN U M CI CS G S) (theftSimN A simI progI simS progS (opensN A ext)) ≤
      ∑ j : Fin (U + M), owAdvK (inverterN A simI progI simS progS ext j) := by
  have hex : ∀ z : TapeN U M CI CS G S, theftSimN A simI progI simS progS (opensN A ext) z →
      ∃ j, theftSimN A simI progI simS progS (opensJ A ext j) z := fun z hz => hz
  refine (pr_mono hex).trans ((pr_exists_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [← pr_equiv (regroupJ j)]
  unfold owAdvK
  exact pr_mono fun y hy => theftSimN_opensJ A simI progI simS progS ext j y hy

variable [Nonempty G]

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
noncomputable def seEvN (ω : SecN U M) (l : LogR Z) (g : Fin (U + M) → G) (s : S) : Prop :=
  accN A verI verS ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s

/-- **Weak simulation-extractability step.** -/
theorem sim_se_leN {AdmE : ((Fin (U + M) → G) → S → Op Z) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simS) (progM progI progS) (AccOp A.base verI verS)
      (FreshOpN A) (RelOp A.base) ext AdmE εSE)
    (hAE : ∀ iss sp, AdmE (A.out iss sp)) :
    pr (TapeN U M CI CS G S) (theftSimN A simI progI simS progS (seEvN A verI verS ext)) ≤ εSE :=
  simGN_le_of_weakSEN (ρ := Coins 16) hse (fun ω l => xN A (pubOf ω) l)
    (fun ω l => opN A (pubOf ω) l) fun _ _ => hAE _ _

/-- **No theft for `U` Clients and `M` spends, from a bound on the simulated game's
`Acc ∧ Fresh ∧ ¬ Rel` event** (`hse'`; `noTheftN` gets it from `WeakSEN`). -/
theorem noTheftN_of_se [Nonempty S]
    {AdmI : (Option (IssueProof Z) → G → S → Prop) → Prop}
    {AdmS : (Option (SpendProof Z) → G → S → Prop) → Prop}
    {εI εS εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRel (PI' PI) simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkS : ZeroKnowledgeRO SpendRel (PS' PS) simS progS AdmS εS) (hεS : 0 ≤ εS)
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ,
      AdmI (distPI A PI PS simI progI simS progS verI verS ext i ω τ))
    (hAS : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ,
      AdmS (distPS A PI PS simI progI simS progS verI verS ext i ω τ))
    (hse' : pr (TapeN U M CI CS G S)
      (theftSimN A simI progI simS progS (seEvN A verI verS ext)) ≤ εSE) :
    pr (TapeN U M CI CS G S) (theftRealN A PI PS verI verS ext) ≤
      U * εI + M * εS + ∑ i, pr (TapeN U M CI CS G S) (deltaNR A PI PS simI progI simS progS i) +
        εSE + ∑ j : Fin (U + M), owAdvK (inverterN A simI progI simS progS ext j) := by
  have hzkI' : ZeroKnowledgeRO RelRI (PM PI PS) (simM simI simS) (progM progI progS)
      (fun D => AdmI (fun o g s => D (o.map Sum.inl) g s)) εI := zk_sumO_inl hzkI
  have hzkS' : ZeroKnowledgeRO RelRS (PM PI PS) (simM simI simS) (progM progI progS)
      (fun D => AdmS (fun o g s => D (o.map Sum.inr) g s)) εS := zk_sumO_inr hzkS
  have h := theftN_le (Ω := SecN U M) (ρ := Coins 16) (C := CI × CS) (G := G) (S := S)
    (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω)) (fun ω => pgP A progI progS (pubOf ω))
    (accN A verI verS) (freshN A) (relN A ext) (opensN A ext)
    (fun i => if i.val < U then εI else εS)
    (fun i ω τ => by
      have hlen := simPre_length (fun ω => SmP A simI simS (pubOf ω))
        (fun ω => pgP (S := S) A progI progS (pubOf ω)) ω (tapeC τ) i
      by_cases hi : i.val < U
      · have := zk_step hzkI' hεI
          (xwN A ω (simPre (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP (S := S) A progI progS (pubOf ω)) ω (tapeC τ) i).1)
          (xwN_relI A ω _ (by rw [hlen]; exact hi))
          (pairO ((xwN A ω (simPre (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP (S := S) A progI progS (pubOf ω)) ω (tapeC τ) i).1).map Prod.fst))
          (distN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext) i ω τ)
          (fun _ _ _ => by
            have := hAI i hi ω τ
            unfold distPI at this
            rw [← xwN_fst] at this
            exact this)
        simp only [hi, ↓reduceIte]
        rw [xwN_fst] at this
        exact this
      · have := zk_step hzkS' hεS
          (xwN A ω (simPre (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP (S := S) A progI progS (pubOf ω)) ω (tapeC τ) i).1)
          (xwN_relS A ω _ (by rw [hlen]; exact hi))
          (pairO ((xwN A ω (simPre (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP (S := S) A progI progS (pubOf ω)) ω (tapeC τ) i).1).map Prod.fst))
          (distN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
            (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext) i ω τ)
          (fun _ _ _ => by
            have := hAS i (not_lt.1 hi) ω τ
            unfold distPS at this
            rw [← xwN_fst] at this
            exact this)
        simp only [hi, ↓reduceIte]
        rw [xwN_fst] at this
        exact this)
  have hop := sim_opens_leN A simI progI simS progS ext
  have hε : ∑ i : Fin (U + M), (if i.val < U then εI else εS) = U * εI + M * εS := by
    rw [Fin.sum_univ_add]
    simp
  have hsplit : ∑ i : Fin (U + M), ((if i.val < U then εI else εS) +
        pr (TapeN U M CI CS G S) (deltaN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
          (fun ω => pgP A progI progS (pubOf ω)) i)) =
      U * εI + M * εS +
        ∑ i, pr (TapeN U M CI CS G S) (deltaNR A PI PS simI progI simS progS i) := by
    rw [Finset.sum_add_distrib, hε]
    rfl
  rw [hsplit] at h
  have e1 : pr (TapeN U M CI CS G S) (theftRealN A PI PS verI verS ext) =
      pr (TapeN U M CI CS G S) (realGN (PN A PI PS) (fun ω l g s =>
        accN A verI verS ω l g s ∧ freshN A ω l g s ∧
          (¬ relN A ext ω l g s ∨ opensN A ext ω l g s))) := rfl
  have e2 : pr (TapeN U M CI CS G S)
        (theftSimN A simI progI simS progS (seEvN A verI verS ext)) =
      pr (TapeN U M CI CS G S) (simGN (fun ω => SmP A simI simS (pubOf ω))
        (fun ω => pgP A progI progS (pubOf ω)) (fun ω l g s =>
          accN A verI verS ω l g s ∧ freshN A ω l g s ∧ ¬ relN A ext ω l g s)) := rfl
  have e3 : pr (TapeN U M CI CS G S) (theftSimN A simI progI simS progS (opensN A ext)) =
      pr (TapeN U M CI CS G S) (simGN (fun ω => SmP A simI simS (pubOf ω))
        (fun ω => pgP A progI progS (pubOf ω)) (opensN A ext)) := rfl
  rw [e1]
  rw [e2] at hse'
  rw [e3] at hop
  linarith

/-- **No theft for `U` honest Clients and `M` honest spends (Theorem 3, N2a in its extraction
form).** For every adversary, with zero knowledge of both proof systems at the hops'
distinguishers and weak simulation-extractability with `U + M` simulated proofs:

    Pr[BadN] ≤ U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(inverter j). -/
theorem noTheftN [Nonempty S]
    {AdmI : (Option (IssueProof Z) → G → S → Prop) → Prop}
    {AdmS : (Option (SpendProof Z) → G → S → Prop) → Prop}
    {AdmE : ((Fin (U + M) → G) → S → Op Z) → Prop} {εI εS εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRel (PI' PI) simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkS : ZeroKnowledgeRO SpendRel (PS' PS) simS progS AdmS εS) (hεS : 0 ≤ εS)
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ,
      AdmI (distPI A PI PS simI progI simS progS verI verS ext i ω τ))
    (hAS : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ,
      AdmS (distPS A PI PS simI progI simS progS verI verS ext i ω τ))
    (hse : WeakSEN (U + M) (simM simI simS) (progM progI progS) (AccOp A.base verI verS)
      (FreshOpN A) (RelOp A.base) ext AdmE εSE)
    (hAE : ∀ iss sp, AdmE (A.out iss sp)) :
    pr (TapeN U M CI CS G S) (theftRealN A PI PS verI verS ext) ≤
      U * εI + M * εS + ∑ i, pr (TapeN U M CI CS G S) (deltaNR A PI PS simI progI simS progS i) +
        εSE + ∑ j : Fin (U + M), owAdvK (inverterN A simI progI simS progS ext j) :=
  noTheftN_of_se A PI PS simI progI simS progS verI verS ext hzkI hεI hzkS hεS hAI hAS
    (sim_se_leN A simI progI simS progS verI verS ext hse hAE)

end Red

end VoleMole.Theft.Ratatouille
