import VoleMole.Privacy.PermRA
import VoleMole.ZK.ReadsMany

/-!
# Ratatouille unlinkability with many sessions

The games of `Privacy/RatatouilleRO.lean` and `Privacy/RatatouilleRA.lean` have two Clients and
two spend rounds: the challenge. Here the malicious Issuer also serves **any number of further
honest Clients** on the same tables, each issued and spending once, concurrently with the
challenge.

## The game

`AdversaryN` (on `Sizes.labelRows`): key, context and balance as before; stage 1 sees **every**
issuance request (the two challenge Clients' and the further Clients') and gives the challenge
responses and `d₁`, a response and a spend amount for each further Client (`respondIssX`, `dX`);
each further Client finalizes its token and spends it (`issXR`, `spXR`: the spec's
`issue_request_with_seed`, `finalize_issue`, `spend_request_with_seed` with the Lean provers on the
shared tables, its own `(nf, r, ρ)` and `H₃` slices); stage 2 sees round 1's request **and every
further Client's spend request** and gives round 1's response and `d₂`. The guess sees all
requests, the rounds, all slices and the tables, with a budget (`AdversaryN.Budget`); the
interaction does not read the tables.

**`realGameN`** is the two-session game with a table-reading Issuer (`realGameRA`) for the Issuer
composed with the further Clients (`AdversaryN.withClients c`, `c` their tapes): its stages compute
the further Clients' requests on the tables, its guess too.

## The bound

For each fixed `c`, `unlinkabilityRA_lean_numG` applies to `A.withClients c`; averaging over `c`
gives `unlinkabilityN_lean_numG`. The budgets: a further Client's issuance and spend requests are
**consistent** readers (`ZK.Sim.realRO_sreads`; a spend proof only when the Client's checks pass,
and then its witness is in `R_spend`), so each stage reads at most `(0, 2·2³²m, 2·624m, 2·4607m)`
keys (`withClients_iBudget`), and the guess `(q₃, q₅ + 2·624m, q_E + 2·4607m)`
(`withClients_gBudget`). Linear in `m`; in numbers (`unlinkabilityN_lean_le`)
`≤ n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` for `n = m + 2` Clients: `≤ 2⁻⁸¹ + 2·εhide`
for `n ≤ 2²⁰` (`unlinkabilityN_lean_2pow20`) and `≤ 2⁻⁶⁹ + 2·εhide` for `n ≤ 2³²`
(`unlinkabilityN_lean_2pow32`), plus the guess's budget terms. With AES as
random permutations: `unlinkabilityN_lean_num_perm`.

## `N` challenge pairs

`AdversaryP`, `realGameP` (worlds `w : Fin N → Bool × Bool`): stage 1 sees **every** pair's
issuance requests and gives every response and every pair's `d₁`; stage 2 sees every pair's round-1
request **for the pairs whose round 1 runs** (§6's rule, `rq1Of`) and gives every round-1 response
and `d₂`; each pair runs the protocol of the two-session game in its world (`roundsOf`, exactly
`viewR` with real slots: `realGameRA_eq`); the guess sees all requests, every pair's rounds, all
slices and the tables.

The other pairs cannot be `AdversaryN`'s further Clients (those spend once; a pair has two rounds,
the second after the Issuer's response to the first), so each step of the hybrid over the pairs is
a **direct reduction**: `A.hop k c v` is the two-session Issuer that runs the other pairs itself,
with their tapes `c` and worlds `v`, on the tables it is given (`realGameP_iff`,
`realGameRA_hop`). Its stage 2 must hide pair `k`'s round-1 request when §6's rule refuses
round 1, and it does not know pair `k`'s tokens: the rule is computed from the Issuer's view
(`ok1Of_eq_pub`: both responses are preimages of the commitments in the requests, `tkOk`, and
the balance affords `d₁`; an honest finalized token is valid, `fin_issXR`). Budgets
(`hop_iBudget`, `hop_gBudget`): the interaction reads the other pairs' issuances and round-1
spends, `(0, 3(N−1)·2³², 3(N−1)·624, 3(N−1)·4607)`, the guess also their round-2 spends,
`(q₃, q₅ + 4(N−1)·624, q_E + 4(N−1)·4607)`; the readers are factored through the other pairs' proofs
(`issFam`, `sp1Fam`, `sp2Fam`, `hop_msg₁`, `hop_msg₂`, `hop_guess_eq`). `unlinkabilityRA_lean_numG`
applies for every `c`; averaging over `c` (`realGameP_hybrid`) gives, for any two worlds,
`≤ N·εPairR` (`unlinkabilityP_lean_numG`, `_num`, `_num_perm`), in numbers (`εPairR_le`,
`unlinkabilityP_lean_le`) `≤ N·(N·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`: `≤ 2⁻⁶³` for
`2N ≤ 2²⁰` Clients, `≤ 2⁻³⁹` for `2N ≤ 2³²` (`unlinkabilityP_lean_2pow20`, `_2pow32`), plus `N`
times the budget and hiding terms. Quadratic (an artifact of the key-level H4 hop,
`lean/docs/zk.md` §10.8).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- The proof sizes of the Lean provers. -/
local notation "ZL" => Sizes.labelRows

/-! ## A further honest Client on the tables, and what it reads -/

section Honest

/-- A further Client's tape: its issuance tape and its spend tape. -/
abbrev XC := TRe × TRe

variable (pk : PublicKey) (ctx : Context) (tInit : Credits)

/-- **A further Client's issuance** on the tables (`issue_request_with_seed` with the Lean
prover). -/
noncomputable def issXR (x : TRe) (s : ShR R) : Except Error (PendingTokenS × IssueRequest ZL) :=
  issueOf (primI leanPIR x.2.2 s) tInit ctx (vec x.1.1) (vec x.1.2) (vec x.2.1)

/-- The request of an issuance. -/
def reqIX (r : Except Error (PendingTokenS × IssueRequest ZL)) : Except Error (IssueRequest ZL) :=
  match r with
  | .ok q => .ok q.2
  | .error e => .error e

/-- The Client's `finalize_issue` on a response. -/
def finI (r : Except Error (PendingTokenS × IssueRequest ZL)) (resp : Preimage) : Option TokenS :=
  match r with
  | .ok q => match (finalizeIssue pk (some q.1) resp).2 with
    | .ok o => o
    | .error _ => none
  | .error _ => none

/-- **A further Client's spend** of its token on the tables (`spend_request_with_seed` with the
Lean prover). -/
noncomputable def spXR (tok : Option TokenS) (d : Credits) (y : TRe) (s : ShR R) :
    Option TokenS × Except Error (PendingSpendS × SpendRequest ZL) :=
  spendOf (primS leanPSR y.2.2 s) pk tok d ctx (vec y.1.1) (vec y.1.2) (vec y.2.1)

/-- The request of a spend. -/
def reqSX (r : Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)) :
    Except Error (SpendRequest ZL) :=
  match r.2 with
  | .ok q => .ok q.2
  | .error e => .error e

/-- The primitives with a fixed issuance proof `o`. -/
def primKI (o : Option (IssueProof ZL)) : Prim ZL Empty :=
  ⟨fun e => e.elim, fun e => e.elim, fun _ _ _ => o, fun _ _ => true, fun _ _ _ => none, fun _ _ => true⟩

/-- The primitives with a fixed spend proof `o`. -/
def primKS (o : Option (SpendProof ZL)) : Prim ZL Empty :=
  ⟨fun e => e.elim, fun e => e.elim, fun _ _ _ => none, fun _ _ => true, fun _ _ _ => o, fun _ _ => true⟩

/-- The issuance instance and witness of a further Client. -/
def xIX (x : TRe) : IssueInstance := ⟨com (vec x.1.1) ctx tInit (vec x.1.2), tInit, ctx⟩
def wIX (x : TRe) : IssueWitness := ⟨vec x.1.1, vec x.1.2⟩

lemma leanPIR_sreads (x : TRe) :
    SReads pI (fun t : Tb R pI => leanPIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 t.2) 0 nGrind
      624 4607 := by
  have h := (realRO_sreads (R := R) (zkHypI (xIX ctx tInit x) (wIX x) rfl) hashesWF_shake hlab_pI
    x.2.1 x.2.2).map (vecOf Sizes.labelRows.issue)
  refine (congrArg (fun F => SReads pI F 0 nGrind 624 4607) (funext fun t => ?_)).mp h
  exact (leanPIR_vec _ _ x.2.1 x.2.2 t.2).symm

omit [Fintype R] [Nonempty R] [CipherRow R] in
lemma primI_proveIssueX {Z : Sizes} (PI : ProverI R Z) (g : Tab3) (s : ShR R) (X : IssueInstance)
    (W : IssueWitness) (ρ : Rho) : (primI PI g s).proveIssue X W ρ = PI X W ρ g s := rfl

/-- A further Client's issuance is determined by its proof. -/
lemma issXR_det (x : TRe) (s s' : ShR R)
    (h : leanPIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 s' =
      leanPIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 s) :
    issXR ctx tInit x s' = issXR ctx tInit x s := by
  unfold issXR issueOf
  rw [primI_proveIssueX, primI_proveIssueX]
  unfold xIX wIX at h
  rw [h]

/-- **A further Client's issuance is a consistent reader** (`ZK.Sim.realRO_sreads`; its witness
is in `R_iss` by construction). -/
theorem issXR_sreads (x : TRe) :
    SReads pI (fun t : Tb R pI => issXR ctx tInit x t.2) 0 nGrind 624 4607 :=
  (leanPIR_sreads (R := R) ctx tInit x).of_det fun t t' h => issXR_det ctx tInit x t.2 t'.2 h

lemma leanPIR_rd5 (x : TRe) :
    Rd5 (fun s : ShR R => leanPIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 s) 624 := by
  have h := (realRO_rd5 (R := R) (p := pI) (Hb := Hashes.shake) (st := stI (xIX ctx tInit x))
    (w := encI (xIX ctx tInit x) (wIX x)) x.2.1 x.2.2).map (vecOf Sizes.labelRows.issue)
  refine (congrArg (fun F => Rd5 F 624) (funext fun s => ?_)).mp h
  exact (leanPIR_vec _ _ x.2.1 x.2.2 s).symm

lemma leanPIR_rdE (x : TRe) :
    RdE (fun s : ShR R => leanPIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 s) 4607 := by
  have h := (realRO_rdE (R := R) (p := pI) (Hb := Hashes.shake) (st := stI (xIX ctx tInit x))
    (w := encI (xIX ctx tInit x) (wIX x)) hashesWF_shake x.2.1 x.2.2).map (vecOf Sizes.labelRows.issue)
  refine (congrArg (fun F => RdE F 4607) (funext fun s => ?_)).mp h
  exact (leanPIR_vec _ _ x.2.1 x.2.2 s).symm

lemma issXR_rd5 (x : TRe) : Rd5 (issXR (R := R) ctx tInit x) 624 :=
  (leanPIR_rd5 ctx tInit x).of_det fun s s' h => issXR_det ctx tInit x s s' h

lemma issXR_rdE (x : TRe) : RdE (issXR (R := R) ctx tInit x) 4607 :=
  (leanPIR_rdE ctx tInit x).of_det fun s s' h => issXR_det ctx tInit x s s' h

/-- The spend instance and witness of a further Client whose checks passed. -/
def xSX (τ : TokenS) (d t' : Credits) (y : TRe) : SpendInstance :=
  ⟨pk, τ.nf, d, com (vec y.1.1) ctx t' (vec y.1.2), ctx⟩
def wSX (τ : TokenS) (t' : Credits) (y : TRe) : SpendWitness :=
  ⟨τ.t, τ.r, τ.x, τ.s, vec y.1.1, t', vec y.1.2⟩

/-- A further Client's spend with the checks passed is determined by its proof. -/
lemma spXR_det (τ : TokenS) (d t' : Credits) (hv : τ.Valid pk ctx) (hc : clientCheck τ.t τ.x d = some t')
    (y : TRe) (s s' : ShR R)
    (h : leanPSR (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1) y.2.2 s' =
      leanPSR (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1) y.2.2 s) :
    spXR pk ctx (some τ) d y s' = spXR pk ctx (some τ) d y s := by
  simp only [xSX, wSX] at h
  simp only [spXR, spendOf, hv, not_true_eq_false, ↓reduceIte, hc, primS]
  rw [h]

/-- **A further Client's spend is a consistent reader** (a proof only when the Client's checks
pass; its witness is then in `R_spend`). -/
theorem spXR_sreads (tok : Option TokenS) (d : Credits) (y : TRe) :
    SReads pS (fun t : Tb R pS => spXR pk ctx tok d y t.2) 0 nGrind 624 4607 := by
  rcases tok with _ | τ
  · exact (SReads.const (R := R) (p := pS) ((none, .error .logic) :
      Option TokenS × Except Error (PendingSpendS × SpendRequest ZL))).mono le_rfl (Nat.zero_le _)
      (Nat.zero_le _) (Nat.zero_le _)
  by_cases hv : τ.Valid pk ctx
  · rcases hc : clientCheck τ.t τ.x d with _ | t'
    · have e : (fun t : Tb R pS => spXR pk ctx (some τ) d y t.2) = fun _ =>
          ((some τ, .error .invalidArgument) :
            Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)) := by
        funext t
        simp only [spXR, spendOf, hv, not_true_eq_false, ↓reduceIte, hc]
      rw [e]
      exact (SReads.const _).mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · have hrel : SpendRel (xSX pk ctx τ d t' y) (wSX τ t' y) :=
        ⟨hv, rfl, by have := clientCheck_eq hc; simp only [xSX, wSX] at this ⊢; omega⟩
      have h := (realRO_sreads (R := R) (zkHypS _ _ hrel) hashesWF_shake hlab_pS y.2.1 y.2.2).map
        (vecOf Sizes.labelRows.spend)
      have hP : SReads pS (fun t : Tb R pS => leanPSR (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1)
          y.2.2 t.2) 0 nGrind 624 4607 := by
        refine (congrArg (fun F => SReads pS F 0 nGrind 624 4607) (funext fun t => ?_)).mp h
        exact (leanPSR_vec _ _ y.2.1 y.2.2 t.2).symm
      exact hP.of_det fun t t' h => spXR_det pk ctx τ d _ hv hc y t.2 t'.2 h
  · have e : (fun t : Tb R pS => spXR pk ctx (some τ) d y t.2) = fun _ =>
        ((some τ, .error .invalidArgument) :
          Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)) := by
      funext t
      simp only [spXR, spendOf, hv, not_false_eq_true, ↓reduceIte]
    rw [e]
    exact (SReads.const _).mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

lemma leanPSR_rd5 (X : SpendInstance) (W : SpendWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPSR (R := R) X W ρ g) 624 :=
  (realROb_rd5 (R := R) (p := pS) (Hb := Hashes.shake) (st := stS X) (w := encS X W) (bOf ρ) g).map
    fun o => vecOf _ o

lemma leanPSR_rdE (X : SpendInstance) (W : SpendWitness) (ρ : Rho) (g : Tab3) :
    RdE (leanPSR (R := R) X W ρ g) 4607 :=
  (realROb_rdE (R := R) (p := pS) (Hb := Hashes.shake) (st := stS X) (w := encS X W) hashesWF_shake
    (bOf ρ) g).map fun o => vecOf _ o

/-- A further Client's spend is a constant or determined by its proof. -/
lemma spXR_cases (tok : Option TokenS) (d : Credits) (y : TRe) :
    (∃ v, ∀ s : ShR R, spXR pk ctx tok d y s = v) ∨
      ∃ τ t', τ.Valid pk ctx ∧ clientCheck τ.t τ.x d = some t' ∧ tok = some τ := by
  rcases tok with _ | τ
  · exact Or.inl ⟨_, fun s => rfl⟩
  by_cases hv : τ.Valid pk ctx
  · rcases hc : clientCheck τ.t τ.x d with _ | t'
    · exact Or.inl ⟨(some τ, .error .invalidArgument), fun s => by
        simp only [spXR, spendOf, hv, not_true_eq_false, ↓reduceIte, hc]⟩
    · exact Or.inr ⟨τ, t', hv, hc, rfl⟩
  · exact Or.inl ⟨(some τ, .error .invalidArgument), fun s => by
      simp only [spXR, spendOf, hv, not_false_eq_true, ↓reduceIte]⟩

lemma spXR_rd5 (tok : Option TokenS) (d : Credits) (y : TRe) : Rd5 (spXR (R := R) pk ctx tok d y) 624 := by
  rcases spXR_cases (R := R) pk ctx tok d y with ⟨v, hv⟩ | ⟨τ, t', hv, hc, rfl⟩
  · rw [show spXR (R := R) pk ctx tok d y = fun _ => v from funext hv]
    exact (Rd5.const _).mono (Nat.zero_le _)
  · exact (leanPSR_rd5 (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1) y.2.2).of_det fun s s' h =>
      spXR_det pk ctx τ d t' hv hc y s s' h

lemma spXR_rdE (tok : Option TokenS) (d : Credits) (y : TRe) : RdE (spXR (R := R) pk ctx tok d y) 4607 := by
  rcases spXR_cases (R := R) pk ctx tok d y with ⟨v, hv⟩ | ⟨τ, t', hv, hc, rfl⟩
  · rw [show spXR (R := R) pk ctx tok d y = fun _ => v from funext hv]
    exact (RdE.const _).mono (Nat.zero_le _)
  · exact (leanPSR_rdE (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1) y.2.2).of_det fun s s' h =>
      spXR_det pk ctx τ d t' hv hc y s s' h

end Honest

/-! ## The many-session game -/

section Game

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A further Client's issuance request. -/
abbrev IReq := Except Error (IssueRequest ZL)
/-- A further Client's spend request. -/
abbrev SReq := Except Error (SpendRequest ZL)

/-- **The malicious Issuer of the many-session game**: key, context and balance; stage 1 (after
every issuance request) the challenge responses and `d₁`, and a response and a spend amount for
each further Client; stage 2 (after round 1's request and every further Client's spend request)
round 1's response and `d₂`; and a guess that sees all requests, the rounds, all slices and the
tables. The interaction does not read the tables. -/
structure AdversaryN (R : Type) (ι : Type) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr ZL → (ι → IReq) → Bool → Preimage
  d₁ : IssTr ZL → (ι → IReq) → Credits
  respondIssX : IssTr ZL → (ι → IReq) → ι → Preimage
  dX : IssTr ZL → (ι → IReq) → ι → Credits
  respond₁ : IssTr ZL → (ι → IReq) → SReq → (ι → SReq) → SpendResponse
  d₂ : IssTr ZL → (ι → IReq) → SReq → (ι → SReq) → Credits
  guess : IssTr ZL → (ι → IReq) → Rounds ZL → (ι → SReq) → SlicesR → (ι → Tab3 × Tab3) → ShR R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` and the further Clients' slices freely. -/
structure AdversaryN.Budget (A : AdversaryN R ι) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ tr tx y sx (g₁ g₂ g₃ : Tab3) slx s,
    Rd3 (fun g => A.guess tr tx y sx ((g, g₁), (g₂, g₃)) slx s) q3
  h31 : ∀ tr tx y sx (g₀ g₂ g₃ : Tab3) slx s,
    Rd3 (fun g => A.guess tr tx y sx ((g₀, g), (g₂, g₃)) slx s) q3
  h32 : ∀ tr tx y sx (g₀ g₁ g₃ : Tab3) slx s,
    Rd3 (fun g => A.guess tr tx y sx ((g₀, g₁), (g, g₃)) slx s) q3
  h33 : ∀ tr tx y sx (g₀ g₁ g₂ : Tab3) slx s,
    Rd3 (fun g => A.guess tr tx y sx ((g₀, g₁), (g₂, g)) slx s) q3
  h5 : ∀ tr tx y sx sl slx, Rd5 (A.guess tr tx y sx sl slx) q5
  hE : ∀ tr tx y sx sl slx, RdE (A.guess tr tx y sx sl slx) qE

namespace AdversaryN

variable (A : AdversaryN R ι) (c : ι → XC)

/-- The further Clients' issuances on the tables. -/
noncomputable def isX (u : ShR R) : ι → Except Error (PendingTokenS × IssueRequest ZL) :=
  fun j => issXR A.ctx A.tInit (c j).1 u

/-- The further Clients' issuance requests. -/
noncomputable def txN (u : ShR R) : ι → IReq := fun j => reqIX (A.isX c u j)

/-- The further Clients' spends from their issuances `w` (finalized on the stage-1 responses to
the requests `tr`), on the tables. -/
noncomputable def spW (tr : IssTr ZL) (w : ι → Except Error (PendingTokenS × IssueRequest ZL))
    (u : ShR R) : ι → Option TokenS × Except Error (PendingSpendS × SpendRequest ZL) :=
  fun j => spXR A.pk A.ctx (finI A.pk (w j) (A.respondIssX tr (fun j => reqIX (w j)) j))
    (A.dX tr (fun j => reqIX (w j)) j) (c j).2 u

/-- The further Clients' spend requests. -/
noncomputable def spN (tr : IssTr ZL) (u : ShR R) : ι → SReq := fun j => reqSX (A.spW c tr (A.isX c u) u j)

/-- **The Issuer served by the further Clients** with tapes `c`: its stages compute their requests
on the tables the game runs on; so does its guess. -/
noncomputable def withClients : AdversaryRA R ZL where
  pk := A.pk
  ctx := A.ctx
  tInit := A.tInit
  respondIss tr i _ u := A.respondIss tr (A.txN c u) i
  d₁ tr _ u := A.d₁ tr (A.txN c u)
  respond₁ tr rq _ u := A.respond₁ tr (A.txN c u) rq (A.spN c tr u)
  d₂ tr rq _ u := A.d₂ tr (A.txN c u) rq (A.spN c tr u)
  guess tr y sl v := A.guess tr (A.txN c v) y (A.spN c tr v) sl (fun j => ((c j).1.2.2, (c j).2.2.2)) v

end AdversaryN

/-- **The real many-session game** in world `(b₁, b₂)`: the two-session game (`realGameRA`, the
Lean provers on the shared tables) of the Issuer served by the further Clients with tapes
`z.1.2`. -/
noncomputable def realGameN (A : AdversaryN R ι) (b₁ b₂ : Bool)
    (z : (((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR R) : Prop :=
  realGameRA (A.withClients z.1.2) leanPIR leanPSR b₁ b₂ (z.1.1, z.2)

variable (A : AdversaryN R ι) (c : ι → XC)

lemma isX_sreads : SReads pI (fun t : Tb R pI => A.isX c t.2) 0 (Fintype.card ι * nGrind)
    (Fintype.card ι * 624) (Fintype.card ι * 4607) := by
  exact SReads.pi (ι := ι) (f := fun j (t : Tb R pI) => issXR A.ctx A.tInit (c j).1 t.2)
    fun j => issXR_sreads A.ctx A.tInit (c j).1

lemma spW_sreads (tr : IssTr ZL) (w : ι → Except Error (PendingTokenS × IssueRequest ZL)) :
    SReads pI (fun t : Tb R pI => A.spW c tr w t.2) 0 (Fintype.card ι * nGrind)
      (Fintype.card ι * 624) (Fintype.card ι * 4607) := by
  exact SReads.pi (ι := ι) (f := fun j (t : Tb R pI) => A.spW c tr w t.2 j)
    fun j => spXR_sreads A.pk A.ctx _ _ (c j).2

/-- Stage 1 reads the further Clients' issuances. -/
lemma stage1_sreads (tr : IssTr ZL) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.withClients c).msg₁ tr (σ t) t.2) 0 (2 * (Fintype.card ι * nGrind))
      (2 * (Fintype.card ι * 624)) (2 * (Fintype.card ι * 4607)) :=
  ((isX_sreads A c).map fun w : ι → Except Error (PendingTokenS × IssueRequest ZL) =>
    ((A.respondIss tr (fun j => reqIX (w j)) false, A.respondIss tr (fun j => reqIX (w j)) true),
      A.d₁ tr (fun j => reqIX (w j)))).mono le_rfl (by omega) (by omega) (by omega)

/-- Stage 2 reads the further Clients' issuances and spends. -/
lemma stage2_sreads (tr : IssTr ZL) (rq : SReq) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.withClients c).msg₂ tr rq (σ t) t.2) 0 (2 * (Fintype.card ι * nGrind))
      (2 * (Fintype.card ι * 624)) (2 * (Fintype.card ι * 4607)) := by
  have h := (isX_sreads A c).bind (g := fun w (t : Tb R pI) =>
      (A.respond₁ tr (fun j => reqIX (w j)) rq (fun j => reqSX (A.spW c tr w t.2 j)),
        A.d₂ tr (fun j => reqIX (w j)) rq (fun j => reqSX (A.spW c tr w t.2 j))))
    fun w => (spW_sreads A c tr w).map fun o =>
      (A.respond₁ tr (fun j => reqIX (w j)) rq (fun j => reqSX (o j)),
        A.d₂ tr (fun j => reqIX (w j)) rq (fun j => reqSX (o j)))
  refine (h.mono le_rfl (by omega) (by omega) (by omega))

/-- **The interaction's budget**: no slice key, the further Clients' issuance and spend reads. -/
theorem withClients_iBudget : (A.withClients c).IBudget 0 (2 * (Fintype.card ι * nGrind))
    (2 * (Fintype.card ι * 624)) (2 * (Fintype.card ι * 4607)) where
  a0 tr g₁ g₂ g₃ := stage1_sreads A c tr fun t => ((t.1, g₁), (g₂, g₃))
  a1 tr g₀ g₂ g₃ := stage1_sreads A c tr fun t => ((g₀, t.1), (g₂, g₃))
  a2 tr g₀ g₁ g₃ := stage1_sreads A c tr fun t => ((g₀, g₁), (t.1, g₃))
  a3 tr g₀ g₁ g₂ := stage1_sreads A c tr fun t => ((g₀, g₁), (g₂, t.1))
  b0 tr rq g₁ g₂ g₃ := stage2_sreads A c tr rq fun t => ((t.1, g₁), (g₂, g₃))
  b1 tr rq g₀ g₂ g₃ := stage2_sreads A c tr rq fun t => ((g₀, t.1), (g₂, g₃))
  b2 tr rq g₀ g₁ g₃ := stage2_sreads A c tr rq fun t => ((g₀, g₁), (t.1, g₃))
  b3 tr rq g₀ g₁ g₂ := stage2_sreads A c tr rq fun t => ((g₀, g₁), (g₂, t.1))

variable {A} in
/-- **The guess's budget**: the Issuer's plus the further Clients' issuance and spend reads. -/
theorem withClients_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.withClients c).GBudget q3 (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5))
      (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) := fun _ =>
  { h30 := fun _ _ g₁ g₂ g₃ s => hA.h30 _ _ _ _ g₁ g₂ g₃ _ s
    h31 := fun _ _ g₀ g₂ g₃ s => hA.h31 _ _ _ _ g₀ g₂ g₃ _ s
    h32 := fun _ _ g₀ g₁ g₃ s => hA.h32 _ _ _ _ g₀ g₁ g₃ _ s
    h33 := fun _ _ g₀ g₁ g₂ s => hA.h33 _ _ _ _ g₀ g₁ g₂ _ s
    h5 := fun tr y sl => Rd5.bindEq (m := fun s => A.isX c s)
      (f := fun w s => A.guess tr (fun j => reqIX (w j)) y (fun j => reqSX (A.spW c tr w s j)) sl
        (fun j => ((c j).1.2.2, (c j).2.2.2)) s)
      (fun _ => rfl) (Rd5.pi fun j => issXR_rd5 A.ctx A.tInit (c j).1) fun w =>
        Rd5.bindEq (m := fun s => A.spW c tr w s)
          (f := fun o s => A.guess tr (fun j => reqIX (w j)) y (fun j => reqSX (o j)) sl
            (fun j => ((c j).1.2.2, (c j).2.2.2)) s)
          (fun _ => rfl) (Rd5.pi fun _ => spXR_rd5 _ _ _ _ _) fun _ => hA.h5 _ _ _ _ _ _
    hE := fun tr y sl => RdE.bindEq (m := fun s => A.isX c s)
      (f := fun w s => A.guess tr (fun j => reqIX (w j)) y (fun j => reqSX (A.spW c tr w s j)) sl
        (fun j => ((c j).1.2.2, (c j).2.2.2)) s)
      (fun _ => rfl) (RdE.pi fun j => issXR_rdE A.ctx A.tInit (c j).1) fun w =>
        RdE.bindEq (m := fun s => A.spW c tr w s)
          (f := fun o s => A.guess tr (fun j => reqIX (w j)) y (fun j => reqSX (o j)) sl
            (fun j => ((c j).1.2.2, (c j).2.2.2)) s)
          (fun _ => rfl) (RdE.pi fun _ => spXR_rdE _ _ _ _ _) fun _ => hA.hE _ _ _ _ _ _ }

/-- The many-session tape, with the further Clients' tapes first. -/
def tapeN : (ι → XC) × (((TRe × TRe) × (TRe × TRe)) × ShR R) ≃
    (((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Theorem 2 with many Clients, for every type of cipher rows** (`ZKRow R`, `ZKPRow R`; SHAKE
as the base record): with `m = |ι|` further honest Clients, the bound of
`unlinkabilityRA_lean_numG` at `i₃ = 0`, `i₂ = 2·2³²m`, `i₅ = 2·624m`, `i_E = 2·4607m` and the
guess's budget `(q₃, q₅ + 2·624m, q_E + 2·4607m)`; any two worlds. -/
theorem unlinkabilityN_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryN R ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR R) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR R) (realGameN A b₁' b₂')| ≤
      4 * ZKRow.εz R pI (2 * 0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 2 * (2 * (Fintype.card ι * 624)) + 1872) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 2 * (2 * (Fintype.card ι * 4607)) + 13821) +
        2 * εAdG R pS 9 (0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + (2 * (Fintype.card ι * 624)) + 1248) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + (2 * (Fintype.card ι * 4607)) + 13821) 0 (2 * (Fintype.card ι * nGrind)) ((2 * (Fintype.card ι * 624)) + 624)
          ((2 * (Fintype.card ι * 4607)) + 9214) +
        2 * εAdG R pS 9 q3 ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 936) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 13821) (2 * 0) (2 * (2 * (Fintype.card ι * nGrind))) (2 * (2 * (Fintype.card ι * 624)) + 1560)
          (2 * (2 * (Fintype.card ι * 4607)) + 23035) +
        6 * ((0 : ℕ) / 2 ^ 128) + 4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (2 * (2 * (Fintype.card ι * 624)) + 1560) (2 * (2 * (Fintype.card ι * 4607)) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeN, ← pr_equiv tapeN]
  exact abs_pr_prod_sub_le _ _ fun c =>
    unlinkabilityRA_lean_numG (A.withClients c) (withClients_gBudget c hA) (withClients_iBudget A c)
      (hhide c) b₁ b₂ b₁' b₂'

/-- **Theorem 2 with many Clients** (function rows; SHAKE as the base record). -/
theorem unlinkabilityN_lean_num (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁' b₂')| ≤
      4 * εRO (2 * 0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 2 * (2 * (Fintype.card ι * 624)) + 1872) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 2 * (2 * (Fintype.card ι * 4607)) + 13821) +
        2 * εAd 9 (0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + (2 * (Fintype.card ι * 624)) + 1248) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + (2 * (Fintype.card ι * 4607)) + 13821) 0 (2 * (Fintype.card ι * nGrind)) ((2 * (Fintype.card ι * 624)) + 624)
          ((2 * (Fintype.card ι * 4607)) + 9214) +
        2 * εAd 9 q3 ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 936) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 13821) (2 * 0) (2 * (2 * (Fintype.card ι * nGrind))) (2 * (2 * (Fintype.card ι * 624)) + 1560)
          (2 * (2 * (Fintype.card ι * 4607)) + 23035) +
        6 * ((0 : ℕ) / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * (2 * (Fintype.card ι * 624)) + 1560) (2 * (2 * (Fintype.card ι * 4607)) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityN_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- **Theorem 2 with many Clients and AES as uniformly random permutations.** -/
theorem unlinkabilityN_lean_num_perm (A : AdversaryN (Equiv.Perm Blk) ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Equiv.Perm Blk)) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Equiv.Perm Blk)) (realGameN A b₁' b₂')| ≤
      4 * εROPm pI (2 * 0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 2 * (2 * (Fintype.card ι * 624)) + 1872) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 2 * (2 * (Fintype.card ι * 4607)) + 13821) +
        2 * εAdPm pS 9 (0 + q3) ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + (2 * (Fintype.card ι * 624)) + 1248) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + (2 * (Fintype.card ι * 4607)) + 13821) 0 (2 * (Fintype.card ι * nGrind)) ((2 * (Fintype.card ι * 624)) + 624)
          ((2 * (Fintype.card ι * 4607)) + 9214) +
        2 * εAdPm pS 9 q3 ((Fintype.card ι * 624 + (Fintype.card ι * 624 + q5)) + 936) ((Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) + 13821) (2 * 0) (2 * (2 * (Fintype.card ι * nGrind))) (2 * (2 * (Fintype.card ι * 624)) + 1560)
          (2 * (2 * (Fintype.card ι * 4607)) + 23035) +
        6 * ((0 : ℕ) / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * (2 * (Fintype.card ι * 624)) + 1560) (2 * (2 * (Fintype.card ι * 4607)) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityN_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- **The many-Client bound in numbers**: with `n = m + 2` Clients in all, any two worlds differ
by at most

    n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide. -/
theorem unlinkabilityN_lean_le (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁' b₂')| ≤
      (Fintype.card ι + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityN_lean_num A hA hhide b₁ b₂ b₁' b₂'
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 34 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : (Fintype.card ι : ℝ) * (nGrind : ℝ) / 2 ^ 1024 ≤ Fintype.card ι / (4 * 2 ^ 128) := by
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h34 : (2 : ℝ) ^ 32 * 4 = 2 ^ 34 := by norm_num
    calc (Fintype.card ι : ℝ) * 2 ^ 32 * (4 * 2 ^ 128) = ((Fintype.card ι : ℝ) * 2 ^ 128) * (2 ^ 32 * 4) := by
          ring
      _ = ((Fintype.card ι : ℝ) * 2 ^ 128) * 2 ^ 34 := by rw [h34]
      _ ≤ ((Fintype.card ι : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hp.le)
      _ = (Fintype.card ι : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 34 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  unfold εAd h23Term at h
  generalize (2 : ℝ) ^ 1024 = κ at h hK hG
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e4 : ∀ x : ℝ, x / (4 * 2 ^ 128) = x / 4 / 2 ^ 128 := fun x => by rw [div_div]
  rw [e4] at hG
  have hG1 : 2 * ((Fintype.card ι : ℝ) * (nGrind : ℝ)) / κ =
      2 * ((Fintype.card ι : ℝ) * (nGrind : ℝ) / κ) := by ring
  have hG2 : 2 * (2 * ((Fintype.card ι : ℝ) * (nGrind : ℝ))) / κ =
      4 * ((Fintype.card ι : ℝ) * (nGrind : ℝ) / κ) := by ring
  split_ifs at h with h1 h2 h2
  · unfold εROP εRO at h
    push_cast at h ⊢
    rw [e]
    linarith
  · exfalso; omega
  · exfalso; omega
  · unfold εROP εRO at h
    push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸¹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityN_lean_2pow20 (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : Fintype.card ι + 2 ≤ 2 ^ 20) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁' b₂')| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityN_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityN_lean_2pow32 (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b₁ b₂ K, hidingAdv (A.withClients c).ctx
      (reductionRA (A.withClients c) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : Fintype.card ι + 2 ≤ 2 ^ 32) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (ι → XC)) × ShR (Blk → Blk)) (realGameN A b₁' b₂')| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityN_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

/-! ## Many challenge pairs: one pair on the tables -/

section PairRun

/-- A challenge pair's tape: the two issuance tapes, the round-1 and round-2 spend tapes. -/
abbrev PT := (TRe × TRe) × (TRe × TRe)

/-- **The Issuer `K` (its key, context, balance and guess) with the messages `m` of one pair.** -/
def withMsg (K : AdversaryRO R ZL) (m : MsgR) : AdversaryRO R ZL :=
  ⟨K.pk, K.ctx, K.tInit, fun _ c => bif c then m.1.1.2 else m.1.1.1, fun _ => m.1.2,
    fun _ _ => m.2.1, fun _ _ => m.2.2, K.guess⟩

variable (K : AdversaryRO R ZL)

/-- A pair's issuance transcript on the tables. -/
noncomputable def trOf (x : PT) (s : ShR R) : IssTr ZL :=
  (((issRealR K leanPIR x.1.1).out s).req, ((issRealR K leanPIR x.1.2).out s).req)

/-- **A pair's rounds on the tables**, with its messages `m`, in world `(b₁, b₂)`: the spec's
protocol with the Lean provers on the shared tables, exactly as in the two-session game
(`viewR` with real slots). -/
noncomputable def roundsOf (m : MsgR) (b₁ b₂ : Bool) (x : PT) (s : ShR R) : Rounds ZL :=
  let A := withMsg K m
  let i₀ := (issRealR K leanPIR x.1.1).out s
  let i₁ := (issRealR K leanPIR x.1.2).out s
  let tr : IssTr ZL := (i₀.req, i₁.req)
  let tk₀ := i₀.fin (A.respondIss tr false)
  let tk₁ := i₁.fin (A.respondIss tr true)
  let τ₁ := tokD (tokIface A.base) tk₀ tk₁ b₁
  let ok1 := ok₁ A.base (tokIface A.base) tr tk₀ tk₁
  let o₁ := (spRealR K leanPSR x.2.1).out τ₁ (A.d₁ tr) s
  let ch := o₁.fin (A.respond₁ tr o₁.req)
  let o₂ := (spRealR K leanPSR x.2.2).out (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr o₁.req) s
  bif ok1 then
      some (o₁.req, bif ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ o₁.req ch then some o₂.req
        else none) else none

/-- §6's rule for round 1 of a pair, with its stage-1 messages `m₁`. -/
noncomputable def ok1Of (m₁ : M₁) (x : PT) (s : ShR R) : Bool :=
  ok₁ (withMsg K (m₁, m2dflt)).base (tokIface (withMsg K (m₁, m2dflt)).base) (trOf K x s)
    (((issRealR K leanPIR x.1.1).out s).fin m₁.1.1) (((issRealR K leanPIR x.1.2).out s).fin m₁.1.2)

/-- A pair's round-1 request. -/
noncomputable def rq1 (m₁ : M₁) (b₁ : Bool) (x : PT) (s : ShR R) : SReq :=
  ((spRealR K leanPSR x.2.1).out
    (tokD (tokIface K.base) (((issRealR K leanPIR x.1.1).out s).fin m₁.1.1)
      (((issRealR K leanPIR x.1.2).out s).fin m₁.1.2) b₁) m₁.2 s).req

/-- **A pair's round-1 request as stage 2 sees it**: only if §6's rule lets round 1 run. -/
noncomputable def rq1Of (m₁ : M₁) (b₁ : Bool) (x : PT) (s : ShR R) : Option SReq :=
  bif ok1Of K m₁ x s then some (rq1 K m₁ b₁ x s) else none

/-- A pair's four slices. -/
def slOfR (x : PT) : SlicesR := ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2.2, x.2.2.2.2))

/-- Round 1 as stage 2 sees it is the first component of the rounds. -/
lemma roundsOf_map_fst (m : MsgR) (b₁ b₂ : Bool) (x : PT) (s : ShR R) :
    (roundsOf K m b₁ b₂ x s).map Prod.fst = rq1Of K m.1 b₁ x s := by
  have h : ∀ (c c' : Bool) (a : SReq × Option SReq) (a' : SReq), c = c' → a.1 = a' →
      Option.map Prod.fst (bif c then some a else none) = bif c' then some a' else none := by
    rintro c _ a _ rfl rfl
    cases c <;> rfl
  exact h _ _ _ _ rfl rfl

/-- **The two-session game with a table-reading Issuer, unfolded**: the guess at the issuance
transcript, the challenge pair's rounds (`roundsOf` with the transcript's messages) and its slices. -/
theorem realGameRA_eq (H : AdversaryRA R ZL) (b₁ b₂ : Bool) (x : PT) (t : ShR R) :
    realGameRA H leanPIR leanPSR b₁ b₂ (x, t) ↔
      H.guess (trOf H.toRO x t)
        (roundsOf H.toRO (transR H b₁ (issRealR H.toRO leanPIR x.1.1) (issRealR H.toRO leanPIR x.1.2)
          (spRealR H.toRO leanPSR x.2.1) (spRealR H.toRO leanPSR x.2.2) t) b₁ b₂ x t)
        (slOfR x) t :=
  Iff.rfl

/-- A token is accepted by `finalize_issue` exactly when the response is a preimage of the
commitment in the request (`tkOk`). -/
def tkOk (pk : PublicKey) (q : IReq) (resp : Preimage) : Bool :=
  match q with
  | .ok q => decide (uovEval pk resp = tag (issueReqC q) 0)
  | .error _ => false

/-- **§6's rule for round 1 on the Issuer's view**: both tokens finalize (the responses are
preimages of the commitments in the requests) and the initial balance affords `d₁`. -/
def ok₁Pub (pk : PublicKey) (tInit : Credits) (tr : IssTr ZL) (m₁ : M₁) : Bool :=
  tkOk pk tr.1 m₁.1.1 && tkOk pk tr.2 m₁.1.2 && (clientCheck tInit 0 m₁.2).isSome &&
    (clientCheck tInit 0 m₁.2).isSome

lemma issRealR_out (x : TRe) (s : ShR R) :
    (issRealR K leanPIR x).out s = issOutOf K.base (issXR K.ctx K.tInit x s) := rfl

lemma spRealR_outX (y : TRe) (τ : TokenS) (d : Credits) (s : ShR R) :
    (spRealR K leanPSR y).out τ d s = spOutOf K.base (spXR K.pk K.ctx (some τ) d y s).2 := rfl

/-- **A pair's rounds from its issuance and spend results** (`roundsOf`, factored). -/
def roundsW (m : MsgR) (b₁ : Bool) (ri : (Except Error (PendingTokenS × IssueRequest ZL)) ×
    (Except Error (PendingTokenS × IssueRequest ZL)))
    (o₁ o₂ : Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)) : Rounds ZL :=
  let A := withMsg K m
  let i₀ := issOutOf K.base ri.1
  let i₁ := issOutOf K.base ri.2
  let tr : IssTr ZL := (i₀.req, i₁.req)
  let tk₀ := i₀.fin (A.respondIss tr false)
  let tk₁ := i₁.fin (A.respondIss tr true)
  let ok1 := ok₁ A.base (tokIface A.base) tr tk₀ tk₁
  let O₁ := spOutOf K.base o₁.2
  let ch := O₁.fin (A.respond₁ tr O₁.req)
  bif ok1 then
      some (O₁.req, bif ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ O₁.req ch then
        some (spOutOf K.base o₂.2).req else none) else none

/-- Round 1's token from the issuance results. -/
def tau1R (m : MsgR) (b₁ : Bool) (ri : (Except Error (PendingTokenS × IssueRequest ZL)) ×
    (Except Error (PendingTokenS × IssueRequest ZL))) : TokenS :=
  tokD (tokIface (withMsg K m).base)
    ((issOutOf K.base ri.1).fin ((withMsg K m).respondIss ((issOutOf K.base ri.1).req, (issOutOf K.base ri.2).req) false))
    ((issOutOf K.base ri.2).fin ((withMsg K m).respondIss ((issOutOf K.base ri.1).req, (issOutOf K.base ri.2).req) true))
    b₁

/-- Round 2's token from the issuance results and round 1's result. -/
def tau2R (m : MsgR) (b₁ b₂ : Bool) (ri : (Except Error (PendingTokenS × IssueRequest ZL)) ×
    (Except Error (PendingTokenS × IssueRequest ZL)))
    (o₁ : Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)) : TokenS :=
  cur₂ (tokIface (withMsg K m).base) b₁ b₂
    ((issOutOf K.base ri.1).fin ((withMsg K m).respondIss ((issOutOf K.base ri.1).req, (issOutOf K.base ri.2).req) false))
    ((issOutOf K.base ri.2).fin ((withMsg K m).respondIss ((issOutOf K.base ri.1).req, (issOutOf K.base ri.2).req) true))
    ((spOutOf K.base o₁.2).fin ((withMsg K m).respond₁ ((issOutOf K.base ri.1).req, (issOutOf K.base ri.2).req)
      (spOutOf K.base o₁.2).req))

lemma roundsOf_eq_W (m : MsgR) (b₁ b₂ : Bool) (x : PT) (s : ShR R) :
    roundsOf K m b₁ b₂ x s =
      roundsW K m b₁ (issXR K.ctx K.tInit x.1.1 s, issXR K.ctx K.tInit x.1.2 s)
        (spXR K.pk K.ctx (some (tau1R K m b₁ (issXR K.ctx K.tInit x.1.1 s, issXR K.ctx K.tInit x.1.2 s)))
          m.1.2 x.2.1 s)
        (spXR K.pk K.ctx (some (tau2R K m b₁ b₂ (issXR K.ctx K.tInit x.1.1 s, issXR K.ctx K.tInit x.1.2 s)
          (spXR K.pk K.ctx (some (tau1R K m b₁ (issXR K.ctx K.tInit x.1.1 s, issXR K.ctx K.tInit x.1.2 s)))
            m.1.2 x.2.1 s))) m.2.2 x.2.2 s) := by
  simp only [roundsOf, roundsW, tau1R, tau2R, issRealR_out, spRealR_outX]
  rfl

/-- An honest issuance's token: it finalizes exactly when `tkOk`, and then it is valid with
balance `T_init` and refund `0`. -/
lemma fin_issXR (x : TRe) (s : ShR R) (resp : Preimage) (d : Credits) :
    (((issRealR K leanPIR x).out s).fin resp).isSome = tkOk K.pk ((issRealR K leanPIR x).out s).req resp ∧
      ∀ τ, ((issRealR K leanPIR x).out s).fin resp = some τ →
        (tokIface K.base).ok τ d = (clientCheck K.tInit 0 d).isSome := by
  rw [issRealR_out]
  unfold issXR issueOf
  split_ifs with h0
  · exact ⟨rfl, fun τ h => by simp [issOutOf] at h⟩
  · rcases hp : (primI leanPIR x.2.2 s).proveIssue ⟨com (vec x.1.1) K.ctx K.tInit (vec x.1.2), K.tInit, K.ctx⟩
        ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) with _ | pf
    · exact ⟨rfl, fun τ h => by simp [issOutOf] at h⟩
    · by_cases hc : uovEval K.pk resp = tag (com (vec x.1.1) K.ctx K.tInit (vec x.1.2)) 0
      · have hc' : uovEval K.base.pk resp = tag (com (vec x.1.1) K.ctx K.tInit (vec x.1.2)) 0 := hc
        refine ⟨?_, fun τ h => ?_⟩
        · simp [issOutOf, finalizeIssue, tkOk, issueReqC_mk, hc']
          exact hc
        · simp only [issOutOf, finalizeIssue, hc', ↓reduceIte, Option.some.injEq] at h
          subst h
          have hv : TokenS.Valid K.base.pk K.base.ctx ⟨vec x.1.1, K.tInit, vec x.1.2, 0, resp⟩ := hc
          simp only [tokIface, hv, decide_true, Bool.true_and]
      · have hc' : ¬ uovEval K.base.pk resp = tag (com (vec x.1.1) K.ctx K.tInit (vec x.1.2)) 0 := hc
        refine ⟨?_, fun τ h => ?_⟩
        · simp [issOutOf, finalizeIssue, tkOk, issueReqC_mk, hc']
          exact hc
        · simp [issOutOf, finalizeIssue, hc'] at h

/-- **§6's rule for round 1 is computed from the Issuer's view** (`ok₁Pub`), for honest
issuances. -/
theorem ok1Of_eq_pub (m₁ : M₁) (x : PT) (s : ShR R) :
    ok1Of K m₁ x s = ok₁Pub K.pk K.tInit (trOf K x s) m₁ := by
  obtain ⟨f0, v0⟩ := fin_issXR K x.1.1 s m₁.1.1 m₁.2
  obtain ⟨f1, v1⟩ := fin_issXR K x.1.2 s m₁.1.2 m₁.2
  have hI : tokIface (withMsg K (m₁, m2dflt)).base = tokIface K.base := rfl
  have hd : ∀ tr, (withMsg K (m₁, m2dflt)).base.d₁ tr = m₁.2 := fun _ => rfl
  unfold ok1Of ok₁ ok₁Pub
  simp only [trOf]
  rw [hI, hd, ← f0, ← f1]
  rcases h0 : ((issRealR K leanPIR x.1.1).out s).fin m₁.1.1 with _ | τ₀
  · simp
  · rcases h1 : ((issRealR K leanPIR x.1.2).out s).fin m₁.1.2 with _ | τ₁
    · simp
    · have e0 := v0 τ₀ h0
      have e1 := v1 τ₁ h1
      simp only [tokD, Bool.cond_false, Bool.cond_true, Option.getD_some, Option.isSome_some,
        Bool.true_and, e0, e1]

end PairRun

/-! ## Many challenge pairs -/

section Pairs

variable {N : ℕ}

/-- `a` at position `k`, `f` at the others. -/
def joinK {α : Type*} (k : Fin N) (a : α) (f : {j : Fin N // j ≠ k} → α) : Fin N → α :=
  fun j => if h : j = k then a else f ⟨j, h⟩

lemma joinK_self {α : Type*} (k : Fin N) (a : α) (f : {j : Fin N // j ≠ k} → α) : joinK k a f k = a := by
  simp [joinK]

lemma joinK_ne {α : Type*} {k j : Fin N} (a : α) (f : {j : Fin N // j ≠ k} → α) (h : j ≠ k) :
    joinK k a f j = f ⟨j, h⟩ := by
  simp [joinK, h]

/-- **The malicious Issuer of the game with `N` challenge pairs**: key, context and balance;
stage 1 (after **every** issuance request) the responses to every Client and every pair's
round-1 amount; stage 2 (after every pair's round-1 request, for the pairs whose round 1 runs)
every pair's round-1 response and round-2 amount; and a guess that sees all issuance requests,
every pair's rounds, all slices and the tables. The interaction does not read the tables. -/
structure AdversaryP (R : Type) (N : ℕ) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : (Fin N → IssTr ZL) → Fin N → Bool → Preimage
  d₁ : (Fin N → IssTr ZL) → Fin N → Credits
  respond₁ : (Fin N → IssTr ZL) → (Fin N → Option SReq) → Fin N → SpendResponse
  d₂ : (Fin N → IssTr ZL) → (Fin N → Option SReq) → Fin N → Credits
  guess : (Fin N → IssTr ZL) → (Fin N → Rounds ZL) → (Fin N → SlicesR) → ShR R → Prop

/-- **The guess's budget**: each of the `4N` slices at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` freely. -/
structure AdversaryP.Budget (A : AdversaryP R N) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T Y (sl : Fin N → SlicesR) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((g, (sl k).1.2), (sl k).2)) s) q3
  h31 : ∀ T Y (sl : Fin N → SlicesR) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k (((sl k).1.1, g), (sl k).2)) s) q3
  h32 : ∀ T Y (sl : Fin N → SlicesR) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((sl k).1, (g, (sl k).2.2))) s) q3
  h33 : ∀ T Y (sl : Fin N → SlicesR) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((sl k).1, ((sl k).2.1, g))) s) q3
  h5 : ∀ T Y sl, Rd5 (A.guess T Y sl) q5
  hE : ∀ T Y sl, RdE (A.guess T Y sl) qE

namespace AdversaryP

variable (A : AdversaryP R N)

/-- The Issuer's key, context and balance (for the Clients' slots). -/
def keyRO : AdversaryRO R ZL :=
  ⟨A.pk, A.ctx, A.tInit, fun _ c => bif c then m1dflt.1.2 else m1dflt.1.1, fun _ => m1dflt.2,
    fun _ _ => m2dflt.1, fun _ _ => m2dflt.2, fun _ _ _ _ => True⟩

/-- Pair `j`'s stage-1 messages at the issuance transcripts `T`. -/
def M1 (T : Fin N → IssTr ZL) (j : Fin N) : M₁ := ((A.respondIss T j false, A.respondIss T j true), A.d₁ T j)

/-- Pair `j`'s stage-2 messages at the transcripts `T` and the round-1 requests `Q`. -/
def M2 (T : Fin N → IssTr ZL) (Q : Fin N → Option SReq) (j : Fin N) : M₂ :=
  (A.respond₁ T Q j, A.d₂ T Q j)

/-- All issuance transcripts on the tables. -/
noncomputable def TRP (z : Fin N → PT) (s : ShR R) : Fin N → IssTr ZL := fun j => trOf A.keyRO (z j) s

/-- All round-1 requests as stage 2 sees them. -/
noncomputable def RQP (w : Fin N → Bool × Bool) (z : Fin N → PT) (s : ShR R) : Fin N → Option SReq :=
  fun j => rq1Of A.keyRO (A.M1 (A.TRP z s) j) (w j).1 (z j) s

end AdversaryP

/-- **The real game with `N` challenge pairs** in world `w : Fin N → Bool × Bool`: every pair runs
the protocol of the two-session game with the Lean provers on the shared tables (each Client with
its own randomness and `H₃` slices), pair `j` in world `w j`; the Issuer's stages see all pairs. -/
noncomputable def realGameP (A : AdversaryP R N) (w : Fin N → Bool × Bool) (z : (Fin N → PT) × ShR R) :
    Prop :=
  A.guess (A.TRP z.1 z.2)
    (fun j => roundsOf A.keyRO (A.M1 (A.TRP z.1 z.2) j, A.M2 (A.TRP z.1 z.2) (A.RQP w z.1 z.2) j)
      (w j).1 (w j).2 (z.1 j) z.2)
    (fun j => slOfR (z.1 j)) z.2

namespace AdversaryP

variable (A : AdversaryP R N) (k : Fin N) (c : {j : Fin N // j ≠ k} → PT)
  (v : {j : Fin N // j ≠ k} → Bool × Bool)

/-- The issuance transcripts at pair `k`'s transcript `tr`, the other pairs run on the tables. -/
noncomputable def hopTR (tr : IssTr ZL) (u : ShR R) : Fin N → IssTr ZL :=
  joinK k tr fun j => trOf A.keyRO (c j) u

/-- The other pairs' round-1 requests as stage 2 sees them. -/
noncomputable def hopRQ (tr : IssTr ZL) (u : ShR R) : {j : Fin N // j ≠ k} → Option SReq :=
  fun j => rq1Of A.keyRO (A.M1 (A.hopTR k c tr u) j) (v j).1 (c j) u

/-- All round-1 requests as stage 2 sees them, pair `k`'s masked by §6's rule on the Issuer's
view (`ok₁Pub`). -/
noncomputable def hopQ (tr : IssTr ZL) (rq : SReq) (u : ShR R) : Fin N → Option SReq :=
  joinK k (bif ok₁Pub A.pk A.tInit tr (A.M1 (A.hopTR k c tr u) k) then some rq else none)
    (A.hopRQ k c v tr u)

/-- All pairs' rounds, pair `k`'s given. -/
noncomputable def hopY (tr : IssTr ZL) (y : Rounds ZL) (u : ShR R) : Fin N → Rounds ZL :=
  joinK k y fun j => roundsOf A.keyRO (A.M1 (A.hopTR k c tr u) j,
    A.M2 (A.hopTR k c tr u) (joinK k (y.map Prod.fst) (A.hopRQ k c v tr u)) j) (v j).1 (v j).2 (c j) u

/-- **The Issuer of the two-session game for pair `k`**: it runs the other pairs itself, with
their tapes `c` and worlds `v`, on the tables it is given; its stage 2 masks pair `k`'s round-1
request by §6's rule computed from what it has seen (`ok₁Pub`). -/
noncomputable def hop : AdversaryRA R ZL where
  pk := A.pk
  ctx := A.ctx
  tInit := A.tInit
  respondIss tr i _ u := A.respondIss (A.hopTR k c tr u) k i
  d₁ tr _ u := A.d₁ (A.hopTR k c tr u) k
  respond₁ tr rq _ u := A.respond₁ (A.hopTR k c tr u) (A.hopQ k c v tr rq u) k
  d₂ tr rq _ u := A.d₂ (A.hopTR k c tr u) (A.hopQ k c v tr rq u) k
  guess tr y sl u := A.guess (A.hopTR k c tr u) (A.hopY k c v tr y u) (joinK k sl fun j => slOfR (c j)) u

/-! ### The hop's stages and guess, factored through the other pairs' proofs -/

/-- An issuance result. -/
abbrev IssRes := Except Error (PendingTokenS × IssueRequest ZL)
/-- A spend result. -/
abbrev SpRes := Option TokenS × Except Error (PendingSpendS × SpendRequest ZL)

/-- The other pairs' issuances on the tables. -/
noncomputable def issFam (u : ShR R) : {j : Fin N // j ≠ k} → IssRes × IssRes :=
  fun j => (issXR A.keyRO.ctx A.keyRO.tInit (c j).1.1 u, issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 u)

/-- The transcripts, from the other pairs' issuance results. -/
def trW (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) : Fin N → IssTr ZL :=
  joinK k tr fun j => ((issOutOf A.keyRO.base (W j).1).req, (issOutOf A.keyRO.base (W j).2).req)

/-- Another pair's round-1 token. -/
def tk1W (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) (j : {j : Fin N // j ≠ k}) :
    TokenS :=
  tokD (tokIface A.keyRO.base) ((issOutOf A.keyRO.base (W j).1).fin (A.M1 (A.trW k tr W) j).1.1)
    ((issOutOf A.keyRO.base (W j).2).fin (A.M1 (A.trW k tr W) j).1.2) (v j).1

/-- The other pairs' round-1 spends on the tables. -/
noncomputable def sp1Fam (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) (u : ShR R) :
    {j : Fin N // j ≠ k} → SpRes :=
  fun j => spXR A.keyRO.pk A.keyRO.ctx (some (A.tk1W k v tr W j)) (A.M1 (A.trW k tr W) j).2 (c j).2.1 u

/-- Another pair's §6 rule for round 1. -/
def okW (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) (j : {j : Fin N // j ≠ k}) : Bool :=
  ok₁ (withMsg A.keyRO (A.M1 (A.trW k tr W) j, m2dflt)).base
    (tokIface (withMsg A.keyRO (A.M1 (A.trW k tr W) j, m2dflt)).base)
    ((issOutOf A.keyRO.base (W j).1).req, (issOutOf A.keyRO.base (W j).2).req)
    ((issOutOf A.keyRO.base (W j).1).fin (A.M1 (A.trW k tr W) j).1.1)
    ((issOutOf A.keyRO.base (W j).2).fin (A.M1 (A.trW k tr W) j).1.2)

/-- The other pairs' round-1 requests as stage 2 sees them. -/
def rqW (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes)
    (S : {j : Fin N // j ≠ k} → SpRes) : {j : Fin N // j ≠ k} → Option SReq :=
  fun j => bif A.okW k tr W j then some (spOutOf A.keyRO.base (S j).2).req else none

lemma hopTR_eq (tr : IssTr ZL) (u : ShR R) : A.hopTR k c tr u = A.trW k tr (A.issFam k c u) := by
  simp only [hopTR, trW, issFam, trOf, issRealR_out]

lemma hopRQ_eq (tr : IssTr ZL) (u : ShR R) :
    A.hopRQ k c v tr u = A.rqW k tr (A.issFam k c u) (A.sp1Fam k c v tr (A.issFam k c u) u) := by
  funext j
  simp only [hopRQ, rqW, okW, sp1Fam, tk1W, issFam, rq1Of, ok1Of, rq1, trOf, issRealR_out, spRealR_outX,
    hopTR_eq]

/-! ### The hop's budgets -/

/-- The other pairs' issuances, read together. -/
lemma issFam_sreads :
    SReads pI (fun t : Tb R pI => A.issFam k c t.2) 0
      (Fintype.card {j : Fin N // j ≠ k} * (nGrind + nGrind))
      (Fintype.card {j : Fin N // j ≠ k} * (624 + 624))
      (Fintype.card {j : Fin N // j ≠ k} * (4607 + 4607)) := by
  have h := SReads.pi (ι := {j : Fin N // j ≠ k})
    (f := fun j (t : Tb R pI) => (issXR A.keyRO.ctx A.keyRO.tInit (c j).1.1 t.2,
      issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 t.2))
    fun j => (issXR_sreads A.keyRO.ctx A.keyRO.tInit (c j).1.1).pair
      (issXR_sreads A.keyRO.ctx A.keyRO.tInit (c j).1.2)
  exact h.mono (by simp) le_rfl le_rfl le_rfl

/-- The other pairs' round-1 spends, read together. -/
lemma sp1Fam_sreads (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) :
    SReads pI (fun t : Tb R pI => A.sp1Fam k c v tr W t.2) 0
      (Fintype.card {j : Fin N // j ≠ k} * nGrind) (Fintype.card {j : Fin N // j ≠ k} * 624)
      (Fintype.card {j : Fin N // j ≠ k} * 4607) := by
  have h := SReads.pi (ι := {j : Fin N // j ≠ k})
    (f := fun j (t : Tb R pI) => A.sp1Fam k c v tr W t.2 j)
    fun j => spXR_sreads A.keyRO.pk A.keyRO.ctx _ _ (c j).2.1
  exact h.mono (by simp) le_rfl le_rfl le_rfl

/-- The hop's stage 1, factored through the other pairs' issuances. -/
lemma hop_msg₁ (tr : IssTr ZL) (sl : SlicesR) (u : ShR R) :
    (A.hop k c v).msg₁ tr sl u =
      (fun W => ((A.respondIss (A.trW k tr W) k false, A.respondIss (A.trW k tr W) k true),
        A.d₁ (A.trW k tr W) k)) (A.issFam k c u) := by
  simp only [AdversaryRA.msg₁, hop, hopTR_eq]

/-- The hop's stage 2, factored through the other pairs' issuances and round-1 spends. -/
def msg₂W (tr : IssTr ZL) (rq : SReq) (W : {j : Fin N // j ≠ k} → IssRes × IssRes)
    (S : {j : Fin N // j ≠ k} → SpRes) : M₂ :=
  (A.respond₁ (A.trW k tr W)
      (joinK k (bif ok₁Pub A.pk A.tInit tr (A.M1 (A.trW k tr W) k) then some rq else none)
        (A.rqW k tr W S)) k,
    A.d₂ (A.trW k tr W)
      (joinK k (bif ok₁Pub A.pk A.tInit tr (A.M1 (A.trW k tr W) k) then some rq else none)
        (A.rqW k tr W S)) k)

lemma hop_msg₂ (tr : IssTr ZL) (rq : SReq) (sl : SlicesR) (u : ShR R) :
    (A.hop k c v).msg₂ tr rq sl u =
      A.msg₂W k tr rq (A.issFam k c u) (A.sp1Fam k c v tr (A.issFam k c u) u) := by
  simp only [AdversaryRA.msg₂, hop, hopQ, hopTR_eq, hopRQ_eq, msg₂W]

/-- Stage 1 of the hop reads the other pairs' issuances. -/
lemma hop_stage1 (tr : IssTr ZL) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.hop k c v).msg₁ tr (σ t) t.2) 0
      (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind))
      (3 * (Fintype.card {j : Fin N // j ≠ k} * 624)) (3 * (Fintype.card {j : Fin N // j ≠ k} * 4607)) := by
  have h := (A.issFam_sreads k c).map fun W =>
    (((A.respondIss (A.trW k tr W) k false, A.respondIss (A.trW k tr W) k true),
      A.d₁ (A.trW k tr W) k) : M₁)
  refine ((congrArg (fun F => SReads pI F _ _ _ _) (funext fun t => ?_)).mp h).mono le_rfl
    (by rw [Nat.mul_add]; omega) (by omega) (by omega)
  exact (A.hop_msg₁ k c v tr (σ t) t.2).symm

/-- Stage 2 of the hop reads the other pairs' issuances and round-1 spends. -/
lemma hop_stage2 (tr : IssTr ZL) (rq : SReq) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.hop k c v).msg₂ tr rq (σ t) t.2) 0
      (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind))
      (3 * (Fintype.card {j : Fin N // j ≠ k} * 624)) (3 * (Fintype.card {j : Fin N // j ≠ k} * 4607)) := by
  have h := (A.issFam_sreads k c).bind (g := fun W (t : Tb R pI) =>
      A.msg₂W k tr rq W (A.sp1Fam k c v tr W t.2))
    fun W => (A.sp1Fam_sreads k c v tr W).map fun S => A.msg₂W k tr rq W S
  refine ((congrArg (fun F => SReads pI F _ _ _ _) (funext fun t => ?_)).mp h).mono (by simp)
    (by rw [Nat.mul_add]; omega) (by omega) (by omega)
  exact (A.hop_msg₂ k c v tr rq (σ t) t.2).symm

/-- **The hop's interaction budget**: the other pairs' issuances and round-1 spends. -/
theorem hop_iBudget : (A.hop k c v).IBudget 0 (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind))
    (3 * (Fintype.card {j : Fin N // j ≠ k} * 624)) (3 * (Fintype.card {j : Fin N // j ≠ k} * 4607)) where
  a0 tr g₁ g₂ g₃ := A.hop_stage1 k c v tr fun t => ((t.1, g₁), (g₂, g₃))
  a1 tr g₀ g₂ g₃ := A.hop_stage1 k c v tr fun t => ((g₀, t.1), (g₂, g₃))
  a2 tr g₀ g₁ g₃ := A.hop_stage1 k c v tr fun t => ((g₀, g₁), (t.1, g₃))
  a3 tr g₀ g₁ g₂ := A.hop_stage1 k c v tr fun t => ((g₀, g₁), (g₂, t.1))
  b0 tr rq g₁ g₂ g₃ := A.hop_stage2 k c v tr rq fun t => ((t.1, g₁), (g₂, g₃))
  b1 tr rq g₀ g₂ g₃ := A.hop_stage2 k c v tr rq fun t => ((g₀, t.1), (g₂, g₃))
  b2 tr rq g₀ g₁ g₃ := A.hop_stage2 k c v tr rq fun t => ((g₀, g₁), (t.1, g₃))
  b3 tr rq g₀ g₁ g₂ := A.hop_stage2 k c v tr rq fun t => ((g₀, g₁), (g₂, t.1))

/-- Another pair's messages, from the issuance results `W`, round-1 results `S` and pair `k`'s
rounds `y`. -/
def mW (tr : IssTr ZL) (y : Rounds ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes)
    (S : {j : Fin N // j ≠ k} → SpRes) (j : {j : Fin N // j ≠ k}) : MsgR :=
  (A.M1 (A.trW k tr W) j, A.M2 (A.trW k tr W) (joinK k (y.map Prod.fst) (A.rqW k tr W S)) j)

/-- The other pairs' round-2 spends on the tables. -/
noncomputable def sp2Fam (tr : IssTr ZL) (y : Rounds ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes)
    (S : {j : Fin N // j ≠ k} → SpRes) (u : ShR R) : {j : Fin N // j ≠ k} → SpRes :=
  fun j => spXR A.keyRO.pk A.keyRO.ctx
    (some (tau2R A.keyRO (A.mW k tr y W S j) (v j).1 (v j).2 (W j) (S j))) (A.mW k tr y W S j).2.2
    (c j).2.2 u

/-- The hop's guess, factored through the other pairs' proofs. -/
def guessW (tr : IssTr ZL) (y : Rounds ZL) (sl : SlicesR) (W : {j : Fin N // j ≠ k} → IssRes × IssRes)
    (S S₂ : {j : Fin N // j ≠ k} → SpRes) (u : ShR R) : Prop :=
  A.guess (A.trW k tr W)
    (joinK k y fun j => roundsW A.keyRO (A.mW k tr y W S j) (v j).1 (W j) (S j) (S₂ j))
    (joinK k sl fun j => slOfR (c j)) u

lemma tau1R_eq (K : AdversaryRO R ZL) (m : MsgR) (b₁ : Bool) (ri : IssRes × IssRes) :
    tau1R K m b₁ ri = tokD (tokIface K.base) ((issOutOf K.base ri.1).fin m.1.1.1)
      ((issOutOf K.base ri.2).fin m.1.1.2) b₁ := rfl

lemma hop_guess_eq (tr : IssTr ZL) (y : Rounds ZL) (sl : SlicesR) (u : ShR R) :
    (A.hop k c v).guess tr y sl u =
      A.guessW k c v tr y sl (A.issFam k c u) (A.sp1Fam k c v tr (A.issFam k c u) u)
        (A.sp2Fam k c v tr y (A.issFam k c u) (A.sp1Fam k c v tr (A.issFam k c u) u) u) u := by
  simp only [hop, hopTR_eq, hopY, hopRQ_eq, roundsOf_eq_W, tau1R_eq, guessW, sp2Fam, sp1Fam, tk1W,
    mW, issFam]

lemma joinK_update {α : Type*} (k : Fin N) (a a' : α) (f : {j : Fin N // j ≠ k} → α) :
    joinK k a' f = Function.update (joinK k a f) k a' := funext fun j => by
  by_cases h : j = k
  · subst h; simp [joinK]
  · simp [joinK, h]

/-- **The hop's guess budget**: the Issuer's, plus the other pairs' issuances and both rounds. -/
theorem hop_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.hop k c v).GBudget q3 (4 * (Fintype.card {j : Fin N // j ≠ k} * 624) + q5)
      (4 * (Fintype.card {j : Fin N // j ≠ k} * 4607) + qE) := fun mm => by
  let S : {j : Fin N // j ≠ k} → SlicesR := fun j => slOfR (c j)
  have hk : ∀ sl : SlicesR, joinK k sl S k = sl := fun sl => joinK_self _ _ _
  have hI5 : Rd5 (fun u => A.issFam k c u) (Fintype.card {j : Fin N // j ≠ k} * (624 + 624)) :=
    Rd5.pi fun j => (issXR_rd5 A.keyRO.ctx A.keyRO.tInit (c j).1.1).bind
      (f := fun a u => (a, issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 u))
      fun a => (issXR_rd5 A.keyRO.ctx A.keyRO.tInit (c j).1.2).map (Prod.mk a)
  have hIE : RdE (fun u => A.issFam k c u) (Fintype.card {j : Fin N // j ≠ k} * (4607 + 4607)) :=
    RdE.pi fun j => (issXR_rdE A.keyRO.ctx A.keyRO.tInit (c j).1.1).bind
      (f := fun a u => (a, issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 u))
      fun a => (issXR_rdE A.keyRO.ctx A.keyRO.tInit (c j).1.2).map (Prod.mk a)
  refine ⟨fun tr y g₁ g₂ g₃ s => ?_, fun tr y g₀ g₂ g₃ s => ?_, fun tr y g₀ g₁ g₃ s => ?_,
    fun tr y g₀ g₁ g₂ s => ?_, fun tr y sl => ?_, fun tr y sl => ?_⟩
  · have e : (fun g => ((A.hop k c v).fixR mm).guess tr y ((g, g₁), (g₂, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr s) (A.hopY k c v tr y s)
          (Function.update (joinK k ((g₁, g₁), (g₂, g₃)) S) k
            ((g, (joinK k ((g₁, g₁), (g₂, g₃)) S k).1.2), (joinK k ((g₁, g₁), (g₂, g₃)) S k).2)) s := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h30 _ _ _ s k
  · have e : (fun g => ((A.hop k c v).fixR mm).guess tr y ((g₀, g), (g₂, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr s) (A.hopY k c v tr y s)
          (Function.update (joinK k ((g₀, g₀), (g₂, g₃)) S) k
            (((joinK k ((g₀, g₀), (g₂, g₃)) S k).1.1, g), (joinK k ((g₀, g₀), (g₂, g₃)) S k).2)) s := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h31 _ _ _ s k
  · have e : (fun g => ((A.hop k c v).fixR mm).guess tr y ((g₀, g₁), (g, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr s) (A.hopY k c v tr y s)
          (Function.update (joinK k ((g₀, g₁), (g₃, g₃)) S) k
            ((joinK k ((g₀, g₁), (g₃, g₃)) S k).1, (g, (joinK k ((g₀, g₁), (g₃, g₃)) S k).2.2))) s := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h32 _ _ _ s k
  · have e : (fun g => ((A.hop k c v).fixR mm).guess tr y ((g₀, g₁), (g₂, g)) s) = fun g =>
        A.guess (A.hopTR k c tr s) (A.hopY k c v tr y s)
          (Function.update (joinK k ((g₀, g₁), (g₂, g₂)) S) k
            ((joinK k ((g₀, g₁), (g₂, g₂)) S k).1, ((joinK k ((g₀, g₁), (g₂, g₂)) S k).2.1, g))) s := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h33 _ _ _ s k
  · have h := Rd5.bindEq (m := fun u => A.issFam k c u)
      (f := fun W u => A.guessW k c v tr y sl W (A.sp1Fam k c v tr W u)
        (A.sp2Fam k c v tr y W (A.sp1Fam k c v tr W u) u) u)
      (F := fun u => ((A.hop k c v).fixR mm).guess tr y sl u)
      (fun u => A.hop_guess_eq k c v tr y sl u) hI5 fun W =>
        Rd5.bindEq (m := fun u => A.sp1Fam k c v tr W u)
          (f := fun S1 u => A.guessW k c v tr y sl W S1 (A.sp2Fam k c v tr y W S1 u) u)
          (fun _ => rfl) (Rd5.pi fun j => spXR_rd5 _ _ _ _ _) fun S1 =>
            Rd5.bindEq (m := fun u => A.sp2Fam k c v tr y W S1 u)
              (f := fun S2 u => A.guessW k c v tr y sl W S1 S2 u)
              (fun _ => rfl) (Rd5.pi fun j => spXR_rd5 _ _ _ _ _) fun S2 => hA.h5 _ _ _
    exact h.mono (by rw [Nat.mul_add]; omega)
  · have h := RdE.bindEq (m := fun u => A.issFam k c u)
      (f := fun W u => A.guessW k c v tr y sl W (A.sp1Fam k c v tr W u)
        (A.sp2Fam k c v tr y W (A.sp1Fam k c v tr W u) u) u)
      (F := fun u => ((A.hop k c v).fixR mm).guess tr y sl u)
      (fun u => A.hop_guess_eq k c v tr y sl u) hIE fun W =>
        RdE.bindEq (m := fun u => A.sp1Fam k c v tr W u)
          (f := fun S1 u => A.guessW k c v tr y sl W S1 (A.sp2Fam k c v tr y W S1 u) u)
          (fun _ => rfl) (RdE.pi fun j => spXR_rdE _ _ _ _ _) fun S1 =>
            RdE.bindEq (m := fun u => A.sp2Fam k c v tr y W S1 u)
              (f := fun S2 u => A.guessW k c v tr y sl W S1 S2 u)
              (fun _ => rfl) (RdE.pi fun j => spXR_rdE _ _ _ _ _) fun S2 => hA.hE _ _ _
    exact h.mono (by rw [Nat.mul_add]; omega)

/-- **The two-session game of `A.hop k`, unfolded**: the guess at all transcripts, all rounds
(pair `k`'s with its messages, the others' recomputed) and all slices. -/
theorem realGameRA_hop (b₁ b₂ : Bool) (x : PT) (t : ShR R) :
    realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂ (x, t) ↔
      A.guess (A.hopTR k c (trOf A.keyRO x t) t)
        (A.hopY k c v (trOf A.keyRO x t)
          (roundsOf A.keyRO (A.M1 (A.hopTR k c (trOf A.keyRO x t) t) k,
            A.M2 (A.hopTR k c (trOf A.keyRO x t) t)
              (A.hopQ k c v (trOf A.keyRO x t)
                (rq1 A.keyRO (A.M1 (A.hopTR k c (trOf A.keyRO x t) t) k) b₁ x t) t) k) b₁ b₂ x t) t)
        (joinK k (slOfR x) fun j => slOfR (c j)) t :=
  Iff.rfl

end AdversaryP

/-- **The game with `N` pairs is, at pair `k`, the two-session game of `A.hop k`** with the other
pairs' tapes and worlds, tape by tape. -/
theorem realGameP_iff (A : AdversaryP R N) (w : Fin N → Bool × Bool) (k : Fin N) (z : Fin N → PT)
    (s : ShR R) :
    realGameP A w (z, s) ↔
      realGameRA (A.hop k (fun j => z j.1) (fun j => w j.1)) leanPIR leanPSR (w k).1 (w k).2 (z k, s) := by
  rw [AdversaryP.realGameRA_hop]
  have key : ∀ T T' Y Y' S S', T = T' → Y = Y' → S = S' → (A.guess T Y S s ↔ A.guess T' Y' S' s) := by
    rintro _ _ _ _ _ _ rfl rfl rfl
    exact Iff.rfl
  have eT : A.TRP z s = A.hopTR k (fun j => z j.1) (trOf A.keyRO (z k) s) s := by
    funext j
    by_cases h : j = k
    · subst h; rw [AdversaryP.hopTR, joinK_self]; rfl
    · rw [AdversaryP.hopTR, joinK_ne _ _ h]; rfl
  have eQ : A.hopQ k (fun j => z j.1) (fun j => w j.1) (trOf A.keyRO (z k) s)
      (rq1 A.keyRO (A.M1 (A.TRP z s) k) (w k).1 (z k) s) s = A.RQP w z s := by
    funext j
    by_cases h : j = k
    · subst h
      rw [AdversaryP.hopQ, joinK_self, ← eT]
      show _ = rq1Of A.keyRO (A.M1 (A.TRP z s) j) (w j).1 (z j) s
      rw [rq1Of, ok1Of_eq_pub]
      rfl
    · rw [AdversaryP.hopQ, joinK_ne _ _ h, AdversaryP.hopRQ, ← eT]
      rfl
  have eY : ∀ y : Rounds ZL, y.map Prod.fst = A.RQP w z s k →
      joinK k (y.map Prod.fst) (A.hopRQ k (fun j => z j.1) (fun j => w j.1) (trOf A.keyRO (z k) s) s) =
        A.RQP w z s := fun y hy => by
    funext j
    by_cases h : j = k
    · subst h; rw [joinK_self, hy]
    · rw [joinK_ne _ _ h, AdversaryP.hopRQ, ← eT]
      rfl
  refine key _ _ _ _ _ _ eT (funext fun j => ?_) (funext fun j => ?_)
  · rw [AdversaryP.hopY, ← eT, eQ]
    by_cases h : j = k
    · subst h; rw [joinK_self]
    · rw [joinK_ne _ _ h, eY _ (roundsOf_map_fst A.keyRO
        (A.M1 (A.TRP z s) k, A.M2 (A.TRP z s) (A.RQP w z s) k) (w k).1 (w k).2 (z k) s)]
  · by_cases h : j = k
    · subst h; rw [joinK_self]
    · rw [joinK_ne _ _ h]

end Pairs

/-! ## The bound with `N` challenge pairs -/

section PairsBound

variable {N : ℕ}

lemma card_ne (k : Fin N) : Fintype.card {j : Fin N // j ≠ k} = N - 1 := by
  simp [Fintype.card_subtype_compl]

/-- The tape split at pair `k`: the other pairs' tapes, then pair `k`'s tape and the tables. -/
def eqR (k : Fin N) : (Fin N → PT) × ShR R ≃ ({j : Fin N // j ≠ k} → PT) × (PT × ShR R) where
  toFun z := (fun j => z.1 j.1, (z.1 k, z.2))
  invFun q := (joinK k q.2.1 q.1, q.2.2)
  left_inv z := Prod.ext (funext fun j => by
    by_cases h : j = k
    · subst h; exact joinK_self _ _ _
    · exact joinK_ne _ _ h) rfl
  right_inv q := Prod.ext (funext fun j => joinK_ne _ _ j.2) (Prod.ext (joinK_self _ _ _) rfl)

/-- The probability of the `N`-pair game, as the average over the other pairs' tapes of the
two-session game of pair `k`'s hop. -/
lemma pr_realGameP_eq (A : AdversaryP R N) (k : Fin N) (u : Fin N → Bool × Bool) :
    pr ((Fin N → PT) × ShR R) (realGameP A u) =
      pr (({j : Fin N // j ≠ k} → PT) × (PT × ShR R))
        (fun q => realGameRA (A.hop k q.1 fun j => u j.1) leanPIR leanPSR (u k).1 (u k).2 q.2) := by
  rw [← pr_equiv (eqR (R := R) k)]
  exact pr_congr fun z => realGameP_iff A u k z.1 z.2

/-- **The hybrid over the pairs**: if every step's two-session game (for every tape of the other
pairs) is `ε`-close across worlds, any two worlds of the `N`-pair game are `N·ε`-close. -/
lemma realGameP_hybrid (A : AdversaryP R N) (ε : ℝ)
    (h : ∀ (k : Fin N) (c : {j : Fin N // j ≠ k} → PT) (v : {j : Fin N // j ≠ k} → Bool × Bool)
      (b₁ b₂ b₁' b₂' : Bool),
      |pr (PT × ShR R) (realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂) -
        pr (PT × ShR R) (realGameRA (A.hop k c v) leanPIR leanPSR b₁' b₂')| ≤ ε)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR R) (realGameP A w) - pr ((Fin N → PT) × ShR R) (realGameP A w')| ≤
      N * ε := by
  refine abs_sub_le_mul_of_worlds (fun u => pr ((Fin N → PT) × ShR R) (realGameP A u)) ε
    (fun k u u' hu => ?_) w w'
  have hv : (fun j : {j : Fin N // j ≠ k} => u j.1) = fun j => u' j.1 :=
    funext fun j => hu j.1 j.2
  show |pr _ (realGameP A u) - pr _ (realGameP A u')| ≤ ε
  rw [pr_realGameP_eq A k u, pr_realGameP_eq A k u', ← hv]
  exact abs_pr_prod_sub_le _ _ fun c => h k c _ _ _ _ _

/-- The error of one pair's step in the game with `N` pairs: `unlinkabilityRA_lean_numG` for the
hop, whose interaction reads the other `N − 1` pairs' issuances and round-1 spends and whose guess
also their round-2 spends. -/
noncomputable def εPairR (R : Type) [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R] [ZKPRow R]
    (N q3 q5 qE : ℕ) (εhide : ℝ) : ℝ :=
  4 * ZKRow.εz R pI (2 * 0 + q3) (4 * ((N - 1) * 624) + q5 + 2 * (3 * ((N - 1) * 624)) + 1872)
      (4 * ((N - 1) * 4607) + qE + 2 * (3 * ((N - 1) * 4607)) + 13821) +
    2 * εAdG R pS 9 (0 + q3) (4 * ((N - 1) * 624) + q5 + 3 * ((N - 1) * 624) + 1248)
      (4 * ((N - 1) * 4607) + qE + 3 * ((N - 1) * 4607) + 13821) 0 (3 * ((N - 1) * nGrind))
      (3 * ((N - 1) * 624) + 624) (3 * ((N - 1) * 4607) + 9214) +
    2 * εAdG R pS 9 q3 (4 * ((N - 1) * 624) + q5 + 936) (4 * ((N - 1) * 4607) + qE + 13821) (2 * 0)
      (2 * (3 * ((N - 1) * nGrind))) (2 * (3 * ((N - 1) * 624)) + 1560)
      (2 * (3 * ((N - 1) * 4607)) + 23035) +
    6 * ((0 : ℕ) / 2 ^ 128) +
    4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (2 * (3 * ((N - 1) * 624)) + 1560)
      (2 * (3 * ((N - 1) * 4607)) + 23035)) +
    6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide

/-- **Theorem 2 with `N` challenge pairs, for every type of cipher rows** (`ZKRow R`, `ZKPRow R`;
SHAKE as the base record): any two worlds `w, w' : Fin N → Bool × Bool` differ by at most `N`
times the two-session bound for the hop that runs the other `N − 1` pairs itself (a hybrid over
the pairs; each step is `unlinkabilityRA_lean_numG` for the pair that changes, averaged over the
other pairs' tapes). Hiding is assumed for the explicit reductions of every hop. -/
theorem unlinkabilityP_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryP R N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR R) (realGameP A w) - pr ((Fin N → PT) × ShR R) (realGameP A w')| ≤
      N * εPairR R N q3 q5 qE εhide := by
  refine realGameP_hybrid A _ (fun k c v b₁ b₂ b₁' b₂' => ?_) w w'
  have hb := unlinkabilityRA_lean_numG (A.hop k c v) (A.hop_gBudget k c v hA) (A.hop_iBudget k c v)
    (hhide k c v) b₁ b₂ b₁' b₂'
  rw [card_ne] at hb
  exact hb

/-- **Theorem 2 with `N` challenge pairs** (function rows). -/
theorem unlinkabilityP_lean_num (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w) -
        pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w')| ≤
      N * εPairR (Blk → Blk) N q3 q5 qE εhide :=
  unlinkabilityP_lean_numG A hA hhide w w'

/-- **Theorem 2 with `N` challenge pairs and AES as uniformly random permutations.** -/
theorem unlinkabilityP_lean_num_perm (A : AdversaryP (Equiv.Perm Blk) N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR (Equiv.Perm Blk)) (realGameP A w) -
        pr ((Fin N → PT) × ShR (Equiv.Perm Blk)) (realGameP A w')| ≤
      N * εPairR (Equiv.Perm Blk) N q3 q5 qE εhide :=
  unlinkabilityP_lean_numG A hA hhide w w'

/-- **One step in numbers** (function rows): `εPairR ≤ N·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
2·εhide` for `N ≥ 1`. -/
lemma εPairR_le (N q3 q5 qE : ℕ) (εhide : ℝ) (hN : 1 ≤ N) :
    εPairR (Blk → Blk) N q3 q5 qE εhide ≤
      (N : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  set m := N - 1 with hm_def
  have hNm : (N : ℝ) = m + 1 := by
    have : N = m + 1 := by omega
    rw [this]; push_cast; ring
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 34 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : (m : ℝ) * (nGrind : ℝ) / 2 ^ 1024 ≤ m / (4 * 2 ^ 128) := by
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h34 : (2 : ℝ) ^ 32 * 4 = 2 ^ 34 := by norm_num
    calc (m : ℝ) * 2 ^ 32 * (4 * 2 ^ 128) = ((m : ℝ) * 2 ^ 128) * (2 ^ 32 * 4) := by ring
      _ = ((m : ℝ) * 2 ^ 128) * 2 ^ 34 := by rw [h34]
      _ ≤ ((m : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hp.le)
      _ = (m : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 34 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  unfold εPairR
  show 4 * εRO _ _ _ + 2 * εAd _ _ _ _ _ _ _ _ + 2 * εAd _ _ _ _ _ _ _ _ + _ +
    4 * (_ + εROP _ _ _ _ _) + _ + _ + _ ≤ _
  unfold εAd h23Term
  generalize (2 : ℝ) ^ 1024 = κ at hK hG
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e4 : ∀ x : ℝ, x / (4 * 2 ^ 128) = x / 4 / 2 ^ 128 := fun x => by rw [div_div]
  rw [e4] at hG
  have hG1 : ((3 * (m * nGrind) : ℕ) : ℝ) / κ = 3 * ((m : ℝ) * (nGrind : ℝ) / κ) := by
    push_cast; ring
  have hG2 : ((2 * (3 * (m * nGrind)) : ℕ) : ℝ) / κ = 6 * ((m : ℝ) * (nGrind : ℝ) / κ) := by
    push_cast; ring
  split_ifs with h1 h2 h2
  · unfold εROP εRO
    push_cast
    rw [e, hNm]
    linarith
  · exfalso; omega
  · exfalso; omega
  · unfold εROP εRO
    rw [hG1, hG2]
    push_cast
    rw [e, hNm]
    linarith

/-- **`N` pairs in numbers**: `≤ N·(N·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`. -/
theorem unlinkabilityP_lean_le (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w) -
        pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w')| ≤
      N * ((N : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0
    have : w = w' := funext fun j => j.elim0
    subst this
    simp
  exact (unlinkabilityP_lean_num A hA hhide w w').trans
    (mul_le_mul_of_nonneg_left (εPairR_le N q3 q5 qE εhide hN0) (Nat.cast_nonneg _))

/-- **`2²⁰` Clients in `N` pairs**: `≤ 2⁻⁶³` plus `N` times the guess's budget terms and
`2·εhide`. -/
theorem unlinkabilityP_lean_2pow20 (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) (hN : 2 * N ≤ 2 ^ 20) :
    |pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w) -
        pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w')| ≤
      1 / 2 ^ 63 + N * (8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  have h := unlinkabilityP_lean_le A hA hhide w w'
  have h1 : (N : ℝ) ≤ 2 ^ 19 := by
    have : N ≤ 2 ^ 19 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((N : ℕ) / 2 ^ 101) ≤ 1 / 2 ^ 63 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [add_assoc, mul_add] at h
  linarith

/-- **`2³²` Clients in `N` pairs**: `≤ 2⁻³⁹` plus `N` times the guess's budget terms and
`2·εhide`. -/
theorem unlinkabilityP_lean_2pow32 (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v b₁ b₂ K, hidingAdv (A.hop k c v).ctx
      (reductionRA (A.hop k c v) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (w w' : Fin N → Bool × Bool) (hN : 2 * N ≤ 2 ^ 32) :
    |pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w) -
        pr ((Fin N → PT) × ShR (Blk → Blk)) (realGameP A w')| ≤
      1 / 2 ^ 39 + N * (8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  have h := unlinkabilityP_lean_le A hA hhide w w'
  have h1 : (N : ℝ) ≤ 2 ^ 31 := by
    have : N ≤ 2 ^ 31 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((N : ℕ) / 2 ^ 101) ≤ 1 / 2 ^ 39 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [add_assoc, mul_add] at h
  linarith

end PairsBound

end VoleMole.Privacy.Ratatouille
