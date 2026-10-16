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

end VoleMole.Privacy.Ratatouille
