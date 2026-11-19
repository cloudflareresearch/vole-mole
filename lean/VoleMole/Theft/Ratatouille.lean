import VoleMole.Theft.Basic
import VoleMole.Privacy.Ratatouille

/-!
# Ratatouille: no theft (N2a, `security/ratatouille.md` §5, Theorem 3)

**The game.** An honest Client with secret coins `ω = ((nf, r), (nf', r'))` runs the executable
spec (`Spec/Ratatouille.lean`, through `Privacy/Ratatouille.lean`'s `issueOf` and `spendOf`, the
spec functions at the output of the seed expansion): it requests a token worth `T_init` under
`ctx`, finalizes the Issuer's response (`finalize_issue`), and spends `d` from it. The adversary
(`Thief`) chooses the Issuer's key `pk`, `ctx`, `T_init`, the issuance response and `d`, from
the messages it sees (not from the tables: the zero-knowledge theorems are for statements fixed
before the tables, as in `Privacy/RatatouilleRO.lean`). It may therefore be the Issuer itself. It
then reads the random tables (the proofs' private `H₃` slices `g₁`, `g₂` and the shared tables `s`)
and outputs an Issuer operation (`Op`): an issuance request or a spend request, with its own
context. The proofs are made by a prover and checked by a verifier on the tables (abstract here;
`ProverI`, `ProverS` of `Privacy/RatatouilleRO.lean` for the Lean prover).

**The event** (`Bad`): the operation is accepted by the verifier with the key `pk` (`AccOp`), its
statement differs from the honest Client's statements (`FreshOp`: weak non-malleability; a
verbatim copy is excluded, since it is allowed, F2), and the witness the extractor `ext` reads off
the run is **not a witness** (`RelOp` fails) **or opens one of the honest Client's commitments**
`c = Com(nf, ctx, T_init, r)`, `c' = Com(nf', ctx, t', r')` (`OpensOp`: an issuance's opening, a
spend's parent opening or change opening). Off this event every accepted fresh operation comes
with a witness that spends a state the honest Client never held (`not_theft`): a spend that
consumes the honest nullifier `nf` (nullifier squatting, which the note's N2a misses; see the
docs) has an extracted parent commitment different from `c` and `c'`, with a valid signature, so
it spends a separately certified state.

**`noTheft`**:

    Pr[Bad] ≤ ε_I + ε_S + δ_S + ε_SE + Adv^ow(B),

* `ε_I`, `ε_S`: zero knowledge of the issuance and spend proof systems (`ZeroKnowledgeRO`), at the
  two hops' distinguishers (`hAI`, `hAS`: they are admissible);
* `δ_S` (`deltaS`): the real spend proof reads the tables differently with and without the
  simulated issuance's programming (as `δS₁` of `Privacy/RatatouilleRO.lean`);
* `ε_SE`: weak simulation-extractability (`Theft.WeakSE2`), **a hypothesis** (L8 on paper);
* `Adv^ow(B)` (`owAdv`): the explicit inverter `inverter` finds an opening of `c` or `c'` from
  `nf` and the commitment functions alone (`sim_opens_le`: in the simulated world the openings
  enter only through the commitments). With `KP800` an ideal permutation this is
  `≤ q_K·2⁻¹²⁷` (the note's §2.2 argument, on paper).

The note's bound for Theorem 3 also lists `ε_ext + ε_bind^K + Adv^{ompi}`; they are not needed
(`docs/security/ratatouille.md` §5).
-/

open Finset

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {Z : Sizes} {G S : Type}

/-- The honest Client's secret coins: `(nf, r)` of its issuance, `(nf', r')` of its spend. -/
abbrev Sec := (Coins 24 × Coins 16) × (Coins 24 × Coins 16)

/-- **The adversary**: the Issuer's key, context and `T_init`, the issuance response and the
amount from the issuance request it saw, and a last stage that reads the tables and outputs an
Issuer operation. -/
structure Thief (Z : Sizes) (G S : Type) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respond : Except Error (IssueRequest Z) → Preimage
  d : Except Error (IssueRequest Z) → Credits
  out : Except Error (IssueRequest Z) → Except Error (SpendRequest Z) → G → G → S → Op Z

variable (A : Thief Z G S)

/-! ## The Client, in public form -/

/-- The issuance statement, for the commitment function `K₁ = (t ↦ Com(nf, ctx, t, r))`; none if
`T_init = 0` (no proof is made). -/
def xIo (K₁ : Credits → Commitment) : Option IssueInstance :=
  if A.tInit = 0 then none else some ⟨K₁ A.tInit, A.tInit, A.ctx⟩

/-- **The issuance request** from the proof (`issueOf`, `issue_request_with_seed`). -/
def reqI (K₁ : Credits → Commitment) (π : Option (IssueProof Z)) : Except Error (IssueRequest Z) :=
  if A.tInit = 0 then .error .invalidArgument else
  match π with
  | none => .error .runtime
  | some pf => .ok (issueReqBytes (K₁ A.tInit) pf)

/-- The change value `t' = T_init − d` the Client computes (`0` if it refuses). -/
def tNext (req : Except Error (IssueRequest Z)) : Credits := (clientCheck A.tInit 0 (A.d req)).getD 0

/-- **The spend statement**, if the Client spends: it got a valid token (`finalize_issue`) and
affords `d`. -/
def xS (nf : Nullifier) (K₁ K₂ : Credits → Commitment) (req : Except Error (IssueRequest Z)) :
    Option SpendInstance :=
  match req with
  | .error _ => none
  | .ok _ =>
    if uovEval A.pk (A.respond req) = tag (K₁ A.tInit) 0 then
      match clientCheck A.tInit 0 (A.d req) with
      | none => none
      | some t' => some ⟨A.pk, nf, A.d req, K₂ t', A.ctx⟩
    else none

/-- **The spend request** from the proof (`spendOf`, `spend_request_with_seed`). -/
def reqS (nf : Nullifier) (K₁ K₂ : Credits → Commitment) (req : Except Error (IssueRequest Z))
    (π : Option (SpendProof Z)) : Except Error (SpendRequest Z) :=
  match req with
  | .error _ => .error .logic
  | .ok _ =>
    if uovEval A.pk (A.respond req) = tag (K₁ A.tInit) 0 then
      match clientCheck A.tInit 0 (A.d req) with
      | none => .error .invalidArgument
      | some t' =>
        match π with
        | none => .error .runtime
        | some pf => .ok (SpendReq.toBytes ⟨nf, A.d req, K₂ t', pf⟩)
    else .error .logic

/-! ## The Client, from the spec -/

/-- The commitment function `t ↦ Com(nf, ctx, t, r)`. -/
def comK (nf : Nullifier) (r : Opening) : Credits → Commitment := fun t => com nf A.ctx t r

/-- The honest Client's issued commitment function and change commitment function. -/
def K₁ (ω : Sec) : Credits → Commitment := comK A (vec ω.1.1) (vec ω.1.2)
def K₂ (ω : Sec) : Credits → Commitment := comK A (vec ω.2.1) (vec ω.2.2)

/-- The issuance prover with the tables. -/
def primT (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
    (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z)) (g : G) (s : S) :
    Prim Z Empty :=
  ⟨fun e => e.elim, fun e => e.elim, fun x w ρ => PI x w ρ g s, fun _ _ => true,
    fun x w ρ => PS x w ρ g s, fun _ _ => true⟩

/-- The Client's token after `finalize_issue` on the adversary's response. -/
def tokS (ω : Sec) (req : Except Error (IssueRequest Z)) : Option TokenS :=
  match req with
  | .error _ => none
  | .ok _ =>
    match (finalizeIssue A.pk (some ⟨vec ω.1.1, vec ω.1.2, A.tInit,
        com (vec ω.1.1) A.ctx A.tInit (vec ω.1.2)⟩) (A.respond req)).2 with
    | .ok o => o
    | .error _ => none

variable (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
  (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))

/-- **The real issuance**: `issue_request_with_seed` at `(nf, r, ρ)`, the prover on the tables. -/
def specI (ω : Sec) (ρ : Coins 16) (g : G) (s : S) : Except Error (IssueRequest Z) :=
  (issueOf (primT PI PS g s) A.tInit A.ctx (vec ω.1.1) (vec ω.1.2) (vec ρ)).map Prod.snd

/-- **The real spend**: `spend_request_with_seed` at `(nf', r', ρ)` from the Client's token. -/
def specS (ω : Sec) (req : Except Error (IssueRequest Z)) (ρ : Coins 16) (g : G) (s : S) :
    Except Error (SpendRequest Z) :=
  ((spendOf (primT PI PS g s) A.pk (tokS A ω req) (A.d req) A.ctx (vec ω.2.1) (vec ω.2.2)
    (vec ρ)).2).map Prod.snd

/-- The issuance statement and witness of the Client. -/
def xwI (ω : Sec) : Option (IssueInstance × IssueWitness) :=
  if A.tInit = 0 then none else
    some (⟨com (vec ω.1.1) A.ctx A.tInit (vec ω.1.2), A.tInit, A.ctx⟩, ⟨vec ω.1.1, vec ω.1.2⟩)

/-- The spend statement and witness of the Client. -/
def xwS (ω : Sec) (req : Except Error (IssueRequest Z)) : Option (SpendInstance × SpendWitness) :=
  match req with
  | .error _ => none
  | .ok _ =>
    if uovEval A.pk (A.respond req) = tag (K₁ A ω A.tInit) 0 then
      match clientCheck A.tInit 0 (A.d req) with
      | none => none
      | some t' => some (⟨A.pk, vec ω.1.1, A.d req, K₂ A ω t', A.ctx⟩,
          ⟨A.tInit, vec ω.1.2, 0, A.respond req, vec ω.2.1, t', vec ω.2.2⟩)
    else none

/-- The provers with uniform randomness. -/
abbrev PI' (x : IssueInstance) (w : IssueWitness) (ρ : Coins 16) (g : G) (s : S) :
    Option (IssueProof Z) := PI x w (vec ρ) g s
abbrev PS' (x : SpendInstance) (w : SpendWitness) (ρ : Coins 16) (g : G) (s : S) :
    Option (SpendProof Z) := PS x w (vec ρ) g s

theorem xwI_fst (ω : Sec) : (xwI A ω).map Prod.fst = xIo A (K₁ A ω) := by
  unfold xwI xIo; split_ifs <;> rfl

theorem xwS_fst (ω : Sec) (req : Except Error (IssueRequest Z)) :
    (xwS A ω req).map Prod.fst = xS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req := by
  unfold xwS xS
  rcases req with e | q
  · rfl
  · simp only
    split_ifs
    · cases clientCheck A.tInit 0 (A.d (.ok q)) <;> rfl
    · rfl

theorem xwI_rel (ω : Sec) : ∀ x w, xwI A ω = some (x, w) → IssueRel x w := by
  intro x w h
  unfold xwI at h
  split_ifs at h
  cases h
  rfl

theorem xwS_rel (ω : Sec) (req : Except Error (IssueRequest Z)) :
    ∀ x w, xwS A ω req = some (x, w) → SpendRel x w := by
  intro x w h
  unfold xwS at h
  rcases req with e | q
  · cases h
  · simp only at h
    split_ifs at h with hv
    cases hc : clientCheck A.tInit 0 (A.d (.ok q)) with
    | none => rw [hc] at h; cases h
    | some t' =>
      rw [hc] at h
      cases h
      refine ⟨hv, rfl, ?_⟩
      have := clientCheck_eq hc
      simp only [UInt64.toNat_zero, add_zero] at this ⊢
      omega

/-- **The spec's issuance is `reqI` of the proof.** -/
theorem specI_eq (ω : Sec) (ρ : Coins 16) (g : G) (s : S) :
    specI A PI PS ω ρ g s = reqI A (K₁ A ω) (proveO (PI' PI) (xwI A ω) ρ g s) := by
  unfold specI reqI xwI issueOf
  by_cases h : A.tInit = 0
  · simp [h, Except.map]
  · simp only [h, ite_false, proveO, PI', primT]
    cases PI _ _ (vec ρ) g s <;> rfl

/-- **The spec's spend is `reqS` of the proof.** -/
theorem specS_eq (ω : Sec) (req : Except Error (IssueRequest Z)) (ρ : Coins 16) (g : G) (s : S) :
    specS A PI PS ω req ρ g s =
      reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req (proveO (PS' PS) (xwS A ω req) ρ g s) := by
  unfold specS reqS xwS tokS
  simp only [K₁, K₂, comK]
  rcases req with e | q
  · rfl
  · simp only [finalizeIssue]
    by_cases hv : uovEval A.pk (A.respond (.ok q)) =
        tag (com (vec ω.1.1) A.ctx A.tInit (vec ω.1.2)) 0
    · simp only [hv, ite_true]
      unfold spendOf
      have hval : TokenS.Valid A.pk A.ctx ⟨vec ω.1.1, A.tInit, vec ω.1.2, 0, A.respond (.ok q)⟩ :=
        hv
      simp only [hval, not_true_eq_false, ite_false]
      cases hc : clientCheck A.tInit 0 (A.d (.ok q)) with
      | none => rfl
      | some t' =>
        simp only [proveO, PS', primT]
        cases PS _ _ (vec ρ) g s <;> rfl
    · simp only [hv, ite_false]
      rfl

/-! ## The event -/

/-- Statement and proof of the Client's issuance request. -/
def stI (req : Except Error (IssueRequest Z)) : Option (IssueInstance × IssueProof Z) :=
  match req with
  | .ok q => some (⟨issueReqC q, A.tInit, A.ctx⟩, issueReqProof q)
  | .error _ => none

/-- Statement and proof of the Client's spend request. -/
def stS (req : Except Error (SpendRequest Z)) : Option (SpendInstance × SpendProof Z) :=
  match req with
  | .ok q => some (⟨A.pk, (SpendReq.parse q).nf, (SpendReq.parse q).d, (SpendReq.parse q).cNext,
      A.ctx⟩, (SpendReq.parse q).proof)
  | .error _ => none

/-- The issuance statement of an operation. -/
def opXI (q : IssueRequest Z) (t : Credits) (c : Context) : IssueInstance := ⟨issueReqC q, t, c⟩

/-- The spend statement of an operation, for the key `pk`. -/
def opXS (q : SpendRequest Z) (c : Context) : SpendInstance :=
  ⟨A.pk, (SpendReq.parse q).nf, (SpendReq.parse q).d, (SpendReq.parse q).cNext, c⟩

/-- **The operation is accepted** by the verifiers with the key `pk`, on the tables `s`. -/
def AccOp (verI : IssueInstance → IssueProof Z → S → Bool)
    (verS : SpendInstance → SpendProof Z → S → Bool) (op : Op Z) (s : S) : Prop :=
  match op with
  | .issue q t c => verI (opXI q t c) (issueReqProof q) s = true
  | .spend q c _ => verS (opXS A q c) (SpendReq.parse q).proof s = true

/-- **Its statement is fresh**: it differs from the statement of the Client's request of the same
relation, if the Client made one (weak non-malleability). -/
def FreshOp (p₁ : Option (IssueInstance × IssueProof Z)) (p₂ : Option (SpendInstance × SpendProof Z))
    (op : Op Z) : Prop :=
  match op with
  | .issue q t c => ∀ y, p₁ = some y → opXI q t c ≠ y.1
  | .spend q c _ => ∀ y, p₂ = some y → opXS A q c ≠ y.1

/-- The extracted witnesses (one per relation; the operation's kind picks one). -/
abbrev Wit := IssueWitness × SpendWitness

/-- **The extracted witness is a witness** for the operation's statement. -/
def RelOp (op : Op Z) (w : Wit) : Prop :=
  match op with
  | .issue q t c => IssueRel (opXI q t c) w.1
  | .spend q c _ => SpendRel (opXS A q c) w.2

/-- A commitment opening `(nf, ctx, t, r)`. -/
abbrev Open4 := Nullifier × Context × Credits × Opening

/-- Its commitment. -/
def comOf (o : Open4) : Commitment := com o.1 o.2.1 o.2.2.1 o.2.2.2

/-- **The openings a witness carries**: an issuance's `(nf, ctx, T_init, r)`; a spend's parent
`(nf, ctx, t, r)` and change `(nf', ctx, t', r')`. -/
def opensOf : Op Z → Wit → List Open4
  | .issue _ t c, w => [(w.1.nf, c, t, w.1.r)]
  | .spend q c _, w => [((SpendReq.parse q).nf, c, w.2.t, w.2.r), (w.2.nf', c, w.2.t', w.2.r')]

/-- **The witness opens one of the commitments `h₁`, `h₂`.** -/
def OpensOp (h₁ h₂ : Commitment) (op : Op Z) (w : Wit) : Prop :=
  ∃ o ∈ opensOf op w, comOf o = h₁ ∨ comOf o = h₂

/-- **The extractor**: from the Client's statements and proofs, the adversary's last stage (a
function of the tables) and the tables, a witness. -/
abbrev Ext (Z : Sizes) (G S : Type) :=
  Option (IssueInstance × IssueProof Z) → Option (SpendInstance × SpendProof Z) →
    (G → G → S → Op Z) → G → G → S → Wit

variable (verI : IssueInstance → IssueProof Z → S → Bool)
  (verS : SpendInstance → SpendProof Z → S → Bool) (ext : Ext Z G S)

/-- The four parts of the event, as functions of the run. -/
def accE (_ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  AccOp A verI verS (A.out o₁ o₂ g₁ g₂ s) s

def freshE (_ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  FreshOp A (stI A o₁) (stS A o₂) (A.out o₁ o₂ g₁ g₂ s)

def relE (_ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  RelOp A (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) g₁ g₂ s)

def opensE (ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  OpensOp (K₁ A ω A.tInit) (K₂ A ω (tNext A o₁)) (A.out o₁ o₂ g₁ g₂ s)
    (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) g₁ g₂ s)

/-- **The bad event**: an accepted operation with a fresh statement whose extracted witness is not
a witness or opens one of the Client's commitments. -/
def Bad (ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
    (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ opensE A ext ω o₁ o₂ g₁ g₂ s)

/-- **The real game** (`N2a`): the Client's coins, the spend's randomness and `H₃` slice, the
issuance's, and the shared tables, all uniform; the Client runs the spec with the real provers. -/
def theftReal (z : (Sec × (Coins 16 × G)) × ((Coins 16 × G) × S)) : Prop :=
  Bad A verI verS ext z.1.1 (specI A PI PS z.1.1 z.2.1.1 z.2.1.2 z.2.2)
    (specS A PI PS z.1.1 (specI A PI PS z.1.1 z.2.1.1 z.2.1.2 z.2.2) z.1.2.1 z.1.2.2 z.2.2)
    z.2.1.2 z.1.2.2 z.2.2

/-- **Off the bad event there is no theft.** If the operation is accepted and fresh and the bad
event fails, the extracted witness is a witness that opens neither of the Client's commitments.
For a spend: its parent `Com(nf*, ctx*, t, r)` is a commitment other than `c` and `c'` with a
valid signature on `Tag(·, x)` (V1), so the spend consumes a separately certified state, even if
`nf* = nf` (nullifier squatting), and its change commitment is not `c` or `c'`; for an issuance,
its commitment is not `c` or `c'`. -/
theorem not_theft (ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) (hA : accE A verI verS ω o₁ o₂ g₁ g₂ s) (hF : freshE A ω o₁ o₂ g₁ g₂ s)
    (hB : ¬ Bad A verI verS ext ω o₁ o₂ g₁ g₂ s) :
    relE A ext ω o₁ o₂ g₁ g₂ s ∧ ¬ opensE A ext ω o₁ o₂ g₁ g₂ s := by
  unfold Bad at hB
  tauto

/-- For a spend: the extracted parent differs from both honest commitments, and so does the new
commitment of the request. -/
theorem not_theft_spend (ω : Sec) (o₁ : Except Error (IssueRequest Z))
    (o₂ : Except Error (SpendRequest Z)) (g₁ g₂ : G) (s : S) (q : SpendRequest Z) (c : Context)
    (x : Credits) (hq : A.out o₁ o₂ g₁ g₂ s = .spend q c x)
    (hA : accE A verI verS ω o₁ o₂ g₁ g₂ s) (hF : freshE A ω o₁ o₂ g₁ g₂ s)
    (hB : ¬ Bad A verI verS ext ω o₁ o₂ g₁ g₂ s) :
    let w := (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) g₁ g₂ s).2
    SpendRel (opXS A q c) w ∧
      com (SpendReq.parse q).nf c w.t w.r ≠ K₁ A ω A.tInit ∧
      com (SpendReq.parse q).nf c w.t w.r ≠ K₂ A ω (tNext A o₁) ∧
      (SpendReq.parse q).cNext ≠ K₁ A ω A.tInit ∧ (SpendReq.parse q).cNext ≠ K₂ A ω (tNext A o₁) := by
  obtain ⟨hR, hO⟩ := not_theft A verI verS ext ω o₁ o₂ g₁ g₂ s hA hF hB
  simp only [relE, opensE, hq, RelOp, OpensOp, opensOf, List.mem_cons,
    List.not_mem_nil, or_false, comOf] at hR hO
  refine ⟨hR, fun h => hO ⟨_, Or.inl rfl, Or.inl h⟩, fun h => hO ⟨_, Or.inl rfl, Or.inr h⟩,
    fun h => hO ⟨_, Or.inr rfl, Or.inl ?_⟩, fun h => hO ⟨_, Or.inr rfl, Or.inr ?_⟩⟩
  · rw [← h]; exact hR.2.1.symm
  · rw [← h]; exact hR.2.1.symm

/-! ## The simulated world and the reductions -/

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → S → S) (simS : SpendInstance → CS → Option (SpendProof Z))
  (progS : SpendInstance → CS → S → S)

/-- The simulated issuance. -/
def simIss (ω : Sec) (c : CI) : Except Error (IssueRequest Z) :=
  reqI A (K₁ A ω) (simO simI (xIo A (K₁ A ω)) c)

/-- Its programming (none if no proof is made). -/
def pgI (ω : Sec) (c : CI) (s : S) : S := progO progI (xIo A (K₁ A ω)) c s

/-- The simulated spend. -/
def simSp (ω : Sec) (req : Except Error (IssueRequest Z)) (c : CS) : Except Error (SpendRequest Z) :=
  reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req (simO simS (xS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req) c)

/-- Its programming (none if the Client does not spend). -/
def pgS (ω : Sec) (req : Except Error (IssueRequest Z)) (c : CS) (s : S) : S :=
  progO progS (xS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req) c s

/-- **The simulated issuance is the spec's `issueSim`** (`Privacy/Ratatouille.lean`). -/
theorem simIss_spec (ω : Sec) (c : CI) :
    simIss A simI ω c = (issueSim simI A.tInit A.ctx (vec ω.1.1) (vec ω.1.2) c).map Prod.snd := by
  unfold simIss reqI issueSim xIo simO
  simp only [K₁, comK]
  by_cases h : A.tInit = 0
  · simp [h, Except.map]
  · simp only [h, ite_false]
    cases simI _ c <;> rfl

/-- **The simulated spend is the spec's `spendSim`** from the Client's token. -/
theorem simSp_spec (ω : Sec) (req : Except Error (IssueRequest Z)) (c : CS) :
    simSp A simS ω req c = match tokS A ω req with
      | none => .error .logic
      | some τ => (spendSim simS A.pk τ (A.d req) A.ctx (vec ω.2.1) (vec ω.2.2) c).map Prod.snd := by
  unfold simSp reqS xS tokS simO
  simp only [K₁, K₂, comK]
  rcases req with e | q
  · rfl
  · simp only [finalizeIssue]
    by_cases hv : uovEval A.pk (A.respond (.ok q)) =
        tag (com (vec ω.1.1) A.ctx A.tInit (vec ω.1.2)) 0
    · simp only [hv, ite_true]
      unfold spendSim
      have hval : TokenS.Valid A.pk A.ctx ⟨vec ω.1.1, A.tInit, vec ω.1.2, 0, A.respond (.ok q)⟩ :=
        hv
      simp only [hval, not_true_eq_false, ite_false]
      cases hc : clientCheck A.tInit 0 (A.d (.ok q)) with
      | none => rfl
      | some t' =>
        simp only
        cases simS _ c <;> rfl
    · simp only [hv, ite_false]

/-- **The simulated game**: both proofs simulated, the adversary's last stage on the tables both
simulations programmed. -/
def theftSim (z : (Sec × (CI × G)) × ((CS × G) × S)) : Prop :=
  simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS) (Bad A verI verS ext) z

/-- **The collision term** `δ_S`: the real spend proof, after the simulated issuance, reads the
tables differently with and without the issuance's programming. -/
def deltaS (z : (Sec × (CI × G)) × ((Coins 16 × G) × S)) : Prop :=
  deltaG (simIss A simI) (pgI A progI) (specS A PI PS) z

/-- **The first hop's distinguisher**: the rest of the game, with the real spend, as a function of
the issuance proof (`ω`, the spend's randomness and slice fixed). -/
def distI (ω : Sec) (r₂ : Coins 16) (g₂ : G) (p : Option (IssueProof Z)) (g : G) (u : S) : Prop :=
  D₁ (specS A PI PS) (Bad A verI verS ext) ω r₂ g₂ (reqI A (K₁ A ω) p) g u

/-- **The second hop's distinguisher**: the event as a function of the spend proof, on the tables
the simulated issuance programs (`ω`, its coins and slice fixed). -/
def distS (ω : Sec) (c₁ : CI) (g₁ : G) (p : Option (SpendProof Z)) (g : G) (u : S) : Prop :=
  D₂ (simIss A simI) (pgI A progI) (Bad A verI verS ext) ω c₁ g₁
    (reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (simIss A simI ω c₁) p) g u

variable [Fintype CI] [Fintype CS] [Fintype G] [Fintype S]

section OW

/-- **One-wayness of `Com` in the opening, for the Client's two commitments.** The inverter `B`
sees the token's nullifier `nf`, the commitment functions `t ↦ Com(nf, ctx, t, r)` and
`t ↦ Com(nf', ctx, t, r')` (it may evaluate them at credit values of its choice; `r`, `nf'`, `r'`
stay hidden) and auxiliary coins `β`. It wins with a choice `b` of the commitment, a credit value
`t` and an opening of `Com(·, ctx, t, ·)` (any opening: a different one is a collision). -/
noncomputable def owAdv {β : Type} [Fintype β] (ctx : Context)
    (B : Nullifier → (Credits → Commitment) → (Credits → Commitment) → β → Bool × Credits × Open4) :
    ℝ :=
  pr (Sec × β) fun z =>
    comOf (B (vec z.1.1.1) (fun t => com (vec z.1.1.1) ctx t (vec z.1.1.2))
        (fun t => com (vec z.1.2.1) ctx t (vec z.1.2.2)) z.2).2.2 =
      if (B (vec z.1.1.1) (fun t => com (vec z.1.1.1) ctx t (vec z.1.1.2))
          (fun t => com (vec z.1.2.1) ctx t (vec z.1.2.2)) z.2).1
      then com (vec z.1.2.1) ctx (B (vec z.1.1.1) (fun t => com (vec z.1.1.1) ctx t (vec z.1.1.2))
          (fun t => com (vec z.1.2.1) ctx t (vec z.1.2.2)) z.2).2.1 (vec z.1.2.2)
      else com (vec z.1.1.1) ctx (B (vec z.1.1.1) (fun t => com (vec z.1.1.1) ctx t (vec z.1.1.2))
          (fun t => com (vec z.1.2.1) ctx t (vec z.1.2.2)) z.2).2.1 (vec z.1.1.2)

/-- A default opening. -/
def open0 : Open4 := (Vector.replicate 24 0, Vector.replicate 16 0, 0, Vector.replicate 16 0)

/-- The first opening in a list that opens `h₁` (at `t₁`) or `h₂` (at `t₂`). -/
def pick (h₁ h₂ : Commitment) (t₁ t₂ : Credits) : List Open4 → Bool × Credits × Open4
  | [] => (false, t₁, open0)
  | o :: os => if comOf o = h₁ then (false, t₁, o) else if comOf o = h₂ then (true, t₂, o)
      else pick h₁ h₂ t₁ t₂ os

theorem pick_spec (h₁ h₂ : Commitment) (t₁ t₂ : Credits) (l : List Open4)
    (h : ∃ o ∈ l, comOf o = h₁ ∨ comOf o = h₂) :
    (comOf (pick h₁ h₂ t₁ t₂ l).2.2 = if (pick h₁ h₂ t₁ t₂ l).1 then h₂ else h₁) ∧
      (pick h₁ h₂ t₁ t₂ l).2.1 = if (pick h₁ h₂ t₁ t₂ l).1 then t₂ else t₁ := by
  induction l with
  | nil => obtain ⟨o, ho, _⟩ := h; cases ho
  | cons a l ih =>
    simp only [pick]
    by_cases ha : comOf a = h₁
    · simp [ha]
    · by_cases hb : comOf a = h₂
      · have hne : h₂ ≠ h₁ := fun e => ha (hb.trans e)
        simp [hb, hne]
      · simp only [ha, hb, ite_false]
        apply ih
        obtain ⟨o, ho, ho'⟩ := h
        rcases List.mem_cons.1 ho with rfl | ho
        · exact absurd ho' (by tauto)
        · exact ⟨o, ho, ho'⟩

/-- `pick` finds an opening of `L₁ t₁` or `L₂ t₂` if the list has one. -/
theorem pick_win (L₁ L₂ : Credits → Commitment) (t₁ t₂ : Credits) (l : List Open4)
    (h : ∃ o ∈ l, comOf o = L₁ t₁ ∨ comOf o = L₂ t₂) :
    comOf (pick (L₁ t₁) (L₂ t₂) t₁ t₂ l).2.2 =
      if (pick (L₁ t₁) (L₂ t₂) t₁ t₂ l).1 then L₂ (pick (L₁ t₁) (L₂ t₂) t₁ t₂ l).2.1
      else L₁ (pick (L₁ t₁) (L₂ t₂) t₁ t₂ l).2.1 := by
  obtain ⟨h1, h2⟩ := pick_spec _ _ t₁ t₂ l h
  rw [h1, h2]
  split_ifs <;> rfl

/-- **The inverter**: it runs the simulated world from `nf` and the commitment functions alone
(the Client's openings enter it nowhere else), the adversary, and the extractor, and outputs
the first extracted opening of `c = K₁(T_init)` or `c' = K₂(t')`. -/
def inverter (nf : Nullifier) (L₁ L₂ : Credits → Commitment) (b : (CI × G) × ((CS × G) × S)) :
    Bool × Credits × Open4 :=
  let o₁ := reqI A L₁ (simO simI (xIo A L₁) b.1.1)
  let x₂ := xS A nf L₁ L₂ o₁
  let o₂ := reqS A nf L₁ L₂ o₁ (simO simS x₂ b.2.1.1)
  let s := progO progI (xIo A L₁) b.1.1 (progO progS x₂ b.2.1.1 b.2.2)
  pick (L₁ A.tInit) (L₂ (tNext A o₁)) A.tInit (tNext A o₁)
    (opensOf (A.out o₁ o₂ b.1.2 b.2.1.2 s) (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) b.1.2 b.2.1.2 s))

/-- **One-wayness step**: in the simulated world, the extracted witness opens a Client commitment
with probability at most the inverter's advantage. -/
theorem sim_opens_le :
    pr ((Sec × (CI × G)) × ((CS × G) × S))
        (simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS) (opensE A ext)) ≤
      owAdv A.ctx (inverter A ext simI progI simS progS) := by
  unfold owAdv
  rw [← pr_equiv (Equiv.prodAssoc Sec (CI × G) ((CS × G) × S)).symm]
  refine pr_mono fun z hz => ?_
  exact pick_win _ _ _ _ _ hz

end OW

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
def seEv (ω : Sec) (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z))
    (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧ ¬ relE A ext ω o₁ o₂ g₁ g₂ s

omit [Fintype G] [Fintype S] in
theorem stI_reqI (L₁ : Credits → Commitment) (π : Option (IssueProof Z)) :
    stI A (reqI A L₁ π) = pairO (xIo A L₁) π := by
  unfold stI reqI xIo pairO
  by_cases h : A.tInit = 0
  · simp [h]
  · simp only [h, ite_false]
    cases π with
    | none => rfl
    | some pf => simp [issueReqC_mk, issueReqProof_mk]

omit [Fintype G] [Fintype S] in
theorem stS_reqS (nf : Nullifier) (L₁ L₂ : Credits → Commitment) (req : Except Error (IssueRequest Z))
    (π : Option (SpendProof Z)) :
    stS A (reqS A nf L₁ L₂ req π) = pairO (xS A nf L₁ L₂ req) π := by
  unfold stS reqS xS pairO
  rcases req with e | q
  · rfl
  · simp only
    split_ifs
    · cases clientCheck A.tInit 0 (A.d (.ok q)) with
      | none => rfl
      | some t' =>
        cases π with
        | none => rfl
        | some pf => simp [parse_toBytes]
    · rfl

/-- **Weak simulation-extractability step**: the simulated `Acc ∧ Fresh ∧ ¬ Rel` is the event of
`WeakSE2` for the adversary that samples the Client's coins and runs `A`. -/
theorem sim_se_le {AdmE : (G → G → S → Op Z) → Prop} {εSE : ℝ}
    (hse : WeakSE2 simI progI simS progS (AccOp A verI verS) (FreshOp A) (RelOp A) ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CS × G) × S))
        (simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS) (seEv A verI verS ext)) ≤
      εSE := by
  have h := hse Sec (fun ω => xIo A (K₁ A ω))
    (fun ω π₁ => xS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (reqI A (K₁ A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI A (K₁ A ω) π₁)
      (reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (reqI A (K₁ A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine le_of_eq_of_le (pr_congr fun z => ?_) h
  simp only [simG, seEv, accE, freshE, relE, simIss, simSp, pgI, pgS, stI_reqI, stS_reqS]

/-- **No theft (Theorem 3, N2a).** For every adversary, with zero knowledge of both proof systems
at the hops' distinguishers and weak simulation-extractability:

    Pr[Bad] ≤ ε_I + ε_S + δ_S + ε_SE + Adv^ow(inverter). -/
theorem noTheft [Nonempty CI] [Nonempty CS] [Nonempty G] [Nonempty S]
    {AdmI : (Option (IssueProof Z) → G → S → Prop) → Prop}
    {AdmS : (Option (SpendProof Z) → G → S → Prop) → Prop}
    {AdmE : (G → G → S → Op Z) → Prop} {εI εS εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRel (PI' PI) simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkS : ZeroKnowledgeRO SpendRel (PS' PS) simS progS AdmS εS) (hεS : 0 ≤ εS)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PI PS verI verS ext ω r₂ g₂))
    (hAS : ∀ ω c₁ g₁, AdmS (distS A verI verS ext simI progI ω c₁ g₁))
    (hse : WeakSE2 simI progI simS progS (AccOp A verI verS) (FreshOp A) (RelOp A) ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (theftReal A PI PS verI verS ext) ≤
      εI + εS + pr _ (deltaS A PI PS simI progI) + εSE +
        owAdv A.ctx (inverter A ext simI progI simS progS) := by
  have h := theft_le (Ω := Sec) (ρ₁ := Coins 16) (ρ₂ := Coins 16) (C₁ := CI) (C₂ := CS) (G := G)
    (S := S) (specI A PI PS) (simIss A simI) (pgI A progI) (specS A PI PS) (simSp A simS)
    (pgS A progS) (accE A verI verS) (freshE A) (relE A ext) (opensE A ext) (ε₁ := εI) (ε₂ := εS)
    (fun ω r₂ g₂ => by
      have := zk_step hzkI hεI (xwI A ω) (xwI_rel A ω) (reqI A (K₁ A ω))
        (D₁ (specS A PI PS) (Bad A verI verS ext) ω r₂ g₂)
        (fun _ _ _ => hAI ω r₂ g₂)
      rw [xwI_fst] at this
      simp only [specI_eq]
      exact this)
    (fun ω c₁ g₁ => by
      have := zk_step hzkS hεS (xwS A ω (simIss A simI ω c₁)) (xwS_rel A ω _)
        (reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (simIss A simI ω c₁))
        (D₂ (simIss A simI) (pgI A progI) (Bad A verI verS ext) ω c₁ g₁)
        (fun _ _ _ => hAS ω c₁ g₁)
      rw [xwS_fst] at this
      simp only [specS_eq]
      exact this)
  have hse' : pr ((Sec × (CI × G)) × ((CS × G) × S))
      (simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          ¬ relE A ext ω o₁ o₂ g₁ g₂ s)) ≤ εSE :=
    sim_se_le A verI verS ext simI progI simS progS hse hAE
  have hop := sim_opens_le A ext simI progI simS progS
  have hd : pr ((Sec × (CI × G)) × ((Coins 16 × G) × S)) (deltaS A PI PS simI progI) =
      pr ((Sec × (CI × G)) × ((Coins 16 × G) × S)) (deltaG (simIss A simI) (pgI A progI) (specS A PI PS)) :=
    rfl
  have hr : pr ((Sec × (Coins 16 × G)) × ((Coins 16 × G) × S)) (theftReal A PI PS verI verS ext) =
      pr ((Sec × (Coins 16 × G)) × ((Coins 16 × G) × S)) (realG (specI A PI PS) (specS A PI PS)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ opensE A ext ω o₁ o₂ g₁ g₂ s))) :=
    rfl
  rw [hr, hd]
  linarith

end VoleMole.Theft.Ratatouille
