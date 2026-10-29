import VoleMole.Privacy.RatatouilleRAK
import VoleMole.Privacy.RatatouilleMany

/-!
# Ratatouille unlinkability with adaptively scheduled sessions

`Privacy/RatatouilleMany.lean` has any number of further honest Clients in one concurrent
schedule: their issuance requests are seen by stage 1, their spend requests by stage 2. Here the
malicious Issuer **starts further sessions after seeing earlier sessions' outcomes**: before the
challenge, between the challenge issuance requests and stage 1 (the challenge responses and
`d₁`), between round 1's request and stage 2 (round 1's response and `d₂`; these sessions happen
only if round 1 runs), and after the challenge outcome. Each further session's key, context and
balance (`CfgR`), and the Issuer's response to it and its spend amount (`AnsR`), are chosen from
everything seen so far; the challenge key, context and balance from the sessions before the
challenge.

## A whole session is a consistent table reader

A further session run to the end (`fullXR`: the issuance request, then `finalize_issue` on the
Issuer's response and a spend of the token with round 1 for the chosen amount) reads, through its
issuance and spend proofs, `H₅` at `2·624` keys, the cipher at `2·4607` and `H₂³` at the `2·2³²`
grinding points of its two prefixes, consistently (`issXR_sreads`, `spXR_sreads`; `fullXR_sreads`),
and sequential sessions compose (`runSeqR_sreads`).

## The game and the reduction

`AdversaryAdR`, `realGameAdR`: the game with a table-reading key stage
(`Privacy/RatatouilleRAK.lean`) of the Issuer `A.red c` that runs the further sessions with their
tapes `c` itself (as `realGameN` is the `RA` game of the Issuer served by the further Clients): its
key stage the `m₁` sessions before the challenge, its stage 1 the `m₂` sessions after the challenge
issuance requests, its stage 2 also the `m₃` sessions after round 1's request, its guess also the
`m₄` sessions after the challenge outcome. Budgets: key stage `KBudget (0, m₁·2·2³², m₁·1248,
m₁·9214)` (`red_kBudget`), both stages `IBudget (0, M·2·2³², M·1248, M·9214)` with `M = m₂ + m₃`
(`red_iBudget`), guess `(q₃, q₅ + (m₂ + m₃ + m₄)·1248, q_E + (m₂ + m₃ + m₄)·9214)` (`red_gBudget`).

## The bound

`unlinkabilityRAK_lean_numG` for every `c`, averaged over `c`: `unlinkabilityAd_lean_numG`,
`unlinkabilityAd_lean_num` (function rows), `unlinkabilityAd_lean_num_perm`; in numbers
(`unlinkabilityAd_lean_le`) `≤ n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` for
`n = m₁ + m₂ + m₃ + m₄ + 2` Clients in all: `≤ 2⁻⁸¹ + 2·εhide` for `n ≤ 2²⁰`
(`unlinkabilityAd_lean_2pow20`), `≤ 2⁻⁶⁹ + 2·εhide` for `n ≤ 2³²` (`unlinkabilityAd_lean_2pow32`),
plus the guess's budget terms; the non-adaptive schedule's numbers. The `H₂³` reads are counted by
keys, `2·2⁻¹⁰²⁴` each (the simulated block's `128`-byte `ã`): no prefix count is needed. Hiding of
`Com` is assumed for the reductions of every `A.red c`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- The proof sizes of the Lean provers. -/
local notation "ZL" => Sizes.labelRows

/-! ## A whole further session -/

section Full

/-- A reader of the shared tables for the spend parameters is one for the issuance parameters
(the two have the same prefix length, so the tables are the same). -/
lemma SReads.pS_pI {X : Type} {f : ShR R → X} {a3 a2 a5 aE : ℕ}
    (h : SReads pS (fun t : Tb R pS => f t.2) a3 a2 a5 aE) :
    SReads pI (fun t : Tb R pI => f t.2) a3 a2 a5 aE := h

/-- And conversely. -/
lemma SReads.pI_pS {X : Type} {f : ShR R → X} {a3 a2 a5 aE : ℕ}
    (h : SReads pI (fun t : Tb R pI => f t.2) a3 a2 a5 aE) :
    SReads pS (fun t : Tb R pS => f t.2) a3 a2 a5 aE := h

/-- **A further session's configuration**: the Issuer's key, the context and the balance. -/
abbrev CfgR := PublicKey × Context × Credits

/-- **The Issuer's answer to a further Client's issuance request**: the response, and the amount
the Client then spends. -/
abbrev AnsR := Preimage × Credits

/-- What the Issuer has seen of a finished further session: its issuance and spend requests. -/
abbrev HistR := IReq × SReq

/-- **A further session run to the end**: its issuance request, and its spend (round 1) of the
token finalized on the Issuer's answer `ρ` to that request. -/
noncomputable def fullXR (k : CfgR) (ρ : IReq → AnsR) (x : XC) (s : ShR R) : HistR :=
  (reqIX (issXR k.2.1 k.2.2 x.1 s),
    reqSX (spXR k.1 k.2.1 (finI k.1 (issXR k.2.1 k.2.2 x.1 s) (ρ (reqIX (issXR k.2.1 k.2.2 x.1 s))).1)
      (ρ (reqIX (issXR k.2.1 k.2.2 x.1 s))).2 x.2 s))

/-- **A whole further session is a consistent reader** of `H₅` (`2·624` keys), the cipher
(`2·4607`) and `H₂³` (the grinding points of its two prefixes), and of no slice key. -/
theorem fullXR_sreads (k : CfgR) (ρ : IReq → AnsR) (x : XC) :
    SReads pI (fun t : Tb R pI => fullXR k ρ x t.2) 0 (2 * nGrind) 1248 9214 := by
  have h := (issXR_sreads (R := R) k.2.1 k.2.2 x.1).bind
    (g := fun w (t : Tb R pI) => (reqIX w, reqSX (spXR k.1 k.2.1 (finI k.1 w (ρ (reqIX w)).1)
      (ρ (reqIX w)).2 x.2 t.2)))
    fun w => SReads.pS_pI (f := fun s => (reqIX w, reqSX (spXR k.1 k.2.1 (finI k.1 w (ρ (reqIX w)).1)
      (ρ (reqIX w)).2 x.2 s)))
      ((spXR_sreads (R := R) k.1 k.2.1 _ _ x.2).map fun o => (reqIX w, reqSX o))
  exact h.mono le_rfl (by omega) (by omega) (by omega)

/-- **Further sessions one after the other**: each one's configuration (`next`) and the Issuer's
answer to its request (`resp`) are chosen from the sessions before it, each session runs to the
end on the tables with its own tape. -/
noncomputable def runSeqR (next : List HistR → CfgR) (resp : List HistR → IReq → AnsR) :
    List XC → List HistR → ShR R → List HistR
  | [], H, _ => H
  | x :: cs, H, s => runSeqR next resp cs (H ++ [fullXR (next H) (resp H) x s]) s

/-- **Sequential sessions are a consistent reader**: `|cs|` times a session's keys. -/
theorem runSeqR_sreads (next : List HistR → CfgR) (resp : List HistR → IReq → AnsR) (cs : List XC) :
    ∀ H, SReads pI (fun t : Tb R pI => runSeqR next resp cs H t.2) 0 (cs.length * (2 * nGrind))
      (cs.length * 1248) (cs.length * 9214) := by
  induction cs with
  | nil => intro H; simpa [runSeqR] using SReads.const (R := R) (p := pI) H
  | cons x cs ih =>
    intro H
    have h := (fullXR_sreads (R := R) (next H) (resp H) x).bind
      (g := fun y (t : Tb R pI) => runSeqR next resp cs (H ++ [y]) t.2) fun y => ih (H ++ [y])
    refine (h.mono le_rfl ?_ ?_ ?_)
    · simp only [List.length_cons]; exact le_of_eq (by ring)
    · simp only [List.length_cons]; exact le_of_eq (by ring)
    · simp only [List.length_cons]; exact le_of_eq (by ring)

end Full

/-! ## The adaptive game -/

section Game

variable {m₁ m₂ m₃ m₄ : ℕ}

/-- **The malicious Issuer of the adaptive game**: before the challenge, `m₁` further sessions
one after the other (`next₁`, `resp₁`); then the challenge key, context and balance from them;
after the challenge issuance requests, `m₂` further sessions (`next₂`, `resp₂`) and stage 1 (the
challenge responses and `d₁`); after round 1's request, `m₃` further sessions (`next₃`, `resp₃`)
and stage 2 (round 1's response and `d₂`); after the challenge outcome, `m₄` further sessions
(`next₄`, `resp₄`); and a guess that sees everything, the challenge slices and the tables. The
interaction does not read the tables itself (the further sessions it runs do). -/
structure AdversaryAdR (R : Type) where
  next₁ : List HistR → CfgR
  resp₁ : List HistR → IReq → AnsR
  pk : List HistR → PublicKey
  ctx : List HistR → Context
  tInit : List HistR → Credits
  next₂ : List HistR → IssTr ZL → List HistR → CfgR
  resp₂ : List HistR → IssTr ZL → List HistR → IReq → AnsR
  respondIss : List HistR → IssTr ZL → List HistR → Bool → Preimage
  d₁ : List HistR → IssTr ZL → List HistR → Credits
  next₃ : List HistR → IssTr ZL → List HistR → SReq → List HistR → CfgR
  resp₃ : List HistR → IssTr ZL → List HistR → SReq → List HistR → IReq → AnsR
  respond₁ : List HistR → IssTr ZL → List HistR → SReq → List HistR → SpendResponse
  d₂ : List HistR → IssTr ZL → List HistR → SReq → List HistR → Credits
  next₄ : List HistR → IssTr ZL → List HistR → Rounds ZL → List HistR → List HistR → CfgR
  resp₄ : List HistR → IssTr ZL → List HistR → Rounds ZL → List HistR → List HistR → IReq → AnsR
  guess : List HistR → IssTr ZL → List HistR → Rounds ZL → List HistR → List HistR → SlicesR →
    ShR R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` freely. -/
structure AdversaryAdR.Budget (A : AdversaryAdR R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ H₁ tr H₂ y H₃ H₄ (g₁ g₂ g₃ : Tab3) s,
    Rd3 (fun g => A.guess H₁ tr H₂ y H₃ H₄ ((g, g₁), (g₂, g₃)) s) q3
  h31 : ∀ H₁ tr H₂ y H₃ H₄ (g₀ g₂ g₃ : Tab3) s,
    Rd3 (fun g => A.guess H₁ tr H₂ y H₃ H₄ ((g₀, g), (g₂, g₃)) s) q3
  h32 : ∀ H₁ tr H₂ y H₃ H₄ (g₀ g₁ g₃ : Tab3) s,
    Rd3 (fun g => A.guess H₁ tr H₂ y H₃ H₄ ((g₀, g₁), (g, g₃)) s) q3
  h33 : ∀ H₁ tr H₂ y H₃ H₄ (g₀ g₁ g₂ : Tab3) s,
    Rd3 (fun g => A.guess H₁ tr H₂ y H₃ H₄ ((g₀, g₁), (g₂, g)) s) q3
  h5 : ∀ H₁ tr H₂ y H₃ H₄ sl, Rd5 (A.guess H₁ tr H₂ y H₃ H₄ sl) q5
  hE : ∀ H₁ tr H₂ y H₃ H₄ sl, RdE (A.guess H₁ tr H₂ y H₃ H₄ sl) qE

/-- The further sessions' tapes, stage by stage. -/
abbrev TapesAdR (m₁ m₂ m₃ m₄ : ℕ) :=
  (Fin m₁ → XC) × (Fin m₂ → XC) × (Fin m₃ → XC) × (Fin m₄ → XC)

namespace AdversaryAdR

variable (A : AdversaryAdR R) (c : TapesAdR m₁ m₂ m₃ m₄)

/-- The sessions before the challenge. -/
noncomputable def hist₁ (s : ShR R) : List HistR := runSeqR A.next₁ A.resp₁ (List.ofFn c.1) [] s

/-- The sessions between the challenge issuance requests and stage 1. -/
noncomputable def hist₂ (H₁ : List HistR) (tr : IssTr ZL) (s : ShR R) : List HistR :=
  runSeqR (A.next₂ H₁ tr) (A.resp₂ H₁ tr) (List.ofFn c.2.1) [] s

/-- The sessions between round 1's request and stage 2. -/
noncomputable def hist₃ (H₁ : List HistR) (tr : IssTr ZL) (H₂ : List HistR) (rq : SReq) (s : ShR R) :
    List HistR :=
  runSeqR (A.next₃ H₁ tr H₂ rq) (A.resp₃ H₁ tr H₂ rq) (List.ofFn c.2.2.1) [] s

/-- The sessions between round 1's request and stage 2, as the guess sees them: none if round 1
did not run. -/
noncomputable def hist₃G (H₁ : List HistR) (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL)
    (s : ShR R) : List HistR :=
  (y.map Prod.fst).elim [] fun rq => A.hist₃ c H₁ tr H₂ rq s

/-- The sessions after the challenge outcome. -/
noncomputable def hist₄ (H₁ : List HistR) (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL)
    (H₃ : List HistR) (s : ShR R) : List HistR :=
  runSeqR (A.next₄ H₁ tr H₂ y H₃) (A.resp₄ H₁ tr H₂ y H₃) (List.ofFn c.2.2.2) [] s

/-- **The table-reading Issuer at the state `H₁`** (the sessions before the challenge): its key,
context and balance from `H₁`; stage 1 runs the sessions after the challenge issuance requests,
stage 2 also those after round 1's request, the guess also those after the challenge outcome. -/
noncomputable def atH (H₁ : List HistR) : AdversaryRA R ZL where
  pk := A.pk H₁
  ctx := A.ctx H₁
  tInit := A.tInit H₁
  respondIss tr i _ u := A.respondIss H₁ tr (A.hist₂ c H₁ tr u) i
  d₁ tr _ u := A.d₁ H₁ tr (A.hist₂ c H₁ tr u)
  respond₁ tr rq _ u := A.respond₁ H₁ tr (A.hist₂ c H₁ tr u) rq
    (A.hist₃ c H₁ tr (A.hist₂ c H₁ tr u) rq u)
  d₂ tr rq _ u := A.d₂ H₁ tr (A.hist₂ c H₁ tr u) rq (A.hist₃ c H₁ tr (A.hist₂ c H₁ tr u) rq u)
  guess tr y sl v := A.guess H₁ tr (A.hist₂ c H₁ tr v) y (A.hist₃G c H₁ tr (A.hist₂ c H₁ tr v) y v)
    (A.hist₄ c H₁ tr (A.hist₂ c H₁ tr v) y (A.hist₃G c H₁ tr (A.hist₂ c H₁ tr v) y v) v) sl v

/-- **The reduction**: the Issuer with a table-reading key stage that runs the further sessions
itself, with their tapes `c` fixed. Its key stage runs the sessions before the challenge. -/
noncomputable def red : AdversaryRAK R ZL (List HistR) :=
  ⟨fun _ s => A.hist₁ c s, A.atH c⟩

end AdversaryAdR

/-- **The adaptive game** in world `(b₁, b₂)`: the game with a table-reading key stage
(`realGameRAK`, the Lean provers on the shared tables) of the Issuer that runs the further sessions
with tapes `z.1.2` (`AdversaryAdR.red`): the sessions before the challenge, then the challenge key,
context and balance from them and the challenge protocol of `realGameRA`, the Issuer's stages and
guess running the later sessions on the tables. -/
noncomputable def realGameAdR (A : AdversaryAdR R) (b₁ b₂ : Bool)
    (z : (((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR R) : Prop :=
  realGameRAK (A.red z.1.2) leanPIR leanPSR b₁ b₂ (z.1.1, z.2)

/-- **The adaptive game at a tape** is `realGameRA` of the Issuer at the state the sessions before
the challenge produce. -/
theorem realGameAdR_iff (A : AdversaryAdR R) (b₁ b₂ : Bool) (x : (TRe × TRe) × (TRe × TRe))
    (c : TapesAdR m₁ m₂ m₃ m₄) (s : ShR R) :
    realGameAdR A b₁ b₂ ((x, c), s) ↔ realGameRA (A.atH c (A.hist₁ c s)) leanPIR leanPSR b₁ b₂ (x, s) :=
  Iff.rfl

namespace AdversaryAdR

variable (A : AdversaryAdR R) (c : TapesAdR m₁ m₂ m₃ m₄)

/-- **The reduction's key-stage budget**: the `m₁` sessions before the challenge. -/
theorem red_kBudget :
    (A.red c).KBudget 0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214) := by
  have h := runSeqR_sreads (R := R) A.next₁ A.resp₁ (List.ofFn c.1) []
  simp only [List.length_ofFn] at h
  exact ⟨fun _ _ _ => h, fun _ _ _ => h,
    fun _ _ _ => SReads.pI_pS (f := fun s => A.hist₁ c s) h,
    fun _ _ _ => SReads.pI_pS (f := fun s => A.hist₁ c s) h⟩

/-- Stage 1 at the state `H₁` reads the `m₂` sessions after the challenge issuance requests. -/
lemma stage1_sreads (H₁ : List HistR) (tr : IssTr ZL) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.atH c H₁).msg₁ tr (σ t) t.2) 0 ((m₂ + m₃) * (2 * nGrind))
      ((m₂ + m₃) * 1248) ((m₂ + m₃) * 9214) := by
  have h := (runSeqR_sreads (R := R) (A.next₂ H₁ tr) (A.resp₂ H₁ tr) (List.ofFn c.2.1) []).map
    fun H₂ => ((A.respondIss H₁ tr H₂ false, A.respondIss H₁ tr H₂ true), A.d₁ H₁ tr H₂)
  simp only [List.length_ofFn] at h
  exact h.mono le_rfl (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

/-- Stage 2 at the state `H₁` reads the `m₂` and the `m₃` sessions. -/
lemma stage2_sreads (H₁ : List HistR) (tr : IssTr ZL) (rq : SReq) (σ : Tb R pI → SlicesR) :
    SReads pI (fun t : Tb R pI => (A.atH c H₁).msg₂ tr rq (σ t) t.2) 0 ((m₂ + m₃) * (2 * nGrind))
      ((m₂ + m₃) * 1248) ((m₂ + m₃) * 9214) := by
  have h := (runSeqR_sreads (R := R) (A.next₂ H₁ tr) (A.resp₂ H₁ tr) (List.ofFn c.2.1) []).bind
    (g := fun H₂ (t : Tb R pI) =>
      (A.respond₁ H₁ tr H₂ rq (A.hist₃ c H₁ tr H₂ rq t.2), A.d₂ H₁ tr H₂ rq (A.hist₃ c H₁ tr H₂ rq t.2)))
    fun H₂ => (runSeqR_sreads (R := R) (A.next₃ H₁ tr H₂ rq) (A.resp₃ H₁ tr H₂ rq)
      (List.ofFn c.2.2.1) []).map fun H₃ => (A.respond₁ H₁ tr H₂ rq H₃, A.d₂ H₁ tr H₂ rq H₃)
  simp only [List.length_ofFn] at h
  exact h.mono le_rfl (by rw [Nat.add_mul]) (by rw [Nat.add_mul]) (by rw [Nat.add_mul])

/-- **The reduction's interaction budget**: each stage reads at most the `m₂ + m₃` sessions run in
the stages. -/
theorem red_iBudget :
    (A.red c).IBudget 0 ((m₂ + m₃) * (2 * nGrind)) ((m₂ + m₃) * 1248) ((m₂ + m₃) * 9214) := by
  intro H₁
  exact
    { a0 := fun tr g₁ g₂ g₃ => stage1_sreads A c H₁ tr fun t => ((t.1, g₁), (g₂, g₃))
      a1 := fun tr g₀ g₂ g₃ => stage1_sreads A c H₁ tr fun t => ((g₀, t.1), (g₂, g₃))
      a2 := fun tr g₀ g₁ g₃ => SReads.pI_pS (f := fun s => (A.atH c H₁).msg₁ tr ((g₀, g₁), (default, g₃)) s)
        (stage1_sreads A c H₁ tr fun _ => ((g₀, g₁), (default, g₃)))
      a3 := fun tr g₀ g₁ g₂ => SReads.pI_pS (f := fun s => (A.atH c H₁).msg₁ tr ((g₀, g₁), (g₂, default)) s)
        (stage1_sreads A c H₁ tr fun _ => ((g₀, g₁), (g₂, default)))
      b0 := fun tr rq g₁ g₂ g₃ => stage2_sreads A c H₁ tr rq fun t => ((t.1, g₁), (g₂, g₃))
      b1 := fun tr rq g₀ g₂ g₃ => stage2_sreads A c H₁ tr rq fun t => ((g₀, t.1), (g₂, g₃))
      b2 := fun tr rq g₀ g₁ g₃ => SReads.pI_pS
        (f := fun s => (A.atH c H₁).msg₂ tr rq ((g₀, g₁), (default, g₃)) s)
        (stage2_sreads A c H₁ tr rq fun _ => ((g₀, g₁), (default, g₃)))
      b3 := fun tr rq g₀ g₁ g₂ => SReads.pI_pS
        (f := fun s => (A.atH c H₁).msg₂ tr rq ((g₀, g₁), (g₂, default)) s)
        (stage2_sreads A c H₁ tr rq fun _ => ((g₀, g₁), (g₂, default))) }

/-- **The reduction's guess budget**: the Issuer's plus the `m₂ + m₃ + m₄` sessions after the
challenge issuance requests. -/
theorem red_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.red c).GBudget q3 (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)))
      (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE))) := by
  intro H₁ m
  have r2 (tr : IssTr ZL) : Rd5 (fun s => A.hist₂ c H₁ tr s) (m₂ * 1248) := by
    have h := (runSeqR_sreads (R := R) (A.next₂ H₁ tr) (A.resp₂ H₁ tr) (List.ofFn c.2.1) []).rd5 default
    simp only [List.length_ofFn] at h
    exact h
  have r2E (tr : IssTr ZL) : RdE (fun s => A.hist₂ c H₁ tr s) (m₂ * 9214) := by
    have h := (runSeqR_sreads (R := R) (A.next₂ H₁ tr) (A.resp₂ H₁ tr) (List.ofFn c.2.1) []).rdE default
    simp only [List.length_ofFn] at h
    exact h
  have r3 (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL) :
      Rd5 (fun s => A.hist₃G c H₁ tr H₂ y s) (m₃ * 1248) := by
    unfold hist₃G
    rcases y.map Prod.fst with _ | rq
    · exact (Rd5.const _).mono (Nat.zero_le _)
    · have h := (runSeqR_sreads (R := R) (A.next₃ H₁ tr H₂ rq) (A.resp₃ H₁ tr H₂ rq)
        (List.ofFn c.2.2.1) []).rd5 default
      simp only [List.length_ofFn] at h
      exact h
  have r3E (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL) :
      RdE (fun s => A.hist₃G c H₁ tr H₂ y s) (m₃ * 9214) := by
    unfold hist₃G
    rcases y.map Prod.fst with _ | rq
    · exact (RdE.const _).mono (Nat.zero_le _)
    · have h := (runSeqR_sreads (R := R) (A.next₃ H₁ tr H₂ rq) (A.resp₃ H₁ tr H₂ rq)
        (List.ofFn c.2.2.1) []).rdE default
      simp only [List.length_ofFn] at h
      exact h
  have r4 (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL) (H₃ : List HistR) :
      Rd5 (fun s => A.hist₄ c H₁ tr H₂ y H₃ s) (m₄ * 1248) := by
    have h := (runSeqR_sreads (R := R) (A.next₄ H₁ tr H₂ y H₃) (A.resp₄ H₁ tr H₂ y H₃)
      (List.ofFn c.2.2.2) []).rd5 default
    simp only [List.length_ofFn] at h
    exact h
  have r4E (tr : IssTr ZL) (H₂ : List HistR) (y : Rounds ZL) (H₃ : List HistR) :
      RdE (fun s => A.hist₄ c H₁ tr H₂ y H₃ s) (m₄ * 9214) := by
    have h := (runSeqR_sreads (R := R) (A.next₄ H₁ tr H₂ y H₃) (A.resp₄ H₁ tr H₂ y H₃)
      (List.ofFn c.2.2.2) []).rdE default
    simp only [List.length_ofFn] at h
    exact h
  exact
    { h30 := fun tr y g₁ g₂ g₃ s => hA.h30 _ _ _ _ _ _ g₁ g₂ g₃ s
      h31 := fun tr y g₀ g₂ g₃ s => hA.h31 _ _ _ _ _ _ g₀ g₂ g₃ s
      h32 := fun tr y g₀ g₁ g₃ s => hA.h32 _ _ _ _ _ _ g₀ g₁ g₃ s
      h33 := fun tr y g₀ g₁ g₂ s => hA.h33 _ _ _ _ _ _ g₀ g₁ g₂ s
      h5 := fun tr y sl => Rd5.bindEq (m := fun s => A.hist₂ c H₁ tr s)
        (f := fun H₂ s => A.guess H₁ tr H₂ y (A.hist₃G c H₁ tr H₂ y s)
          (A.hist₄ c H₁ tr H₂ y (A.hist₃G c H₁ tr H₂ y s) s) sl s) (fun _ => rfl) (r2 tr) fun H₂ =>
        Rd5.bindEq (m := fun s => A.hist₃G c H₁ tr H₂ y s)
          (f := fun H₃ s => A.guess H₁ tr H₂ y H₃ (A.hist₄ c H₁ tr H₂ y H₃ s) sl s) (fun _ => rfl)
          (r3 tr H₂ y) fun H₃ =>
          Rd5.bindEq (m := fun s => A.hist₄ c H₁ tr H₂ y H₃ s)
            (f := fun H₄ s => A.guess H₁ tr H₂ y H₃ H₄ sl s) (fun _ => rfl) (r4 tr H₂ y H₃)
            fun H₄ => hA.h5 _ _ _ _ _ _ _
      hE := fun tr y sl => RdE.bindEq (m := fun s => A.hist₂ c H₁ tr s)
        (f := fun H₂ s => A.guess H₁ tr H₂ y (A.hist₃G c H₁ tr H₂ y s)
          (A.hist₄ c H₁ tr H₂ y (A.hist₃G c H₁ tr H₂ y s) s) sl s) (fun _ => rfl) (r2E tr) fun H₂ =>
        RdE.bindEq (m := fun s => A.hist₃G c H₁ tr H₂ y s)
          (f := fun H₃ s => A.guess H₁ tr H₂ y H₃ (A.hist₄ c H₁ tr H₂ y H₃ s) sl s) (fun _ => rfl)
          (r3E tr H₂ y) fun H₃ =>
          RdE.bindEq (m := fun s => A.hist₄ c H₁ tr H₂ y H₃ s)
            (f := fun H₄ s => A.guess H₁ tr H₂ y H₃ H₄ sl s) (fun _ => rfl) (r4E tr H₂ y H₃)
            fun H₄ => hA.hE _ _ _ _ _ _ _ }

end AdversaryAdR

/-- The adaptive tape, with the further sessions' tapes first. -/
def tapeAdR : TapesAdR m₁ m₂ m₃ m₄ × (((TRe × TRe) × (TRe × TRe)) × ShR R) ≃
    (((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {m₁ m₂ m₃ m₄ : ℕ}

/-- **Theorem 2 with adaptively scheduled further sessions, for every type of cipher rows**
(`ZKRow R`, `ZKPRow R`; SHAKE as the base record): with `m₁` further sessions before the
challenge, `m₂` between the challenge issuance requests and stage 1, `m₃` between round 1's
request and stage 2 and `m₄` after the challenge outcome, the bound of
`unlinkabilityRAK_lean_numG` at the key-stage budget `(0, 2·2³²m₁, 1248m₁, 9214m₁)`, the
interaction budget `(0, 2·2³²M, 1248M, 9214M)`, `M = m₂ + m₃`, and the guess budget
`(q₃, q₅ + 1248(m₂ + m₃ + m₄), q_E + 9214(m₂ + m₃ + m₄))`; any two worlds. -/
theorem unlinkabilityAd_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryAdR R) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR R) (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR R) (realGameAdR A b₁' b₂')| ≤
      4 * εAdG R pI 9 (2 * 0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 2 * ((m₂ + m₃) * 1248) + 1872)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 2 * ((m₂ + m₃) * 9214) + 13821)
          0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214) +
        2 * εAdG R pS 9 (0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + (m₂ + m₃) * 1248 + 1248)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + (m₂ + m₃) * 9214 + 13821)
          (0 + 0) (m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind))
          (m₁ * 1248 + (m₂ + m₃) * 1248 + 624) (m₁ * 9214 + (m₂ + m₃) * 9214 + 9214) +
        2 * εAdG R pS 9 q3 (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 936)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 13821)
          (0 + 2 * 0) (m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind)))
          (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560) (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560)
          (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeAdR, ← pr_equiv tapeAdR]
  exact abs_pr_prod_sub_le _ _ fun c =>
    unlinkabilityRAK_lean_numG (A.red c) (A.red_gBudget c hA) (A.red_iBudget c) (A.red_kBudget c)
      (hhide c) b₁ b₂ b₁' b₂'

/-- **Theorem 2 with adaptively scheduled further sessions** (function rows). -/
theorem unlinkabilityAd_lean_num (A : AdversaryAdR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk)) (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk))
          (realGameAdR A b₁' b₂')| ≤
      4 * εAd 9 (2 * 0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 2 * ((m₂ + m₃) * 1248) + 1872)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 2 * ((m₂ + m₃) * 9214) + 13821)
          0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214) +
        2 * εAd 9 (0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + (m₂ + m₃) * 1248 + 1248)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + (m₂ + m₃) * 9214 + 13821)
          (0 + 0) (m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind))
          (m₁ * 1248 + (m₂ + m₃) * 1248 + 624) (m₁ * 9214 + (m₂ + m₃) * 9214 + 9214) +
        2 * εAd 9 q3 (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 936)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 13821)
          (0 + 2 * 0) (m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind)))
          (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560) (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560)
          (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityAd_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- **Theorem 2 with adaptively scheduled further sessions and AES as uniformly random
permutations.** -/
theorem unlinkabilityAd_lean_num_perm (A : AdversaryAdR (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Equiv.Perm Blk))
          (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Equiv.Perm Blk))
          (realGameAdR A b₁' b₂')| ≤
      4 * εAdPm pI 9 (2 * 0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 2 * ((m₂ + m₃) * 1248) + 1872)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 2 * ((m₂ + m₃) * 9214) + 13821)
          0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214) +
        2 * εAdPm pS 9 (0 + q3)
          (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + (m₂ + m₃) * 1248 + 1248)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + (m₂ + m₃) * 9214 + 13821)
          (0 + 0) (m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind))
          (m₁ * 1248 + (m₂ + m₃) * 1248 + 624) (m₁ * 9214 + (m₂ + m₃) * 9214 + 9214) +
        2 * εAdPm pS 9 q3 (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 936)
          (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 13821)
          (0 + 2 * 0) (m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind)))
          (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560) (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560)
          (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityAd_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- `h23Term` without its case split: an affine upper bound. -/
lemma h23Term_le_aff (d n5 nE n2 : ℕ) :
    h23Term d n5 nE n2 ≤ 1 / 2 ^ 113 + εROP 0 312 4607 n5 nE +
      2 * (noHitProb + n2 / 2 ^ (8 * (16 * (d - 1)))) := by
  unfold h23Term
  split_ifs
  · have a0 := εROP_nonneg 0 312 4607 n5 nE
    have a1 : 0 ≤ noHitProb := pr_nonneg _
    have a2 : (0 : ℝ) ≤ 1 / 2 ^ 113 := by norm_num
    have a3 : (0 : ℝ) ≤ (n2 : ℝ) / 2 ^ (8 * (16 * (d - 1))) :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    linarith
  · exact le_refl _

/-- `εAd` at prefix degree `9` without its case split: an affine upper bound. -/
lemma εAd9_le (q3 q5 qE s3 s2 s5 sE : ℕ) :
    εAd 9 q3 q5 qE s3 s2 s5 sE ≤ εROP q3 q5 qE s5 sE + s3 / 2 ^ 128 +
      (1 / 2 ^ 113 + εROP 0 312 4607 s5 sE + 2 * (noHitProb + s2 / 2 ^ 1024)) := by
  unfold εAd
  have h := h23Term_le_aff 9 s5 sE s2
  rw [show (8 * (16 * (9 - 1)) : ℕ) = 1024 from rfl] at h
  exact add_le_add_right h _

/-- A count of `H₂³` keys of at most `M` blocks of `4·2³²` costs at most `M·2⁻¹²⁸` at the
`2⁻¹⁰²⁴` rate. -/
lemma grind_le (n M : ℕ) (h : n ≤ M * (4 * nGrind)) :
    (n : ℝ) / 2 ^ 1024 ≤ M / 2 ^ 128 := by
  have hn : (n : ℝ) ≤ M * 2 ^ 34 := by
    have h' : (n : ℝ) ≤ ((M * (4 * nGrind) : ℕ) : ℝ) := by exact_mod_cast h
    have e : ((M * (4 * nGrind) : ℕ) : ℝ) = M * 2 ^ 34 := by
      simp only [nGrind, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    exact h'.trans (le_of_eq e)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 34 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (n : ℝ) * 2 ^ 128 ≤ ((M : ℝ) * 2 ^ 34) * 2 ^ 128 := mul_le_mul_of_nonneg_right hn hp.le
    _ = ((M : ℝ) * 2 ^ 128) * 2 ^ 34 := mul_right_comm _ _ _
    _ ≤ ((M : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hM hp.le)
    _ = (M : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _

/-- **The adaptive bound in numbers**: with `n = m₁ + m₂ + m₃ + m₄ + 2` Clients in all, any two
worlds differ by at most

    n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide.

(Per session `≈ 0.30·2⁻¹⁰¹` before the challenge, `≈ 0.58·2⁻¹⁰¹` in either stage, `≈ 0.12·2⁻¹⁰¹`
after; the constant is `≈ 0.95·2⁻¹⁰¹`.) -/
theorem unlinkabilityAd_lean_le (A : AdversaryAdR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk)) (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk))
          (realGameAdR A b₁' b₂')| ≤
      (m₁ + m₂ + m₃ + m₄ + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityAd_lean_num A hA hhide b₁ b₂ b₁' b₂'
  have u1 := εAd9_le (2 * 0 + q3)
    (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 2 * ((m₂ + m₃) * 1248) + 1872)
    (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 2 * ((m₂ + m₃) * 9214) + 13821)
    0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214)
  have u2 := εAd9_le (0 + q3)
    (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + (m₂ + m₃) * 1248 + 1248)
    (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + (m₂ + m₃) * 9214 + 13821)
    (0 + 0) (m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind))
    (m₁ * 1248 + (m₂ + m₃) * 1248 + 624) (m₁ * 9214 + (m₂ + m₃) * 9214 + 9214)
  have u3 := εAd9_le q3 (m₂ * 1248 + (m₃ * 1248 + (m₄ * 1248 + q5)) + 936)
    (m₂ * 9214 + (m₃ * 9214 + (m₄ * 9214 + qE)) + 13821)
    (0 + 2 * 0) (m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind)))
    (m₁ * 1248 + 2 * ((m₂ + m₃) * 1248) + 1560) (m₁ * 9214 + 2 * ((m₂ + m₃) * 9214) + 23035)
  have g1 := grind_le (m₁ * (2 * nGrind)) m₁ (by
    have := Nat.mul_le_mul_left m₁ (show 2 * nGrind ≤ 4 * nGrind by omega); exact this)
  have g2 := grind_le (m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind)) (m₁ + m₂ + m₃) (by
    have h1 := Nat.mul_le_mul_left m₁ (show 2 * nGrind ≤ 4 * nGrind by omega)
    have h2 := Nat.mul_le_mul_left (m₂ + m₃) (show 2 * nGrind ≤ 4 * nGrind by omega)
    calc m₁ * (2 * nGrind) + (m₂ + m₃) * (2 * nGrind) ≤ m₁ * (4 * nGrind) + (m₂ + m₃) * (4 * nGrind) :=
          Nat.add_le_add h1 h2
      _ = (m₁ + m₂ + m₃) * (4 * nGrind) := by ring)
  have g3 := grind_le (m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind))) (m₁ + m₂ + m₃) (by
    have h1 := Nat.mul_le_mul_left m₁ (show 2 * nGrind ≤ 4 * nGrind by omega)
    calc m₁ * (2 * nGrind) + 2 * ((m₂ + m₃) * (2 * nGrind)) ≤
          m₁ * (4 * nGrind) + (m₂ + m₃) * (4 * nGrind) := by
            refine Nat.add_le_add h1 (le_of_eq ?_); ring
      _ = (m₁ + m₂ + m₃) * (4 * nGrind) := by ring)
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have h1 : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ m₃ := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ m₄ := Nat.cast_nonneg _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
    have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  generalize (2 : ℝ) ^ 1024 = κ at hK g1 g2 g3 u1 u2 u3 h
  unfold εROP εRO at h u1 u2 u3
  push_cast at h u1 u2 u3 g1 g2 g3 ⊢
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸¹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityAd_lean_2pow20 (A : AdversaryAdR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : m₁ + m₂ + m₃ + m₄ + 2 ≤ 2 ^ 20) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk)) (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk))
          (realGameAdR A b₁' b₂')| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityAd_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((m₁ + m₂ + m₃ + m₄ + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + m₄ + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityAd_lean_2pow32 (A : AdversaryAdR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdR m₁ m₂ m₃ m₄) b₁ b₂ K,
      hidingAdv (A.atH c (A.hist₁ c K.2.2)).ctx
        (reductionRA (A.atH c (A.hist₁ c K.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : m₁ + m₂ + m₃ + m₄ + 2 ≤ 2 ^ 32) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk)) (realGameAdR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × TapesAdR m₁ m₂ m₃ m₄) × ShR (Blk → Blk))
          (realGameAdR A b₁' b₂')| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityAd_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((m₁ + m₂ + m₃ + m₄ + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + m₄ + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Ratatouille
