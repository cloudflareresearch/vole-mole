import VoleMole.Privacy.MoussakaRAK
import VoleMole.Privacy.MoussakaMany

/-!
# Moussaka issuer hiding and unlinkability with adaptively scheduled sessions

`Privacy/MoussakaMany.lean` has any number of further honest Clients in one concurrent schedule:
their issuance requests come before the adversary's first answer, their redemptions are seen only
by the guess. Here the colluding adversary (every Anchor and the Moderator) **starts further
sessions after seeing earlier sessions' outcomes**: before the challenge, between the challenge
issuance requests and the challenge responses, and after the challenge outcome. Each further
session's contexts and issuing key (`CfgX`), and the adversary's response to it and its Anchor Set
and digest (`AnsX`), are chosen from everything seen so far (all earlier requests and outcomes);
the challenge contexts and keys from the sessions before the challenge.

## A whole session is a consistent table reader

A further session run to the end (`fullXM`: the issuance request, then `finalize_issue` on the
adversary's response and `redeem_request` at the Client's own index in the chosen Anchor Set)
reads, through its issuance proof and its redemption proof, `H₅` at `2·624` keys, the cipher at
`2·4607` and `H₂³` at the `2·2³²` grinding points of its two prefixes, consistently: the issuance
request is `issX_req_sreads`, the redemption a consistent reader at the statement the request and
the adversary's answer fix (`redX_sreads`, from `ZK.Sim.realRO_sreads`; no proof if the token does
not finalize or the Client's check fails). So `fullXM_sreads`, and sequential sessions compose
(`runSeqM_sreads`).

## The game and the reduction

`AdversaryAdM`, `realGameAdM`: `m₁` further sessions before the challenge, then the challenge
contexts and keys from them, the two challenge issuance requests, `m₂` further sessions, the
challenge responses and Anchor Sets, the challenge outcome (§6's rule: both redemptions or none),
`m₃` further sessions, the guess. For each tape `c` of the further sessions the game is the game
with a table-reading key stage (`Privacy/MoussakaRAK.lean`) of the adversary `A.red idx c` whose key
stage runs the sessions before the challenge, whose interaction runs those in between and whose
guess runs those after (`realGameAdM_iff`, `Iff.rfl`): key stage `KBudget (0, m₁·2·2³², m₁·1248,
m₁·9214)` (`red_kBudget`), interaction `IBudget (0, m₂·2·2³², m₂·1248, m₂·9214)` (`red_iBudget`),
guess `(q₃, q₅ + (m₂ + m₃)·1248, q_E + (m₂ + m₃)·9214)` (`red_gBudget`).

## The bound

`anonymityRAK_lean_numG` for every `c`, averaged over `c`: `anonymityAd_lean_numG` (every row
type), `anonymityAd_lean_num` (function rows), `anonymityAd_lean_num_perm`; in numbers
(`anonymityAd_lean_le`) `≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` for
`n = m₁ + m₂ + m₃ + 2` Clients in all: `≤ 2⁻⁸² + 2·εhide` for `n ≤ 2²⁰`
(`anonymityAd_lean_2pow20`), `≤ 2⁻⁷⁰ + 2·εhide` for `n ≤ 2³²` (`anonymityAd_lean_2pow32`), plus the
guess's budget terms. The `H₂³` reads are counted by keys: each costs `2·2⁻¹⁰²⁴` (the simulated
block's `128`-byte `ã`), so no prefix count is needed (unlike PomFRIT's `16`-byte `ã`,
`Privacy/PomFRITAdaptivePfx.lean`). Hiding of `Com` is assumed for the reductions of every
`A.red idx c` (the further sessions' tapes fixed).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]

/-! ## A whole further session -/

section Full

variable (ci cr : Bytes)

/-- A further Client's pending token does not read the tables. -/
lemma issX_fst (x : TIr) (s : ShM R) :
    (issX ci cr x s).1 = ⟨List.ofFn x.1.1, List.ofFn x.1.2, ci, cr,
      com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2)⟩ := rfl

/-- **A further Client's redemption is a consistent reader** of `H₅`, the cipher and `H₂³`
(`ZK.Sim.realRO_sreads` at the redemption statement), for contexts and a pending token of the
right lengths: no proof is computed unless the token finalizes and the Client's check passes, and
then the witness is in `RedeemRelW`. -/
theorem redX_sreads (hci : ci.length = ctxBytes) (hcr : cr.length = ctxBytes)
    (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken) (hn : i.nf.length = nfBytes)
    (hr : i.r.length = rBytes) (resp : Coins uovN) (S : AnchorSet × Bytes) (y : TRr) :
    SReads pR (fun t : Tb R pR => redX ci cr idx pk i resp S y t.2) 0 nGrind 624 4607 := by
  rcases hf : finalizeIssue pk i (List.ofFn resp) with _ | tok
  · have e : (fun t : Tb R pR => redX ci cr idx pk i resp S y t.2) =
        fun _ => (.error .invalidToken : Except Error Bytes) := by
      funext t
      simp only [redX, hf]
    rw [e]
    exact (SReads.const _).mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have htk : tok = ⟨i.nf, i.r, List.ofFn resp⟩ := by
    unfold finalizeIssue at hf
    split_ifs at hf
    exact (Option.some.inj hf).symm
  subst htk
  rcases hk : S.1.keys[idx S.1 pk]? with _ | pk'
  · have e : (fun t : Tb R pR => redX ci cr idx pk i resp S y t.2) =
        fun _ => (.error .indexOutOfRange : Except Error Bytes) := by
      funext t
      simp only [redX, hf, redeemRequestOf, hk]
    rw [e]
    exact (SReads.const _).mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  by_cases he : pk'.eval (List.ofFn resp) = com i.nf ci cr i.r
  · have hrel : RedeemRelW ⟨S.1.keys, i.nf, ci, cr, S.2⟩
        (encodeRedeemWitness i.nf ci cr i.r (List.ofFn resp) (idx S.1 pk)) :=
      ⟨⟨_, _, _, pk', hr, List.length_ofFn, hk, rfl, he⟩, S.1.valid.2.1, hn, hci, hcr⟩
    have h := (realRO_sreads (R := R) (zkHypR _ _ hrel) hashesWF_shake hlab_pR y.1 y.2).map
      fun o => (Except.ok (i.nf ++ toL (o.toOption.getD .empty)) : Except Error Bytes)
    refine (congrArg (fun F => SReads pR F 0 nGrind 624 4607) (funext fun t => ?_)).mp h
    simp only [redX, hf, redeemRequestOf, nizkAt, hk, he, ↓reduceIte, leanPR, realRO, toBA_ofFn]
    rfl
  · have e : (fun t : Tb R pR => redX ci cr idx pk i resp S y t.2) =
        fun _ => (.error .invalidToken : Except Error Bytes) := by
      funext t
      simp only [redX, hf, redeemRequestOf, hk, he, ↓reduceIte]
    rw [e]
    exact (SReads.const _).mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- A reader of the shared tables for the redemption parameters is one for the issuance
parameters (the two have the same prefix length, so the tables are the same). -/
lemma SReads.pR_pI {X : Type} {f : ShM R → X} {a3 a2 a5 aE : ℕ}
    (h : SReads pR (fun t : Tb R pR => f t.2) a3 a2 a5 aE) :
    SReads pI (fun t : Tb R pI => f t.2) a3 a2 a5 aE := h

/-- **A further session's configuration**: its contexts and the issuing key. -/
abbrev CfgX := Coins ctxBytes × Coins ctxBytes × UOVKey

/-- **The adversary's answer to a further Client's issuance request**: the response, and the
Anchor Set and digest of the Client's redemption. -/
abbrev AnsX := Coins uovN × (AnchorSet × Bytes)

/-- What the adversary has seen of a finished further session: its issuance request and its
redemption request. -/
abbrev HistM := Bytes × Except Error Bytes

/-- **A further session run to the end**: its issuance request, and its redemption on the
adversary's answer `ρ` to that request. -/
noncomputable def fullXM (idx : AnchorSet → UOVKey → ℕ) (k : CfgX) (ρ : Bytes → AnsX) (x : XC)
    (s : ShM R) : HistM :=
  ((issX (List.ofFn k.1) (List.ofFn k.2.1) x.1 s).2,
    redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2 (issX (List.ofFn k.1) (List.ofFn k.2.1) x.1 s).1
      (ρ (issX (List.ofFn k.1) (List.ofFn k.2.1) x.1 s).2).1
      (ρ (issX (List.ofFn k.1) (List.ofFn k.2.1) x.1 s).2).2 x.2 s)

/-- **A whole further session is a consistent reader** of `H₅` (`2·624` keys), the cipher
(`2·4607`) and `H₂³` (the grinding points of its two prefixes), and of no slice key. -/
theorem fullXM_sreads (idx : AnchorSet → UOVKey → ℕ) (k : CfgX) (ρ : Bytes → AnsX) (x : XC) :
    SReads pI (fun t : Tb R pI => fullXM idx k ρ x t.2) 0 (2 * nGrind) 1248 9214 := by
  have h := (issX_req_sreads (R := R) (List.ofFn k.1) (List.ofFn k.2.1) List.length_ofFn
    List.length_ofFn x.1).bind
    (g := fun q (t : Tb R pI) => (q, redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2
      ⟨List.ofFn x.1.1.1, List.ofFn x.1.1.2, List.ofFn k.1, List.ofFn k.2.1,
        com (List.ofFn x.1.1.1) (List.ofFn k.1) (List.ofFn k.2.1) (List.ofFn x.1.1.2)⟩
      (ρ q).1 (ρ q).2 x.2 t.2))
    fun q => SReads.pR_pI (f := fun s => (q, redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2
      ⟨List.ofFn x.1.1.1, List.ofFn x.1.1.2, List.ofFn k.1, List.ofFn k.2.1,
        com (List.ofFn x.1.1.1) (List.ofFn k.1) (List.ofFn k.2.1) (List.ofFn x.1.1.2)⟩
      (ρ q).1 (ρ q).2 x.2 s)) ((redX_sreads (R := R) (List.ofFn k.1) (List.ofFn k.2.1) List.length_ofFn
      List.length_ofFn idx k.2.2 ⟨List.ofFn x.1.1.1, List.ofFn x.1.1.2, List.ofFn k.1, List.ofFn k.2.1,
        com (List.ofFn x.1.1.1) (List.ofFn k.1) (List.ofFn k.2.1) (List.ofFn x.1.1.2)⟩ List.length_ofFn
      List.length_ofFn (ρ q).1 (ρ q).2 x.2).map fun o => (q, o))
  exact h.mono le_rfl (by omega) (by omega) (by omega)

/-- **Further sessions one after the other**: each one's configuration (`next`) and the
adversary's answer to its request (`resp`) are chosen from the sessions before it, each session
runs to the end on the tables with its own tape. -/
noncomputable def runSeqM (idx : AnchorSet → UOVKey → ℕ) (next : List HistM → CfgX)
    (resp : List HistM → Bytes → AnsX) : List XC → List HistM → ShM R → List HistM
  | [], H, _ => H
  | x :: cs, H, s => runSeqM idx next resp cs (H ++ [fullXM idx (next H) (resp H) x s]) s

/-- **Sequential sessions are a consistent reader**: `|cs|` times a session's keys. -/
theorem runSeqM_sreads (idx : AnchorSet → UOVKey → ℕ) (next : List HistM → CfgX)
    (resp : List HistM → Bytes → AnsX) (cs : List XC) :
    ∀ H, SReads pI (fun t : Tb R pI => runSeqM idx next resp cs H t.2) 0 (cs.length * (2 * nGrind))
      (cs.length * 1248) (cs.length * 9214) := by
  induction cs with
  | nil => intro H; simpa [runSeqM] using SReads.const (R := R) (p := pI) H
  | cons x cs ih =>
    intro H
    have h := (fullXM_sreads (R := R) idx (next H) (resp H) x).bind
      (g := fun y (t : Tb R pI) => runSeqM idx next resp cs (H ++ [y]) t.2) fun y => ih (H ++ [y])
    refine (h.mono le_rfl ?_ ?_ ?_)
    · simp only [List.length_cons]; exact le_of_eq (by ring)
    · simp only [List.length_cons]; exact le_of_eq (by ring)
    · simp only [List.length_cons]; exact le_of_eq (by ring)

end Full

/-! ## The adaptive game -/

section Game

variable {m₁ m₂ m₃ : ℕ}

/-- **The colluding adversary of the adaptive game**: before the challenge, `m₁` further sessions
one after the other (`next₁`, `resp₁`: each session's configuration and the answer to its request
from the earlier sessions); then the challenge contexts and keys from all of them; after the two
challenge issuance requests, `m₂` further sessions (`next₂`, `resp₂`, also seeing the challenge
requests); the challenge responses and Anchor Sets from everything so far; after the challenge
outcome, `m₃` further sessions (`next₃`, `resp₃`); and a guess that sees everything, the challenge
slices and the tables. The interaction does not read the tables itself (the further sessions it
runs do). -/
structure AdversaryAdM (R : Type) where
  next₁ : List HistM → CfgX
  resp₁ : List HistM → Bytes → AnsX
  ctxIss : List HistM → Coins ctxBytes
  ctxRed : List HistM → Coins ctxBytes
  pk : List HistM → Bool → UOVKey
  next₂ : List HistM → Bytes → Bytes → List HistM → CfgX
  resp₂ : List HistM → Bytes → Bytes → List HistM → Bytes → AnsX
  respond : List HistM → Bytes → Bytes → List HistM → Bool → Coins uovN
  choose : List HistM → Bytes → Bytes → List HistM → Bool → AnchorSet × Bytes
  next₃ : List HistM → Bytes → Bytes → List HistM →
    Option (Except Error Bytes × Except Error Bytes) → List HistM → CfgX
  resp₃ : List HistM → Bytes → Bytes → List HistM →
    Option (Except Error Bytes × Except Error Bytes) → List HistM → Bytes → AnsX
  guess : List HistM → Bytes → Bytes → List HistM →
    Option (Except Error Bytes × Except Error Bytes) → List HistM → Slices → ShM R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` freely. -/
structure AdversaryAdM.Budget (A : AdversaryAdM R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ H₁ q₀ q₁ H₂ y H₃ (g₁ gL gR : Tab3) s,
    Rd3 (fun g => A.guess H₁ q₀ q₁ H₂ y H₃ ((g, g₁), (gL, gR)) s) q3
  h31 : ∀ H₁ q₀ q₁ H₂ y H₃ (g₀ gL gR : Tab3) s,
    Rd3 (fun g => A.guess H₁ q₀ q₁ H₂ y H₃ ((g₀, g), (gL, gR)) s) q3
  h3L : ∀ H₁ q₀ q₁ H₂ y H₃ (g₀ g₁ gR : Tab3) s,
    Rd3 (fun g => A.guess H₁ q₀ q₁ H₂ y H₃ ((g₀, g₁), (g, gR)) s) q3
  h3R : ∀ H₁ q₀ q₁ H₂ y H₃ (g₀ g₁ gL : Tab3) s,
    Rd3 (fun g => A.guess H₁ q₀ q₁ H₂ y H₃ ((g₀, g₁), (gL, g)) s) q3
  h5 : ∀ H₁ q₀ q₁ H₂ y H₃ sl, Rd5 (A.guess H₁ q₀ q₁ H₂ y H₃ sl) q5
  hE : ∀ H₁ q₀ q₁ H₂ y H₃ sl, RdE (A.guess H₁ q₀ q₁ H₂ y H₃ sl) qE

/-- The further sessions' tapes, stage by stage. -/
abbrev TapesAdM (m₁ m₂ m₃ : ℕ) := (Fin m₁ → XC) × (Fin m₂ → XC) × (Fin m₃ → XC)

namespace AdversaryAdM

variable (A : AdversaryAdM R) (idx : AnchorSet → UOVKey → ℕ) (c : TapesAdM m₁ m₂ m₃)

/-- The sessions before the challenge. -/
noncomputable def hist₁ (s : ShM R) : List HistM := runSeqM idx A.next₁ A.resp₁ (List.ofFn c.1) [] s

/-- The sessions between the challenge requests and the challenge responses. -/
noncomputable def hist₂ (H₁ : List HistM) (q₀ q₁ : Bytes) (s : ShM R) : List HistM :=
  runSeqM idx (A.next₂ H₁ q₀ q₁) (A.resp₂ H₁ q₀ q₁) (List.ofFn c.2.1) [] s

/-- The sessions after the challenge outcome. -/
noncomputable def hist₃ (H₁ : List HistM) (q₀ q₁ : Bytes) (H₂ : List HistM)
    (y : Option (Except Error Bytes × Except Error Bytes)) (s : ShM R) : List HistM :=
  runSeqM idx (A.next₃ H₁ q₀ q₁ H₂ y) (A.resp₃ H₁ q₀ q₁ H₂ y) (List.ofFn c.2.2) [] s

/-- **The table-reading adversary at the state `H₁`** (the sessions before the challenge): its
contexts and keys from `H₁`, its interaction runs the sessions between the challenge requests and
responses, its guess also those after the challenge outcome. -/
noncomputable def atH (H₁ : List HistM) : AdversaryRA R where
  ctxIss := A.ctxIss H₁
  ctxRed := A.ctxRed H₁
  pk := A.pk H₁
  respond q₀ q₁ i _ u := A.respond H₁ q₀ q₁ (A.hist₂ idx c H₁ q₀ q₁ u) i
  choose q₀ q₁ side _ u := A.choose H₁ q₀ q₁ (A.hist₂ idx c H₁ q₀ q₁ u) side
  guess q₀ q₁ y sl v := A.guess H₁ q₀ q₁ (A.hist₂ idx c H₁ q₀ q₁ v) y
    (A.hist₃ idx c H₁ q₀ q₁ (A.hist₂ idx c H₁ q₀ q₁ v) y v) sl v

/-- **The reduction**: the adversary with a table-reading key stage that runs the further sessions
itself, with their tapes `c` fixed. Its key stage runs the sessions before the challenge. -/
noncomputable def red : AdversaryRAK R (List HistM) :=
  ⟨fun _ s => A.hist₁ idx c s, A.atH idx c⟩

/-- The challenge interaction at the state `H₁`, the requests `q₀`, `q₁` and the sessions `H₂`. -/
def chalAdv (H₁ : List HistM) (q₀ q₁ : Bytes) (H₂ : List HistM) : Adversary :=
  ⟨A.ctxIss H₁, A.ctxRed H₁, A.pk H₁,
    fun _ _ c => bif c then A.respond H₁ q₀ q₁ H₂ true else A.respond H₁ q₀ q₁ H₂ false,
    fun _ _ side => bif side then A.choose H₁ q₀ q₁ H₂ true else A.choose H₁ q₀ q₁ H₂ false,
    fun _ _ _ => True⟩

end AdversaryAdM

/-- **The adaptive game** in world `b`: the further sessions before the challenge, the challenge
contexts and keys from them, the challenge issuance requests (the Lean prover on the shared
tables), the further sessions in between, the challenge responses, Anchor Sets and outcome (§6's
rule: Client `b`'s token redeemed on the left and Client `¬b`'s on the right, or none), the further
sessions after, and the guess. -/
noncomputable def realGameAdM (A : AdversaryAdM R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool)
    (z : (PT × TapesAdM m₁ m₂ m₃) × ShM R) : Prop :=
  let H₁ := A.hist₁ idx z.1.2 z.2
  let q₀ := (issX (List.ofFn (A.ctxIss H₁)) (List.ofFn (A.ctxRed H₁)) z.1.1.1.1 z.2).2
  let q₁ := (issX (List.ofFn (A.ctxIss H₁)) (List.ofFn (A.ctxRed H₁)) z.1.1.1.2 z.2).2
  let H₂ := A.hist₂ idx z.1.2 H₁ q₀ q₁ z.2
  let y := outAt (A.chalAdv H₁ q₀ q₁ H₂) idx b z.1.1 z.2
  A.guess H₁ q₀ q₁ H₂ y (A.hist₃ idx z.1.2 H₁ q₀ q₁ H₂ y z.2) (slOf z.1.1) z.2

/-- **The adaptive game is the game with a table-reading key stage of the reduction**, tape by
tape. -/
theorem realGameAdM_iff (A : AdversaryAdM R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT)
    (c : TapesAdM m₁ m₂ m₃) (s : ShM R) :
    realGameAdM A idx b ((x, c), s) ↔ realGameRAK (A.red idx c) idx leanPI leanPR b (x, s) :=
  Iff.rfl

namespace AdversaryAdM

variable (A : AdversaryAdM R) (idx : AnchorSet → UOVKey → ℕ) (c : TapesAdM m₁ m₂ m₃)

/-- **The reduction's key-stage budget**: the `m₁` sessions before the challenge. -/
theorem red_kBudget :
    (A.red idx c).KBudget 0 (m₁ * (2 * nGrind)) (m₁ * 1248) (m₁ * 9214) := by
  have h := runSeqM_sreads (R := R) idx A.next₁ A.resp₁ (List.ofFn c.1) []
  simp only [List.length_ofFn] at h
  exact ⟨fun _ _ _ => h, fun _ _ _ => h, fun _ _ _ => h, fun _ _ _ => h⟩

/-- **The reduction's interaction budget**: the `m₂` sessions between the challenge requests and
responses. -/
theorem red_iBudget :
    (A.red idx c).IBudget 0 (m₂ * (2 * nGrind)) (m₂ * 1248) (m₂ * 9214) := by
  intro H₁
  have h (q₀ q₁ : Bytes) := (runSeqM_sreads (R := R) idx (A.next₂ H₁ q₀ q₁) (A.resp₂ H₁ q₀ q₁)
    (List.ofFn c.2.1) []).map fun H₂ =>
      ((A.respond H₁ q₀ q₁ H₂ false, A.respond H₁ q₀ q₁ H₂ true),
        (A.choose H₁ q₀ q₁ H₂ false, A.choose H₁ q₀ q₁ H₂ true))
  simp only [List.length_ofFn] at h
  exact ⟨fun q₀ q₁ _ _ _ => h q₀ q₁, fun q₀ q₁ _ _ _ => h q₀ q₁, fun q₀ q₁ _ _ _ => h q₀ q₁,
    fun q₀ q₁ _ _ _ => h q₀ q₁⟩

/-- **The reduction's guess budget**: the adversary's plus the `m₂ + m₃` sessions after the
challenge requests. -/
theorem red_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.red idx c).GBudget q3 (m₂ * 1248 + (m₃ * 1248 + q5)) (m₂ * 9214 + (m₃ * 9214 + qE)) := by
  intro H₁ tr
  refine
    { h30 := fun q₀ q₁ y g₁ gL gR s => hA.h30 _ _ _ _ _ _ g₁ gL gR s
      h31 := fun q₀ q₁ y g₀ gL gR s => hA.h31 _ _ _ _ _ _ g₀ gL gR s
      h3L := fun q₀ q₁ y g₀ g₁ gR s => hA.h3L _ _ _ _ _ _ g₀ g₁ gR s
      h3R := fun q₀ q₁ y g₀ g₁ gL s => hA.h3R _ _ _ _ _ _ g₀ g₁ gL s
      h5 := fun q₀ q₁ y sl => ?_
      hE := fun q₀ q₁ y sl => ?_ }
  · have h2 := (runSeqM_sreads (R := R) idx (A.next₂ H₁ q₀ q₁) (A.resp₂ H₁ q₀ q₁)
      (List.ofFn c.2.1) []).rd5 default
    simp only [List.length_ofFn] at h2
    exact Rd5.bindEq (m := fun s => A.hist₂ idx c H₁ q₀ q₁ s)
      (f := fun H₂ s => A.guess H₁ q₀ q₁ H₂ y (A.hist₃ idx c H₁ q₀ q₁ H₂ y s) sl s)
      (fun _ => rfl) h2 fun H₂ => by
        have h3 := (runSeqM_sreads (R := R) idx (A.next₃ H₁ q₀ q₁ H₂ y) (A.resp₃ H₁ q₀ q₁ H₂ y)
          (List.ofFn c.2.2) []).rd5 default
        simp only [List.length_ofFn] at h3
        exact Rd5.bindEq (m := fun s => A.hist₃ idx c H₁ q₀ q₁ H₂ y s)
          (f := fun H₃ s => A.guess H₁ q₀ q₁ H₂ y H₃ sl s) (fun _ => rfl) h3
          fun H₃ => hA.h5 _ _ _ _ _ _ _
  · have h2 := (runSeqM_sreads (R := R) idx (A.next₂ H₁ q₀ q₁) (A.resp₂ H₁ q₀ q₁)
      (List.ofFn c.2.1) []).rdE default
    simp only [List.length_ofFn] at h2
    exact RdE.bindEq (m := fun s => A.hist₂ idx c H₁ q₀ q₁ s)
      (f := fun H₂ s => A.guess H₁ q₀ q₁ H₂ y (A.hist₃ idx c H₁ q₀ q₁ H₂ y s) sl s)
      (fun _ => rfl) h2 fun H₂ => by
        have h3 := (runSeqM_sreads (R := R) idx (A.next₃ H₁ q₀ q₁ H₂ y) (A.resp₃ H₁ q₀ q₁ H₂ y)
          (List.ofFn c.2.2) []).rdE default
        simp only [List.length_ofFn] at h3
        exact RdE.bindEq (m := fun s => A.hist₃ idx c H₁ q₀ q₁ H₂ y s)
          (f := fun H₃ s => A.guess H₁ q₀ q₁ H₂ y H₃ sl s) (fun _ => rfl) h3
          fun H₃ => hA.hE _ _ _ _ _ _ _

end AdversaryAdM

/-- The adaptive tape, with the further sessions' tapes first. -/
def tapeAdM : TapesAdM m₁ m₂ m₃ × (PT × ShM R) ≃ (PT × TapesAdM m₁ m₂ m₃) × ShM R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {m₁ m₂ m₃ : ℕ}

/-- **Theorem 4(a) with adaptively scheduled further sessions, for every type of cipher rows**
(`ZKRow R`, `ZKPRow R`; SHAKE as the base record): with `m₁` further sessions before the
challenge, `m₂` between the challenge issuance requests and the challenge responses and `m₃`
after the challenge outcome, each started after the adversary has seen the earlier ones' outcomes,
the bound of `anonymityRAK_lean_numG` at the key-stage budget `(0, 2·2³²m₁, 1248m₁, 9214m₁)`, the
interaction budget `(0, 2·2³²m₂, 1248m₂, 9214m₂)` and the guess budget
`(q₃, q₅ + 1248(m₂ + m₃), q_E + 9214(m₂ + m₃))` (for the reduction that runs the further sessions,
averaged over their tapes). -/
theorem anonymityAd_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryAdM R) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM R) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM R) (realGameAdM A idx true)| ≤
      4 * εAdG R pI 9 (0 + q3) (m₂ * 1248 + (m₃ * 1248 + q5) + m₂ * 1248 + 1872)
          (m₂ * 9214 + (m₃ * 9214 + qE) + m₂ * 9214 + 13821) 0 (m₁ * (2 * nGrind)) (m₁ * 1248)
          (m₁ * 9214) +
        4 * εAdG R pR 9 q3 (m₂ * 1248 + (m₃ * 1248 + q5) + 1248)
          (m₂ * 9214 + (m₃ * 9214 + qE) + 13821) (0 + 0) (m₁ * (2 * nGrind) + m₂ * (2 * nGrind))
          (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          ZKPRow.εP R pR 0 312 4607 (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeAdM, ← pr_equiv tapeAdM]
  exact abs_pr_prod_sub_le _ _ fun c =>
    anonymityRAK_lean_numG (A.red idx c) idx (A.red_gBudget idx c hA) (A.red_iBudget idx c)
      (A.red_kBudget idx c) (hhide c)

/-- **Theorem 4(a) with adaptively scheduled further sessions** (function rows). -/
theorem anonymityAd_lean_num (A : AdversaryAdM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx true)| ≤
      4 * εAd 9 (0 + q3) (m₂ * 1248 + (m₃ * 1248 + q5) + m₂ * 1248 + 1872)
          (m₂ * 9214 + (m₃ * 9214 + qE) + m₂ * 9214 + 13821) 0 (m₁ * (2 * nGrind)) (m₁ * 1248)
          (m₁ * 9214) +
        4 * εAd 9 q3 (m₂ * 1248 + (m₃ * 1248 + q5) + 1248)
          (m₂ * 9214 + (m₃ * 9214 + qE) + 13821) (0 + 0) (m₁ * (2 * nGrind) + m₂ * (2 * nGrind))
          (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROP 0 312 4607 (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityAd_lean_numG A idx hA hhide

/-- **Theorem 4(a) with adaptively scheduled further sessions and AES as uniformly random
permutations.** -/
theorem anonymityAd_lean_num_perm (A : AdversaryAdM (Equiv.Perm Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Equiv.Perm Blk)) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Equiv.Perm Blk)) (realGameAdM A idx true)| ≤
      4 * εAdPm pI 9 (0 + q3) (m₂ * 1248 + (m₃ * 1248 + q5) + m₂ * 1248 + 1872)
          (m₂ * 9214 + (m₃ * 9214 + qE) + m₂ * 9214 + 13821) 0 (m₁ * (2 * nGrind)) (m₁ * 1248)
          (m₁ * 9214) +
        4 * εAdPm pR 9 q3 (m₂ * 1248 + (m₃ * 1248 + q5) + 1248)
          (m₂ * 9214 + (m₃ * 9214 + qE) + 13821) (0 + 0) (m₁ * (2 * nGrind) + m₂ * (2 * nGrind))
          (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROPmP pR 0 312 4607 (m₁ * 1248 + m₂ * 1248 + 624) (m₁ * 9214 + m₂ * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityAd_lean_numG A idx hA hhide

/-- **The adaptive bound in numbers**: with `n = m₁ + m₂ + m₃ + 2` Clients in all,

    |Pr[W₀] − Pr[W₁]| ≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide.

(Per session `≈ 0.61·2⁻¹⁰²` before the challenge, `≈ 0.73·2⁻¹⁰²` in between, `≈ 0.24·2⁻¹⁰²`
after; the constant is `≈ 1.53·2⁻¹⁰²`.) -/
theorem anonymityAd_lean_le (A : AdversaryAdM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx true)| ≤
      (m₁ + m₂ + m₃ + 2 : ℕ) / 2 ^ 102 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityAd_lean_num A idx hA hhide
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have h1 : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ m₃ := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : ∀ m : ℕ, (m : ℝ) * (nGrind : ℝ) / 2 ^ 1024 ≤ m / 2 ^ 128 := fun m => by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc (m : ℝ) * 2 ^ 32 * 2 ^ 128 = ((m : ℝ) * 2 ^ 128) * 2 ^ 32 := mul_right_comm _ _ _
      _ ≤ ((m : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hp.le)
      _ = (m : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  unfold εAd h23Term at h
  generalize (2 : ℝ) ^ 1024 = κ at h hK hG
  have hGa : (m₁ : ℝ) * (2 * (nGrind : ℝ)) / κ ≤ 2 * m₁ / 2 ^ 128 := by
    have := hG m₁
    rw [show (m₁ : ℝ) * (2 * (nGrind : ℝ)) / κ = 2 * ((m₁ : ℝ) * nGrind / κ) by ring,
      show (2 : ℝ) * m₁ / 2 ^ 128 = 2 * (m₁ / 2 ^ 128) by ring]
    linarith
  have hGb : ((m₁ : ℝ) * (2 * (nGrind : ℝ)) + (m₂ : ℝ) * (2 * (nGrind : ℝ))) / κ ≤
      2 * (m₁ + m₂) / 2 ^ 128 := by
    have := hG m₁
    have := hG m₂
    rw [show ((m₁ : ℝ) * (2 * (nGrind : ℝ)) + (m₂ : ℝ) * (2 * (nGrind : ℝ))) / κ =
        2 * ((m₁ : ℝ) * nGrind / κ) + 2 * ((m₂ : ℝ) * nGrind / κ) by ring,
      show (2 : ℝ) * (m₁ + m₂) / 2 ^ 128 = 2 * (m₁ / 2 ^ 128) + 2 * (m₂ / 2 ^ 128) by ring]
    linarith
  split_ifs at h <;>
  · unfold εROP εRO at h
    push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸² + 2·εhide` plus the guess's budget terms. -/
theorem anonymityAd_lean_2pow20 (A : AdversaryAdM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 20) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx true)| ≤
      1 / 2 ^ 82 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityAd_lean_le A idx hA hhide
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 82 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁷⁰ + 2·εhide` plus the guess's budget terms. -/
theorem anonymityAd_lean_2pow32 (A : AdversaryAdM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : TapesAdM m₁ m₂ m₃) b cc,
      hidingAdv (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atH idx c (A.hist₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atH idx c (A.hist₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 32) :
    |pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx false) -
        pr ((PT × TapesAdM m₁ m₂ m₃) × ShM (Blk → Blk)) (realGameAdM A idx true)| ≤
      1 / 2 ^ 70 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityAd_lean_le A idx hA hhide
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 70 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Moussaka
