import VoleMole.Privacy.PermRA
import VoleMole.ZK.ReadsMany

/-!
# Moussaka issuer hiding and unlinkability with many sessions

The games of `Privacy/MoussakaRO.lean` and `Privacy/MoussakaRA.lean` have two Clients: the
challenge pair. Here the colluding adversary (every Anchor and the Moderator) also serves **any
number of further honest Clients**, on the same tables.

## The game

`AdversaryN`: contexts and the two challenge Clients' issuing keys as before, an issuing key for
each further Client `j : ι`; after seeing **every** issuance request (the two challenge Clients'
and the further Clients') it answers every Client (`respond`, `respondX`) and chooses, for each
challenge side and for each further Client, an Anchor Set and a challenge digest (`choose`,
`chooseX`). Each further Client finalizes its token and redeems it at its index in its set (the
Client's index rule `idx`), with the Lean prover on the shared tables and its own randomness and
`H₃` slices (`issX`, `redX`); the challenge redemptions follow §6's rule as before. The guess sees
all issuance requests, the challenge redemptions (or the refusal), every further Client's
redemption, all slices and the tables, with a budget (`AdversaryN.Budget`); the interaction does
not read the tables.

**`realGameN`** is the two-session game with a table-reading interaction (`realGameRA`) for the
adversary composed with the further Clients (`AdversaryN.withClients idx c`, `c` their tapes): its
interaction computes the further Clients' issuance requests on the tables the game runs on, its
guess their redemptions.

## The bound

For each fixed `c`, `anonymityRA_lean_numG` applies to `A.withClients idx c`; averaging over `c`
(`abs_pr_prod_sub_le`) gives `anonymityN_lean_numG`. The budgets are the further Clients' reads:

* a further Client's issuance request is a **consistent** reader (`ZK.Sim.realRO_sreads`) of `H₅`
  (`624` keys), the cipher (`4607`) and `H₂³` (the `nGrind = 2³²` grinding points of its prefix),
  so the interaction has budget `IBudget 0 (2³²·m) (624·m) (4607·m)` (`withClients_iBudget`);
* a further Client's issuance and redemption read `H₅` at `624` and the cipher at `4607` keys each,
  so the guess has budget `(q₃, q₅ + 2·624·m, q_E + 2·4607·m)` (`withClients_gBudget`).

**`anonymityN_lean_num`** (function rows): the bound of `anonymityRA_lean_num` with `i₃ = 0`,
`i₂ = 2³²m`, `i₅ = 624m`, `i_E = 4607m` and the guess's budget raised by `2·624m`, `2·4607m`;
linear in `m`. In numbers (`anonymityN_lean_le`): `≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
2·εhide` with `n = m + 2` Clients in all, so `≤ 2⁻⁸² + 2·εhide` for `n ≤ 2²⁰`
(`anonymityN_lean_2pow20`) and `≤ 2⁻⁷⁰ + 2·εhide` for `n ≤ 2³²` (`anonymityN_lean_2pow32`), plus the guess's budget terms. With AES as random
permutations: `anonymityN_lean_num_perm`.

Hiding of `Com` is assumed, as in `anonymityRA_lean_num`, for the explicit reductions of every
`A.withClients idx c` (the further Clients' tapes fixed: a non-uniform reduction).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]

/-! ## A further honest Client on the tables, and what it reads -/

section Honest

/-- A further Client's tape: its issuance tape (`(nf, r)`, `ρ_iss`, its `H₃` slice) and its
redemption tape (`ρ_red`, its slice). -/
abbrev XC := TIr × TRr

variable (ci cr : Bytes)

/-- **A further Client's issuance request** on the tables (`issue_request` with the Lean prover). -/
noncomputable def issX (x : TIr) (s : ShM R) : PendingToken × Bytes :=
  issueRequestOf (nizkAt leanPI x.2.2 s) ci cr (List.ofFn x.1.1) (List.ofFn x.1.2) (List.ofFn x.2.1)

/-- **A further Client's redemption** on the tables: `finalize_issue` on the Anchor's response,
then `redeem_request` at the Client's own index in the Anchor Set (an error if the token did not
finalize). -/
noncomputable def redX (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken)
    (resp : Coins uovN) (S : AnchorSet × Bytes) (y : TRr) (s : ShM R) : Except Error Bytes :=
  match finalizeIssue pk i (List.ofFn resp) with
  | none => .error .invalidToken
  | some tok => redeemRequestOf (nizkAt leanPR y.2 s) tok S.1 (idx S.1 pk) ci cr S.2 (List.ofFn y.1)

lemma leanPIX_rd5 (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPI (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w) (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPIX_rdE (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPI (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPRX_rd5 (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPR (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w) (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma leanPRX_rdE (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPR (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g).map
    fun o => toL (o.toOption.getD .empty)

lemma issX_rd5 (x : TIr) : Rd5 (issX (R := R) ci cr x) 624 :=
  (leanPIX_rd5 (encodeIssueWitness (List.ofFn x.1.1) ci cr (List.ofFn x.1.2))
    ⟨com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), ci⟩ (List.ofFn x.2.1) x.2.2).map fun π =>
    ((⟨List.ofFn x.1.1, List.ofFn x.1.2, ci, cr, com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2)⟩ :
      PendingToken), com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2) ++ π)

lemma issX_rdE (x : TIr) : RdE (issX (R := R) ci cr x) 4607 :=
  (leanPIX_rdE (encodeIssueWitness (List.ofFn x.1.1) ci cr (List.ofFn x.1.2))
    ⟨com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), ci⟩ (List.ofFn x.2.1) x.2.2).map fun π =>
    ((⟨List.ofFn x.1.1, List.ofFn x.1.2, ci, cr, com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2)⟩ :
      PendingToken), com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2) ++ π)

lemma redX_rd5 (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken) (resp : Coins uovN)
    (S : AnchorSet × Bytes) (y : TRr) : Rd5 (redX (R := R) ci cr idx pk i resp S y) 624 := by
  unfold redX
  split
  · exact (Rd5.const _).mono (Nat.zero_le _)
  · simp only [redeemRequestOf, nizkAt]
    split
    · exact (Rd5.const _).mono (Nat.zero_le _)
    · split_ifs
      · exact (leanPRX_rd5 _ _ _ _).map fun π => (Except.ok (_ ++ π) : Except Error Bytes)
      · exact (Rd5.const _).mono (Nat.zero_le _)

lemma redX_rdE (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken) (resp : Coins uovN)
    (S : AnchorSet × Bytes) (y : TRr) : RdE (redX (R := R) ci cr idx pk i resp S y) 4607 := by
  unfold redX
  split
  · exact (RdE.const _).mono (Nat.zero_le _)
  · simp only [redeemRequestOf, nizkAt]
    split
    · exact (RdE.const _).mono (Nat.zero_le _)
    · split_ifs
      · exact (leanPRX_rdE _ _ _ _).map fun π => (Except.ok (_ ++ π) : Except Error Bytes)
      · exact (RdE.const _).mono (Nat.zero_le _)

/-- **A further Client's issuance request is a consistent reader** of `H₅`, the cipher and `H₂³`
(`ZK.Sim.realRO_sreads`), for contexts of the right length. -/
theorem issX_req_sreads (hci : ci.length = ctxBytes) (hcr : cr.length = ctxBytes) (x : TIr) :
    SReads pI (fun t : Tb R pI => (issX ci cr x t.2).2) 0 nGrind 624 4607 := by
  have hrel : IssueRelW ⟨com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), ci⟩
      (encodeIssueWitness (List.ofFn x.1.1) ci cr (List.ofFn x.1.2)) :=
    ⟨⟨_, _, _, by simp [nfBytes], by simp [rBytes], hcr, rfl, rfl⟩, hci⟩
  have h := (realRO_sreads (R := R) (zkHypI _ _ hrel) hashesWF_shake hlab_pI x.2.1 x.2.2).map
    fun o => com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2) ++ toL (o.toOption.getD .empty)
  refine (congrArg (fun F => SReads pI F 0 nGrind 624 4607) (funext fun t => ?_)).mp h
  show _ = com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2) ++
    leanPI (encodeIssueWitness (List.ofFn x.1.1) ci cr (List.ofFn x.1.2))
      ⟨com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), ci⟩ (List.ofFn x.2.1) x.2.2 t.2
  rw [leanPI_ofFn]
  rfl

end Honest

/-! ## The many-session game -/

section Game

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The colluding adversary of the many-session game**: contexts, the challenge Clients' issuing
keys and a key for each further Client `j : ι`; after seeing every issuance request, the responses
to every Client and the Anchor Sets and digests of the two challenge sides and of every further
Client; and a guess that sees all issuance requests, the challenge redemptions (or the refusal),
every further Client's redemption, all slices and the tables. The interaction does not read the
tables. -/
structure AdversaryN (R : Type) (ι : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  pkX : ι → UOVKey
  respond : Bytes → Bytes → (ι → Bytes) → Bool → Coins uovN
  respondX : Bytes → Bytes → (ι → Bytes) → ι → Coins uovN
  choose : Bytes → Bytes → (ι → Bytes) → Bool → AnchorSet × Bytes
  chooseX : Bytes → Bytes → (ι → Bytes) → ι → AnchorSet × Bytes
  guess : Bytes → Bytes → (ι → Bytes) → Option (Except Error Bytes × Except Error Bytes) →
    (ι → Except Error Bytes) → Slices → (ι → Tab3 × Tab3) → ShM R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` and the further Clients' slices freely. -/
structure AdversaryN.Budget (A : AdversaryN R ι) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ q₀ q₁ tx y ox (g₁ gL gR : Tab3) slx s,
    Rd3 (fun g => A.guess q₀ q₁ tx y ox ((g, g₁), (gL, gR)) slx s) q3
  h31 : ∀ q₀ q₁ tx y ox (g₀ gL gR : Tab3) slx s,
    Rd3 (fun g => A.guess q₀ q₁ tx y ox ((g₀, g), (gL, gR)) slx s) q3
  h3L : ∀ q₀ q₁ tx y ox (g₀ g₁ gR : Tab3) slx s,
    Rd3 (fun g => A.guess q₀ q₁ tx y ox ((g₀, g₁), (g, gR)) slx s) q3
  h3R : ∀ q₀ q₁ tx y ox (g₀ g₁ gL : Tab3) slx s,
    Rd3 (fun g => A.guess q₀ q₁ tx y ox ((g₀, g₁), (gL, g)) slx s) q3
  h5 : ∀ q₀ q₁ tx y ox sl slx, Rd5 (A.guess q₀ q₁ tx y ox sl slx) q5
  hE : ∀ q₀ q₁ tx y ox sl slx, RdE (A.guess q₀ q₁ tx y ox sl slx) qE

namespace AdversaryN

variable (A : AdversaryN R ι)

/-- The contexts as byte lists. -/
def ci : Bytes := List.ofFn A.ctxIss
def cr : Bytes := List.ofFn A.ctxRed

/-- The further Clients' issuance requests on the tables. -/
noncomputable def txOf (c : ι → XC) (s : ShM R) : ι → Bytes :=
  fun j => (issX A.ci A.cr (c j).1 s).2

/-- **The adversary served by the further Clients** with tapes `c`: its interaction computes their
issuance requests on the tables the game runs on; its guess runs their redemptions. -/
noncomputable def withClients (idx : AnchorSet → UOVKey → ℕ) (c : ι → XC) : AdversaryRA R where
  ctxIss := A.ctxIss
  ctxRed := A.ctxRed
  pk := A.pk
  respond q₀ q₁ i _ u := A.respond q₀ q₁ (A.txOf c u) i
  choose q₀ q₁ side _ u := A.choose q₀ q₁ (A.txOf c u) side
  guess q₀ q₁ y sl v := A.guess q₀ q₁ (A.txOf c v) y
    (fun j => redX A.ci A.cr idx (A.pkX j) (issX A.ci A.cr (c j).1 v).1
      (A.respondX q₀ q₁ (A.txOf c v) j) (A.chooseX q₀ q₁ (A.txOf c v) j) (c j).2 v) sl
    (fun j => ((c j).1.2.2, (c j).2.2)) v

end AdversaryN

/-- **The real many-session game** in world `b`: the two-session game (`realGameRA`, the Lean
provers on the shared tables) of the adversary served by the further Clients with tapes
`z.1.2`. -/
noncomputable def realGameN (A : AdversaryN R ι) (idx : AnchorSet → UOVKey → ℕ) (b : Bool)
    (z : (((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM R) : Prop :=
  realGameRA (A.withClients idx z.1.2) idx leanPI leanPR b (z.1.1, z.2)

variable {A : AdversaryN R ι} {idx : AnchorSet → UOVKey → ℕ}

lemma ci_length (A : AdversaryN R ι) : A.ci.length = ctxBytes := List.length_ofFn
lemma cr_length (A : AdversaryN R ι) : A.cr.length = ctxBytes := List.length_ofFn

/-- The further Clients' requests, read together. -/
lemma txOf_sreads (A : AdversaryN R ι) (c : ι → XC) :
    SReads pI (fun t : Tb R pI => A.txOf c t.2) 0 (Fintype.card ι * nGrind) (Fintype.card ι * 624)
      (Fintype.card ι * 4607) := by
  exact SReads.pi (ι := ι) (f := fun j (t : Tb R pI) => (issX A.ci A.cr (c j).1 t.2).2)
    fun j => issX_req_sreads A.ci A.cr (ci_length A) (cr_length A) (c j).1

/-- **The interaction's budget**: no slice key, the further Clients' issuance reads. -/
theorem withClients_iBudget (A : AdversaryN R ι) (idx : AnchorSet → UOVKey → ℕ) (c : ι → XC) :
    (A.withClients idx c).IBudget 0 (Fintype.card ι * nGrind) (Fintype.card ι * 624)
      (Fintype.card ι * 4607) where
  s0 q₀ q₁ _ _ _ := (txOf_sreads A c).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  s1 q₀ q₁ _ _ _ := (txOf_sreads A c).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  sL q₀ q₁ _ _ _ := (txOf_sreads A c).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  sR q₀ q₁ _ _ _ := (txOf_sreads A c).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))

/-- **The guess's budget**: the adversary's plus the further Clients' issuance and redemption
reads. -/
theorem withClients_gBudget (A : AdversaryN R ι) (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (c : ι → XC) :
    (A.withClients idx c).GBudget q3 (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5))
      (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE)) := fun _ =>
  { h30 := fun _ _ _ g₁ gL gR s => hA.h30 _ _ _ _ _ g₁ gL gR _ s
    h31 := fun _ _ _ g₀ gL gR s => hA.h31 _ _ _ _ _ g₀ gL gR _ s
    h3L := fun _ _ _ g₀ g₁ gR s => hA.h3L _ _ _ _ _ g₀ g₁ gR _ s
    h3R := fun _ _ _ g₀ g₁ gL s => hA.h3R _ _ _ _ _ g₀ g₁ gL _ s
    h5 := fun q₀ q₁ y sl => Rd5.bindEq (m := fun s j => issX A.ci A.cr (c j).1 s)
      (f := fun (w : ι → PendingToken × Bytes) s => A.guess q₀ q₁ (fun j => (w j).2) y
        (fun j => redX A.ci A.cr idx (A.pkX j) (w j).1 (A.respondX q₀ q₁ (fun j => (w j).2) j)
          (A.chooseX q₀ q₁ (fun j => (w j).2) j) (c j).2 s) sl (fun j => ((c j).1.2.2, (c j).2.2)) s)
      (fun _ => rfl) (Rd5.pi fun j => issX_rd5 A.ci A.cr (c j).1) fun w =>
        Rd5.bindEq (m := fun s j => redX A.ci A.cr idx (A.pkX j) (w j).1
          (A.respondX q₀ q₁ (fun j => (w j).2) j) (A.chooseX q₀ q₁ (fun j => (w j).2) j) (c j).2 s)
          (f := fun o s => A.guess q₀ q₁ (fun j => (w j).2) y o sl (fun j => ((c j).1.2.2, (c j).2.2)) s)
          (fun _ => rfl) (Rd5.pi fun _ => redX_rd5 _ _ _ _ _ _ _ _) fun _ => hA.h5 _ _ _ _ _ _ _
    hE := fun q₀ q₁ y sl => RdE.bindEq (m := fun s j => issX A.ci A.cr (c j).1 s)
      (f := fun (w : ι → PendingToken × Bytes) s => A.guess q₀ q₁ (fun j => (w j).2) y
        (fun j => redX A.ci A.cr idx (A.pkX j) (w j).1 (A.respondX q₀ q₁ (fun j => (w j).2) j)
          (A.chooseX q₀ q₁ (fun j => (w j).2) j) (c j).2 s) sl (fun j => ((c j).1.2.2, (c j).2.2)) s)
      (fun _ => rfl) (RdE.pi fun j => issX_rdE A.ci A.cr (c j).1) fun w =>
        RdE.bindEq (m := fun s j => redX A.ci A.cr idx (A.pkX j) (w j).1
          (A.respondX q₀ q₁ (fun j => (w j).2) j) (A.chooseX q₀ q₁ (fun j => (w j).2) j) (c j).2 s)
          (f := fun o s => A.guess q₀ q₁ (fun j => (w j).2) y o sl (fun j => ((c j).1.2.2, (c j).2.2)) s)
          (fun _ => rfl) (RdE.pi fun _ => redX_rdE _ _ _ _ _ _ _ _) fun _ => hA.hE _ _ _ _ _ _ _ }

/-- The many-session tape, with the further Clients' tapes first. -/
def tapeN : (ι → XC) × (((TIr × TIr) × (TRr × TRr)) × ShM R) ≃
    (((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Theorem 4(a) with many Clients, for every type of cipher rows** (`ZKRow R`, `ZKPRow R`;
SHAKE as the base record): with `m = |ι|` further honest Clients, the bound of
`anonymityRA_lean_numG` at `i₃ = 0`, `i₂ = 2³²m`, `i₅ = 624m`, `i_E = 4607m` and the guess's
budget `(q₃, q₅ + 2·624m, q_E + 2·4607m)`. -/
theorem anonymityN_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryN R ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM R)) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM R)) (realGameN A idx true)| ≤
      4 * ZKRow.εz R pI (0 + q3) (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) +
          Fintype.card ι * 624 + 1872)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + Fintype.card ι * 4607 + 13821) +
      4 * εAdG R pR 9 q3 (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) + 1248)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + 13821) 0 (Fintype.card ι * nGrind)
        (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214) +
      4 * ((0 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
        ZKPRow.εP R pR 0 312 4607 (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214)) +
      6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeN, ← pr_equiv tapeN]
  exact abs_pr_prod_sub_le _ _ fun c =>
    anonymityRA_lean_numG (A.withClients idx c) idx (withClients_gBudget A idx hA c)
      (withClients_iBudget A idx c) (hhide c)

/-- **Theorem 4(a) with many Clients** (function rows; SHAKE as the base record). -/
theorem anonymityN_lean_num (A : AdversaryN (Blk → Blk) ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx true)| ≤
      4 * εRO (0 + q3) (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) + Fintype.card ι * 624 + 1872)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + Fintype.card ι * 4607 + 13821) +
      4 * εAd 9 q3 (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) + 1248)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + 13821) 0 (Fintype.card ι * nGrind)
        (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214) +
      4 * ((0 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
        εROP 0 312 4607 (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214)) +
      6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityN_lean_numG A idx hA hhide

/-- **Theorem 4(a) with many Clients and AES as uniformly random permutations.** -/
theorem anonymityN_lean_num_perm (A : AdversaryN (Equiv.Perm Blk) ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Equiv.Perm Blk))) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Equiv.Perm Blk))) (realGameN A idx true)| ≤
      4 * εROPm pI (0 + q3) (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) + Fintype.card ι * 624 + 1872)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + Fintype.card ι * 4607 + 13821) +
      4 * εAdPm pR 9 q3 (Fintype.card ι * 624 + (Fintype.card ι * 624 + q5) + 1248)
        (Fintype.card ι * 4607 + (Fintype.card ι * 4607 + qE) + 13821) 0 (Fintype.card ι * nGrind)
        (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214) +
      4 * ((0 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
        εROPmP pR 0 312 4607 (Fintype.card ι * 624 + 624) (Fintype.card ι * 4607 + 9214)) +
      6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityN_lean_numG A idx hA hhide

/-- **The many-Client bound in numbers**: with `n = m + 2` Clients in all,

    |Pr[W₀] − Pr[W₁]| ≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide. -/
theorem anonymityN_lean_le (A : AdversaryN (Blk → Blk) ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx true)| ≤
      (Fintype.card ι + 2 : ℕ) / 2 ^ 102 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityN_lean_num A idx hA hhide
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : (Fintype.card ι : ℝ) * (nGrind : ℝ) / 2 ^ 1024 ≤ Fintype.card ι / 2 ^ 128 := by
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc (Fintype.card ι : ℝ) * 2 ^ 32 * 2 ^ 128 = ((Fintype.card ι : ℝ) * 2 ^ 128) * 2 ^ 32 :=
          mul_right_comm _ _ _
      _ ≤ ((Fintype.card ι : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hp.le)
      _ = (Fintype.card ι : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  unfold εAd h23Term at h
  generalize (2 : ℝ) ^ 1024 = κ at h hK hG
  split_ifs at h with h0
  · unfold εROP εRO at h
    push_cast at h ⊢
    have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e]
    linarith
  · unfold εROP εRO at h
    push_cast at h ⊢
    have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e]
    linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸² + 2·εhide` plus the guess's budget terms. -/
theorem anonymityN_lean_2pow20 (A : AdversaryN (Blk → Blk) ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide)
    (hn : Fintype.card ι + 2 ≤ 2 ^ 20) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx true)| ≤
      1 / 2 ^ 82 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityN_lean_le A idx hA hhide
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 82 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁷⁰ + 2·εhide` plus the guess's budget terms. -/
theorem anonymityN_lean_2pow32 (A : AdversaryN (Blk → Blk) ι) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ c b cc, hidingAdv (A.withClients idx c).ctxRO.base.ci (A.withClients idx c).ctxRO.base.cr
      (reductionRA (A.withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide)
    (hn : Fintype.card ι + 2 ≤ 2 ^ 32) :
    |pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx false) -
        pr (((((TIr × TIr) × (TRr × TRr)) × (ι → XC)) × ShM (Blk → Blk))) (realGameN A idx true)| ≤
      1 / 2 ^ 70 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityN_lean_le A idx hA hhide
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 70 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Moussaka
