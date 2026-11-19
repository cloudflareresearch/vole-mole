import VoleMole.Privacy.PermRA
import VoleMole.Privacy.PomFRITMany

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

## `N` challenge pairs

`AdversaryP`, `realGameP` (worlds `w : Fin N → Bool`): two issuing keys per pair; after **every**
issuance request the adversary answers every Client and chooses both sides' Anchor Sets and
digests of every pair; side `s` of pair `j` redeems Client `w j ^^ s`'s token under §6's rule per
pair (`outAt`: both redemptions if all four checks pass, else none). A hybrid over the pairs
(`realGameP_hybrid`, `abs_sub_le_mul_of_worlds`): at step `k` the game is `realGameN` of
`A.hop idx k v` with the other pairs' `2(N − 1)` Clients as further Clients in their current
worlds `v` (`realGameP_iff`; Client `c` of pair `j` redeems at side `v j ^^ c`, `splitM` gives it
that side's redemption tape, and the hop's guess rebuilds each other pair's outcome from its two
Clients' redemptions and §6's rule on the commitments, `outAt_eq`). So any two worlds differ by
`≤ N·εPairM` (`anonymityP_lean_numG`, `_num`, `_num_perm`), in numbers (`anonymityP_lean_le`)
`≤ N·(2N·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`: `≤ 2⁻⁶³` for `2N ≤ 2²⁰` Clients and
`≤ 2⁻³⁹` for `2N ≤ 2³²` (`anonymityP_lean_2pow20`, `_2pow32`), plus `N` times the budget and
hiding terms. Quadratic, as for PomFRIT: each step's H4 hop pays for the other pairs' cipher reads
(an artifact of the key-level hop, `lean/docs/zk.md` §10.8).
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

/-! ## Many challenge pairs -/

section Pairs

open VoleMole.Privacy.PomFRIT (Oth joinP joinP_self joinP_ne card_oth)

variable {N : ℕ}

/-- A challenge pair's tape: the two issuance tapes, the left and right redemption tapes. -/
abbrev PT := (TIr × TIr) × (TRr × TRr)

/-- **The redemption of side `side` in world `b`** for the interaction `B`: the spec's
`redeem_request` at the redemption point of §6 (Client `b ^^ side`'s token at its index in the
side's set), with the Lean prover on the tables and the side's redemption tape. -/
noncomputable def redAt (B : Adversary) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT) (s : ShM R)
    (side : Bool) : Except Error Bytes :=
  redeemRequestOf (nizkAt leanPR (bif side then x.2.2 else x.2.1).2 s)
    (pt B idx b (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) side).tok
    (pt B idx b (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) side).anchors
    (pt B idx b (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) side).i B.ci B.cr
    (pt B idx b (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) side).cd
    (List.ofFn (bif side then x.2.2 else x.2.1).1)

/-- **A challenge pair's outcome in world `b`** for the interaction `B`: both redemptions if §6's
rule allows them, else none. -/
noncomputable def outAt (B : Adversary) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT) (s : ShM R) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif allOk B idx (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) then
    some (redAt B idx b x s false, redAt B idx b x s true) else none

/-- The challenge interaction of a many-Client adversary at the requests `q₀`, `q₁`, `tx`. -/
def AdversaryN.chalAdv {ι : Type} (A : AdversaryN R ι) (q₀ q₁ : Bytes) (tx : ι → Bytes) : Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk, fun _ _ c => bif c then A.respond q₀ q₁ tx true else A.respond q₀ q₁ tx false,
    fun _ _ side => bif side then A.choose q₀ q₁ tx true else A.choose q₀ q₁ tx false,
    fun _ _ _ => True⟩

/-- **The many-Client game, unfolded**: the guess at the real requests, the challenge pair's
outcome (`outAt`), the further Clients' redemptions. -/
theorem realGameN_eq {ι : Type} [Fintype ι] [DecidableEq ι] (A : AdversaryN R ι)
    (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT) (c : ι → XC) (s : ShM R) :
    realGameN A idx b ((x, c), s) ↔
      A.guess (issX A.ci A.cr x.1.1 s).2 (issX A.ci A.cr x.1.2 s).2 (A.txOf c s)
        (outAt (A.chalAdv (issX A.ci A.cr x.1.1 s).2 (issX A.ci A.cr x.1.2 s).2 (A.txOf c s)) idx b x s)
        (fun j => redX A.ci A.cr idx (A.pkX j) (issX A.ci A.cr (c j).1 s).1
          (A.respondX (issX A.ci A.cr x.1.1 s).2 (issX A.ci A.cr x.1.2 s).2 (A.txOf c s) j)
          (A.chooseX (issX A.ci A.cr x.1.1 s).2 (issX A.ci A.cr x.1.2 s).2 (A.txOf c s) j) (c j).2 s)
        (((x.1.1.2.2, x.1.2.2.2), (x.2.1.2, x.2.2.2))) (fun j => ((c j).1.2.2, (c j).2.2)) s :=
  Iff.rfl

/-- **The colluding adversary of the game with `N` challenge pairs**: contexts, two issuing keys
per pair; after seeing **every** issuance request, the responses to every Client and the Anchor
Sets and digests of both sides of every pair; and a guess that sees all issuance requests, each
pair's redemptions (or its refusal, §6's rule per pair), all slices and the tables. The
interaction does not read the tables. -/
structure AdversaryP (R : Type) (N : ℕ) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Fin N → Bool → UOVKey
  respond : (Fin N → Bytes × Bytes) → Fin N → Bool → Coins uovN
  choose : (Fin N → Bytes × Bytes) → Fin N → Bool → AnchorSet × Bytes
  guess : (Fin N → Bytes × Bytes) → (Fin N → Option (Except Error Bytes × Except Error Bytes)) →
    (Fin N → Slices) → ShM R → Prop

/-- **The guess's budget**: each of the `4N` slices at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` freely. -/
structure AdversaryP.Budget (A : AdversaryP R N) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T Y (sl : Fin N → Slices) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((g, (sl k).1.2), (sl k).2)) s) q3
  h31 : ∀ T Y (sl : Fin N → Slices) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k (((sl k).1.1, g), (sl k).2)) s) q3
  h3L : ∀ T Y (sl : Fin N → Slices) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((sl k).1, (g, (sl k).2.2))) s) q3
  h3R : ∀ T Y (sl : Fin N → Slices) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((sl k).1, ((sl k).2.1, g))) s) q3
  h5 : ∀ T Y sl, Rd5 (A.guess T Y sl) q5
  hE : ∀ T Y sl, RdE (A.guess T Y sl) qE

namespace AdversaryP

variable (A : AdversaryP R N)

/-- The contexts as byte lists. -/
def ci : Bytes := List.ofFn A.ctxIss
def cr : Bytes := List.ofFn A.ctxRed

/-- **Pair `j`'s interaction** at the requests `T`, as an `Adversary` (its guess is not used). -/
def pairAdv (T : Fin N → Bytes × Bytes) (j : Fin N) : Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk j, fun _ _ c => bif c then A.respond T j true else A.respond T j false,
    fun _ _ side => bif side then A.choose T j true else A.choose T j false, fun _ _ _ => True⟩

/-- All issuance requests on the tables. -/
noncomputable def reqP (z : Fin N → PT) (s : ShM R) : Fin N → Bytes × Bytes :=
  fun j => ((issX A.ci A.cr (z j).1.1 s).2, (issX A.ci A.cr (z j).1.2 s).2)

/-- **Pair `j`'s outcome in world `b`** (`outAt` of pair `j`'s interaction). -/
noncomputable def outP (idx : AnchorSet → UOVKey → ℕ) (T : Fin N → Bytes × Bytes) (b : Bool) (x : PT)
    (s : ShM R) (j : Fin N) : Option (Except Error Bytes × Except Error Bytes) :=
  outAt (A.pairAdv T j) idx b x s

end AdversaryP

/-- A pair's four slices. -/
def slOf (x : PT) : Slices := ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2, x.2.2.2))

/-- **The real game with `N` challenge pairs** in world `w : Fin N → Bool`: every Client issues
with the Lean prover on the shared tables; pair `j`'s left side redeems Client `w j`'s token, its
right side Client `¬w j`'s. -/
noncomputable def realGameP (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ) (w : Fin N → Bool)
    (z : (Fin N → PT) × ShM R) : Prop :=
  A.guess (A.reqP z.1 z.2) (fun j => A.outP idx (A.reqP z.1 z.2) (w j) (z.1 j) z.2 j)
    (fun j => slOf (z.1 j)) z.2

namespace AdversaryP

variable (A : AdversaryP R N)

/-- The outcomes the hop's guess passes: pair `k`'s, and every other pair's rebuilt from its two
Clients' redemptions and §6's rule on the commitments (`allOkT`). -/
def hopY (idx : AnchorSet → UOVKey → ℕ) (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) (q₀ q₁ : Bytes)
    (tx : Oth k → Bytes) (y : Option (Except Error Bytes × Except Error Bytes))
    (ox : Oth k → Except Error Bytes) : Fin N → Option (Except Error Bytes × Except Error Bytes) :=
  fun j => if h : j = k then y else
    bif allOkT (A.pairAdv (joinP k (q₀, q₁) tx) j) idx (tx (⟨j, h⟩, false)) (tx (⟨j, h⟩, true))
        ((tx (⟨j, h⟩, false)).take uovM) ((tx (⟨j, h⟩, true)).take uovM)
      then some (ox (⟨j, h⟩, v ⟨j, h⟩), ox (⟨j, h⟩, !v ⟨j, h⟩)) else none

/-- The slices the hop's guess passes: pair `k`'s, and every other pair's from its Clients'. -/
def hopS (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) (sl : Slices) (slx : Oth k → Tab3 × Tab3) :
    Fin N → Slices :=
  fun j => if h : j = k then sl else
    (((slx (⟨j, h⟩, false)).1, (slx (⟨j, h⟩, true)).1),
      ((slx (⟨j, h⟩, v ⟨j, h⟩)).2, (slx (⟨j, h⟩, !v ⟨j, h⟩)).2))

/-- **The adversary of the game for pair `k`**, the other pairs' Clients further honest Clients,
their worlds `v`: Client `c` of pair `j` redeems at side `v j ^^ c`; the guess rebuilds each other
pair's outcome from the further redemptions and §6's rule on the commitments (`allOkT`). -/
def hop (idx : AnchorSet → UOVKey → ℕ) (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) :
    AdversaryN R (Oth k) where
  ctxIss := A.ctxIss
  ctxRed := A.ctxRed
  pk := A.pk k
  pkX jc := A.pk jc.1 jc.2
  respond q₀ q₁ tx i := A.respond (joinP k (q₀, q₁) tx) k i
  respondX q₀ q₁ tx jc := A.respond (joinP k (q₀, q₁) tx) jc.1 jc.2
  choose q₀ q₁ tx side := A.choose (joinP k (q₀, q₁) tx) k side
  chooseX q₀ q₁ tx jc := A.choose (joinP k (q₀, q₁) tx) jc.1 (v jc.1 ^^ jc.2)
  guess q₀ q₁ tx y ox sl slx s := A.guess (joinP k (q₀, q₁) tx) (A.hopY idx k v q₀ q₁ tx y ox)
    (hopS k v sl slx) s

end AdversaryP

/-- **The tape split at pair `k`** in the other pairs' worlds `v`: pair `k`'s tape, and for
Client `c` of pair `j` its issuance tape and the redemption tape of the side it redeems at. -/
def splitM (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) : (Fin N → PT) ≃ PT × (Oth k → XC) where
  toFun z := (z k, fun jc => (bif jc.2 then (z jc.1.1).1.2 else (z jc.1.1).1.1,
    bif v jc.1 ^^ jc.2 then (z jc.1.1).2.2 else (z jc.1.1).2.1))
  invFun q := fun j => if h : j = k then q.1 else
    (((q.2 (⟨j, h⟩, false)).1, (q.2 (⟨j, h⟩, true)).1),
      ((q.2 (⟨j, h⟩, v ⟨j, h⟩)).2, (q.2 (⟨j, h⟩, !v ⟨j, h⟩)).2))
  left_inv z := funext fun j => by
    by_cases h : j = k
    · subst h; simp
    · simp only [h, dite_false]
      cases v ⟨j, h⟩ <;> rfl
  right_inv q := by
    refine Prod.ext (by simp) (funext fun jc => ?_)
    obtain ⟨⟨j, h⟩, c⟩ := jc
    simp only [h, dite_false]
    cases hv : v ⟨j, h⟩ <;> cases c <;> simp

lemma issX_take (ci cr : Bytes) (x : TIr) (s : ShM R) :
    (issX ci cr x s).2.take uovM = (issX ci cr x s).1.t := by
  simp only [issX, issueRequestOf]
  exact List.take_left' (length_com _ _ _ _)

/-- **A pair's outcome from its Clients' own redemptions**: §6's rule is `allOkT` on the requests
and commitments, and when it holds each side's redemption is its Client's `redX`. -/
theorem outAt_eq (B : Adversary) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT) (s : ShM R) :
    outAt B idx b x s =
      bif allOkT B idx (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2
          ((issX B.ci B.cr x.1.1 s).2.take uovM) ((issX B.ci B.cr x.1.2 s).2.take uovM) then
        some (redX B.ci B.cr idx (B.pk b) (issX B.ci B.cr (bif b then x.1.2 else x.1.1) s).1
            (B.respond (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 b)
            (B.choose (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 false) x.2.1 s,
          redX B.ci B.cr idx (B.pk !b) (issX B.ci B.cr (bif !b then x.1.2 else x.1.1) s).1
            (B.respond (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 !b)
            (B.choose (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 true) x.2.2 s)
      else none := by
  have hall := allOk_eq_allOkT idx B (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) rfl rfl
  rw [issX_take, issX_take, ← hall]
  unfold outAt
  cases hC : allOk B idx (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s)
  · rfl
  · have h0 : (tok B (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) false).isSome :=
      by unfold allOk at hC; simp only [Bool.and_eq_true] at hC; exact hC.1.1.1.1.1
    have h1 : (tok B (issX B.ci B.cr x.1.1 s) (issX B.ci B.cr x.1.2 s) true).isSome :=
      by unfold allOk at hC; simp only [Bool.and_eq_true] at hC; exact hC.1.1.1.1.2
    obtain ⟨t0, ht0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨t1, ht1⟩ := Option.isSome_iff_exists.1 h1
    have e0 : finalizeIssue (B.pk false) (issX B.ci B.cr x.1.1 s).1
        (List.ofFn (B.respond (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 false)) =
          some t0 := ht0
    have e1 : finalizeIssue (B.pk true) (issX B.ci B.cr x.1.2 s).1
        (List.ofFn (B.respond (issX B.ci B.cr x.1.1 s).2 (issX B.ci B.cr x.1.2 s).2 true)) =
          some t1 := ht1
    simp only [Bool.cond_true]
    cases b
    · simp only [redAt, pt, tokD, ht0, ht1, Option.getD_some, redX, e0, e1,
        Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.cond_false, Bool.cond_true]
    · simp only [redAt, pt, tokD, ht0, ht1, Option.getD_some, redX, e0, e1,
        Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.cond_false, Bool.cond_true]

/-- **Another pair's outcome, rebuilt by the hop's guess** from its two Clients' redemptions. -/
lemma AdversaryP.hop_outAt (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ) (k : Fin N)
    (v : {j : Fin N // j ≠ k} → Bool) (z : Fin N → PT) (s : ShM R) (q₀ q₁ : Bytes) (j : Fin N)
    (h : j ≠ k) :
    outAt (A.pairAdv (joinP k (q₀, q₁) ((A.hop idx k v).txOf (splitM k v z).2 s)) j) idx (v ⟨j, h⟩)
        (z j) s =
      bif allOkT (A.pairAdv (joinP k (q₀, q₁) ((A.hop idx k v).txOf (splitM k v z).2 s)) j) idx
          ((A.hop idx k v).txOf (splitM k v z).2 s (⟨j, h⟩, false))
          ((A.hop idx k v).txOf (splitM k v z).2 s (⟨j, h⟩, true))
          (((A.hop idx k v).txOf (splitM k v z).2 s (⟨j, h⟩, false)).take uovM)
          (((A.hop idx k v).txOf (splitM k v z).2 s (⟨j, h⟩, true)).take uovM) then
        some (redX (A.hop idx k v).ci (A.hop idx k v).cr idx ((A.hop idx k v).pkX (⟨j, h⟩, v ⟨j, h⟩))
            (issX (A.hop idx k v).ci (A.hop idx k v).cr ((splitM k v z).2 (⟨j, h⟩, v ⟨j, h⟩)).1 s).1
            ((A.hop idx k v).respondX q₀ q₁ ((A.hop idx k v).txOf (splitM k v z).2 s) (⟨j, h⟩, v ⟨j, h⟩))
            ((A.hop idx k v).chooseX q₀ q₁ ((A.hop idx k v).txOf (splitM k v z).2 s) (⟨j, h⟩, v ⟨j, h⟩))
            ((splitM k v z).2 (⟨j, h⟩, v ⟨j, h⟩)).2 s,
          redX (A.hop idx k v).ci (A.hop idx k v).cr idx ((A.hop idx k v).pkX (⟨j, h⟩, !v ⟨j, h⟩))
            (issX (A.hop idx k v).ci (A.hop idx k v).cr ((splitM k v z).2 (⟨j, h⟩, !v ⟨j, h⟩)).1 s).1
            ((A.hop idx k v).respondX q₀ q₁ ((A.hop idx k v).txOf (splitM k v z).2 s) (⟨j, h⟩, !v ⟨j, h⟩))
            ((A.hop idx k v).chooseX q₀ q₁ ((A.hop idx k v).txOf (splitM k v z).2 s) (⟨j, h⟩, !v ⟨j, h⟩))
            ((splitM k v z).2 (⟨j, h⟩, !v ⟨j, h⟩)).2 s)
      else none := by
  rw [outAt_eq]
  cases hv : v ⟨j, h⟩
  · simp only [AdversaryP.hop, splitM, Equiv.coe_fn_mk, hv, Bool.not_false, Bool.xor_false,
      Bool.xor_true, Bool.cond_false, Bool.cond_true]
    rfl
  · simp only [AdversaryP.hop, splitM, Equiv.coe_fn_mk, hv, Bool.xor_false,
      Bool.xor_true, Bool.cond_false, Bool.cond_true, Bool.not_true]
    rfl

/-- **The game with `N` pairs is, at pair `k`, the many-Client game of `A.hop idx k`**, tape by
tape. -/
theorem realGameP_iff (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ) (w : Fin N → Bool)
    (k : Fin N) (z : (Fin N → PT) × ShM R) :
    realGameP A idx w z ↔
      realGameN (A.hop idx k fun j => w j.1) idx (w k) (splitM k (fun j => w j.1) z.1, z.2) := by
  obtain ⟨z, s⟩ := z
  rw [show splitM k (fun j => w j.1) z = (z k, (splitM k (fun j => w j.1) z).2) from rfl,
    realGameN_eq]
  have key : ∀ T T' Y Y' S S', T = T' → Y = Y' → S = S' → (A.guess T Y S s ↔ A.guess T' Y' S' s) := by
    rintro _ _ _ _ _ _ rfl rfl rfl
    exact Iff.rfl
  have eT : A.reqP z s = joinP k ((issX A.ci A.cr (z k).1.1 s).2, (issX A.ci A.cr (z k).1.2 s).2)
      ((A.hop idx k fun j => w j.1).txOf (splitM k (fun j => w j.1) z).2 s) := by
    funext j
    by_cases h : j = k
    · subst h; exact (joinP_self _ _ _).symm
    · rw [joinP_ne _ _ h]; rfl
  refine key _ _ _ _ _ _ eT (funext fun j => ?_) (funext fun j => ?_)
  · simp only [AdversaryP.hopY]
    by_cases h : j = k
    · subst h
      simp only [dite_true]
      show outAt (A.pairAdv (A.reqP z s) j) idx (w j) (z j) s = _
      rw [eT]
      rfl
    · simp only [h, dite_false]
      show outAt (A.pairAdv (A.reqP z s) j) idx (w j) (z j) s = _
      rw [eT]
      exact A.hop_outAt idx k (fun j => w j.1) z s _ _ j h
  · simp only [AdversaryP.hopS]
    by_cases h : j = k
    · subst h; simp only [dite_true]; rfl
    · simp only [h, dite_false]
      cases hv : w j <;> simp only [splitM, Equiv.coe_fn_mk, hv] <;> rfl

/-- The budget of the game for pair `k`. -/
theorem AdversaryP.hop_budget {A : AdversaryP R N} {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (idx : AnchorSet → UOVKey → ℕ) (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) :
    (A.hop idx k v).Budget q3 q5 qE := by
  have hS : ∀ sl sl' slx, AdversaryP.hopS k v sl' slx =
      Function.update (AdversaryP.hopS k v sl slx) k sl' := fun sl sl' slx => funext fun j => by
    by_cases h : j = k
    · subst h; simp [AdversaryP.hopS]
    · simp [AdversaryP.hopS, h]
  have hk : ∀ sl slx, AdversaryP.hopS k v sl slx k = sl := fun sl slx => by simp [AdversaryP.hopS]
  refine ⟨fun q₀ q₁ tx y ox g₁ gL gR slx s => ?_, fun q₀ q₁ tx y ox g₀ gL gR slx s => ?_,
    fun q₀ q₁ tx y ox g₀ g₁ gR slx s => ?_, fun q₀ q₁ tx y ox g₀ g₁ gL slx s => ?_,
    fun _ _ _ _ _ _ _ => hA.h5 _ _ _, fun _ _ _ _ _ _ _ => hA.hE _ _ _⟩
  · have e : (fun g => (A.hop idx k v).guess q₀ q₁ tx y ox ((g, g₁), (gL, gR)) slx s) = fun g =>
        A.guess (joinP k (q₀, q₁) tx) (A.hopY idx k v q₀ q₁ tx y ox)
          (Function.update (AdversaryP.hopS k v ((g₁, g₁), (gL, gR)) slx) k
            ((g, (AdversaryP.hopS k v ((g₁, g₁), (gL, gR)) slx k).1.2),
              (AdversaryP.hopS k v ((g₁, g₁), (gL, gR)) slx k).2)) s := by
      funext g
      rw [hk, ← hS]
      rfl
    rw [e]; exact hA.h30 _ _ _ s k
  · have e : (fun g => (A.hop idx k v).guess q₀ q₁ tx y ox ((g₀, g), (gL, gR)) slx s) = fun g =>
        A.guess (joinP k (q₀, q₁) tx) (A.hopY idx k v q₀ q₁ tx y ox)
          (Function.update (AdversaryP.hopS k v ((g₀, g₀), (gL, gR)) slx) k
            (((AdversaryP.hopS k v ((g₀, g₀), (gL, gR)) slx k).1.1, g),
              (AdversaryP.hopS k v ((g₀, g₀), (gL, gR)) slx k).2)) s := by
      funext g
      rw [hk, ← hS]
      rfl
    rw [e]; exact hA.h31 _ _ _ s k
  · have e : (fun g => (A.hop idx k v).guess q₀ q₁ tx y ox ((g₀, g₁), (g, gR)) slx s) = fun g =>
        A.guess (joinP k (q₀, q₁) tx) (A.hopY idx k v q₀ q₁ tx y ox)
          (Function.update (AdversaryP.hopS k v ((g₀, g₁), (gR, gR)) slx) k
            ((AdversaryP.hopS k v ((g₀, g₁), (gR, gR)) slx k).1,
              (g, (AdversaryP.hopS k v ((g₀, g₁), (gR, gR)) slx k).2.2))) s := by
      funext g
      rw [hk, ← hS]
      rfl
    rw [e]; exact hA.h3L _ _ _ s k
  · have e : (fun g => (A.hop idx k v).guess q₀ q₁ tx y ox ((g₀, g₁), (gL, g)) slx s) = fun g =>
        A.guess (joinP k (q₀, q₁) tx) (A.hopY idx k v q₀ q₁ tx y ox)
          (Function.update (AdversaryP.hopS k v ((g₀, g₁), (gL, gL)) slx) k
            ((AdversaryP.hopS k v ((g₀, g₁), (gL, gL)) slx k).1,
              ((AdversaryP.hopS k v ((g₀, g₁), (gL, gL)) slx k).2.1, g))) s := by
      funext g
      rw [hk, ← hS]
      rfl
    rw [e]; exact hA.h3R _ _ _ s k

end Pairs

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

/-! ## The bound with `N` challenge pairs -/

section PairsBound

open VoleMole.Privacy.PomFRIT (Oth card_oth)

variable {N : ℕ}

/-- The error of one pair's step in the game with `N` pairs: the many-Client bound
(`anonymityN_lean_numG`) with the `2(N − 1)` Clients of the other pairs as further Clients. -/
noncomputable def εPairM (R : Type) [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R] [ZKRow R]
    [ZKPRow R] (N q3 q5 qE : ℕ) (εhide : ℝ) : ℝ :=
  4 * ZKRow.εz R pI (0 + q3) ((N - 1) * 2 * 624 + ((N - 1) * 2 * 624 + q5) +
      (N - 1) * 2 * 624 + 1872)
    ((N - 1) * 2 * 4607 + ((N - 1) * 2 * 4607 + qE) + (N - 1) * 2 * 4607 + 13821) +
  4 * εAdG R pR 9 q3 ((N - 1) * 2 * 624 + ((N - 1) * 2 * 624 + q5) + 1248)
    ((N - 1) * 2 * 4607 + ((N - 1) * 2 * 4607 + qE) + 13821) 0 ((N - 1) * 2 * nGrind)
    ((N - 1) * 2 * 624 + 624) ((N - 1) * 2 * 4607 + 9214) +
  4 * ((0 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
    ZKPRow.εP R pR 0 312 4607 ((N - 1) * 2 * 624 + 624) ((N - 1) * 2 * 4607 + 9214)) +
  6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide

/-- The probability of the `N`-pair game in world `u`, as the many-Client game of pair `k`. -/
lemma pr_realGameP_eq (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ) (k : Fin N)
    (u : Fin N → Bool) :
    pr ((Fin N → PT) × ShM R) (realGameP A idx u) =
      pr (((PT × (Oth k → XC)) × ShM R)) (realGameN (A.hop idx k fun j => u j.1) idx (u k)) := by
  rw [← pr_equiv ((splitM k (fun j => u j.1)).prodCongr (Equiv.refl (ShM R)))]
  exact pr_congr fun z => realGameP_iff A idx u k z

/-- **The hybrid over the pairs**: if every step's many-Client game is `ε`-close, any two worlds
are `N·ε`-close. -/
lemma realGameP_hybrid (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ) (ε : ℝ)
    (h : ∀ (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool),
      |pr (((PT × (Oth k → XC)) × ShM R)) (realGameN (A.hop idx k v) idx false) -
        pr (((PT × (Oth k → XC)) × ShM R)) (realGameN (A.hop idx k v) idx true)| ≤ ε)
    (w w' : Fin N → Bool) :
    |pr ((Fin N → PT) × ShM R) (realGameP A idx w) - pr ((Fin N → PT) × ShM R) (realGameP A idx w')| ≤
      N * ε := by
  refine abs_sub_le_mul_of_worlds (fun u => pr ((Fin N → PT) × ShM R) (realGameP A idx u)) ε
    (fun k u u' hu => ?_) w w'
  have hv : (fun j : {j : Fin N // j ≠ k} => u j.1) = fun j => u' j.1 :=
    funext fun j => hu j.1 j.2
  have hb := h k fun j => u j.1
  have hz : 0 ≤ ε := (abs_nonneg _).trans hb
  show |pr _ (realGameP A idx u) - pr _ (realGameP A idx u')| ≤ ε
  rw [pr_realGameP_eq A idx k u, pr_realGameP_eq A idx k u', ← hv]
  rcases hw : u k <;> rcases hw' : u' k
  · simpa using hz
  · exact hb
  · rw [abs_sub_comm]; exact hb
  · simpa using hz

/-- **Theorem 4(a) with `N` challenge pairs, for every type of cipher rows** (`ZKRow R`,
`ZKPRow R`; SHAKE as the base record): any two worlds `w, w' : Fin N → Bool` differ by at most
`N` times the many-Client bound with `2(N − 1)` further Clients (a hybrid over the pairs; each
step is `anonymityN_lean_numG` for the pair that changes, the other pairs' Clients served as
further Clients in their current worlds). Hiding is assumed for the explicit reductions of every
step's composed adversary. -/
theorem anonymityP_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryP R N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) :
    |pr ((Fin N → PT) × ShM R) (realGameP A idx w) - pr ((Fin N → PT) × ShM R) (realGameP A idx w')| ≤
      N * εPairM R N q3 q5 qE εhide := by
  refine realGameP_hybrid A idx _ (fun k v => ?_) w w'
  have hb := anonymityN_lean_numG (A.hop idx k v) idx (AdversaryP.hop_budget hA idx k v) (hhide k v)
  rw [card_oth] at hb
  exact hb

/-- **Theorem 4(a) with `N` challenge pairs** (function rows). -/
theorem anonymityP_lean_num (A : AdversaryP (Blk → Blk) N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) :
    |pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w) -
        pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w')| ≤
      N * εPairM (Blk → Blk) N q3 q5 qE εhide :=
  anonymityP_lean_numG A idx hA hhide w w'

/-- **Theorem 4(a) with `N` challenge pairs and AES as uniformly random permutations.** -/
theorem anonymityP_lean_num_perm (A : AdversaryP (Equiv.Perm Blk) N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) :
    |pr ((Fin N → PT) × ShM (Equiv.Perm Blk)) (realGameP A idx w) -
        pr ((Fin N → PT) × ShM (Equiv.Perm Blk)) (realGameP A idx w')| ≤
      N * εPairM (Equiv.Perm Blk) N q3 q5 qE εhide :=
  anonymityP_lean_numG A idx hA hhide w w'

/-- **`N` pairs in numbers**: `≤ N·(2N·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`. -/
theorem anonymityP_lean_le (A : AdversaryP (Blk → Blk) N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) :
    |pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w) -
        pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w')| ≤
      N * ((2 * N : ℕ) / 2 ^ 102 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  refine realGameP_hybrid A idx _ (fun k v => ?_) w w'
  have hb := anonymityN_lean_le (A.hop idx k v) idx (AdversaryP.hop_budget hA idx k v) (hhide k v)
  have hN : (N - 1) * 2 + 2 = 2 * N := by have := k.isLt; omega
  rw [card_oth, hN] at hb
  exact hb

/-- **`2²⁰` Clients in `N` pairs**: `≤ 2⁻⁶³` plus `N` times the guess's budget terms and
`2·εhide`. -/
theorem anonymityP_lean_2pow20 (A : AdversaryP (Blk → Blk) N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 20) :
    |pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w) -
        pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w')| ≤
      1 / 2 ^ 63 + N * (8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  have h := anonymityP_lean_le A idx hA hhide w w'
  have h1 : (N : ℝ) ≤ 2 ^ 19 := by
    have : N ≤ 2 ^ 19 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((2 * N : ℕ) / 2 ^ 102) ≤ 1 / 2 ^ 63 := by
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [add_assoc, mul_add] at h
  linarith

/-- **`2³²` Clients in `N` pairs**: `≤ 2⁻³⁹` plus `N` times the guess's budget terms and
`2·εhide`. -/
theorem anonymityP_lean_2pow32 (A : AdversaryP (Blk → Blk) N) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k v c b cc, hidingAdv ((A.hop idx k v).withClients idx c).ctxRO.base.ci
      ((A.hop idx k v).withClients idx c).ctxRO.base.cr
      (reductionRA ((A.hop idx k v).withClients idx c) idx (leanSim pI) (leanSim pR) leanProgI
        leanProgR b cc) ≤ εhide)
    (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 32) :
    |pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w) -
        pr ((Fin N → PT) × ShM (Blk → Blk)) (realGameP A idx w')| ≤
      1 / 2 ^ 39 + N * (8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide) := by
  have h := anonymityP_lean_le A idx hA hhide w w'
  have h1 : (N : ℝ) ≤ 2 ^ 31 := by
    have : N ≤ 2 ^ 31 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((2 * N : ℕ) / 2 ^ 102) ≤ 1 / 2 ^ 39 := by
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [add_assoc, mul_add] at h
  linarith

end PairsBound

end VoleMole.Privacy.Moussaka
