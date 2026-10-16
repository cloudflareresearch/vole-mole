import VoleMole.Privacy.PermRA
import VoleMole.ZK.ReadsMany

/-!
# PomFRIT blindness with many sessions

The privacy games of `Privacy/PomFRITRO.lean` and `Privacy/PomFRITRAGame.lean` have two sessions:
the challenge pair. Here the Issuer also runs **any number of further honest sessions**, on the
same tables, and then **any number `N` of challenge pairs**.

## The games

* **`realGameN`** (one challenge pair and `m = |ι|` further sessions, `AdversaryN`): the Issuer
  picks a key and two messages for the challenge pair and a key and a message for each further
  session `j : ι`; all `m + 2` Clients send their requests (the Lean prover's step 1 on the shared
  tables, each session with its own randomness, refresher, `r` and `H₃` slice); the Issuer answers
  every session after seeing every request; each Client finalizes (step 2 on the shared tables).
  The guess sees all requests, the challenge pair's signatures in message order only if both
  complete (`outcome`), every further session's outcome, all slices and all tables. World `b`: the
  first challenge session signs `µ_b`, the second `µ_{¬b}`; the further sessions are the same in
  both worlds. The Issuer's interaction does not read the tables (as in `blindnessRO`); its guess
  reads them with a budget (`AdversaryN.Budget`: each challenge slice at `q₃` keys, `H₅` at `q₅`,
  the cipher at `q_E`; `H₂³` and the further sessions' slices freely).
* **`realGameP`** (`N` challenge pairs, `AdversaryP`, worlds `w : Fin N → Bool`): pair `j` has a
  key and two messages, its first session signs `µ^j_{w j}`, its second `µ^j_{¬w j}`; all `2N`
  requests are sent, the Issuer answers every session after seeing every request, and the guess
  sees each pair's signatures (in message order, if both of its sessions complete), all slices and
  the tables. This is the left-or-right game with `N` queries.

## The proofs

* **One pair with further sessions is a reduction**, not a new hybrid: for each fixed tape `c` of
  the further sessions, `realGameN` is, tape by tape (`realGameN_iff`, `Iff.rfl`), the two-session
  game with a table-reading Issuer (`realGameRA`, `Privacy/PomFRITRAGame.lean`) for the Issuer
  `A.red c` that runs the further sessions itself: its responses read their requests, its guess
  runs them to the end. `blindnessRA_lean_numG` applies to every `A.red c`, and averaging over `c`
  (`abs_pr_prod_sub_le`) gives the bound. The budgets are the further sessions' reads:
  * a session's step 1 is a **consistent** reader of `H₅` and the cipher (`s1R_sreads`,
    `ZK.Sim.step1_cons`: a table that agrees on its `624` gate inputs and its tree's `4607` nodes
    has the same keys and the same output, whatever its `H₂³`; `ZK.Sim.vgIn5_ic_congr`), so the
    requests of `m` sessions are an `SReads` reader of `(0, 0, 624m, 4607m)` keys
    (`ZK.Sim.SReads.pi`): the interaction budget `IBudget 0 (624m) (4607m)` (`red_iBudget`);
  * a whole session reads `H₅` at `624` and the cipher at `4607` keys (`sessX_rd5`, `sessX_rdE`;
    step 2 reads neither), so the guess of `A.red c` has budget `(q₃, q₅ + 624m, q_E + 4607m)`
    (`red_gBudget`, `ZK.Sim.Rd5.pi`, `ZK.Sim.RdE.pi`).
  No collision term is added: the further sessions are part of the distinguisher in every hop of
  the two-session proof, run on whatever tables that hop's game runs on.
* **`N` pairs is a hybrid over the pairs** (`abs_sub_le_mul_of_steps`): step `k` changes pair
  `k`'s bit; it is the one-pair game of `A.hop k v` with the other `2(N − 1)` sessions as further
  sessions in their current worlds (`realGameP_iff`, the tape split `splitP`).

## The bounds

* `blindnessN_lean_numG` (every row type with `ZKRow`, `ZK2ARow`), `blindnessN_lean_num`
  (function rows), `blindnessN_lean_num_perm` (AES as random permutations):

      |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 5m·624 + 1872, q_E + 5m·4607 + 23035)
                           + 2·noHitProb + 2·2⁻¹²⁸,

  linear in `m`; in numbers (`blindnessN_lean_le`) `≤ n·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`
  with `n = m + 2` sessions in all: `≤ 2⁻⁸³` for `n ≤ 2²⁰` (`blindnessN_lean_2pow20`) and
  `≤ 2⁻⁷¹` for `n ≤ 2³²` (`blindnessN_lean_2pow32`), plus the guess's budget terms.
* `blindnessP_lean_numG`, `blindnessP_lean_num`, `blindnessP_lean_num_perm`: any two worlds of
  the `N`-pair game differ by `≤ N·εPair`, `εPair` the one-pair bound with `m = 2(N − 1)`; in
  numbers (`blindnessP_lean_le`) `≤ N·(2N·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸)`: `≤ 2⁻⁶⁴` for
  `2N ≤ 2²⁰` sessions, `≤ 2⁻⁴⁰` for `2N ≤ 2³²` (`blindnessP_lean_2pow20`, `_2pow32`), plus `N`
  times the guess's budget terms. Quadratic in the number of sessions: each of the `N` hops pays
  for the others' `2(N − 1)` sessions' cipher reads in its H4 hop (`221·4607` per session and
  hop). This is an artifact of the key-level hop (a read at a hidden key, at any input, is
  charged), not an attack: with the per-proof `iv` in the cipher's inputs only a key **and** iv
  collision makes sessions interfere, and the bound would be linear; Lean would need `H₄` as a
  table and a point-level H4 (`lean/docs/zk.md` §10.8, "Is the quadratic term inherent?").

The per-session `H₃` slices are independent tables, as in every slice game (a modelling step:
two sessions with equal `(r, binder)` would share their `H₃` inputs; `lean/docs/zk.md` §10.2).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## An honest session on the tables, and what it reads -/

section Honest

variable (Hb : Hashes)

/-- **An honest Client session on the tables**: the spec's `issue_request` and `finalize_issue`
on `Layout.labelRows` with the Lean prover on the shared tables and the session's `H₃` slice, for
the key `pk` and message `msg` (`realSession`). -/
noncomputable def sessX (pk : UOVKey) (msg : Bytes) (x : XR) (s : ShP R) : Session :=
  realSession Layout.labelRows (leanProverRO Hb x.2 s) pk msg x.1

/-- An Issuer with key `pk` and nothing else (`tR`, `sigR` read the Issuer only at its key). -/
def keyAdv (pk : UOVKey) : AdversaryRO R := ⟨pk, fun _ => [], fun _ _ _ => [], fun _ _ _ _ _ => True⟩

variable {Hb}

/-- The keys a real session's step 1 reads. -/
noncomputable def s1Keys (Hb : Hashes) (x : XR) (s : ShP R) : RS pP :=
  (∅, ∅, step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s,
    step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s)

lemma s1Keys_card (x : XR) (s : ShP R) : (s1Keys Hb x s).2.2.1.card ≤ 624 ∧
    (s1Keys Hb x s).2.2.2.card ≤ 4607 := by
  refine ⟨card_image_le.trans ((List.toFinset_card_le _).trans (le_of_eq ?_)),
    card_image_le.trans (le_of_eq (by rw [card_range]; rfl))⟩
  exact @vgIn5_length (icPrg (rowFn s.2.2)) _ _ _ _ _ _

lemma s1Keys_cons (hHb : HashesWF Hb) (x : XR) (s s' : ShP R)
    (h5 : ∀ k ∈ (s1Keys Hb x s).2.2.1, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ (s1Keys Hb x s).2.2.2, s.2.2 k = s'.2.2 k) :
    s1Keys Hb x s' = s1Keys Hb x s ∧ s1R Hb x s' = s1R Hb x s := by
  obtain ⟨e5, eE, eS⟩ := step1_cons (R := R) (Hb := Hb) (st := stOf x.1.2.1)
    (r := toBA (List.ofFn x.1.2.2)) hHb (ba x.1.1) x.2 s s' h5 hE
  refine ⟨?_, ?_⟩
  · unfold s1Keys
    rw [e5, eE]
  · unfold s1R
    rw [eS]

/-- **A real session's step 1 is a consistent reader** of `H₅` (`624` keys) and the cipher
(`4607` keys), and reads neither `H₂³` nor any slice. -/
theorem s1R_sreads (hHb : HashesWF Hb) (x : XR) :
    SReads pP (fun t : Tb R pP => s1R Hb x t.2) 0 0 624 4607 := by
  refine ⟨fun t => s1Keys Hb x t.2, fun t t' h => ?_, fun t => ⟨?_, ?_, (s1Keys_card x t.2).1,
    (s1Keys_card x t.2).2⟩⟩
  · exact s1Keys_cons hHb x t.2 t'.2 h.2.2.1 h.2.2.2
  · simp [s1Keys]
  · simp [s1Keys]

/-- The step-1 state of an honest session on the tables. -/
noncomputable def y1 (Hb : Hashes) (x : XR) (s : ShP R) : Prover.Pending :=
  @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
    CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1)

/-- An honest session from its step-1 state `y`: the request, and the Client's checks followed by
step 2 on the record of the tables. -/
noncomputable def sessOf (Hb : Hashes) (pk : UOVKey) (msg : Bytes) (x : XR) (y : Prover.Pending) (s : ShP R) :
    Session :=
  (tOf (keyAdv (R := R) pk) msg x.1.2.1 x.1.2.2 (y.proof, y.chal1), fun resp =>
    finish pk (tOf (keyAdv (R := R) pk) msg x.1.2.1 x.1.2.2 (y.proof, y.chal1))
      (toL ((Prover.proveCommit (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
        (withInst (stOf x.1.2.1) (leanInst pk (toBA (hOf (keyAdv (R := R) pk) msg x.1.2.1
          (y.proof, y.chal1))) (toBA (List.ofFn x.1.2.1)))) (toBA resp) y).toOption.getD .empty) ++
        comOf x.1.2.1 ++ List.ofFn x.1.2.1) resp)

lemma sessX_eq (pk : UOVKey) (msg : Bytes) (x : XR) (s : ShP R) :
    sessX Hb pk msg x s = sessOf Hb pk msg x (y1 Hb x s) s := by
  exact realSession_eq Hb (keyAdv pk) msg x s

/-- **An honest session's request is a consistent reader** (step 1's keys). -/
theorem sessX_req_sreads (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (x : XR) :
    SReads pP (fun t : Tb R pP => (sessX Hb pk msg x t.2).1) 0 0 624 4607 := by
  have h := (s1R_sreads (R := R) hHb x).map (tOf (keyAdv (R := R) pk) msg x.1.2.1 x.1.2.2)
  refine (congrArg (fun F => SReads pP F 0 0 624 4607) (funext fun t => ?_)).mp h
  rw [sessX_eq]
  rfl

/-- **An honest session reads `H₅` at most at `624` keys** (step 2 does not read it). -/
theorem sessX_rd5 (pk : UOVKey) (msg : Bytes) (x : XR) : Rd5 (sessX (R := R) Hb pk msg x) 624 := by
  have h := Rd5.bind' (fun s => sessX_eq (R := R) (Hb := Hb) pk msg x s)
    (step1_rd5 (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2)
    (b := 0) fun y => Rd5.of_indep _ fun s G5 => by
      have hA : (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 G5).AgreeOff .h5
          (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1) :=
        recHp_agreeOff_h5 (p := pP) (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) x.2 s.1 G5
          s.2.1
      simp only [sessOf, proveCommit_agreeOff_h5 hA]
  simpa using h

/-- **An honest session reads the cipher at most at `4607` keys** (step 2 does not use it). -/
theorem sessX_rdE (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (x : XR) :
    RdE (sessX (R := R) Hb pk msg x) 4607 := by
  have h := RdE.bind' (fun s => sessX_eq (R := R) (Hb := Hb) pk msg x s)
    (step1_rdE (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) hHb (ba x.1.1) x.2)
    (b := 0) fun y => RdE.of_indep (R := R) (p := pP) (sessOf Hb pk msg x y) fun s E => rfl
  simpa using h

end Honest

/-! ## The many-session game -/

section Game

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The Issuer of the many-session game**: the challenge pair's key and messages, a key and a
message for each of the further honest sessions `j : ι`, the responses to every session (each a
function of all requests), and a guess that sees all requests, the challenge signatures (in message
order, only if both challenge sessions complete), every further session's outcome, all slices and
the tables. The interaction does not read the tables. -/
structure AdversaryN (R : Type) (ι : Type) where
  pk : UOVKey
  msg : Bool → Bytes
  pkX : ι → UOVKey
  msgX : ι → Bytes
  respond : Bytes → Bytes → (ι → Bytes) → Bool → Bytes
  respondX : Bytes → Bytes → (ι → Bytes) → ι → Bytes
  guess : Bytes → Bytes → (ι → Bytes) → Option (Bytes × Bytes) → (ι → Except Error (Option Bytes)) →
    SlP → (ι → Tab3) → ShP R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`
(each with everything else fixed); `H₂³` and the further sessions' slices freely. -/
structure AdversaryN.Budget (A : AdversaryN R ι) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ t₀ t₁ tx y ox (g₁ : Tab3) slx s, Rd3 (fun g => A.guess t₀ t₁ tx y ox (g, g₁) slx s) q3
  h31 : ∀ t₀ t₁ tx y ox (g₀ : Tab3) slx s, Rd3 (fun g => A.guess t₀ t₁ tx y ox (g₀, g) slx s) q3
  h5 : ∀ t₀ t₁ tx y ox sl slx, Rd5 (A.guess t₀ t₁ tx y ox sl slx) q5
  hE : ∀ t₀ t₁ tx y ox sl slx, RdE (A.guess t₀ t₁ tx y ox sl slx) qE

variable (Hb : Hashes)

/-- The further sessions' requests on the tables. -/
noncomputable def txOf (A : AdversaryN R ι) (c : ι → XR) (s : ShP R) : ι → Bytes :=
  fun j => (sessX Hb (A.pkX j) (A.msgX j) (c j) s).1

/-- **The real many-session game** in world `b`: the challenge sessions on `µ_b`, `µ_{¬b}` and
the further honest sessions, all with the Lean prover on the shared tables (each with its own
`H₃` slice); the Issuer answers after seeing every request. -/
noncomputable def realGameN (A : AdversaryN R ι) (b : Bool) (z : ((XR × XR) × (ι → XR)) × ShP R) :
    Prop :=
  A.guess (sessX Hb A.pk (A.msg b) z.1.1.1 z.2).1 (sessX Hb A.pk (A.msg !b) z.1.1.2 z.2).1
    (txOf Hb A z.1.2 z.2)
    (outcome b ((sessX Hb A.pk (A.msg b) z.1.1.1 z.2).2 (A.respond (sessX Hb A.pk (A.msg b) z.1.1.1 z.2).1
        (sessX Hb A.pk (A.msg !b) z.1.1.2 z.2).1 (txOf Hb A z.1.2 z.2) false))
      ((sessX Hb A.pk (A.msg !b) z.1.1.2 z.2).2 (A.respond (sessX Hb A.pk (A.msg b) z.1.1.1 z.2).1
        (sessX Hb A.pk (A.msg !b) z.1.1.2 z.2).1 (txOf Hb A z.1.2 z.2) true)))
    (fun j => (sessX Hb (A.pkX j) (A.msgX j) (z.1.2 j) z.2).2
      (A.respondX (sessX Hb A.pk (A.msg b) z.1.1.1 z.2).1 (sessX Hb A.pk (A.msg !b) z.1.1.2 z.2).1
        (txOf Hb A z.1.2 z.2) j))
    (z.1.1.1.2, z.1.1.2.2) (fun j => (z.1.2 j).2) z.2

/-- **The reduction**: the Issuer of the two-session game with table-reading interaction that runs
the further honest sessions itself, with their tapes `c` fixed. Its responses read the further
sessions' requests (step 1 of each), its guess runs them to the end. -/
noncomputable def AdversaryN.red (A : AdversaryN R ι) (c : ι → XR) : AdversaryRA R where
  pk _ _ := A.pk
  msg b _ _ := A.msg b
  respond t₀ t₁ i _ s := A.respond t₀ t₁ (txOf Hb A c s) i
  guess t₀ t₁ y sl s := A.guess t₀ t₁ (txOf Hb A c s) y
    (fun j => (sessX Hb (A.pkX j) (A.msgX j) (c j) s).2 (A.respondX t₀ t₁ (txOf Hb A c s) j)) sl
    (fun j => (c j).2) s

/-- **The many-session game is the two-session game of the reduction**, tape by tape. -/
theorem realGameN_iff (A : AdversaryN R ι) (b : Bool) (a : XR × XR) (c : ι → XR) (s : ShP R) :
    realGameN Hb A b ((a, c), s) ↔ realGameRA Hb (A.red Hb c) b (a, s) :=
  Iff.rfl

variable {Hb}

/-- The further sessions' requests, read together. -/
lemma txOf_sreads (hHb : HashesWF Hb) (A : AdversaryN R ι) (c : ι → XR) :
    SReads pP (fun t : Tb R pP => txOf Hb A c t.2) 0 0 (Fintype.card ι * 624)
      (Fintype.card ι * 4607) := by
  exact SReads.pi (ι := ι) (f := fun j (t : Tb R pP) => (sessX Hb (A.pkX j) (A.msgX j) (c j) t.2).1)
    fun j => sessX_req_sreads hHb (A.pkX j) (A.msgX j) (c j)

/-- **The reduction's interaction budget**: no slice key, no `H₂³` key, the further sessions'
step-1 keys. -/
theorem AdversaryN.red_iBudget (hHb : HashesWF Hb) (A : AdversaryN R ι) (c : ι → XR) :
    (A.red Hb c).IBudget 0 (Fintype.card ι * 624) (Fintype.card ι * 4607) where
  k0 _ := (SReads.const (R := R) (p := pP) (A.pk, A.msg false, A.msg true)).mono le_rfl le_rfl
    (Nat.zero_le _) (Nat.zero_le _)
  k1 _ := (SReads.const (R := R) (p := pP) (A.pk, A.msg false, A.msg true)).mono le_rfl le_rfl
    (Nat.zero_le _) (Nat.zero_le _)
  r0 t₀ t₁ _ := (txOf_sreads hHb A c).map fun y => (A.respond t₀ t₁ y false, A.respond t₀ t₁ y true)
  r1 t₀ t₁ _ := (txOf_sreads hHb A c).map fun y => (A.respond t₀ t₁ y false, A.respond t₀ t₁ y true)

/-- **The reduction's guess budget**: the Issuer's plus the further sessions' reads. -/
theorem AdversaryN.red_gBudget (hHb : HashesWF Hb) (A : AdversaryN R ι) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (c : ι → XR) :
    (A.red Hb c).GBudget q3 (Fintype.card ι * 624 + q5) (Fintype.card ι * 4607 + qE) where
  h30 _ _ _ g₁ s := hA.h30 _ _ _ _ _ g₁ _ s
  h31 _ _ _ g₀ s := hA.h31 _ _ _ _ _ g₀ _ s
  h5 t₀ t₁ y sl := Rd5.bind' (m := fun s j => sessX Hb (A.pkX j) (A.msgX j) (c j) s)
    (f := fun (w : ι → Session) s => A.guess t₀ t₁ (fun j => (w j).1) y
      (fun j => (w j).2 (A.respondX t₀ t₁ (fun j => (w j).1) j)) sl (fun j => (c j).2) s)
    (fun _ => rfl) (Rd5.pi fun j => sessX_rd5 (A.pkX j) (A.msgX j) (c j))
    fun _ => hA.h5 _ _ _ _ _ _ _
  hE t₀ t₁ y sl := RdE.bind' (m := fun s j => sessX Hb (A.pkX j) (A.msgX j) (c j) s)
    (f := fun (w : ι → Session) s => A.guess t₀ t₁ (fun j => (w j).1) y
      (fun j => (w j).2 (A.respondX t₀ t₁ (fun j => (w j).1) j)) sl (fun j => (c j).2) s)
    (fun _ => rfl) (RdE.pi fun j => sessX_rdE hHb (A.pkX j) (A.msgX j) (c j))
    fun _ => hA.hE _ _ _ _ _ _ _

/-- The many-session tape, with the further sessions' tapes first. -/
def tapeN : (ι → XR) × ((XR × XR) × ShP R) ≃ ((XR × XR) × (ι → XR)) × ShP R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## Many challenge pairs -/

section Pairs

variable {N : ℕ}

/-- **The Issuer of the game with `N` challenge pairs**: for each pair `j` a key and two messages,
the responses to every session (each a function of all requests), and a guess that sees all
requests, each pair's signatures (in message order, only if both of its sessions complete), all
slices and the tables. The interaction does not read the tables. -/
structure AdversaryP (R : Type) (N : ℕ) where
  pk : Fin N → UOVKey
  msg : Fin N → Bool → Bytes
  respond : (Fin N → Bytes × Bytes) → Fin N → Bool → Bytes
  guess : (Fin N → Bytes × Bytes) → (Fin N → Option (Bytes × Bytes)) → (Fin N → SlP) → ShP R → Prop

/-- **The guess's budget**: each of the `2N` slices at `q3` keys, `H₅` at `q5`, the cipher at
`qE` (each with everything else fixed); `H₂³` freely. -/
structure AdversaryP.Budget (A : AdversaryP R N) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T Y (sl : Fin N → SlP) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k (g, (sl k).2)) s) q3
  h31 : ∀ T Y (sl : Fin N → SlP) s k,
    Rd3 (fun g => A.guess T Y (Function.update sl k ((sl k).1, g)) s) q3
  h5 : ∀ T Y sl, Rd5 (A.guess T Y sl) q5
  hE : ∀ T Y sl, RdE (A.guess T Y sl) qE

variable (Hb : Hashes)

/-- The two sessions of pair `j` in world `w` (the first on `µ_{w j}`, the second on
`µ_{¬w j}`). -/
noncomputable def sessP (A : AdversaryP R N) (w : Fin N → Bool) (z : Fin N → XR × XR) (s : ShP R)
    (j : Fin N) : Session × Session :=
  (sessX Hb (A.pk j) (A.msg j (w j)) (z j).1 s, sessX Hb (A.pk j) (A.msg j (!w j)) (z j).2 s)

/-- All requests. -/
noncomputable def reqP (A : AdversaryP R N) (w : Fin N → Bool) (z : Fin N → XR × XR) (s : ShP R) :
    Fin N → Bytes × Bytes :=
  fun j => ((sessP Hb A w z s j).1.1, (sessP Hb A w z s j).2.1)

/-- **The real game with `N` challenge pairs** in world `w : Fin N → Bool`. -/
noncomputable def realGameP (A : AdversaryP R N) (w : Fin N → Bool) (z : (Fin N → XR × XR) × ShP R) :
    Prop :=
  A.guess (reqP Hb A w z.1 z.2)
    (fun j => outcome (w j) ((sessP Hb A w z.1 z.2 j).1.2 (A.respond (reqP Hb A w z.1 z.2) j false))
      ((sessP Hb A w z.1 z.2 j).2.2 (A.respond (reqP Hb A w z.1 z.2) j true)))
    (fun j => ((z.1 j).1.2, (z.1 j).2.2)) z.2

/-- The other pairs' sessions, as the further sessions of the game for pair `k`. -/
abbrev Oth (k : Fin N) := {j : Fin N // j ≠ k} × Bool

/-- Pair `k`'s value and the other sessions' values, as one value per pair. -/
def joinP {α : Type*} (k : Fin N) (a : α × α) (f : Oth k → α) : Fin N → α × α :=
  fun j => if h : j = k then a else (f (⟨j, h⟩, false), f (⟨j, h⟩, true))

lemma joinP_self {α : Type*} (k : Fin N) (a : α × α) (f : Oth k → α) : joinP k a f k = a :=
  dite_eq_left_iff.2 fun h => absurd rfl h

lemma joinP_ne {α : Type*} {k j : Fin N} (a : α × α) (f : Oth k → α) (h : j ≠ k) :
    joinP k a f j = (f (⟨j, h⟩, false), f (⟨j, h⟩, true)) := by
  simp only [joinP, h, dite_false]

/-- **The tape split at pair `k`**: pair `k`'s tapes, the other sessions' tapes. -/
def splitP (k : Fin N) : (Fin N → XR × XR) ≃ (XR × XR) × (Oth k → XR) where
  toFun z := (z k, fun jb => bif jb.2 then (z jb.1).2 else (z jb.1).1)
  invFun q := joinP k q.1 q.2
  left_inv z := funext fun j => by
    show joinP k (z k) (fun jb => bif jb.2 then (z jb.1).2 else (z jb.1).1) j = z j
    by_cases h : j = k
    · subst h; exact joinP_self _ _ _
    · rw [joinP_ne _ _ h]; rfl
  right_inv q := by
    refine Prod.ext (joinP_self _ _ _) (funext fun jb => ?_)
    obtain ⟨⟨j, h⟩, b⟩ := jb
    cases b <;> simp only [joinP_ne _ _ h, Bool.cond_false, Bool.cond_true]

/-- **The Issuer of the game for pair `k`**, the other pairs' sessions further honest sessions,
their worlds `v`. -/
def AdversaryP.hop (A : AdversaryP R N) (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool) :
    AdversaryN R (Oth k) where
  pk := A.pk k
  msg := A.msg k
  pkX jb := A.pk jb.1
  msgX jb := A.msg jb.1 (bif jb.2 then !v jb.1 else v jb.1)
  respond t₀ t₁ tx i := A.respond (joinP k (t₀, t₁) tx) k i
  respondX t₀ t₁ tx jb := A.respond (joinP k (t₀, t₁) tx) jb.1 jb.2
  guess t₀ t₁ tx y ox sl slx s := A.guess (joinP k (t₀, t₁) tx)
    (fun j => if h : j = k then y else outcome (v ⟨j, h⟩) (ox (⟨j, h⟩, false)) (ox (⟨j, h⟩, true)))
    (joinP k sl slx) s

/-- **The game with `N` pairs is, at pair `k`, the many-session game of `A.hop k`**, tape by
tape. -/
theorem realGameP_iff (A : AdversaryP R N) (w : Fin N → Bool) (k : Fin N)
    (z : (Fin N → XR × XR) × ShP R) :
    realGameP Hb A w z ↔
      realGameN Hb (A.hop k fun j => w j.1) (w k) ((splitP k z.1), z.2) := by
  obtain ⟨z, s⟩ := z
  have key : ∀ T T' Y Y' S S', T = T' → Y = Y' → S = S' → (A.guess T Y S s ↔ A.guess T' Y' S' s) := by
    rintro _ _ _ _ _ _ rfl rfl rfl
    exact Iff.rfl
  have eT : reqP Hb A w z s = joinP k ((sessX Hb (A.pk k) (A.msg k (w k)) (z k).1 s).1,
      (sessX Hb (A.pk k) (A.msg k (!w k)) (z k).2 s).1)
      (txOf Hb (A.hop k fun j => w j.1) (splitP k z).2 s) := by
    funext j
    by_cases h : j = k
    · subst h; exact (joinP_self _ _ _).symm
    · rw [joinP_ne _ _ h]; rfl
  refine key _ _ _ _ _ _ eT (funext fun j => ?_) (funext fun j => ?_)
  · by_cases h : j = k
    · subst h
      simp only [dite_true]
      rw [eT]
      rfl
    · simp only [h, dite_false]
      rw [eT]
      rfl
  · by_cases h : j = k
    · subst h; exact (joinP_self _ _ _).symm
    · rw [joinP_ne _ _ h]; rfl

omit [Fintype R] [Nonempty R] in
lemma card_oth (k : Fin N) : Fintype.card (Oth k) = (N - 1) * 2 := by
  simp [Oth, Fintype.card_prod, Fintype.card_subtype_compl]

variable {Hb}

/-- The budget of the game for pair `k`. -/
theorem AdversaryP.hop_budget {A : AdversaryP R N} {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) (k : Fin N)
    (v : {j : Fin N // j ≠ k} → Bool) : (A.hop k v).Budget q3 q5 qE where
  h30 t₀ t₁ tx y ox g₁ slx s := by
    have e : (fun g => (A.hop k v).guess t₀ t₁ tx y ox (g, g₁) slx s) = fun g =>
        A.guess (joinP k (t₀, t₁) tx) (fun j => if h : j = k then y else
          outcome (v ⟨j, h⟩) (ox (⟨j, h⟩, false)) (ox (⟨j, h⟩, true)))
          (Function.update (joinP k (g₁, g₁) slx) k (g, (joinP k (g₁, g₁) slx k).2)) s := by
      funext g
      show A.guess _ _ (joinP k (g, g₁) slx) s = A.guess _ _ _ s
      congr 1
      funext j
      by_cases h : j = k
      · subst h; rw [Function.update_self, joinP_self, joinP_self]
      · rw [Function.update_of_ne h, joinP_ne _ _ h, joinP_ne _ _ h]
    rw [e]
    exact hA.h30 _ _ _ s k
  h31 t₀ t₁ tx y ox g₀ slx s := by
    have e : (fun g => (A.hop k v).guess t₀ t₁ tx y ox (g₀, g) slx s) = fun g =>
        A.guess (joinP k (t₀, t₁) tx) (fun j => if h : j = k then y else
          outcome (v ⟨j, h⟩) (ox (⟨j, h⟩, false)) (ox (⟨j, h⟩, true)))
          (Function.update (joinP k (g₀, g₀) slx) k ((joinP k (g₀, g₀) slx k).1, g)) s := by
      funext g
      show A.guess _ _ (joinP k (g₀, g) slx) s = A.guess _ _ _ s
      congr 1
      funext j
      by_cases h : j = k
      · subst h; rw [Function.update_self, joinP_self, joinP_self]
      · rw [Function.update_of_ne h, joinP_ne _ _ h, joinP_ne _ _ h]
    rw [e]
    exact hA.h31 _ _ _ s k
  h5 _ _ _ _ _ _ _ := hA.h5 _ _ _
  hE _ _ _ _ _ _ _ := hA.hE _ _ _

end Pairs


/-! ## The bound -/

section Bound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **PomFRIT blindness with many sessions, for every type of cipher rows** (`ZKRow R`,
`ZK2ARow R`; SHAKE as the base record): with `m = |ι|` further honest sessions besides the
challenge pair,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃, q₅ + 5m·624 + 1872, q_E + 5m·4607 + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessN_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryN R ι) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (ι → XR)) × ShP R) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP R) (realGameN Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP q3 (q5 + 5 * (Fintype.card ι * 624) + 1872)
          (qE + 5 * (Fintype.card ι * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128 := by
  rw [← pr_equiv tapeN, ← pr_equiv tapeN]
  refine abs_pr_prod_sub_le _ _ fun c => ?_
  have h := blindnessRA_lean_numG (A.red Hashes.shake c) (A.red_gBudget hashesWF_shake hA c)
    (A.red_iBudget hashesWF_shake c)
  have m := ZKRow.εz_mono (R := R) pP (q3 := q3 + 4 * 0) (q3' := q3)
    (q5 := Fintype.card ι * 624 + q5 + 4 * (Fintype.card ι * 624) + 1872)
    (q5' := q5 + 5 * (Fintype.card ι * 624) + 1872)
    (qE := Fintype.card ι * 4607 + qE + 4 * (Fintype.card ι * 4607) + 23035)
    (qE' := qE + 5 * (Fintype.card ι * 4607) + 23035) (by omega) (by omega) (by omega)
  exact h.trans (by linarith)

/-- **PomFRIT blindness with many sessions** (function rows; SHAKE as the base record):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 5m·624 + 1872, q_E + 5m·4607 + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸,

`m` the number of further honest sessions. -/
theorem blindnessN_lean_num (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A true)| ≤
      4 * εRO q3 (q5 + 5 * (Fintype.card ι * 624) + 1872) (qE + 5 * (Fintype.card ι * 4607) + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessN_lean_numG A hA

/-- **PomFRIT blindness with many sessions and AES as uniformly random permutations**
(`blindnessN_lean_numG` at permutation rows). -/
theorem blindnessN_lean_num_perm (A : AdversaryN (Equiv.Perm Blk) ι) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (ι → XR)) × ShP (Equiv.Perm Blk)) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP (Equiv.Perm Blk)) (realGameN Hashes.shake A true)| ≤
      4 * εROPm pP q3 (q5 + 5 * (Fintype.card ι * 624) + 1872)
          (qE + 5 * (Fintype.card ι * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessN_lean_numG A hA

/-- **The many-session bound in numbers**: with `n = m + 2` sessions in all,

    |Pr[W₀] − Pr[W₁]| ≤ n·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸,

so `≤ 2⁻⁸³` for `n ≤ 2²⁰` and `≤ 2⁻⁷¹` for `n ≤ 2³²` sessions, plus the guess's budget terms. -/
theorem blindnessN_lean_le (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A true)| ≤
      (Fintype.card ι + 2 : ℕ) / 2 ^ 103 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessN_lean_num A hA
  have hn := noHitProb_le_128
  unfold εRO at h
  push_cast at h ⊢
  have e : ∀ x : ℝ, x / 2 ^ 103 = x * 33554432 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  linarith

/-- **`2²⁰` sessions**: `≤ 2⁻⁸³` plus the guess's budget terms. -/
theorem blindnessN_lean_2pow20 (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hn : Fintype.card ι + 2 ≤ 2 ^ 20) :
    |pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A true)| ≤
      1 / 2 ^ 83 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessN_lean_le A hA
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 103 ≤ 1 / 2 ^ 83 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` sessions**: `≤ 2⁻⁷¹` plus the guess's budget terms. -/
theorem blindnessN_lean_2pow32 (A : AdversaryN (Blk → Blk) ι) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hn : Fintype.card ι + 2 ≤ 2 ^ 32) :
    |pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A false) -
        pr (((XR × XR) × (ι → XR)) × ShP (Blk → Blk)) (realGameN Hashes.shake A true)| ≤
      1 / 2 ^ 71 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessN_lean_le A hA
  have : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℝ) / 2 ^ 103 ≤ 1 / 2 ^ 71 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- The error of one pair's step in the game with `N` pairs: the many-session bound with the
`2(N − 1)` sessions of the other pairs as further sessions. -/
noncomputable def εPair (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (N q3 q5 qE : ℕ) : ℝ :=
  4 * ZKRow.εz R pP q3 (q5 + 5 * ((N - 1) * 2 * 624) + 1872) (qE + 5 * ((N - 1) * 2 * 4607) + 23035) +
    2 * noHitProb + 2 / 2 ^ 128

lemma εPair_nonneg [ZKRow R] (N q3 q5 qE : ℕ) : 0 ≤ εPair R N q3 q5 qE := by
  have := ZKRow.εz_nonneg (R := R) pP q3 (q5 + 5 * ((N - 1) * 2 * 624) + 1872)
    (qE + 5 * ((N - 1) * 2 * 4607) + 23035)
  have : 0 ≤ noHitProb := pr_nonneg _
  have : (0 : ℝ) ≤ 2 / 2 ^ 128 := by positivity
  unfold εPair
  linarith

/-- **PomFRIT blindness with `N` challenge pairs, for every type of cipher rows**: any two worlds
`w`, `w' : Fin N → Bool` differ by at most `N` times the many-session bound with `2(N − 1)`
further sessions (a hybrid over the pairs, `abs_sub_le_mul_of_steps`; each step is
`blindnessN_lean_numG` for the pair that changes, the other pairs' sessions run as honest
sessions in their current worlds). -/
theorem blindnessP_lean_numG [ZKRow R] [ZK2ARow R] {N : ℕ} (A : AdversaryP R N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) :
    |pr ((Fin N → XR × XR) × ShP R) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP R) (realGameP Hashes.shake A w')| ≤ N * εPair R N q3 q5 qE := by
  let mix : ℕ → Fin N → Bool := fun k j => if j.val < k then w' j else w j
  let P : ℕ → ℝ := fun k => pr ((Fin N → XR × XR) × ShP R) (realGameP Hashes.shake A (mix k))
  have h0 : mix 0 = w := funext fun j => by simp [mix]
  have hN : mix N = w' := funext fun j => by simp [mix, j.isLt]
  have key := abs_sub_le_mul_of_steps P (εPair R N q3 q5 qE) N fun k hk => by
    let kk : Fin N := ⟨k, hk⟩
    have e : ∀ v : Fin N → Bool, pr ((Fin N → XR × XR) × ShP R) (realGameP Hashes.shake A v) =
        pr (((XR × XR) × (Oth kk → XR)) × ShP R)
          (realGameN Hashes.shake (A.hop kk fun j => v j.1) (v kk)) := fun v => by
      rw [← pr_equiv ((splitP kk).prodCongr (Equiv.refl (ShP R)))]
      exact pr_congr fun z => realGameP_iff Hashes.shake A v kk z
    have hv : (fun j : {j : Fin N // j ≠ kk} => mix k j.1) = fun j => mix (k + 1) j.1 := by
      funext ⟨j, hj⟩
      have : j.val ≠ k := fun h => hj (Fin.ext h)
      simp only [mix]
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    have m0 : mix k kk = w kk := by simp [mix, kk]
    have m1 : mix (k + 1) kk = w' kk := by simp [mix, kk]
    show |pr _ (realGameP Hashes.shake A (mix k)) - pr _ (realGameP Hashes.shake A (mix (k + 1)))| ≤ _
    rw [e, e, ← hv, m0, m1]
    have hb := blindnessN_lean_numG (A.hop kk fun j => mix k j.1) (AdversaryP.hop_budget hA kk _)
    rw [card_oth] at hb
    have hz := εPair_nonneg (R := R) N q3 q5 qE
    rcases hw : w kk <;> rcases hw' : w' kk
    · simpa using hz
    · exact hb
    · rw [abs_sub_comm]; exact hb
    · simpa using hz
  simpa only [P, h0, hN] using key

/-- **PomFRIT blindness with `N` challenge pairs** (function rows; SHAKE as the base record). -/
theorem blindnessP_lean_num {N : ℕ} (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) :
    |pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w')| ≤
      N * (4 * εRO q3 (q5 + 5 * ((N - 1) * 2 * 624) + 1872) (qE + 5 * ((N - 1) * 2 * 4607) + 23035) +
        2 * noHitProb + 2 / 2 ^ 128) :=
  blindnessP_lean_numG A hA w w'

/-- **PomFRIT blindness with `N` challenge pairs and AES as uniformly random permutations**. -/
theorem blindnessP_lean_num_perm {N : ℕ} (A : AdversaryP (Equiv.Perm Blk) N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) :
    |pr ((Fin N → XR × XR) × ShP (Equiv.Perm Blk)) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP (Equiv.Perm Blk)) (realGameP Hashes.shake A w')| ≤
      N * (4 * εROPm pP q3 (q5 + 5 * ((N - 1) * 2 * 624) + 1872)
          (qE + 5 * ((N - 1) * 2 * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128) :=
  blindnessP_lean_numG A hA w w'

/-- **`N` pairs in numbers**: `≤ N·(2N·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸)`, so `≤ 2⁻⁶⁴` for
`2N ≤ 2²⁰` sessions and `≤ 2⁻⁴⁰` for `2N ≤ 2³²`, plus `N` times the guess's budget terms. -/
theorem blindnessP_lean_le {N : ℕ} (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) :
    |pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w')| ≤
      N * ((2 * N : ℕ) / 2 ^ 103 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0
    have : w = w' := funext fun j => j.elim0
    subst this
    simp
  refine (blindnessP_lean_num A hA w w').trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hn := noHitProb_le_128
  have hm : ((N - 1 : ℕ) : ℝ) + 1 = N := by
    rw [Nat.cast_sub hN0]; simp
  unfold εRO
  push_cast
  have e : ∀ x : ℝ, x / 2 ^ 103 = x * 33554432 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  have h1 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **`2²⁰` sessions in `N` pairs**: `≤ 2⁻⁶⁴` plus `N` times the guess's budget terms. -/
theorem blindnessP_lean_2pow20 {N : ℕ} (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 20) :
    |pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w')| ≤
      1 / 2 ^ 64 + N * (4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  have h := blindnessP_lean_le A hA w w'
  have h1 : (N : ℝ) ≤ 2 ^ 19 := by
    have : N ≤ 2 ^ 19 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((2 * N : ℕ) / 2 ^ 103) ≤ 1 / 2 ^ 64 := by
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [mul_add] at h
  linarith

/-- **`2³²` sessions in `N` pairs**: `≤ 2⁻⁴⁰` plus `N` times the guess's budget terms. -/
theorem blindnessP_lean_2pow32 {N : ℕ} (A : AdversaryP (Blk → Blk) N) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 32) :
    |pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w) -
        pr ((Fin N → XR × XR) × ShP (Blk → Blk)) (realGameP Hashes.shake A w')| ≤
      1 / 2 ^ 40 + N * (4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  have h := blindnessP_lean_le A hA w w'
  have h1 : (N : ℝ) ≤ 2 ^ 31 := by
    have : N ≤ 2 ^ 31 := by omega
    exact_mod_cast this
  have h2 : (N : ℝ) * ((2 * N : ℕ) / 2 ^ 103) ≤ 1 / 2 ^ 40 := by
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  rw [mul_add] at h
  linarith

end Bound

end VoleMole.Privacy.PomFRIT
