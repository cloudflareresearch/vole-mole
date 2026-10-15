import VoleMole.Privacy.PomFRITLean
import VoleMole.ZK.TwoPhaseReadsRO

/-!
# PomFRIT blindness in the random-oracle and ideal-cipher model

`Privacy.PomFRIT.blindness_lean_shake` (`Privacy/PomFRITLean.lean`) assumes the hop hypotheses of
the two-phase tape argument. Here the Issuer also sees the random tables the proofs are computed
with, as in `ZK.Sim.zk2_rom_ic_h23_num`, and both sessions **share** them: `H₂³` on every grinding
point, `H₅` on every `37`-byte input, the cipher of the whole BAVC and VOLE expansion (`ShP`), and
each session's own `H₃` slice (`Tab3`).

## The model

* **The Issuer** (`AdversaryRO`): `Adversary`'s key, messages and responses, which **do not read
  the tables** (as in `Privacy/MoussakaRO.lean`), and a guess that sees all tables, with a budget
  (`Budget`): `q₃` keys of each slice, `q₅` of `H₅`, `q_E` of the cipher, `H₂³` freely.
* **The real game** (`realGameRO`): the spec's protocol (`realSession`, `issueRequestOf`,
  `Layout.finalizeIssue` on `Layout.labelRows`) with the Lean prover run on the tables
  (`leanProverRO`: step 1 `ZK.Sim.step1` and step 2 `Prover.proveCommit` with the record
  `recH Hb (st1 (leanBase com)) r G3 G2 G5` and the ideal-cipher PRG). `hash_to_target`, `XOF_seed`
  and the refresher commitment stay fixed functions (SHAKE).

## The hybrids (world `false`; world `true` is world `false` for the Issuer with the sessions'
roles exchanged, `A.swap`, `realGameRO_true`)

The Issuer answers both sessions after seeing both requests, so a session's instance is chosen by a
continuation that depends on the other session's request, which depends on the tables: this is
`zk2_ro`'s table-reading continuation (`Hyp2RO`). A session's step 2 is run only when **both**
responses are valid (`kOf`, `bothOK`): the view is the same (the signatures are revealed only
then, `realGameRO_iff`), and the simulators then program symmetrically.

* `G0` (both real) → `G1` (session `0` simulated): `zk2_ro` for session `0`, the distinguisher
  running session `1` for real (reads `624` `H₅` keys, `4607` cipher keys), the continuation
  reading session `1`'s step 1 (the same counts): `hop0`.
* `G1` → `G2` (both simulated): `zk2_ro` for session `1`, the distinguisher simulating session `0`
  and applying its programming with session `1`'s output (`312` `H₅` keys, `3·4607` cipher keys),
  the continuation reading the simulated session `0`'s step 1 (`4607` cipher keys), **plus the
  collision term** `δ = Pr[session 1, run for real, reads H₂³ differently on the tables session 0
  programmed]` (`deltaRO`, an explicit probability of the game; on paper it is the probability
  that session `1`'s grinding points meet session `0`'s, `lean/docs/zk.md` §10.2): `hop1`.
* `G2` for `A` and for `A.swap` coincide (`G2_swap`): the requests are one-time pads
  (`h ⊕ r`, re-parametrized by `r`) and the simulated sessions, their programming and the
  signatures depend on the responses only through `bothOK`, which is symmetric.

**`blindnessRO`**: for every Issuer with a budget,

    |Pr[A accepts in world 0] − Pr[A accepts in world 1]| ≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428)
      + δ(A) + δ(A.swap),

`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`.
**`blindnessRO_lean`**: the same with SHAKE.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

-- `Com` and the UOV map evaluate Keccak and the public map; nothing below needs to unfold them.
attribute [local irreducible] commitRefresher UOVKey.eval

/-- PomFRIT's parameters with dedicated label rows. -/
abbrev pP : Params := pomfritParams true

/-- **The tables both sessions share**: `H₂³`, `H₅`, the cipher. -/
abbrev ShP := Sh pP

/-- The two sessions' `H₃` slices. -/
abbrev SlP := Tab3 × Tab3

/-- **The Issuer in the random-oracle model**: `Adversary`'s interaction, which does not read the
tables, and a guess that sees all of them. -/
structure AdversaryRO where
  pk : UOVKey
  msg : Bool → Bytes
  respond : Bytes → Bytes → Bool → Bytes
  guess : Bytes → Bytes → Option (Bytes × Bytes) → SlP → ShP → Prop

/-- **The Issuer's budget**: its guess reads each slice at `q3` keys, `H₅` at `q5` and the cipher
at `qE` keys (each with everything else fixed), and `H₂³` freely. -/
structure AdversaryRO.Budget (A : AdversaryRO) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ t₀ t₁ y (g₁ : Tab3) s, Rd3 (fun g => A.guess t₀ t₁ y (g, g₁) s) q3
  h31 : ∀ t₀ t₁ y (g₀ : Tab3) s, Rd3 (fun g => A.guess t₀ t₁ y (g₀, g) s) q3
  h5 : ∀ t₀ t₁ y sl, Rd5 (A.guess t₀ t₁ y sl) q5
  hE : ∀ t₀ t₁ y sl, RdE (A.guess t₀ t₁ y sl) qE

/-- **The Issuer with the sessions' roles exchanged**: it answers and guesses with the two
requests (and slices) swapped. -/
def AdversaryRO.swap (A : AdversaryRO) : AdversaryRO where
  pk := A.pk
  msg := A.msg
  respond t₀ t₁ i := A.respond t₁ t₀ (!i)
  guess t₀ t₁ y sl s := A.guess t₁ t₀ y (sl.2, sl.1) s

lemma AdversaryRO.Budget.swap {A : AdversaryRO} {q3 q5 qE : ℕ} (h : A.Budget q3 q5 qE) :
    A.swap.Budget q3 q5 qE :=
  ⟨fun t₀ t₁ y g₁ s => h.h31 t₁ t₀ y g₁ s, fun t₀ t₁ y g₀ s => h.h30 t₁ t₀ y g₀ s,
    fun t₀ t₁ y sl => h.h5 t₁ t₀ y (sl.2, sl.1), fun t₀ t₁ y sl => h.hE t₁ t₀ y (sl.2, sl.1)⟩

/-! ## The real game: the spec's protocol with the Lean prover on the tables -/

section Real

variable (Hb : Hashes)

/-- **The Lean prover on the tables** (`leanProver` with the record of the random-oracle model and
the ideal-cipher PRG): step 1 on the record with the session's `H₃` slice `G3`, step 2 on the same
record (its state keeps the binder and `r`). -/
noncomputable def leanProverRO (G3 : Tab3) (s : ShP) :
    Prover (ByteArray × ByteArray × Prover.Pending) where
  voleGen r rho b :=
    let p := @step1 (icPrg s.2.2) (recH Hb (st1 (leanBase (toBA b))) (toBA r) G3 s.1 s.2.1)
      CrtGen.tables (leanBase (toBA b)) (toBA r) (toBA rho)
    (toL p.proof, toL p.chal1, (toBA b, toBA r, p))
  proveCommit _ pk h sfx b₂ st :=
    toL ((Prover.proveCommit (recH Hb (st1 (leanBase st.1)) st.2.1 G3 s.1 s.2.1)
      (withInst (leanBase st.1) (leanInst pk (toBA h) (toBA b₂))) (toBA sfx) st.2.2).toOption.getD
        .empty)

/-- A real session's tape: `rho`, the refresher, `r`, and its `H₃` slice. -/
abbrev XR := (Coins proveSeedBytes × Coins refresherBytes × Coins uovM) × Tab3

/-- The Issuer's view and guess, from the two sessions, with the slices and the tables. -/
def viewS (A : AdversaryRO) (b : Bool) (s₀ s₁ : Session) (sl : SlP) (v : ShP) : Prop :=
  A.guess s₀.1 s₁.1
    (outcome b (s₀.2 (A.respond s₀.1 s₁.1 false)) (s₁.2 (A.respond s₀.1 s₁.1 true))) sl v

/-- **The real game in the random-oracle and ideal-cipher model**: world `b`, the first session
on `µ_b`, the second on `µ_{¬b}`, both with the Lean prover on the shared tables. -/
noncomputable def realGameRO (A : AdversaryRO) (b : Bool) (z : (XR × XR) × ShP) : Prop :=
  viewS A b (realSession Layout.labelRows (leanProverRO Hb z.1.1.2 z.2) A.pk (A.msg b) z.1.1.1)
    (realSession Layout.labelRows (leanProverRO Hb z.1.2.2 z.2) A.pk (A.msg !b) z.1.2.1)
    (z.1.1.2, z.1.2.2) z.2

/-- Exchange the two sessions' tapes. -/
def swapXR : (XR × XR) × ShP ≃ (XR × XR) × ShP where
  toFun z := ((z.1.2, z.1.1), z.2)
  invFun z := ((z.1.2, z.1.1), z.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma outcome_swap (o₀ o₁ : Except Error (Option Bytes)) :
    outcome true o₀ o₁ = outcome false o₁ o₀ := by
  unfold outcome
  rcases o₀ with _ | _ | x <;> rcases o₁ with _ | _ | y <;> rfl

/-- **World `true` is world `false` for the Issuer with the roles exchanged.** -/
theorem realGameRO_true (A : AdversaryRO) (z : (XR × XR) × ShP) :
    realGameRO Hb A true z ↔ realGameRO Hb A.swap false (swapXR z) := by
  simp only [realGameRO, viewS, AdversaryRO.swap, swapXR, Equiv.coe_fn_mk, Bool.not_true,
    Bool.not_false, outcome_swap]

end Real

/-! ## The sessions as two-phase runs -/

section Internal

variable (Hb : Hashes) (A : AdversaryRO)

/-- The refresher commitment. -/
def comOf (ref : Coins refresherBytes) : Bytes := commitRefresher (List.ofFn ref)

/-- A session's statement: PomFRIT's with the binder `refresher_com`. -/
def stOf (ref : Coins refresherBytes) : Statement := leanBase (toBA (comOf ref))

/-- `hash_to_target` of a step-1 output (proof buffer, `chal1`). -/
def hOf (msg : Bytes) (ref : Coins refresherBytes) (o1 : ByteArray × ByteArray) : Bytes :=
  Layout.labelRows.hashToTarget A.pk.digest (toL o1.2) (toL o1.1 ++ comOf ref ++ List.ofFn ref) msg

/-- A session's request `t = h ⊕ r`. -/
def tOf (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (o1 : ByteArray × ByteArray) :
    Bytes :=
  xorBytes (hOf A msg ref o1) (List.ofFn r)

/-- The Client's check on a response. -/
def validB (resp t : Bytes) : Bool := decide (resp.length = uovN ∧ A.pk.eval resp = t)

/-- **Both responses pass the Clients' checks** (the only case in which the Issuer sees the
signatures). -/
def bothOK (t₀ t₁ : Bytes) : Bool :=
  validB A (A.respond t₀ t₁ false) t₀ && validB A (A.respond t₀ t₁ true) t₁

/-- **The continuation of the session at position `i`**, given the other session's request `t'`:
step 2 for the instance `(pk, h)` and the Issuer's response, if both responses are valid. -/
def kOf (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool) (t' : Bytes) :
    Cont2 := fun o1 =>
  if bothOK A (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t') then
    some (leanInst A.pk (toBA (hOf A msg ref o1)) (toBA (List.ofFn ref)),
      toBA (A.respond (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t')
        i))
  else none

/-- The signature of a two-phase output: the final proof, `refresher_com`, `refresher`. -/
def sigOf (ref : Coins refresherBytes) (o : Out2) : Bytes :=
  toL (((o.2.2.getD (.ok .empty)).toOption).getD .empty) ++ comOf ref ++ List.ofFn ref

/-- **The Issuer's view from two two-phase outputs** (each with its message, refresher and `r`):
the requests, the signatures in message order if both responses are valid, the slices, the
tables. -/
def view2 (b : Bool) (m₀ m₁ : Bytes × Coins refresherBytes × Coins uovM) (o₀ o₁ : Out2) (sl : SlP)
    (v : ShP) : Prop :=
  A.guess (tOf A m₀.1 m₀.2.1 m₀.2.2 (o₀.1, o₀.2.1)) (tOf A m₁.1 m₁.2.1 m₁.2.2 (o₁.1, o₁.2.1))
    (if bothOK A (tOf A m₀.1 m₀.2.1 m₀.2.2 (o₀.1, o₀.2.1)) (tOf A m₁.1 m₁.2.1 m₁.2.2 (o₁.1, o₁.2.1))
      then some (bif b then (sigOf m₁.2.1 o₁, sigOf m₀.2.1 o₀) else (sigOf m₀.2.1 o₀, sigOf m₁.2.1 o₁))
      else none) sl v

/-- A real session's step-1 output on the tables. -/
noncomputable def s1R (x : XR) (s : ShP) : ByteArray × ByteArray :=
  ((@step1 (icPrg s.2.2) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
      CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1)).proof,
    (@step1 (icPrg s.2.2) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
      CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1)).chal1)

/-- A real session's request. -/
noncomputable def tR (msg : Bytes) (x : XR) (s : ShP) : Bytes :=
  tOf A msg x.1.2.1 x.1.2.2 (s1R Hb x s)

/-- **A real session at position `i`**, given the other session's request (a function of the
tables): `realRO2` with the continuation `kOf`. -/
noncomputable def oR (msg : Bytes) (i : Bool) (x : XR) (t' : ShP → Bytes) (s : ShP) : Out2 :=
  realRO2 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
    (fun s => kOf A msg x.1.2.1 x.1.2.2 i (t' s)) x.1.1 x.2 s

lemma oR_s1 (msg : Bytes) (i : Bool) (x : XR) (t' : ShP → Bytes) (s : ShP) :
    ((oR Hb A msg i x t' s).1, (oR Hb A msg i x t' s).2.1) = s1R Hb x s := rfl

/-- A simulated session's tape: the two-phase simulator's coins, the refresher, `r`, the slice. -/
abbrev XS := (SimCoins2 pP × Coins refresherBytes × Coins uovM) × Tab3

/-- A simulated session's step-1 output, from its simulator coins and refresher (it does not
depend on the continuation). -/
noncomputable def s1C (ref : Coins refresherBytes) (c : SimCoins2 pP) (s : ShP) :
    ByteArray × ByteArray :=
  ((@simRun2 (icPrg s.2.2) Hb (stOf ref) uovM (fun _ => none) c).1,
    (@simRun2 (icPrg s.2.2) Hb (stOf ref) uovM (fun _ => none) c).2.1)

/-- A simulated session's step-1 output. -/
noncomputable def s1S (y : XS) (s : ShP) : ByteArray × ByteArray := s1C Hb y.1.2.1 y.1.1 s

/-- A simulated session's request. -/
noncomputable def tS (msg : Bytes) (y : XS) (s : ShP) : Bytes := tOf A msg y.1.2.1 y.1.2.2 (s1S Hb y s)

/-- **A simulated session at position `i`**: `simRO2` with the continuation `kOf`. -/
noncomputable def oS (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP) : Out2 :=
  simRO2 Hb (stOf y.1.2.1) uovM (fun s => kOf A msg y.1.2.1 y.1.2.2 i (t' s)) y.1.1 s

/-- **A simulated session's programming**: `progRO2` with the continuation `kOf`. -/
noncomputable def pS (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP) : ShP :=
  progRO2 Hb (stOf y.1.2.1) uovM (fun s => kOf A msg y.1.2.1 y.1.2.2 i (t' s)) y.1.1 s

lemma simRun2_s1 [HasPrg] (Hs : Hashes) (st : Statement) (n : ℕ) (k k' : Cont2)
    (c : SimCoins2 st.params) :
    ((simRun2 Hs st n k c).1, (simRun2 Hs st n k c).2.1) =
      ((simRun2 Hs st n k' c).1, (simRun2 Hs st n k' c).2.1) := by
  unfold simRun2
  rcases firstHit c.1.1.2.1 with _ | ⟨ctr, d⟩ <;> rfl

lemma oS_eq (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP) :
    oS Hb A msg i y t' s =
      @simRun2 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (kOf A msg y.1.2.1 y.1.2.2 i (t' s)) y.1.1 := by
  delta oS simRO2
  rfl

lemma oS_s1 (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP) :
    ((oS Hb A msg i y t' s).1, (oS Hb A msg i y t' s).2.1) = s1S Hb y s := by
  rw [oS_eq]
  exact @simRun2_s1 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (kOf A msg y.1.2.1 y.1.2.2 i (t' s))
    (fun _ => none) y.1.1

lemma oR_def (msg : Bytes) (i : Bool) (x : XR) (t' : ShP → Bytes) (s : ShP) :
    oR Hb A msg i x t' s = realRO2 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
      (fun s => kOf A msg x.1.2.1 x.1.2.2 i (t' s)) x.1.1 x.2 s := rfl

/-- A real session reads the other request only at the tables it runs on. -/
lemma oR_cont (msg : Bytes) (i : Bool) (x : XR) {t₁ t₂ : ShP → Bytes} (s : ShP)
    (h : t₁ s = t₂ s) : oR Hb A msg i x t₁ s = oR Hb A msg i x t₂ s := by
  rw [oR_def, oR_def]
  unfold realRO2
  beta_reduce
  rw [h]

lemma oS_cont (msg : Bytes) (i : Bool) (y : XS) {t₁ t₂ : ShP → Bytes} (s : ShP)
    (h : t₁ s = t₂ s) : oS Hb A msg i y t₁ s = oS Hb A msg i y t₂ s := by
  rw [oS_eq, oS_eq, h]

lemma pS_eq (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP) :
    pS Hb A msg i y t' s = progK Hb (stOf y.1.2.1) uovM (kOf A msg y.1.2.1 y.1.2.2 i (t' s)) y.1.1 s := by
  delta pS progRO2 progK simRO2
  rfl

lemma pS_cont (msg : Bytes) (i : Bool) (y : XS) {t₁ t₂ : ShP → Bytes} (s : ShP)
    (h : t₁ s = t₂ s) : pS Hb A msg i y t₁ s = pS Hb A msg i y t₂ s := by
  rw [pS_eq, pS_eq, h]

/-! ## The hybrids (world `false`) -/

/-- **`G0`**: both sessions real (session `1`'s continuation reads session `0`'s request off its
output). -/
noncomputable def G0 (z : (XR × XR) × ShP) : Prop :=
  view2 A false (A.msg false, z.1.1.1.2.1, z.1.1.1.2.2) (A.msg true, z.1.2.1.2.1, z.1.2.1.2.2)
    (oR Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2)
    (oR Hb A (A.msg true) true z.1.2 (fun _ => tOf A (A.msg false) z.1.1.1.2.1 z.1.1.1.2.2
      ((oR Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2).1,
       (oR Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2).2.1)) z.2)
    (z.1.1.2, z.1.2.2) z.2

/-- **`G1`**: session `0` simulated (and programming `H₂³`), session `1` real on the programmed
tables. -/
noncomputable def G1 (z : (XS × XR) × ShP) : Prop :=
  view2 A false (A.msg false, z.1.1.1.2.1, z.1.1.1.2.2) (A.msg true, z.1.2.1.2.1, z.1.2.1.2.2)
    (oS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2)
    (oR Hb A (A.msg true) true z.1.2 (fun _ => tOf A (A.msg false) z.1.1.1.2.1 z.1.1.1.2.2
      ((oS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2).1,
       (oS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2).2.1))
      (pS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2)) (z.1.1.2, z.1.2.2)
    (pS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2)

/-- **`G2`**: both sessions simulated, the tables programmed by both (session `1` first). -/
noncomputable def G2 (z : (XS × XS) × ShP) : Prop :=
  view2 A false (A.msg false, z.1.1.1.2.1, z.1.1.1.2.2) (A.msg true, z.1.2.1.2.1, z.1.2.1.2.2)
    (oS Hb A (A.msg false) false z.1.1 (fun _ => tOf A (A.msg true) z.1.2.1.2.1 z.1.2.1.2.2
      ((oS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2).1,
       (oS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2).2.1))
      (pS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2))
    (oS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2) (z.1.1.2, z.1.2.2)
    (pS Hb A (A.msg false) false z.1.1 (fun _ => tOf A (A.msg true) z.1.2.1.2.1 z.1.2.1.2.2
      ((oS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2).1,
       (oS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2).2.1))
      (pS Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2))

end Internal

/-! ## The real game is `G0` -/

section RealIff

variable (Hb : Hashes) (A : AdversaryRO)

lemma proofBytes_pP : pP.proofBytes = Layout.labelRows.proofBytes := by decide

/-- The final signature of a real session for a response `resp`. -/
noncomputable def sigR (msg : Bytes) (x : XR) (s : ShP) (resp : Bytes) : Bytes :=
  toL ((Prover.proveCommit (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
      (withInst (stOf x.1.2.1) (leanInst A.pk (toBA (hOf A msg x.1.2.1 (s1R Hb x s)))
        (toBA (List.ofFn x.1.2.1)))) (toBA resp)
      (@step1 (icPrg s.2.2) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
        CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1))).toOption.getD .empty) ++
    comOf x.1.2.1 ++ List.ofFn x.1.2.1

/-- **A real session of the spec on the tables** is the request `tR` and the Client's checks
followed by the signature `sigR`. -/
theorem realSession_eq (msg : Bytes) (x : XR) (s : ShP) :
    realSession Layout.labelRows (leanProverRO Hb x.2 s) A.pk msg x.1 =
      (tR Hb A msg x s, fun resp => finish A.pk (tR Hb A msg x s) (sigR Hb A msg x s resp) resp) := by
  set y := @step1 (icPrg s.2.2) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
    CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) with hy
  have hpl : (toL y.proof).length = Layout.labelRows.proofBytes := by
    rw [length_toL, Pending_proof_size]; exact proofBytes_pP
  obtain ⟨-, f2, f3, -, -, -⟩ := Layout.labelRows.sig_fields hpl
    (length_commitRefresher (List.ofFn x.1.2.1))
    (by simp [refresherBytes] : (List.ofFn x.1.2.1).length = refresherBytes)
  have hv : (leanProverRO Hb x.2 s).voleGen (List.ofFn x.1.2.2) (List.ofFn x.1.1)
      (commitRefresher (List.ofFn x.1.2.1)) =
      (toL y.proof, toL y.chal1, (toBA (commitRefresher (List.ofFn x.1.2.1)),
        toBA (List.ofFn x.1.2.2), y)) := by
    rw [hy]
    delta leanProverRO
    simp only [toBA_ofFn]
    rfl
  have hc : ∀ a h r' (b₂ : Bytes), (leanProverRO Hb x.2 s).proveCommit a A.pk h r' b₂
      (toBA (commitRefresher (List.ofFn x.1.2.1)), toBA (List.ofFn x.1.2.2), y) =
      toL ((Prover.proveCommit (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
        (withInst (stOf x.1.2.1) (leanInst A.pk (toBA h) (toBA b₂))) (toBA r') y).toOption.getD
          .empty) := fun _ _ _ _ => rfl
  have ht : tR Hb A msg x s = xorBytes (Layout.labelRows.hashToTarget A.pk.digest (toL y.chal1)
      (toL y.proof ++ commitRefresher (List.ofFn x.1.2.1) ++ List.ofFn x.1.2.1) msg)
      (List.ofFn x.1.2.2) := rfl
  have hsig : ∀ resp, sigR Hb A msg x s resp =
      toL ((Prover.proveCommit (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
        (withInst (stOf x.1.2.1) (leanInst A.pk (toBA (Layout.labelRows.hashToTarget A.pk.digest
          (toL y.chal1) (toL y.proof ++ commitRefresher (List.ofFn x.1.2.1) ++ List.ofFn x.1.2.1) msg))
          (toBA (List.ofFn x.1.2.1)))) (toBA resp) y).toOption.getD .empty) ++
        commitRefresher (List.ofFn x.1.2.1) ++ List.ofFn x.1.2.1 := fun _ => rfl
  refine Prod.ext (by simp only [realSession, issueRequestOf, hv, ← ht]) (funext fun resp => ?_)
  simp only [realSession, issueRequestOf, Layout.finalizeIssue, hv, f2, f3, hc, ← ht, hsig, finish,
    ne_eq, not_true_eq_false, ↓reduceIte]

lemma validB_iff (resp t : Bytes) : validB A resp t = true ↔ resp.length = uovN ∧ A.pk.eval resp = t :=
  decide_eq_true_iff

lemma tOf_s1R (msg : Bytes) (x : XR) (s : ShP) :
    tOf A msg x.1.2.1 x.1.2.2 (s1R Hb x s) = tR Hb A msg x s := rfl

lemma bothOK_iff (t₀ t₁ : Bytes) : bothOK A t₀ t₁ = true ↔
    ((A.respond t₀ t₁ false).length = uovN ∧ A.pk.eval (A.respond t₀ t₁ false) = t₀) ∧
      ((A.respond t₀ t₁ true).length = uovN ∧ A.pk.eval (A.respond t₀ t₁ true) = t₁) := by
  unfold bothOK
  rw [Bool.and_eq_true, validB_iff, validB_iff]

/-- With both responses valid, a session's continuation runs step 2 with its response. -/
lemma kOf_of_bothOK (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool)
    (t' : Bytes) (o1 : ByteArray × ByteArray)
    (hB : bothOK A (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t') =
      true) :
    kOf A msg ref r i t' o1 = some (leanInst A.pk (toBA (hOf A msg ref o1)) (toBA (List.ofFn ref)),
      toBA (A.respond (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t')
        i)) := by
  simp only [kOf, hB, ↓reduceIte]

/-- The signature of a real two-phase output whose continuation continues. -/
lemma sigOf_oR (msg : Bytes) (i : Bool) (x : XR) (t' : ShP → Bytes) (s : ShP)
    (hB : bothOK A (bif i then t' s else tR Hb A msg x s) (bif i then tR Hb A msg x s else t' s) =
      true) :
    sigOf x.1.2.1 (oR Hb A msg i x t' s) =
      sigR Hb A msg x s (A.respond (bif i then t' s else tR Hb A msg x s)
        (bif i then tR Hb A msg x s else t' s) i) := by
  have hk := kOf_of_bothOK A msg x.1.2.1 x.1.2.2 i (t' s) (s1R Hb x s) hB
  have e : (oR Hb A msg i x t' s).2.2 = (kOf A msg x.1.2.1 x.1.2.2 i (t' s) (s1R Hb x s)).map
      fun z => Prover.proveCommit (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
        (withInst (stOf x.1.2.1) z.1) z.2
        (@step1 (icPrg s.2.2) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
          CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1)) := rfl
  unfold sigOf
  rw [e, hk, Option.map_some, Option.getD_some]
  rfl

/-- **The real game is `G0`**: the view only reads the signatures when both responses are valid,
and then the two-phase runs of `G0` run step 2 with the Issuer's responses. -/
theorem realGameRO_iff (z : (XR × XR) × ShP) : realGameRO Hb A false z ↔ G0 Hb A z := by
  obtain ⟨⟨x₀, x₁⟩, s⟩ := z
  simp only [realGameRO, viewS, realSession_eq, Bool.not_false, outcome_finish]
  simp only [G0, view2, oR_s1, tOf_s1R]
  by_cases hB : bothOK A (tR Hb A (A.msg false) x₀ s) (tR Hb A (A.msg true) x₁ s) = true
  · have hB' := (bothOK_iff A _ _).1 hB
    rw [sigOf_oR Hb A (A.msg false) false x₀ (tR Hb A (A.msg true) x₁) s hB,
      sigOf_oR Hb A (A.msg true) true x₁ (fun _ => tR Hb A (A.msg false) x₀ s) s hB]
    simp only [hB, hB', and_self, ↓reduceIte, Bool.cond_true, Bool.cond_false]
  · have hB' : ¬ (((A.respond (tR Hb A (A.msg false) x₀ s) (tR Hb A (A.msg true) x₁ s) false).length =
        uovN ∧ A.pk.eval (A.respond (tR Hb A (A.msg false) x₀ s) (tR Hb A (A.msg true) x₁ s) false) =
          tR Hb A (A.msg false) x₀ s) ∧
        ((A.respond (tR Hb A (A.msg false) x₀ s) (tR Hb A (A.msg true) x₁ s) true).length = uovN ∧
        A.pk.eval (A.respond (tR Hb A (A.msg false) x₀ s) (tR Hb A (A.msg true) x₁ s) true) =
          tR Hb A (A.msg true) x₁ s)) := fun h => hB ((bothOK_iff A _ _).2 h)
    simp only [hB, hB', Bool.false_eq_true, ↓reduceIte]

end RealIff

/-! ## The continuations satisfy the two-phase hypotheses -/

section Hyps

variable (Hb : Hashes) (A : AdversaryRO)

/-- **Every instance a session's continuation picks is satisfied by its witness** `r ‖ resp`:
it is picked only if the response passes the Client's check `P(resp) = h ⊕ r`. -/
theorem hyp2_kOf (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool)
    (t' : Bytes) : Hyp2 (stOf ref) (toBA (List.ofFn r)) (kOf A msg ref r i t') where
  hk o x sfx hko := by
    unfold kOf at hko
    split_ifs at hko with hB
    simp only [Option.some.injEq, Prod.mk.injEq] at hko
    obtain ⟨rfl, rfl⟩ := hko
    have hv := (bothOK_iff A _ _).1 hB
    have hval : (A.respond (bif i then t' else tOf A msg ref r o) (bif i then tOf A msg ref r o else t')
        i).length = uovN ∧ A.pk.eval (A.respond (bif i then t' else tOf A msg ref r o)
          (bif i then tOf A msg ref r o else t') i) = tOf A msg ref r o := by
      cases i
      · exact hv.1
      · exact hv.2
    have hr : (List.ofFn r).length = uovM := List.length_ofFn
    have hh : (hOf A msg ref o).length = uovM := Layout.labelRows.length_hashToTarget _ _ _ _
    exact
      { hvals := leanInst_values A.pk _ _ (toBA (comOf ref))
        hdeg := fun _ _ => PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _
        hd := show 1 ≤ 2 by decide
        hd' := show 2 + 1 < 2 ^ 64 by decide
        hsat := fun c1 lb => leanInst_holds A.pk (hOf A msg ref o) (List.ofFn r) _
          (toBA (List.ofFn ref)) hr hh hval.1 hval.2 c1 lb
        hw := by rw [ByteArray.size_append, size_toBA, size_toBA, hr, hval.1]; rfl
        hI := Interp.interpOk_two }
  hr := by rw [size_toBA, List.length_ofFn]; show 45 ≤ 164; decide
  hlr := rfl
  hnm := show 2 - 1 + 4 ≤ 32 by decide

/-- A real session's step 1 does not read `H₂³`. -/
lemma s1R_h23 (x : XR) (s : ShP) (G2 : Tab2G pP) : s1R Hb x (G2, s.2) = s1R Hb x s := by
  have h := @step1_agreeOff_h23 (icPrg s.2.2) _ _ (recH_agreeOff_h23 (Hb := Hb)
    (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) x.2 G2 s.1 s.2.1) CrtGen.tables
    (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1)
  simp only [s1R, h]

/-- A real session's step 1 reads `H₅` at `624` keys. -/
lemma s1R_rd5 (x : XR) : Rd5 (s1R Hb x) 624 :=
  (step1_rd5 (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2).map
    fun y => (y.proof, y.chal1)

/-- A real session's step 1 reads the cipher at `4607` keys. -/
lemma s1R_rdE (hHb : HashesWF Hb) (x : XR) : RdE (s1R Hb x) 4607 :=
  (step1_rdE (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) hHb (ba x.1.1)
    x.2).map fun y => (y.proof, y.chal1)

/-- A simulated session's step 1 reads only the cipher. -/
lemma s1S_eq (y : XS) (s s' : ShP) (h : s'.2.2 = s.2.2) : s1S Hb y s' = s1S Hb y s := by
  unfold s1S s1C
  rw [h]

/-- A simulated session's step 1 reads the cipher at the `4607` nodes of its opening. -/
lemma s1S_rdE (y : XS) : RdE (s1S Hb y) 4607 :=
  ⟨fun s => hRd s.2.2 Hb (st1 (stOf y.1.2.1)) y.1.1.1.1 (deltaOf y.1.1.1.1.2.1),
    fun s => rdKeys_card _ _ _ _, fun s E hE => by
      simp only [s1S, s1C, simRun2_ic_congr Hb (stOf y.1.2.1) uovM (fun _ => none) y.1.1 hE]⟩

/-- **The continuation of session `0` with session `1` real.** -/
theorem hyp2RO_R (hHb : HashesWF Hb) (msg msg' : Bytes) (ref : Coins refresherBytes)
    (r : Coins uovM) (i : Bool) (x' : XR) :
    Hyp2RO (stOf ref) (toBA (List.ofFn r)) uovM (fun s => kOf A msg ref r i (tR Hb A msg' x' s))
      624 4607 where
  hyp _ := hyp2_kOf A msg ref r i _
  size := by rw [size_toBA, List.length_ofFn]
  h2 s G2 := congrArg (kOf A msg ref r i) (congrArg (tOf A msg' x'.1.2.1 x'.1.2.2)
    (s1R_h23 Hb x' s G2))
  h5 := (s1R_rd5 Hb x').map fun o => kOf A msg ref r i (tOf A msg' x'.1.2.1 x'.1.2.2 o)
  hE := (s1R_rdE Hb hHb x').map fun o => kOf A msg ref r i (tOf A msg' x'.1.2.1 x'.1.2.2 o)

/-- **The continuation of a session with the other session simulated.** -/
theorem hyp2RO_S (msg msg' : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool)
    (y' : XS) :
    Hyp2RO (stOf ref) (toBA (List.ofFn r)) uovM (fun s => kOf A msg ref r i (tS Hb A msg' y' s))
      0 4607 where
  hyp _ := hyp2_kOf A msg ref r i _
  size := by rw [size_toBA, List.length_ofFn]
  h2 s G2 := congrArg (kOf A msg ref r i) (congrArg (tOf A msg' y'.1.2.1 y'.1.2.2)
    (s1S_eq Hb y' s (G2, s.2) rfl))
  h5 := Rd5.of_indep _ fun s G5 => congrArg (kOf A msg ref r i)
    (congrArg (tOf A msg' y'.1.2.1 y'.1.2.2) (s1S_eq Hb y' s (s.1, G5, s.2.2) rfl))
  hE := (s1S_rdE Hb y').map fun o => kOf A msg ref r i (tOf A msg' y'.1.2.1 y'.1.2.2 o)

end Hyps

/-! ## Hop 0: session `0` simulated -/

section Hop0

variable (Hb : Hashes) (A : AdversaryRO)

/-- **The reduction for session `0`**: the rest of the game, session `1` run for real on the
tables it is given, its continuation from session `0`'s request. -/
noncomputable def D0 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) (o : Out2) (g : Tab3)
    (s : ShP) : Prop :=
  view2 A false (A.msg false, ref₀, r₀) (A.msg true, x₁.1.2.1, x₁.1.2.2) o
    (oR Hb A (A.msg true) true x₁ (fun _ => tOf A (A.msg false) ref₀ r₀ (o.1, o.2.1)) s) (g, x₁.2) s

variable {Hb A}

/-- **The reduction's budget**: the Issuer's, plus session `1`'s real run (`624` `H₅` keys,
`4607` cipher keys). -/
theorem budget_D0 (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) :
    Budget pP q3 (q5 + 624) (qE + 4607) (D0 Hb A ref₀ r₀ x₁) where
  h3 o s := hA.h30 _ _ _ _ _
  h5 o g := by
    have h := (realRO2_rd5 (Hb := Hb) (st := stOf x₁.1.2.1) (r := toBA (List.ofFn x₁.1.2.2))
      (K := fun _ => kOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 true
        (tOf A (A.msg false) ref₀ r₀ (o.1, o.2.1))) (Rd5.const _) x₁.1.1 x₁.2).bind
      (f := fun (o₁ : Out2) (s : ShP) => view2 A false (A.msg false, ref₀, r₀)
        (A.msg true, x₁.1.2.1, x₁.1.2.2) o o₁ (g, x₁.2) s) fun o₁ => hA.h5 _ _ _ _
    exact h.mono (by omega)
  hE o g := by
    have h := (realRO2_rdE (Hb := Hb) (st := stOf x₁.1.2.1) (r := toBA (List.ofFn x₁.1.2.2))
      (K := fun _ => kOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 true
        (tOf A (A.msg false) ref₀ r₀ (o.1, o.2.1))) hHb (RdE.const _) x₁.1.1 x₁.2).bind
      (f := fun (o₁ : Out2) (s : ShP) => view2 A false (A.msg false, ref₀, r₀)
        (A.msg true, x₁.1.2.1, x₁.1.2.2) o o₁ (g, x₁.2) s) fun o₁ => hA.hE _ _ _ _
    exact h.mono (by omega)

variable (Hb A) in
lemma G0_iff_D0 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (a : (Bytes 16 × Tab3) × ShP) :
    G0 Hb A ((((a.1.1, ref₀, r₀), a.1.2), x₁), a.2) ↔ D0 Hb A ref₀ r₀ x₁
      (realRO2 Hb (stOf ref₀) (toBA (List.ofFn r₀))
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.1.2 a.2)
      a.1.2 a.2 := Iff.rfl

variable (Hb A) in
lemma G1_iff_D0 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (a : (SimCoins2 pP × Tab3) × ShP) :
    G1 Hb A ((((a.1.1, ref₀, r₀), a.1.2), x₁), a.2) ↔ D0 Hb A ref₀ r₀ x₁
      (simRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.2) := by
  have e1 : ∀ s, oS Hb A (A.msg false) false (((a.1.1, ref₀, r₀), a.1.2)) (tR Hb A (A.msg true) x₁) s =
      simRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 s := fun _ => rfl
  have e2 : ∀ s, pS Hb A (A.msg false) false (((a.1.1, ref₀, r₀), a.1.2)) (tR Hb A (A.msg true) x₁) s =
      progRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 s := fun _ => rfl
  unfold G1 D0
  dsimp only
  rw [e1, e2]

/-- Regroup the real game's tape around session `0`'s proof. -/
def eqR0 : ((Coins refresherBytes × Coins uovM) × XR) × ((Bytes 16 × Tab3) × ShP) ≃
    (XR × XR) × ShP where
  toFun c := ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)
  invFun z := (((z.1.1.1.2.1, z.1.1.1.2.2), z.1.2), ((z.1.1.1.1, z.1.1.2), z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup `G1`'s tape around session `0`'s simulation. -/
def eqS0 : ((Coins refresherBytes × Coins uovM) × XR) × ((SimCoins2 pP × Tab3) × ShP) ≃
    (XS × XR) × ShP where
  toFun c := ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)
  invFun z := (((z.1.1.1.2.1, z.1.1.1.2.2), z.1.2), ((z.1.1.1.1, z.1.1.2), z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Hop 0** (`G0 → G1`): session `0` simulated, by `zk2_ro` for its two-phase run with the
reduction `D0` and the continuation that reads session `1`'s step 1. -/
theorem hop0 (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP) (G0 Hb A) - pr ((XS × XR) × ShP) (G1 Hb A)| ≤
      εRO q3 ((q5 + 624) + 624) ((qE + 4607) + 4607) := by
  have e1 : pr ((XR × XR) × ShP) (G0 Hb A) =
      pr (((Coins refresherBytes × Coins uovM) × XR) × ((Bytes 16 × Tab3) × ShP)) (fun c =>
        G0 Hb A ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)) :=
    (pr_equiv eqR0 (G0 Hb A)).symm
  have e2 : pr ((XS × XR) × ShP) (G1 Hb A) =
      pr (((Coins refresherBytes × Coins uovM) × XR) × ((SimCoins2 pP × Tab3) × ShP)) (fun c =>
        G1 Hb A ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)) :=
    (pr_equiv eqS0 (G1 Hb A)).symm
  rw [e1, e2]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨⟨ref₀, r₀⟩, x₁⟩ := ζ
  have key := zk2_ro Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM
    (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s))
    (hyp2RO_R Hb A hHb (A.msg false) (A.msg true) ref₀ r₀ false x₁) hHb
    (smallParams_of_le (p := pP) (by decide) (by decide)) (D0 Hb A ref₀ r₀ x₁) (budget_D0 hHb hA ref₀ r₀ x₁)
  have key' : |pr ((Bytes 16 × Tab3) × ShP) (fun a => D0 Hb A ref₀ r₀ x₁
      (realRO2 Hb (stOf ref₀) (toBA (List.ofFn r₀))
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.1.2 a.2)
      a.1.2 a.2) -
    pr ((SimCoins2 pP × Tab3) × ShP) (fun a => D0 Hb A ref₀ r₀ x₁
      (simRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₀) uovM
        (fun s => kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) x₁ s)) a.1.1 a.2))| ≤
      εRO q3 ((q5 + 624) + 624) ((qE + 4607) + 4607) := key
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key'
  · exact pr_congr fun a => G0_iff_D0 Hb A ref₀ r₀ x₁ a
  · exact pr_congr fun a => G1_iff_D0 Hb A ref₀ r₀ x₁ a

end Hop0

/-! ## Hop 1: session `1` simulated -/

section Hop1

variable (Hb : Hashes) (A : AdversaryRO)

/-- **The reduction for session `1`**: session `0` simulated (its coins fixed), its continuation
and its programming computed from session `1`'s output, the programming applied on top of the
tables it is given. -/
noncomputable def D1 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS) (o : Out2) (g : Tab3)
    (s : ShP) : Prop :=
  view2 A false (A.msg false, y₀.1.2.1, y₀.1.2.2) (A.msg true, ref₁, r₁)
    (oS Hb A (A.msg false) false y₀ (fun _ => tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1)) s) o (y₀.2, g)
    (pS Hb A (A.msg false) false y₀ (fun _ => tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1)) s)

variable {Hb A}

/-- **The reduction's budget**: the Issuer's, plus the simulated session `0`'s `chal1` (`4607`
cipher keys) and its programming (`312` `H₅` keys, `2·4607` cipher keys). -/
theorem budget_D1 {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (y₀ : XS) :
    Budget pP q3 (q5 + 312) (qE + 13821) (D1 Hb A ref₁ r₁ y₀) where
  h3 o s := hA.h31 _ _ _ _ _
  h5 o g := by
    have hP := progRO2_isProg (Hb := Hb) (st := stOf y₀.1.2.1) (n := uovM)
      (K := fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
        (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) (Rd5.const _) (RdE.const _) y₀.1.1
    have h := (simRO2_rd5 (Hb := Hb) (st := stOf y₀.1.2.1) (n := uovM)
      (K := fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
        (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) (Rd5.const _) y₀.1.1).bind
      (f := fun (y : Out2) (s : ShP) => view2 A false (A.msg false, y₀.1.2.1, y₀.1.2.2)
        (A.msg true, ref₁, r₁) y o (y₀.2, g)
        (progRO2 Hb (stOf y₀.1.2.1) uovM (fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
          (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) y₀.1.1 s))
      fun y => (hA.h5 _ _ _ _).comp_prog hP
    exact h.mono (by omega)
  hE o g := by
    have hP := progRO2_isProg (Hb := Hb) (st := stOf y₀.1.2.1) (n := uovM)
      (K := fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
        (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) (Rd5.const _) (RdE.const _) y₀.1.1
    have h := (simRO2_rdE (Hb := Hb) (st := stOf y₀.1.2.1) (n := uovM)
      (K := fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
        (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) (RdE.const _) y₀.1.1).bind
      (f := fun (y : Out2) (s : ShP) => view2 A false (A.msg false, y₀.1.2.1, y₀.1.2.2)
        (A.msg true, ref₁, r₁) y o (y₀.2, g)
        (progRO2 Hb (stOf y₀.1.2.1) uovM (fun _ => kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false
          (tOf A (A.msg true) ref₁ r₁ (o.1, o.2.1))) y₀.1.1 s))
      fun y => (hA.hE _ _ _ _).comp_prog hP
    exact h.mono (by omega)

variable (Hb A)

/-- `G1` with session `1` on the unprogrammed tables: the zero-knowledge reduction's real side. -/
noncomputable def G1' (z : (XS × XR) × ShP) : Prop :=
  D1 Hb A z.1.2.1.2.1 z.1.2.1.2.2 z.1.1
    (oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2) z.1.2.2 z.2

/-- **The programming collision term of world `false`**: session `1`, run for real, reads `H₂³`
differently on the tables session `0`'s simulator programmed than on the original ones. -/
noncomputable def deltaRO : ℝ :=
  pr ((XS × XR) × ShP) (fun z =>
    oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1)
        (pS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2) ≠
      oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2)

/-- **`G1` and the reduction's real side agree unless session `1` reads a programmed point.** -/
theorem G1_G1' : |pr ((XS × XR) × ShP) (G1 Hb A) - pr ((XS × XR) × ShP) (G1' Hb A)| ≤
    deltaRO Hb A := by
  refine abs_pr_sub_le_of_agree _ _ _ fun z hz => ?_
  obtain ⟨⟨y₀, x₁⟩, s⟩ := z
  have hz' := not_not.1 hz
  dsimp only at hz'
  set v := pS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s with hv
  set o := oR Hb A (A.msg true) true x₁ (tS Hb A (A.msg false) y₀) s with ho
  have ho1 : (o.1, o.2.1) = s1R Hb x₁ s := oR_s1 Hb A _ _ _ _ _
  have hvs : v.2.2 = s.2.2 := rfl
  have h1 : oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s =
      oS Hb A (A.msg false) false y₀ (fun _ => tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    oS_cont Hb A _ _ _ s (by rw [ho1]; rfl)
  have h2 : v = pS Hb A (A.msg false) false y₀
      (fun _ => tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    pS_cont Hb A _ _ _ s (by rw [ho1]; rfl)
  have h3 : oR Hb A (A.msg true) true x₁ (fun _ => tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
       (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1)) v = o := by
    have hc : tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
        ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
         (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1) =
        tS Hb A (A.msg false) y₀ v := by
      rw [oS_s1, tS, s1S_eq Hb y₀ s v hvs]
    rw [oR_cont Hb A (A.msg true) true x₁ v (t₁ := fun _ => tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
       (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1))
      (t₂ := tS Hb A (A.msg false) y₀) hc, ← hz']
  show G1 Hb A ((y₀, x₁), s) ↔ G1' Hb A ((y₀, x₁), s)
  unfold G1 G1' D1
  dsimp only
  rw [← hv, h3, h1, ← h2]

/-- Regroup `G1'`'s tape around session `1`'s proof. -/
def eqR1 : ((XS × (Coins refresherBytes × Coins uovM)) × ((Bytes 16 × Tab3) × ShP)) ≃
    (XS × XR) × ShP where
  toFun c := ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)
  invFun z := ((z.1.1, (z.1.2.1.2.1, z.1.2.1.2.2)), ((z.1.2.1.1, z.1.2.2), z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup `G2`'s tape around session `1`'s simulation. -/
def eqS1 : ((XS × (Coins refresherBytes × Coins uovM)) × ((SimCoins2 pP × Tab3) × ShP)) ≃
    (XS × XS) × ShP where
  toFun c := ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)
  invFun z := ((z.1.1, (z.1.2.1.2.1, z.1.2.1.2.2)), ((z.1.2.1.1, z.1.2.2), z.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma G1'_iff_D1 (y₀ : XS) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (a : (Bytes 16 × Tab3) × ShP) :
    G1' Hb A ((y₀, ((a.1.1, ref₁, r₁), a.1.2)), a.2) ↔ D1 Hb A ref₁ r₁ y₀
      (realRO2 Hb (stOf ref₁) (toBA (List.ofFn r₁))
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.1.2 a.2)
      a.1.2 a.2 := Iff.rfl

lemma G2_iff_D1 (y₀ : XS) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (a : (SimCoins2 pP × Tab3) × ShP) :
    G2 Hb A ((y₀, ((a.1.1, ref₁, r₁), a.1.2)), a.2) ↔ D1 Hb A ref₁ r₁ y₀
      (simRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.2) := by
  have e1 : ∀ s, oS Hb A (A.msg true) true (((a.1.1, ref₁, r₁), a.1.2)) (tS Hb A (A.msg false) y₀) s =
      simRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 s := fun _ => rfl
  have e2 : ∀ s, pS Hb A (A.msg true) true (((a.1.1, ref₁, r₁), a.1.2)) (tS Hb A (A.msg false) y₀) s =
      progRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 s := fun _ => rfl
  unfold G2 D1
  dsimp only
  rw [e1, e2]

variable {Hb A}

/-- **Hop 1** (`G1 → G2`): session `1` simulated, by `zk2_ro` for its two-phase run with the
reduction `D1` and the continuation that reads the simulated session `0`'s step 1, plus the
programming collision term. -/
theorem hop1 (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr ((XS × XR) × ShP) (G1 Hb A) - pr ((XS × XS) × ShP) (G2 Hb A)| ≤
      εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607) + deltaRO Hb A := by
  have hδ := G1_G1' Hb A
  suffices h : |pr ((XS × XR) × ShP) (G1' Hb A) - pr ((XS × XS) × ShP) (G2 Hb A)| ≤
      εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607) by
    have := abs_sub_le (pr ((XS × XR) × ShP) (G1 Hb A)) (pr ((XS × XR) × ShP) (G1' Hb A))
      (pr ((XS × XS) × ShP) (G2 Hb A))
    linarith
  have e1 : pr ((XS × XR) × ShP) (G1' Hb A) =
      pr ((XS × (Coins refresherBytes × Coins uovM)) × ((Bytes 16 × Tab3) × ShP)) (fun c =>
        G1' Hb A ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)) :=
    (pr_equiv eqR1 (G1' Hb A)).symm
  have e2 : pr ((XS × XS) × ShP) (G2 Hb A) =
      pr ((XS × (Coins refresherBytes × Coins uovM)) × ((SimCoins2 pP × Tab3) × ShP)) (fun c =>
        G2 Hb A ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)) :=
    (pr_equiv eqS1 (G2 Hb A)).symm
  rw [e1, e2]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨y₀, ref₁, r₁⟩ := ζ
  have key := zk2_ro Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM
    (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s))
    (hyp2RO_S Hb A (A.msg true) (A.msg false) ref₁ r₁ true y₀) hHb
    (smallParams_of_le (p := pP) (by decide) (by decide)) (D1 Hb A ref₁ r₁ y₀)
    (budget_D1 hA ref₁ r₁ y₀)
  have key' : |pr ((Bytes 16 × Tab3) × ShP) (fun a => D1 Hb A ref₁ r₁ y₀
      (realRO2 Hb (stOf ref₁) (toBA (List.ofFn r₁))
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.1.2 a.2)
      a.1.2 a.2) -
    pr ((SimCoins2 pP × Tab3) × ShP) (fun a => D1 Hb A ref₁ r₁ y₀
      (simRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₁) uovM
        (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1 a.2))| ≤
      εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607) := key
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key'
  · exact pr_congr fun a => G1'_iff_D1 Hb A y₀ ref₁ r₁ a
  · exact pr_congr fun a => G2_iff_D1 Hb A y₀ ref₁ r₁ a

end Hop1

/-! ## `G2` is the same for the Issuer and for the Issuer with the roles exchanged -/

section Swap

variable (Hb : Hashes) (A : AdversaryRO)

/-- The simulated run depends on its continuation only through whether it continues at its
step-1 output. -/
lemma simRun2_kcongr [HasPrg] (Hs : Hashes) (st : Statement) (n : ℕ) {k k' : Cont2}
    (c : SimCoins2 st.params)
    (h : (k ((simRun2 Hs st n (fun _ => none) c).1, (simRun2 Hs st n (fun _ => none) c).2.1)).map
        Prod.fst =
      (k' ((simRun2 Hs st n (fun _ => none) c).1, (simRun2 Hs st n (fun _ => none) c).2.1)).map
        Prod.fst) :
    simRun2 Hs st n k c = simRun2 Hs st n k' c := by
  have hm : ∀ {α : Type} (o : Option (Inst2 × ByteArray)) (x : α),
      o.map (fun _ => x) = (o.map Prod.fst).map (fun _ => x) := fun o x => by
    cases o <;> rfl
  unfold simRun2 at h ⊢
  rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, d⟩
  · simp only [hf] at h ⊢
    rw [hm, h, ← hm]
  · simp only [hf] at h ⊢
    rw [hm, h, ← hm]

/-- The recomputed prefix reads the continuation only through the instance it picks. -/
lemma outPre2_kcongr [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) {k k' : Cont2}
    (G5 : Tab5F) (o : Out2) (h : (k (o.1, o.2.1)).map Prod.fst = (k' (o.1, o.2.1)).map Prod.fst) :
    outPre2 Hs T st k G5 o = outPre2 Hs T st k' G5 o := by
  unfold outPre2
  generalize k (o.1, o.2.1) = a at h ⊢
  generalize k' (o.1, o.2.1) = b at h ⊢
  generalize o.2.2 = e
  rcases a with _ | ⟨y, u⟩ <;> rcases b with _ | ⟨y', u'⟩
  · rfl
  · cases h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rcases e with _ | _ | _ <;> rfl

/-- So does its programming (the recomputed prefix reads the instance). -/
lemma progK_kcongr (st : Statement) (n : ℕ) {k k' : Cont2} (c : SimCoins2 st.params)
    (s : Sh st.params)
    (h' : (k ((@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).1,
        (@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).2.1)).map Prod.fst =
      (k' ((@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).1,
        (@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).2.1)).map Prod.fst) :
    progK Hb st n k c s = progK Hb st n k' c s := by
  have hS := @simRun2_kcongr (icPrg s.2.2) Hb st n k k' c h'
  have hS1 : ((@simRun2 (icPrg s.2.2) Hb st n k' c).1, (@simRun2 (icPrg s.2.2) Hb st n k' c).2.1) =
      ((@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).1,
        (@simRun2 (icPrg s.2.2) Hb st n (fun _ => none) c).2.1) :=
    @simRun2_s1 (icPrg s.2.2) Hb st n k' (fun _ => none) c
  have hO := @outPre2_kcongr (icPrg s.2.2) Hb CrtGen.tables st k k' s.2.1
    (@simRun2 (icPrg s.2.2) Hb st n k' c) (by rw [hS1]; exact h')
  unfold progK simTab2
  rw [hS, hO]

/-- The simulated run's final output depends on its continuation only through whether it
continues. -/
lemma simRun2_22 [HasPrg] (Hs : Hashes) (st : Statement) (n : ℕ) {k k' : Cont2}
    (c : SimCoins2 st.params)
    (h : (k ((simRun2 Hs st n (fun _ => none) c).1, (simRun2 Hs st n (fun _ => none) c).2.1)).isSome =
      (k' ((simRun2 Hs st n (fun _ => none) c).1, (simRun2 Hs st n (fun _ => none) c).2.1)).isSome) :
    (simRun2 Hs st n k c).2.2 = (simRun2 Hs st n k' c).2.2 := by
  have hm : ∀ {α : Type} (o : Option (Inst2 × ByteArray)) (x : α),
      o.map (fun _ => x) = if o.isSome then some x else none := fun o x => by
    cases o <;> rfl
  unfold simRun2 at h ⊢
  rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, d⟩
  · simp only [hf] at h ⊢
    rw [hm, h, ← hm]
  · simp only [hf] at h ⊢
    rw [hm, h, ← hm]

/-- **A simulated session's signature** (when it is revealed: the continuation continued). -/
noncomputable def sigS (y : XS) (s : ShP) : Bytes :=
  sigOf y.1.2.1 (@simRun2 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (fun _ => some (default, .empty)) y.1.1)

lemma sigOf_oS (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP)
    (hB : (kOf A msg y.1.2.1 y.1.2.2 i (t' s) (s1S Hb y s)).isSome = true) :
    sigOf y.1.2.1 (oS Hb A msg i y t' s) = sigS Hb y s := by
  rw [oS_eq]
  unfold sigOf sigS
  rw [@simRun2_22 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (kOf A msg y.1.2.1 y.1.2.2 i (t' s))
    (fun _ => some (default, .empty)) y.1.1 hB]
  rfl

lemma kOf_isSome (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool) (t' : Bytes)
    (o1 : ByteArray × ByteArray) :
    (kOf A msg ref r i t' o1).isSome =
      bothOK A (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t') := by
  unfold kOf
  split_ifs with h
  · rw [h]; rfl
  · rw [Bool.not_eq_true] at h; rw [h]; rfl

lemma kOf_fst (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM) (i : Bool) (t' : Bytes)
    (o1 : ByteArray × ByteArray) :
    (kOf A msg ref r i t' o1).map Prod.fst =
      if bothOK A (bif i then t' else tOf A msg ref r o1) (bif i then tOf A msg ref r o1 else t') then
        some (leanInst A.pk (toBA (hOf A msg ref o1)) (toBA (List.ofFn ref))) else none := by
  unfold kOf
  split_ifs <;> rfl

lemma bothOK_swap (t₀ t₁ : Bytes) : bothOK A.swap t₁ t₀ = bothOK A t₀ t₁ := by
  simp only [bothOK, validB, AdversaryRO.swap, Bool.not_false, Bool.not_true]
  exact Bool.and_comm _ _

/-- **`G2` in canonical form**: the requests, the signatures if both responses are valid, the
tables programmed by both simulators. -/
noncomputable def G2c (z : (XS × XS) × ShP) : Prop :=
  A.guess (tS Hb A (A.msg false) z.1.1 z.2) (tS Hb A (A.msg true) z.1.2 z.2)
    (if bothOK A (tS Hb A (A.msg false) z.1.1 z.2) (tS Hb A (A.msg true) z.1.2 z.2) then
      some (sigS Hb z.1.1 z.2, sigS Hb z.1.2 z.2) else none) (z.1.1.2, z.1.2.2)
    (pS Hb A (A.msg false) false z.1.1 (fun _ => tS Hb A (A.msg true) z.1.2 z.2)
      (pS Hb A (A.msg true) true z.1.2 (fun _ => tS Hb A (A.msg false) z.1.1 z.2) z.2))

lemma G2_iff_G2c (z : (XS × XS) × ShP) : G2 Hb A z ↔ G2c Hb A z := by
  obtain ⟨⟨y₀, y₁⟩, s⟩ := z
  have hv2 : (pS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s).2.2 = s.2.2 := rfl
  have ht1 : tOf A (A.msg true) y₁.1.2.1 y₁.1.2.2
      ((oS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s).1,
       (oS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s).2.1) =
      tS Hb A (A.msg true) y₁ s := by rw [oS_s1]; rfl
  have ho0 : oS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s)
      (pS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s) =
      oS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s) s := by
    rw [oS_eq, oS_eq, hv2]
  have hp0 : pS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s)
      (pS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s) =
      pS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s)
        (pS Hb A (A.msg true) true y₁ (fun _ => tS Hb A (A.msg false) y₀ s) s) := by
    rw [pS_cont Hb A (A.msg true) true y₁ (t₁ := tS Hb A (A.msg false) y₀)
      (t₂ := fun _ => tS Hb A (A.msg false) y₀ s) s rfl]
  have h0 : tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s) s).1,
       (oS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s) s).2.1) =
      tS Hb A (A.msg false) y₀ s := by rw [oS_s1]; rfl
  simp only [G2, view2, G2c, ht1]
  rw [ho0, hp0, h0]
  by_cases hB : bothOK A (tS Hb A (A.msg false) y₀ s) (tS Hb A (A.msg true) y₁ s) = true
  · have k0 : (kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false ((fun _ => tS Hb A (A.msg true) y₁ s) s)
        (s1S Hb y₀ s)).isSome = true := by
      rw [kOf_isSome]; exact hB
    have k1 : (kOf A (A.msg true) y₁.1.2.1 y₁.1.2.2 true (tS Hb A (A.msg false) y₀ s)
        (s1S Hb y₁ s)).isSome = true := by
      rw [kOf_isSome]; exact hB
    rw [sigOf_oS Hb A (A.msg false) false y₀ (fun _ => tS Hb A (A.msg true) y₁ s) s k0,
      sigOf_oS Hb A (A.msg true) true y₁ (tS Hb A (A.msg false) y₀) s k1]
    simp only [hB, ↓reduceIte, Bool.cond_false]
  · simp only [hB, Bool.false_eq_true, ↓reduceIte]

/-- `t = h ⊕ r` as the one-time pad `pad h r`. -/
lemma xorBytes_eq_pad {n : ℕ} {h : Bytes} (hl : h.length = n) (r : Coins n) :
    xorBytes h (List.ofFn r) = List.ofFn (pad h r) := by
  have := xorBytes_pad hl (pad h r)
  rwa [pad_pad] at this

/-- The `hash_to_target` of a simulated session, from its simulator coins and refresher. -/
noncomputable def hS (msg : Bytes) (ref : Coins refresherBytes) (c : SimCoins2 pP) (s : ShP) : Bytes :=
  hOf A msg ref (s1C Hb ref c s)

lemma hS_swap : hS Hb A.swap = hS Hb A := rfl

lemma tS_pad (msg : Bytes) (y : XS) (s : ShP) :
    tS Hb A msg y s = List.ofFn (pad (hS Hb A msg y.1.2.1 y.1.1 s) y.1.2.2) :=
  xorBytes_eq_pad (Layout.labelRows.length_hashToTarget _ _ _ _) _

/-- **The re-parametrization of `G2`'s tape**: the requests are one-time pads, so swap them (and
the slices) between the two positions, keeping each session's simulator coins and refresher. -/
noncomputable def swapS (z : (XS × XS) × ShP) : (XS × XS) × ShP :=
  ((((z.1.1.1.1, z.1.1.1.2.1, pad (hS Hb A (A.msg false) z.1.1.1.2.1 z.1.1.1.1 z.2)
      (pad (hS Hb A (A.msg true) z.1.2.1.2.1 z.1.2.1.1 z.2) z.1.2.1.2.2)), z.1.2.2),
    ((z.1.2.1.1, z.1.2.1.2.1, pad (hS Hb A (A.msg true) z.1.2.1.2.1 z.1.2.1.1 z.2)
      (pad (hS Hb A (A.msg false) z.1.1.1.2.1 z.1.1.1.1 z.2) z.1.1.1.2.2)), z.1.1.2)), z.2)

lemma swapS_involutive : Function.Involutive (swapS Hb A) := by
  rintro ⟨⟨⟨⟨c₀, ref₀, r₀⟩, g₀⟩, ⟨⟨c₁, ref₁, r₁⟩, g₁⟩⟩, s⟩
  simp only [swapS, pad_pad]

lemma tS_swapS₀ (z : (XS × XS) × ShP) :
    tS Hb A.swap (A.msg false) (swapS Hb A z).1.1 (swapS Hb A z).2 =
      tS Hb A (A.msg true) z.1.2 z.2 := by
  rw [tS_pad, tS_pad]
  simp only [swapS, hS_swap, pad_pad]

lemma tS_swapS₁ (z : (XS × XS) × ShP) :
    tS Hb A.swap (A.msg true) (swapS Hb A z).1.2 (swapS Hb A z).2 =
      tS Hb A (A.msg false) z.1.1 z.2 := by
  rw [tS_pad, tS_pad]
  simp only [swapS, hS_swap, pad_pad]

/-- The inner programming (session `1`'s) is the same after the re-parametrization. -/
lemma pS_swap_in (z : (XS × XS) × ShP) :
    pS Hb A.swap (A.msg true) true (swapS Hb A z).1.2 (fun _ => tS Hb A (A.msg true) z.1.2 z.2)
        (swapS Hb A z).2 =
      pS Hb A (A.msg true) true z.1.2 (fun _ => tS Hb A (A.msg false) z.1.1 z.2) z.2 := by
  refine (pS_eq Hb A.swap _ _ _ _ _).trans ((progK_kcongr Hb (stOf z.1.2.1.2.1) uovM z.1.2.1.1 z.2
    ?_).trans (pS_eq Hb A _ _ _ _ _).symm)
  have hS1 : ((@simRun2 (icPrg z.2.2.2) Hb (stOf z.1.2.1.2.1) uovM (fun _ => none) z.1.2.1.1).1,
      (@simRun2 (icPrg z.2.2.2) Hb (stOf z.1.2.1.2.1) uovM (fun _ => none) z.1.2.1.1).2.1) =
      s1S Hb z.1.2 z.2 := rfl
  have e1 : tOf A.swap (A.msg true) (swapS Hb A z).1.2.1.2.1 (swapS Hb A z).1.2.1.2.2
      (s1S Hb z.1.2 z.2) = tS Hb A (A.msg false) z.1.1 z.2 :=
    tS_swapS₁ Hb A z
  have e2 : tOf A (A.msg true) z.1.2.1.2.1 z.1.2.1.2.2 (s1S Hb z.1.2 z.2) =
      tS Hb A (A.msg true) z.1.2 z.2 := rfl
  rw [hS1, kOf_fst, kOf_fst, Bool.cond_true, Bool.cond_true, Bool.cond_true, Bool.cond_true, e1, e2,
    bothOK_swap]
  rfl

/-- So is the outer programming (session `0`'s), on any tables with the same cipher. -/
lemma pS_swap_out (z : (XS × XS) × ShP) (s'' : ShP) (hs : s''.2.2 = z.2.2.2) :
    pS Hb A.swap (A.msg false) false (swapS Hb A z).1.1 (fun _ => tS Hb A (A.msg false) z.1.1 z.2)
        s'' =
      pS Hb A (A.msg false) false z.1.1 (fun _ => tS Hb A (A.msg true) z.1.2 z.2) s'' := by
  refine (pS_eq Hb A.swap _ _ _ _ _).trans ((progK_kcongr Hb (stOf z.1.1.1.2.1) uovM z.1.1.1.1 s''
    ?_).trans (pS_eq Hb A _ _ _ _ _).symm)
  have hS1 : ((@simRun2 (icPrg s''.2.2) Hb (stOf z.1.1.1.2.1) uovM (fun _ => none) z.1.1.1.1).1,
      (@simRun2 (icPrg s''.2.2) Hb (stOf z.1.1.1.2.1) uovM (fun _ => none) z.1.1.1.1).2.1) =
      s1S Hb z.1.1 z.2 := s1S_eq Hb z.1.1 z.2 s'' hs
  have e1 : tOf A.swap (A.msg false) (swapS Hb A z).1.1.1.2.1 (swapS Hb A z).1.1.1.2.2
      (s1S Hb z.1.1 z.2) = tS Hb A (A.msg true) z.1.2 z.2 :=
    tS_swapS₀ Hb A z
  have e2 : tOf A (A.msg false) z.1.1.1.2.1 z.1.1.1.2.2 (s1S Hb z.1.1 z.2) =
      tS Hb A (A.msg false) z.1.1 z.2 := rfl
  rw [hS1, kOf_fst, kOf_fst, Bool.cond_false, Bool.cond_false, Bool.cond_false, Bool.cond_false,
    e1, e2, ← bothOK_swap A (tS Hb A (A.msg false) z.1.1 z.2)]
  rfl

lemma swap_msg : A.swap.msg = A.msg := rfl

/-- **After the re-parametrization, `G2` for the exchanged roles is `G2`**. -/
theorem G2c_swap (z : (XS × XS) × ShP) : G2c Hb A.swap (swapS Hb A z) ↔ G2c Hb A z := by
  have e0 := tS_swapS₀ Hb A z
  have e1 := tS_swapS₁ Hb A z
  have hin := pS_swap_in Hb A z
  have hout := pS_swap_out Hb A z
    (pS Hb A (A.msg true) true z.1.2 (fun _ => tS Hb A (A.msg false) z.1.1 z.2) z.2) rfl
  unfold G2c
  rw [swap_msg, e0, e1, hin, hout, bothOK_swap]
  rfl

/-- **`G2`: the two worlds' fully simulated games are equal** (the Issuer with the roles
exchanged in world `false` is world `true`). -/
theorem G2_swap : pr ((XS × XS) × ShP) (G2 Hb A) = pr ((XS × XS) × ShP) (G2 Hb A.swap) := by
  rw [← pr_equiv (swapS_involutive Hb A).toPerm (G2 Hb A.swap)]
  refine pr_congr fun z => ?_
  rw [G2_iff_G2c, G2_iff_G2c]
  exact (G2c_swap Hb A z).symm

end Swap

/-! ## Blindness -/

section Blind

variable {Hb : Hashes}

/-- **The chain of world `false`**: `G0 → G1 → G2`. -/
theorem chain_false (hHb : HashesWF Hb) {A : AdversaryRO} {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP) (G0 Hb A) - pr ((XS × XS) × ShP) (G2 Hb A)| ≤
      εRO q3 ((q5 + 624) + 624) ((qE + 4607) + 4607) +
        (εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607) + deltaRO Hb A) :=
  (abs_sub_le _ _ _).trans (add_le_add (hop0 hHb hA) (hop1 hHb hA))

/-- **PomFRIT blindness in the random-oracle and ideal-cipher model** (label rows, the Lean prover
on the shared tables): for every Issuer with a budget `(q₃, q₅, q_E)`, the acceptance
probabilities of the two worlds differ by at most the four zero-knowledge errors at the
reductions' budgets and the two worlds' programming collision terms. -/
theorem blindnessRO (hHb : HashesWF Hb) (A : AdversaryRO) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP) (realGameRO Hb A false) - pr ((XR × XR) × ShP) (realGameRO Hb A true)| ≤
      2 * (εRO q3 ((q5 + 624) + 624) ((qE + 4607) + 4607) +
        εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607)) + deltaRO Hb A + deltaRO Hb A.swap := by
  have h0 : pr ((XR × XR) × ShP) (realGameRO Hb A false) = pr ((XR × XR) × ShP) (G0 Hb A) :=
    pr_congr (realGameRO_iff Hb A)
  have h1 : pr ((XR × XR) × ShP) (realGameRO Hb A true) = pr ((XR × XR) × ShP) (G0 Hb A.swap) :=
    (pr_congr (realGameRO_true Hb A)).trans ((pr_equiv swapXR (realGameRO Hb A.swap false)).trans
      (pr_congr (realGameRO_iff Hb A.swap)))
  have c0 := chain_false hHb hA
  have c1 := chain_false hHb hA.swap
  have hs := G2_swap Hb A
  rw [h0, h1]
  rw [hs] at c0
  have := abs_sub_le (pr ((XR × XR) × ShP) (G0 Hb A)) (pr ((XS × XS) × ShP) (G2 Hb A.swap))
    (pr ((XR × XR) × ShP) (G0 Hb A.swap))
  rw [abs_sub_comm (pr ((XS × XS) × ShP) (G2 Hb A.swap))] at this
  linarith

/-- **`blindnessRO` with one error term**: `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)`. -/
theorem blindnessRO' (hHb : HashesWF Hb) (A : AdversaryRO) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP) (realGameRO Hb A false) - pr ((XR × XR) × ShP) (realGameRO Hb A true)| ≤
      4 * εRO q3 (q5 + 1248) (qE + 18428) + deltaRO Hb A + deltaRO Hb A.swap := by
  have h := blindnessRO hHb A hA
  have e1 : εRO q3 ((q5 + 624) + 624) ((qE + 4607) + 4607) ≤ εRO q3 (q5 + 1248) (qE + 18428) :=
    εRO_mono le_rfl (by omega) (by omega)
  have e2 : εRO q3 ((q5 + 312) + 0) ((qE + 13821) + 4607) ≤ εRO q3 (q5 + 1248) (qE + 18428) :=
    εRO_mono le_rfl (by omega) (by omega)
  linarith

/-- **PomFRIT blindness in the random-oracle and ideal-cipher model, with SHAKE as the base
record** (the domains other than `H₃`, `H₂³`, `H₅` and the cipher). -/
theorem blindnessRO_lean (A : AdversaryRO) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP) (realGameRO Hashes.shake A false) -
        pr ((XR × XR) × ShP) (realGameRO Hashes.shake A true)| ≤
      4 * εRO q3 (q5 + 1248) (qE + 18428) + deltaRO Hashes.shake A + deltaRO Hashes.shake A.swap :=
  blindnessRO' hashesWF_shake A hA

end Blind

end VoleMole.Privacy.PomFRIT
