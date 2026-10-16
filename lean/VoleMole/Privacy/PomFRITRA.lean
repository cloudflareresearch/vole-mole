import VoleMole.Privacy.PomFRITDelta
import VoleMole.ZK.TwoPhaseAd
import VoleMole.ZK.AdaptRO

/-!
# PomFRIT blindness with an Issuer whose key, messages and responses read the tables

`blindnessRO_lean_num` (`Privacy/PomFRITRO.lean`, `Privacy/PomFRITDelta.lean`) assumes that the
Issuer's key, messages and responses do not read the random tables; only its final guess does.
Here they do (`AdversaryRA`): the key and the two messages are functions of the two sessions'
`H₃` slices and of the shared `H₅` and cipher tables, and so are the two responses, which also see
both requests. `hash_to_target`, `XOF_seed` (the games draw its outputs) and the refresher
commitment stay fixed functions (SHAKE), outside the tables, as in `Privacy/PomFRITRO.lean`.

## The model

* **The Issuer** (`AdversaryRA`): `pk sl s`, `msg b sl s`, `respond t₀ t₁ i sl s` (`sl` the two
  slices, `s` the shared tables) and the guess. At fixed tables it is an `AdversaryRO`
  (`AdversaryRA.at`). **Its interaction's budget** (`IBudget i₃ i₅ i_E`): the key-and-messages
  stage (`keyOf`) and, for every pair of requests, the response stage (`respOf`) are consistent
  table readers (`ZK.Sim.SReads`) of each slice (the other fixed) and the shared tables, reading at
  most `i₃` slice keys, `i₅` `H₅` keys, `i_E` cipher keys and **no `H₂³` key**. The guess's budget
  (`GBudget`) is `AdversaryRO.Budget`'s.
* **The real game** (`realGameRA`, `Privacy/PomFRITRAGame.lean`): `realGameRO` (the spec's
  protocol on `Layout.labelRows` with the Lean prover on the tables) for the Issuer at the game's
  slices and tables.

## The proof

This file has the model, the reads and the budgets; the game, the hops and the bound are in
`Privacy/PomFRITRAGame.lean`. As `blindnessRO`, with the Issuer at the original tables in every
hybrid (the simulators program only `H₂³`, which the interaction does not read: `at_h23`). The
zero-knowledge hops are `ZK.Sim.zk2_adaptive`: a session's continuation is the Issuer's response
to the request computed from the session's step-1 output, so it reads the slice and the shared
tables at keys that depend on that output (`hyp2RA_R`, `hyp2RA_S`). A function of the Issuer reads
it only at its key and messages and at its responses to the requests it computes (`kOf_fixR`,
`kOf_fixS`, `D0_fix`, `D1_fix`: the Issuer with these fixed, `AdversaryRA.fix`), which gives the
budgets (`budget_D0A`, `budget_D1A`):

* `hop0RA`: `εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 13821)`;
* `hop1RA`: `εRO(q₃ + 4i₃, q₅ + 4i₅ + 312, q_E + 4i_E + 23035)` and the collision term
  `deltaRA ≤ noHitProb + 2⁻¹²⁸` (`deltaRA_le`, from `deltaRO_event'` at the Issuer at the tables);
* `G2RA_swap`: the re-parametrization `swapS` at the Issuer at the tables.

The interaction is counted twice in each hop (as the continuation's reads and as the reduction's),
and the step-1 reads of the session whose request the interaction answers once more (`s1R`,
`s1S`).

**`blindnessRA_lean_num`**: `|Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872,
q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`.

**Not covered**: an interaction that reads `H₂³`. The two-phase simulator programs `H₂³` at the
zero-prefix block when the continuation stops (`simTab2` at `outPre2 = ∅`), which such an Issuer
could read before deciding whether to answer validly; the programming hop would need a collision
term for a continuation that read the block it later programs; and a reduction, which sees only
the programmed tables, would compute the other session's responses on them
(`ZK/TwoPhaseAd.lean`, `lean/docs/zk.md` §10.3).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

-- `Com` and the UOV map evaluate Keccak and the public map; nothing below needs to unfold them.
attribute [local irreducible] commitRefresher UOVKey.eval

/-! ## The model -/

/-- **The Issuer whose interaction reads the tables**: its key, messages and responses are
functions of the two sessions' `H₃` slices and the shared tables; the guess sees all of them. -/
structure AdversaryRA where
  pk : SlP → ShP → UOVKey
  msg : Bool → SlP → ShP → Bytes
  respond : Bytes → Bytes → Bool → SlP → ShP → Bytes
  guess : Bytes → Bytes → Option (Bytes × Bytes) → SlP → ShP → Prop

namespace AdversaryRA

variable (A : AdversaryRA)

/-- **The Issuer at the slices `sl` and the tables `s`**. -/
def «at» (sl : SlP) (s : ShP) : AdversaryRO where
  pk := A.pk sl s
  msg b := A.msg b sl s
  respond t₀ t₁ i := A.respond t₀ t₁ i sl s
  guess := A.guess

/-- The key-and-messages stage. -/
def keyOf (sl : SlP) (s : ShP) : UOVKey × Bytes × Bytes :=
  (A.pk sl s, A.msg false sl s, A.msg true sl s)

/-- The response stage at the requests `t₀`, `t₁`. -/
def respOf (t₀ t₁ : Bytes) (sl : SlP) (s : ShP) : Bytes × Bytes :=
  (A.respond t₀ t₁ false sl s, A.respond t₀ t₁ true sl s)

/-- **The Issuer with its key and messages `P` and a pair of responses `R`** (to every request). -/
def fix (P : UOVKey × Bytes × Bytes) (R : Bytes × Bytes) : AdversaryRO where
  pk := P.1
  msg b := bif b then P.2.2 else P.2.1
  respond _ _ i := bif i then R.2 else R.1
  guess := A.guess

/-- **The Issuer with the sessions' roles exchanged** (and the slices). -/
def swap : AdversaryRA where
  pk sl s := A.pk (sl.2, sl.1) s
  msg b sl s := A.msg b (sl.2, sl.1) s
  respond t₀ t₁ i sl s := A.respond t₁ t₀ (!i) (sl.2, sl.1) s
  guess t₀ t₁ y sl s := A.guess t₁ t₀ y (sl.2, sl.1) s

/-- **The interaction's budget**: as a function of each slice (the other fixed) and the shared
tables, the key-and-messages stage and the response stage at every pair of requests read at most
`i₃` slice keys, `i₅` `H₅` keys, `i_E` cipher keys and no `H₂³` key, consistently. -/
structure IBudget (i3 i5 iE : ℕ) : Prop where
  k0 : ∀ g₁ : Tab3, SReads pP (fun t : Tb pP => A.keyOf (t.1, g₁) t.2) i3 0 i5 iE
  k1 : ∀ g₀ : Tab3, SReads pP (fun t : Tb pP => A.keyOf (g₀, t.1) t.2) i3 0 i5 iE
  r0 : ∀ (t₀ t₁ : Bytes) (g₁ : Tab3),
    SReads pP (fun t : Tb pP => A.respOf t₀ t₁ (t.1, g₁) t.2) i3 0 i5 iE
  r1 : ∀ (t₀ t₁ : Bytes) (g₀ : Tab3),
    SReads pP (fun t : Tb pP => A.respOf t₀ t₁ (g₀, t.1) t.2) i3 0 i5 iE

/-- **The guess's budget** (`AdversaryRO.Budget`'s). -/
structure GBudget (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ t₀ t₁ y (g₁ : Tab3) s, Rd3 (fun g => A.guess t₀ t₁ y (g, g₁) s) q3
  h31 : ∀ t₀ t₁ y (g₀ : Tab3) s, Rd3 (fun g => A.guess t₀ t₁ y (g₀, g) s) q3
  h5 : ∀ t₀ t₁ y sl, Rd5 (A.guess t₀ t₁ y sl) q5
  hE : ∀ t₀ t₁ y sl, RdE (A.guess t₀ t₁ y sl) qE

variable {A}

lemma GBudget.fix {q3 q5 qE : ℕ} (h : A.GBudget q3 q5 qE) (P : UOVKey × Bytes × Bytes)
    (R : Bytes × Bytes) : (A.fix P R).Budget q3 q5 qE :=
  ⟨h.h30, h.h31, h.h5, h.hE⟩

lemma GBudget.swap {q3 q5 qE : ℕ} (h : A.GBudget q3 q5 qE) : A.swap.GBudget q3 q5 qE :=
  ⟨fun t₀ t₁ y g₁ s => h.h31 t₁ t₀ y g₁ s, fun t₀ t₁ y g₀ s => h.h30 t₁ t₀ y g₀ s,
    fun t₀ t₁ y sl => h.h5 t₁ t₀ y (sl.2, sl.1), fun t₀ t₁ y sl => h.hE t₁ t₀ y (sl.2, sl.1)⟩

lemma IBudget.swap {i3 i5 iE : ℕ} (h : A.IBudget i3 i5 iE) : A.swap.IBudget i3 i5 iE :=
  ⟨fun g₁ => h.k1 g₁, fun g₀ => h.k0 g₀,
    fun t₀ t₁ g₁ => (h.r1 t₁ t₀ g₁).map Prod.swap,
    fun t₀ t₁ g₀ => (h.r0 t₁ t₀ g₀).map Prod.swap⟩

/-- At the slices exchanged, the Issuer with the roles exchanged is the exchanged Issuer. -/
lemma swap_at (g₀ g₁ : Tab3) (s : ShP) : A.swap.at (g₁, g₀) s = (A.at (g₀, g₁) s).swap := rfl


end AdversaryRA

/-- A table reader that reads no `H₂³` key does not depend on `H₂³`. -/
lemma SReads.h23 {X : Type*} {p : Params} {f : Tb p → X} {a3 a5 aE : ℕ}
    (h : SReads p f a3 0 a5 aE) (g : Tab3) (s : Sh p) (G2 : Tab2G p) :
    f (g, (G2, s.2)) = f (g, s) := by
  obtain ⟨Q, hQ, hc⟩ := h
  have h0 : (Q (g, s)).2.1 = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hc _).2.1)
  refine (hQ (g, s) (g, (G2, s.2)) ⟨fun _ _ => rfl, fun k hk => ?_, fun _ _ => rfl,
    fun _ _ => rfl⟩).2
  rw [h0] at hk
  exact absurd hk (Finset.notMem_empty _)

namespace AdversaryRA

variable {A : AdversaryRA} {i3 i5 iE : ℕ}

/-- **The interaction does not read `H₂³`**, so the Issuer at programmed tables is the Issuer at
the original ones. -/
lemma IBudget.at_h23 (hI : A.IBudget i3 i5 iE) (sl : SlP) (s : ShP) (G2 : Tab2G pP) :
    A.at sl (G2, s.2) = A.at sl s := by
  obtain ⟨g₀, g₁⟩ := sl
  have hk := SReads.h23 (hI.k0 g₁) g₀ s G2
  have hr : ∀ t₀ t₁, A.respOf t₀ t₁ (g₀, g₁) (G2, s.2) = A.respOf t₀ t₁ (g₀, g₁) s :=
    fun t₀ t₁ => SReads.h23 (hI.r0 t₀ t₁ g₁) g₀ s G2
  simp only [keyOf, Prod.mk.injEq] at hk
  obtain ⟨hpk, hm0, hm1⟩ := hk
  unfold AdversaryRA.at
  congr 1
  · funext b
    cases b
    · exact hm0
    · exact hm1
  · funext t₀ t₁ i
    have := hr t₀ t₁
    simp only [respOf, Prod.mk.injEq] at this
    cases i
    · exact this.1
    · exact this.2

end AdversaryRA

/-! ## A function of the Issuer reads it only at the requests it computes -/

section Congr

variable (Hb : Hashes) {A₁ A₂ : AdversaryRO}

lemma hOf_congr (h : A₁.pk = A₂.pk) : hOf A₁ = hOf A₂ := by
  funext msg ref o1
  simp only [hOf, h]

lemma tOf_congr (h : A₁.pk = A₂.pk) : tOf A₁ = tOf A₂ := by
  funext msg ref r o1
  simp only [tOf, hOf_congr h]

lemma validB_congr (h : A₁.pk = A₂.pk) : validB A₁ = validB A₂ := by
  funext resp t
  simp only [validB, h]

lemma bothOK_congr (h : A₁.pk = A₂.pk) {t₀ t₁ : Bytes}
    (hr : ∀ i, A₁.respond t₀ t₁ i = A₂.respond t₀ t₁ i) : bothOK A₁ t₀ t₁ = bothOK A₂ t₀ t₁ := by
  simp only [bothOK, validB_congr h, hr]

/-- **A session's continuation reads the Issuer only at its key and its responses to the
requests of that session's step-1 output.** -/
lemma kOf_congr (h : A₁.pk = A₂.pk) (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM)
    (i : Bool) (t' : Bytes) (o1 : ByteArray × ByteArray)
    (hr : ∀ j, A₁.respond (bif i then t' else tOf A₁ msg ref r o1)
      (bif i then tOf A₁ msg ref r o1 else t') j =
      A₂.respond (bif i then t' else tOf A₁ msg ref r o1) (bif i then tOf A₁ msg ref r o1 else t') j) :
    kOf A₁ msg ref r i t' o1 = kOf A₂ msg ref r i t' o1 := by
  have ht := tOf_congr h
  have hb := bothOK_congr h hr
  unfold kOf
  rw [← ht, hb, hOf_congr h, h, hr i]

lemma view2_congr (h : A₁.pk = A₂.pk) (hg : A₁.guess = A₂.guess) (b : Bool)
    (m₀ m₁ : Bytes × Coins refresherBytes × Coins uovM) (o₀ o₁ : Out2) (sl : SlP) (v : ShP)
    (hr : ∀ i, A₁.respond (tOf A₁ m₀.1 m₀.2.1 m₀.2.2 (o₀.1, o₀.2.1))
      (tOf A₁ m₁.1 m₁.2.1 m₁.2.2 (o₁.1, o₁.2.1)) i =
      A₂.respond (tOf A₁ m₀.1 m₀.2.1 m₀.2.2 (o₀.1, o₀.2.1))
        (tOf A₁ m₁.1 m₁.2.1 m₁.2.2 (o₁.1, o₁.2.1)) i) :
    view2 A₁ b m₀ m₁ o₀ o₁ sl v ↔ view2 A₂ b m₀ m₁ o₀ o₁ sl v := by
  have ht := tOf_congr h
  have hb := bothOK_congr h hr
  unfold view2
  rw [← ht, hb, hg]

/-- The real two-phase run reads its continuation only at its step-1 output. -/
lemma realRun2_kcongr [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray)
    {k k' : Cont2} (rho : ByteArray)
    (h : k ((step1 Hs T st r rho).proof, (step1 Hs T st r rho).chal1) =
      k' ((step1 Hs T st r rho).proof, (step1 Hs T st r rho).chal1)) :
    realRun2 Hs T st r k rho = realRun2 Hs T st r k' rho := by
  unfold realRun2
  dsimp only
  rw [h]

lemma oR_congr (msg : Bytes) (i : Bool) (x : XR) (t' : ShP → Bytes) (s : ShP)
    (h : kOf A₁ msg x.1.2.1 x.1.2.2 i (t' s) (s1R Hb x s) =
      kOf A₂ msg x.1.2.1 x.1.2.2 i (t' s) (s1R Hb x s)) :
    oR Hb A₁ msg i x t' s = oR Hb A₂ msg i x t' s := by
  rw [oR_def, oR_def]
  exact @realRun2_kcongr (icPrg s.2.2) _ _ _ _ _ _ _ h

/-- The re-parametrization of `G2`'s tape reads the Issuer only at its key and messages. -/
lemma swapS_congr (h : A₁.pk = A₂.pk) (hm : A₁.msg = A₂.msg) : swapS Hb A₁ = swapS Hb A₂ := by
  funext z
  simp only [swapS, hS, hOf_congr h, hm]

lemma oS_congr (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP)
    (h : kOf A₁ msg y.1.2.1 y.1.2.2 i (t' s) (s1S Hb y s) =
      kOf A₂ msg y.1.2.1 y.1.2.2 i (t' s) (s1S Hb y s)) :
    oS Hb A₁ msg i y t' s = oS Hb A₂ msg i y t' s := by
  rw [oS_eq, oS_eq]
  refine @simRun2_kcongr' (icPrg s.2.2) Hb (stOf y.1.2.1) uovM _ _ y.1.1 ?_
  have e := oS_s1 Hb A₁ msg i y t' s
  rw [oS_eq] at e
  rw [e]
  exact h

lemma pS_congr (msg : Bytes) (i : Bool) (y : XS) (t' : ShP → Bytes) (s : ShP)
    (h : kOf A₁ msg y.1.2.1 y.1.2.2 i (t' s) (s1S Hb y s) =
      kOf A₂ msg y.1.2.1 y.1.2.2 i (t' s) (s1S Hb y s)) :
    pS Hb A₁ msg i y t' s = pS Hb A₂ msg i y t' s := by
  rw [pS_eq, pS_eq]
  refine progK_kcongr Hb (stOf y.1.2.1) uovM y.1.1 s ?_
  have e : ((@simRun2 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (fun _ => none) y.1.1).1,
      (@simRun2 (icPrg s.2.2) Hb (stOf y.1.2.1) uovM (fun _ => none) y.1.1).2.1) = s1S Hb y s := rfl
  rw [e, h]

/-- **`D0` reads the Issuer at its key and messages and at the responses to the two requests.** -/
lemma D0_congr (h : A₁.pk = A₂.pk) (hg : A₁.guess = A₂.guess) (h0 : A₁.msg false = A₂.msg false)
    (h1 : A₁.msg true = A₂.msg true) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o : Out2) (g : Tab3) (s : ShP)
    (hr : ∀ i, A₁.respond (tOf A₁ (A₁.msg false) ref₀ r₀ (o.1, o.2.1)) (tR Hb A₁ (A₁.msg true) x₁ s) i =
      A₂.respond (tOf A₁ (A₁.msg false) ref₀ r₀ (o.1, o.2.1)) (tR Hb A₁ (A₁.msg true) x₁ s) i) :
    D0 Hb A₁ ref₀ r₀ x₁ o g s ↔ D0 Hb A₂ ref₀ r₀ x₁ o g s := by
  have ht := tOf_congr h
  have hk : kOf A₁ (A₁.msg true) x₁.1.2.1 x₁.1.2.2 true
      ((fun _ => tOf A₁ (A₁.msg false) ref₀ r₀ (o.1, o.2.1)) s) (s1R Hb x₁ s) =
      kOf A₂ (A₁.msg true) x₁.1.2.1 x₁.1.2.2 true
      ((fun _ => tOf A₁ (A₁.msg false) ref₀ r₀ (o.1, o.2.1)) s) (s1R Hb x₁ s) :=
    kOf_congr h _ _ _ true _ _ hr
  have hO := oR_congr Hb (A₁.msg true) true x₁ (fun _ => tOf A₁ (A₁.msg false) ref₀ r₀ (o.1, o.2.1))
    s hk
  unfold D0
  rw [← h0, ← h1, ← ht, ← hO]
  refine view2_congr h hg _ _ _ _ _ _ _ ?_
  rw [oR_s1]
  exact hr

/-- **`D1` reads the Issuer at its key and messages and at the responses to the two requests.** -/
lemma D1_congr (h : A₁.pk = A₂.pk) (hg : A₁.guess = A₂.guess) (h0 : A₁.msg false = A₂.msg false)
    (h1 : A₁.msg true = A₂.msg true) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (o : Out2) (g : Tab3) (s : ShP)
    (hr : ∀ i, A₁.respond (tS Hb A₁ (A₁.msg false) y₀ s) (tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1)) i =
      A₂.respond (tS Hb A₁ (A₁.msg false) y₀ s) (tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1)) i) :
    D1 Hb A₁ ref₁ r₁ y₀ o g s ↔ D1 Hb A₂ ref₁ r₁ y₀ o g s := by
  have ht := tOf_congr h
  have hk : kOf A₁ (A₁.msg false) y₀.1.2.1 y₀.1.2.2 false
      ((fun _ => tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1)) s) (s1S Hb y₀ s) =
      kOf A₂ (A₁.msg false) y₀.1.2.1 y₀.1.2.2 false
      ((fun _ => tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1)) s) (s1S Hb y₀ s) :=
    kOf_congr h _ _ _ false _ _ hr
  have hO := oS_congr Hb (A₁.msg false) false y₀ (fun _ => tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1))
    s hk
  have hP := pS_congr Hb (A₁.msg false) false y₀ (fun _ => tOf A₁ (A₁.msg true) ref₁ r₁ (o.1, o.2.1))
    s hk
  unfold D1
  rw [← h0, ← h1, ← ht, ← hO, ← hP]
  refine view2_congr h hg _ _ _ _ _ _ _ ?_
  rw [oS_s1]
  exact hr

end Congr

/-! ## Binding reads -/

section BindReads

variable {p : Params} {X Y : Sort*} {a b : ℕ}

/-- A pair with a component that does not read `H₅`. -/
lemma Rd5.pair_indep {Y' X' : Type*} {m : Sh p → Y'} {n : Sh p → X'} (hm : Rd5 m a)
    (hn : ∀ s G5, n (s.1, G5, s.2.2) = n s) : Rd5 (fun s => (m s, n s)) a := by
  obtain ⟨Q, hQ, hf⟩ := hm
  exact ⟨Q, hQ, fun s G5 h => by simp only [hf s G5 h, hn s G5]⟩

lemma Rd3.bind' {m : Tab3 → Y} {f : Y → Tab3 → X} {F : Tab3 → X} (hF : ∀ g, F g = f (m g) g)
    (hm : Rd3 m a) (hf : ∀ y, Rd3 (f y) b) : Rd3 F (a + b) := by
  have e : F = fun g => f (m g) g := funext hF
  subst e
  exact hm.bind hf

lemma Rd5.bind' {m : Sh p → Y} {f : Y → Sh p → X} {F : Sh p → X} (hF : ∀ s, F s = f (m s) s)
    (hm : Rd5 m a) (hf : ∀ y, Rd5 (f y) b) : Rd5 F (a + b) := by
  have e : F = fun s => f (m s) s := funext hF
  subst e
  exact hm.bind hf

lemma RdE.bind' {m : Sh p → Y} {f : Y → Sh p → X} {F : Sh p → X} (hF : ∀ s, F s = f (m s) s)
    (hm : RdE m a) (hf : ∀ y, RdE (f y) b) : RdE F (a + b) := by
  have e : F = fun s => f (m s) s := funext hF
  subst e
  exact hm.bind hf

end BindReads

/-! ## The Issuer at the tables, with its key and responses fixed -/

section Fix

variable (Hb : Hashes) (A : AdversaryRA)

/-- A request from a key and messages `P` (`tOf` reads the Issuer only at its key). -/
def tK (P : UOVKey × Bytes × Bytes) (msg : Bytes) (ref : Coins refresherBytes) (r : Coins uovM)
    (o1 : ByteArray × ByteArray) : Bytes :=
  xorBytes (Layout.labelRows.hashToTarget P.1.digest (toL o1.2) (toL o1.1 ++ comOf ref ++
    List.ofFn ref) msg) (List.ofFn r)

lemma tOf_eq_tK {A' : AdversaryRO} {P : UOVKey × Bytes × Bytes} (h : A'.pk = P.1) :
    tOf A' = tK P := by
  funext msg ref r o1
  simp only [tOf, hOf, tK, h]

variable {A}

/-- **Session `0`'s continuation, session `1` real**: the Issuer at the tables answers the request
of session `0`'s step-1 output and session `1`'s request. -/
lemma kOf_fixR (sl : SlP) (s : ShP) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o1 : ByteArray × ByteArray) :
    kOf (A.at sl s) ((A.at sl s).msg false) ref₀ r₀ false
        (tR Hb (A.at sl s) ((A.at sl s).msg true) x₁ s) o1 =
      kOf (A.fix (A.keyOf sl s) (A.respOf (tK (A.keyOf sl s) (A.msg false sl s) ref₀ r₀ o1)
          (tK (A.keyOf sl s) (A.msg true sl s) x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) sl s))
        (A.msg false sl s) ref₀ r₀ false
        (tK (A.keyOf sl s) (A.msg true sl s) x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) o1 := by
  have ht : tOf (A.at sl s) = tK (A.keyOf sl s) := tOf_eq_tK rfl
  have hR : tR Hb (A.at sl s) ((A.at sl s).msg true) x₁ s =
      tK (A.keyOf sl s) (A.msg true sl s) x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s) := by
    rw [tR, ht]; rfl
  rw [hR]
  refine kOf_congr rfl _ _ _ false _ _ fun j => ?_
  cases j <;> (rw [ht]; try rfl)

/-- **Session `1`'s continuation, session `0` simulated.** -/
lemma kOf_fixS (sl : SlP) (s : ShP) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (o1 : ByteArray × ByteArray) :
    kOf (A.at sl s) ((A.at sl s).msg true) ref₁ r₁ true
        (tS Hb (A.at sl s) ((A.at sl s).msg false) y₀ s) o1 =
      kOf (A.fix (A.keyOf sl s) (A.respOf
          (tK (A.keyOf sl s) (A.msg false sl s) y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
          (tK (A.keyOf sl s) (A.msg true sl s) ref₁ r₁ o1) sl s))
        (A.msg true sl s) ref₁ r₁ true
        (tK (A.keyOf sl s) (A.msg false sl s) y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s)) o1 := by
  have ht : tOf (A.at sl s) = tK (A.keyOf sl s) := tOf_eq_tK rfl
  have hS : tS Hb (A.at sl s) ((A.at sl s).msg false) y₀ s =
      tK (A.keyOf sl s) (A.msg false sl s) y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s) := by
    rw [tS, ht]; rfl
  rw [hS]
  refine kOf_congr rfl _ _ _ true _ _ fun j => ?_
  cases j <;> (rw [ht]; try rfl)

/-- **`D0` at the Issuer at the tables** is `D0` at the Issuer with its key and its responses to
the two requests fixed. -/
lemma D0_fix (sl : SlP) (s : ShP) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o : Out2) (g : Tab3) :
    D0 Hb (A.at sl s) ref₀ r₀ x₁ o g s ↔
      D0 Hb (A.fix (A.keyOf sl s) (A.respOf (tK (A.keyOf sl s) (A.msg false sl s) ref₀ r₀ (o.1, o.2.1))
          (tK (A.keyOf sl s) (A.msg true sl s) x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) sl s))
        ref₀ r₀ x₁ o g s := by
  have ht : tOf (A.at sl s) = tK (A.keyOf sl s) := tOf_eq_tK rfl
  refine D0_congr Hb (A₁ := A.at sl s)
    (A₂ := A.fix (A.keyOf sl s) (A.respOf (tK (A.keyOf sl s) (A.msg false sl s) ref₀ r₀ (o.1, o.2.1))
      (tK (A.keyOf sl s) (A.msg true sl s) x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) sl s))
    rfl rfl rfl rfl ref₀ r₀ x₁ o g s fun i => ?_
  cases i <;> (rw [tR, ht]; try rfl)

/-- **`D1` at the Issuer at the tables** is `D1` at the Issuer with its key and its responses to
the two requests fixed. -/
lemma D1_fix (sl : SlP) (s : ShP) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (o : Out2) (g : Tab3) :
    D1 Hb (A.at sl s) ref₁ r₁ y₀ o g s ↔
      D1 Hb (A.fix (A.keyOf sl s) (A.respOf
          (tK (A.keyOf sl s) (A.msg false sl s) y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
          (tK (A.keyOf sl s) (A.msg true sl s) ref₁ r₁ (o.1, o.2.1)) sl s))
        ref₁ r₁ y₀ o g s := by
  have ht : tOf (A.at sl s) = tK (A.keyOf sl s) := tOf_eq_tK rfl
  refine D1_congr Hb (A₁ := A.at sl s)
    (A₂ := A.fix (A.keyOf sl s) (A.respOf
      (tK (A.keyOf sl s) (A.msg false sl s) y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
      (tK (A.keyOf sl s) (A.msg true sl s) ref₁ r₁ (o.1, o.2.1)) sl s))
    rfl rfl rfl rfl ref₁ r₁ y₀ o g s fun i => ?_
  cases i <;> (rw [tS, ht]; try rfl)

end Fix

/-! ## The continuations satisfy the hypotheses of `zk2_adaptive` -/

section Hyps

variable (Hb : Hashes) (A : AdversaryRA) {i3 i5 iE : ℕ}

/-- **Session `0`'s continuation with session `1` real**: the Issuer at the tables (with session
`0`'s slice `g`) answers the two requests. -/
noncomputable def K0 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) (g : Tab3)
    (s : ShP) : Cont2 :=
  kOf (A.at (g, x₁.2) s) ((A.at (g, x₁.2) s).msg false) ref₀ r₀ false
    (tR Hb (A.at (g, x₁.2) s) ((A.at (g, x₁.2) s).msg true) x₁ s)

/-- **Session `1`'s continuation with session `0` simulated.** -/
noncomputable def K1 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS) (g : Tab3)
    (s : ShP) : Cont2 :=
  kOf (A.at (y₀.2, g) s) ((A.at (y₀.2, g) s).msg true) ref₁ r₁ true
    (tS Hb (A.at (y₀.2, g) s) ((A.at (y₀.2, g) s).msg false) y₀ s)

variable {Hb A}

/-- A simulated session's step 1 does not read `H₅`. -/
lemma K0_h23 (hI : A.IBudget i3 i5 iE) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (g : Tab3) (s : ShP) (G2 : Tab2G pP) :
    K0 Hb A ref₀ r₀ x₁ g (G2, s.2) = K0 Hb A ref₀ r₀ x₁ g s := by
  unfold K0
  rw [hI.at_h23, tR, tR, s1R_h23]

lemma K1_h23 (hI : A.IBudget i3 i5 iE) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (g : Tab3) (s : ShP) (G2 : Tab2G pP) :
    K1 Hb A ref₁ r₁ y₀ g (G2, s.2) = K1 Hb A ref₁ r₁ y₀ g s := by
  unfold K1
  rw [hI.at_h23, tS, tS, s1S_eq Hb y₀ s (G2, s.2) rfl]

/-- **The hypotheses of `zk2_adaptive` for session `0`'s continuation**: it reads session `0`'s
slice at `2·i₃` keys (the key stage and the response stage), `H₅` at `2·i₅ + 624` and the cipher
at `2·i_E + 4607` keys (and session `1`'s step 1, for its request). -/
theorem hyp2RA_R (hHb : HashesWF Hb) (hI : A.IBudget i3 i5 iE) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) :
    Hyp2RA (stOf ref₀) (toBA (List.ofFn r₀)) uovM (K0 Hb A ref₀ r₀ x₁) (i3 + i3) (i5 + 624 + i5)
      (iE + 4607 + iE) where
  hyp g s := hyp2_kOf _ _ _ _ _ _
  size := by rw [size_toBA, List.length_ofFn]
  h2 g s G2 := K0_h23 hI ref₀ r₀ x₁ g s G2
  h3 o1 s := Rd3.bind' (m := fun g => A.keyOf (g, x₁.2) s)
    (f := fun P g => kOf (A.fix P (A.respOf (tK P P.2.1 ref₀ r₀ o1)
        (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) (g, x₁.2) s))
      P.2.1 ref₀ r₀ false (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) o1)
    (fun g => kOf_fixR Hb (g, x₁.2) s ref₀ r₀ x₁ o1) ((hI.k0 x₁.2).rd3 s)
    (fun P => ((hI.r0 (tK P P.2.1 ref₀ r₀ o1) (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s))
      x₁.2).rd3 s).map fun R => kOf (A.fix P R) P.2.1 ref₀ r₀ false
        (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) o1)
  h5 o1 g := Rd5.bind' (m := fun s => (A.keyOf (g, x₁.2) s, s1R Hb x₁ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ o1)
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s))
      Py.1.2.1 ref₀ r₀ false (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) o1)
    (fun s => kOf_fixR Hb (g, x₁.2) s ref₀ r₀ x₁ o1)
    (((hI.k0 x₁.2).rd5 g).bind fun P => (s1R_rd5 Hb x₁).map fun y => (P, y))
    (fun Py => ((hI.r0 (tK Py.1 Py.1.2.1 ref₀ r₀ o1) (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2)
      x₁.2).rd5 g).map fun R => kOf (A.fix Py.1 R) Py.1.2.1 ref₀ r₀ false
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) o1)
  hE o1 g := RdE.bind' (m := fun s => (A.keyOf (g, x₁.2) s, s1R Hb x₁ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ o1)
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s))
      Py.1.2.1 ref₀ r₀ false (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) o1)
    (fun s => kOf_fixR Hb (g, x₁.2) s ref₀ r₀ x₁ o1)
    (((hI.k0 x₁.2).rdE g).bind fun P => (s1R_rdE Hb hHb x₁).map fun y => (P, y))
    (fun Py => ((hI.r0 (tK Py.1 Py.1.2.1 ref₀ r₀ o1) (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2)
      x₁.2).rdE g).map fun R => kOf (A.fix Py.1 R) Py.1.2.1 ref₀ r₀ false
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) o1)

set_option maxHeartbeats 1000000 in
/-- **The hypotheses of `zk2_adaptive` for session `1`'s continuation**, session `0` simulated:
`2·i₃` slice keys, `2·i₅` `H₅` keys, `2·i_E + 4607` cipher keys (session `0`'s simulated step 1). -/
theorem hyp2RA_S (hI : A.IBudget i3 i5 iE) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (y₀ : XS) :
    Hyp2RA (stOf ref₁) (toBA (List.ofFn r₁)) uovM (K1 Hb A ref₁ r₁ y₀) (i3 + i3) (i5 + i5)
      (iE + 4607 + iE) where
  hyp g s := hyp2_kOf _ _ _ _ _ _
  size := by rw [size_toBA, List.length_ofFn]
  h2 g s G2 := K1_h23 hI ref₁ r₁ y₀ g s G2
  h3 o1 s := Rd3.bind' (m := fun g => A.keyOf (y₀.2, g) s)
    (f := fun P g => kOf (A.fix P (A.respOf (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
        (tK P P.2.2 ref₁ r₁ o1) (y₀.2, g) s))
      P.2.2 ref₁ r₁ true (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s)) o1)
    (fun g => kOf_fixS Hb (y₀.2, g) s ref₁ r₁ y₀ o1) ((hI.k1 y₀.2).rd3 s)
    (fun P => ((hI.r1 (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s)) (tK P P.2.2 ref₁ r₁ o1)
      y₀.2).rd3 s).map fun R => kOf (A.fix P R) P.2.2 ref₁ r₁ true
        (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s)) o1)
  h5 o1 g := Rd5.bind' (m := fun s => (A.keyOf (y₀.2, g) s, s1S Hb y₀ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ o1) (y₀.2, g) s))
      Py.1.2.2 ref₁ r₁ true (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) o1)
    (fun s => kOf_fixS Hb (y₀.2, g) s ref₁ r₁ y₀ o1)
    (Rd5.pair_indep ((hI.k1 y₀.2).rd5 g) fun s G5 => s1S_eq Hb y₀ s (s.1, G5, s.2.2) rfl)
    (fun Py => ((hI.r1 (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ o1)
      y₀.2).rd5 g).map fun R => kOf (A.fix Py.1 R) Py.1.2.2 ref₁ r₁ true
        (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) o1)
  hE o1 g := RdE.bind' (m := fun s => (A.keyOf (y₀.2, g) s, s1S Hb y₀ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ o1) (y₀.2, g) s))
      Py.1.2.2 ref₁ r₁ true (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) o1)
    (fun s => kOf_fixS Hb (y₀.2, g) s ref₁ r₁ y₀ o1)
    (((hI.k1 y₀.2).rdE g).bind fun P => (s1S_rdE Hb y₀).map fun y => (P, y))
    (fun Py => ((hI.r1 (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ o1)
      y₀.2).rdE g).map fun R => kOf (A.fix Py.1 R) Py.1.2.2 ref₁ r₁ true
        (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) o1)

end Hyps

/-! ## The reductions' budgets -/

section Budgets

variable {Hb : Hashes} {A : AdversaryRA} {q3 q5 qE i3 i5 iE : ℕ}

/-- **The reduction for session `0`** at the Issuer at the tables (session `0`'s slice `g`). -/
noncomputable def D0A (Hb : Hashes) (A : AdversaryRA) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM)
    (x₁ : XR) (o : Out2) (g : Tab3) (s : ShP) : Prop :=
  D0 Hb (A.at (g, x₁.2) s) ref₀ r₀ x₁ o g s

/-- **The reduction for session `1`** at the Issuer at the tables (session `1`'s slice `g`). -/
noncomputable def D1A (Hb : Hashes) (A : AdversaryRA) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (y₀ : XS) (o : Out2) (g : Tab3) (s : ShP) : Prop :=
  D1 Hb (A.at (y₀.2, g) s) ref₁ r₁ y₀ o g s

/-- **The budget of the reduction for session `0`**: the guess's, the interaction's (key stage and
response stage), session `1`'s real run and its step 1 (for its request). -/
theorem budget_D0A (hHb : HashesWF Hb) (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE)
    (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) :
    Budget pP (i3 + (i3 + q3)) (i5 + 624 + (i5 + (q5 + 624))) (iE + 4607 + (iE + (qE + 4607)))
      (D0A Hb A ref₀ r₀ x₁) where
  h3 o s := Rd3.bind' (m := fun g => A.keyOf (g, x₁.2) s)
    (f := fun P g => D0 Hb (A.fix P (A.respOf (tK P P.2.1 ref₀ r₀ (o.1, o.2.1))
      (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) (g, x₁.2) s)) ref₀ r₀ x₁ o g s)
    (fun g => propext (D0_fix Hb (g, x₁.2) s ref₀ r₀ x₁ o g)) ((hI.k0 x₁.2).rd3 s)
    (fun P => Rd3.bind' (m := fun g => A.respOf (tK P P.2.1 ref₀ r₀ (o.1, o.2.1))
        (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) (g, x₁.2) s)
      (f := fun R g => D0 Hb (A.fix P R) ref₀ r₀ x₁ o g s) (fun _ => rfl)
      ((hI.r0 (tK P P.2.1 ref₀ r₀ (o.1, o.2.1)) (tK P P.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s))
        x₁.2).rd3 s)
      (fun R => (budget_D0 hHb (hA.fix P R) ref₀ r₀ x₁).h3 o s))
  h5 o g := Rd5.bind' (m := fun s => (A.keyOf (g, x₁.2) s, s1R Hb x₁ s))
    (f := fun Py s => D0 Hb (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1))
      (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s)) ref₀ r₀ x₁ o g s)
    (fun s => propext (D0_fix Hb (g, x₁.2) s ref₀ r₀ x₁ o g))
    (((hI.k0 x₁.2).rd5 g).bind fun P => (s1R_rd5 Hb x₁).map fun y => (P, y))
    (fun Py => Rd5.bind' (m := fun s => A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1))
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s)
      (f := fun R s => D0 Hb (A.fix Py.1 R) ref₀ r₀ x₁ o g s) (fun _ => rfl)
      ((hI.r0 (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1)) (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2)
        x₁.2).rd5 g) (fun R => (budget_D0 hHb (hA.fix Py.1 R) ref₀ r₀ x₁).h5 o g))
  hE o g := RdE.bind' (m := fun s => (A.keyOf (g, x₁.2) s, s1R Hb x₁ s))
    (f := fun Py s => D0 Hb (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1))
      (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s)) ref₀ r₀ x₁ o g s)
    (fun s => propext (D0_fix Hb (g, x₁.2) s ref₀ r₀ x₁ o g))
    (((hI.k0 x₁.2).rdE g).bind fun P => (s1R_rdE Hb hHb x₁).map fun y => (P, y))
    (fun Py => RdE.bind' (m := fun s => A.respOf (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1))
        (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2) (g, x₁.2) s)
      (f := fun R s => D0 Hb (A.fix Py.1 R) ref₀ r₀ x₁ o g s) (fun _ => rfl)
      ((hI.r0 (tK Py.1 Py.1.2.1 ref₀ r₀ (o.1, o.2.1)) (tK Py.1 Py.1.2.2 x₁.1.2.1 x₁.1.2.2 Py.2)
        x₁.2).rdE g) (fun R => (budget_D0 hHb (hA.fix Py.1 R) ref₀ r₀ x₁).hE o g))

set_option maxHeartbeats 1000000 in
/-- **The budget of the reduction for session `1`**: the guess's, the interaction's, the simulated
session `0`'s run and programming and its step 1 (for its request). -/
theorem budget_D1A (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE)
    (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS) :
    Budget pP (i3 + (i3 + q3)) (i5 + (i5 + (q5 + 312))) (iE + 4607 + (iE + (qE + 13821)))
      (D1A Hb A ref₁ r₁ y₀) where
  h3 o s := Rd3.bind' (m := fun g => A.keyOf (y₀.2, g) s)
    (f := fun P g => D1 Hb (A.fix P (A.respOf (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
      (tK P P.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)) ref₁ r₁ y₀ o g s)
    (fun g => propext (D1_fix Hb (y₀.2, g) s ref₁ r₁ y₀ o g)) ((hI.k1 y₀.2).rd3 s)
    (fun P => Rd3.bind' (m := fun g => A.respOf (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s))
        (tK P P.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)
      (f := fun R g => D1 Hb (A.fix P R) ref₁ r₁ y₀ o g s) (fun _ => rfl)
      ((hI.r1 (tK P P.2.1 y₀.1.2.1 y₀.1.2.2 (s1S Hb y₀ s)) (tK P P.2.2 ref₁ r₁ (o.1, o.2.1))
        y₀.2).rd3 s)
      (fun R => (budget_D1 (hA.fix P R) ref₁ r₁ y₀).h3 o s))
  h5 o g := Rd5.bind' (m := fun s => (A.keyOf (y₀.2, g) s, s1S Hb y₀ s))
    (f := fun Py s => D1 Hb (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
      (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)) ref₁ r₁ y₀ o g s)
    (fun s => propext (D1_fix Hb (y₀.2, g) s ref₁ r₁ y₀ o g))
    (Rd5.pair_indep ((hI.k1 y₀.2).rd5 g) fun s G5 => s1S_eq Hb y₀ s (s.1, G5, s.2.2) rfl)
    (fun Py => Rd5.bind' (m := fun s => A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)
      (f := fun R s => D1 Hb (A.fix Py.1 R) ref₁ r₁ y₀ o g s) (fun _ => rfl)
      ((hI.r1 (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1))
        y₀.2).rd5 g) (fun R => (budget_D1 (hA.fix Py.1 R) ref₁ r₁ y₀).h5 o g))
  hE o g := RdE.bind' (m := fun s => (A.keyOf (y₀.2, g) s, s1S Hb y₀ s))
    (f := fun Py s => D1 Hb (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
      (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)) ref₁ r₁ y₀ o g s)
    (fun s => propext (D1_fix Hb (y₀.2, g) s ref₁ r₁ y₀ o g))
    (((hI.k1 y₀.2).rdE g).bind fun P => (s1S_rdE Hb y₀).map fun y => (P, y))
    (fun Py => RdE.bind' (m := fun s => A.respOf (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1)) (y₀.2, g) s)
      (f := fun R s => D1 Hb (A.fix Py.1 R) ref₁ r₁ y₀ o g s) (fun _ => rfl)
      ((hI.r1 (tK Py.1 Py.1.2.1 y₀.1.2.1 y₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ (o.1, o.2.1))
        y₀.2).rdE g) (fun R => (budget_D1 (hA.fix Py.1 R) ref₁ r₁ y₀).hE o g))

end Budgets

end VoleMole.Privacy.PomFRIT
