import VoleMole.Privacy.PomFRITMany
import VoleMole.ZK.ReadsPoint

/-!
# PomFRIT with many sessions and `H₄` a table: no per-session cipher charge

The many-session and `N`-pair bounds of `Privacy/PomFRITMany.lean` are linear resp. quadratic in
the number of sessions because each further session is part of the distinguisher of the
two-session hybrids: its `4607` cipher reads are charged `221·2⁻¹²⁸` each in every H4 hop, and its
`624` `H₅` reads `2⁻¹²⁸` each in every H6 hop (`lean/docs/zk.md` §10.8). Here `H₄` (the `iv`
derivation `iv = H₄(iv_pre ‖ µ₁ ‖ 4)`) is a uniform table of the game, and the further sessions are
taken out of the tables altogether, by lazy sampling: each step costs the two-session bound with
**no** further-session reads, plus a collision term of order `2⁻¹²⁸` per pair of sessions.

## The model

* `hb4 G4`: the base record with `H₄` answered by a table `G4 : Bytes 49 → Bytes 16` on every
  `49`-byte input (SHAKE elsewhere). The sessions run the executable Lean prover with this record
  (`realGameN (hb4 G4)`, `realGameP (hb4 G4)`), so a session's `iv` is the table's answer at its
  `iv_pre ‖ µ₁ ‖ 4` (`step1Iv_hb4`); the Issuer is a family `Tab4 → AdversaryN` (it may read all
  of `H₄`, unbudgeted). `realGameNH`, `realGamePH`: the games averaged over a uniform `G4`.
* Function rows only (`FR = Blk → Blk`): lazy sampling patches the cipher at single points.

## The argument (one step: one challenge pair, the other sessions further sessions)

* **Step 1 reads points** (`ZK/ReadsPoint.lean`, `step1_consP`): a session's step 1 reads `H₅` at
  its `624` gate inputs and the cipher only at its tree's nodes **on the CTR blocks of its `iv`**
  (`rdX`); a table agreeing there has the same step-1 state and reads (`rdX_cons`), and step 2
  reads neither (`sessOf_tables`). The further sessions together are such a reader (`QX_cons`).
* **Lazy sampling** (`red_close_redP`, `Privacy.pr_resample`): the game's `(H₅, cipher)` pair is
  `mixR (QX c t₁) t₁ t₂`, the further sessions' view `t₁` on their read set and a fresh `t₂`
  elsewhere. Unless a challenge session's reads on `t₂` meet the further sessions' reads on `t₁`
  (`badQ`), the challenge sessions see `t₂` (`realGameRA_patch_iff`), so the game is that of the
  **reduction** `A.redP c t₁` (`AdversaryN.redP`): the two-session table-reading game whose
  interaction reads **no table** (the further sessions' requests come from the private `t₁`,
  `redP_iBudget`) and whose guess reads the patched tables with the Issuer's own budget
  (`redP_gBudget`). `blindnessRA` applies for every `t₁` (`red_step`):
  `εPair0 = 4·εRO(q₃, q₅ + 1872, q_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`.
* **The bad event** (`pr_badQ_le`, `pr_Bp_le`): for one challenge session and one further session,
  a common `H₅` key means equal `iv`s (`k5X_iv`: the keys begin with the `iv`), and a common
  cipher point means a common tree node **and** equal second lanes of the `iv`s
  (`lane1_of_ctrBlock_eq`). With `iv = H₄(iv_pre ‖ µ₁ ‖ 4)` from the table and `iv_pre`, the seed
  from the sessions' independent slices, this has probability `≤ 2⁻¹²⁸` (equal `iv_pre`s) `+
  2⁻¹²⁸` (an `H₄` collision) `+ 2⁻¹²⁸` (equal root seeds) `+ 2⁻³²·4607²·2⁻¹²⁸` (equal lanes and a
  collision of two nodes not both roots, each non-root node uniform on a uniform cipher,
  `pr_treeNode_eq_le`) `≤ 4·2⁻¹²⁸` (`pr_Bp_le`); a step has `2·m` such pairs.

## The bounds

* `blindnessNH_lean` (one challenge pair, `m` further sessions):
  `≤ εPair0(q₃, q₅, q_E) + 16·m·2⁻¹²⁸`; in numbers `≤ 2⁻¹⁰³ + 16·m·2⁻¹²⁸ + 4·(q₃ + q₅ +
  221·q_E)·2⁻¹²⁸` (`blindnessNH_lean_le`), `≤ 2⁻¹⁰²` resp. `≤ 2⁻⁹¹` plus budget terms for
  `m ≤ 2²⁰` resp. `m ≤ 2³²` (`blindnessNH_lean_2pow20`, `blindnessNH_lean_2pow32`; the key-level
  `blindnessN_lean_2pow20`, `_2pow32` give `2⁻⁸³`, `2⁻⁷¹`).
* `blindnessPH_lean` (`N` pairs, the hybrid over the pairs): `≤ N·(εPair0 + 32(N − 1)·2⁻¹²⁸)`;
  in numbers `≤ N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸ + N·4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`
  (`blindnessPH_lean_le`), i.e. `n·2⁻¹⁰⁴ + n²·2⁻¹²⁵` for `n = 2N` sessions: `≤ 2⁻⁸³` at
  `2N ≤ 2²⁰` (`blindnessPH_lean_2pow20`; key-level: `2⁻⁶⁴`) and `≤ 2⁻⁶⁰` at `2N ≤ 2³²`
  (`blindnessPH_lean_2pow32`; key-level: `2⁻⁴⁰`), plus `N` times the budget terms.

The per-session cost is gone; what is quadratic is the birthday bound of the 128-bit `iv`s and
seeds (`n²·2⁻¹²⁵`), which comes from the `H₅` part of the bad event: two sessions with equal `iv`s
are counted as colliding although their `H₅` inputs also contain gate labels; bounding that would
need the labels' distribution. The budget terms are still charged once per pair (no joint bad
event over all proofs).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

/-! ## `H₄` as a table -/

/-- **The `H₄` table** on every `49`-byte input `iv_pre ‖ µ₁ ‖ 4`. -/
abbrev Tab4 := Bytes 49 → Bytes 16

/-- **The base record with `H₄` a table**: SHAKE in every other domain. The executable prover
run with this record computes its `iv` as the table's answer (`step1Iv_hb4`). -/
noncomputable def hb4 (G4 : Tab4) : Hashes := Hashes.shake.withTable .h4 (fun k : Bytes 49 => ba k) G4

lemma hb4_wf (G4 : Tab4) : HashesWF (hb4 G4) := hashesWF_shake.withTable _ _ _

lemma hb4_h4 (G4 : Tab4) {x : ByteArray} (hx : x.size = 49) : (hb4 G4).hash .h4 x = ba (G4 (blk 49 x)) := by
  have h := Hashes.withTable_enc Hashes.shake .h4 (fun k : Bytes 49 => ba k) G4 (blk 49 x)
  rw [keyOf_eq ba_injective, ba_blk_of_size hx] at h
  exact h

lemma hb4_ne (G4 : Tab4) {k : Kind} (hk : k ≠ .h4) : (hb4 G4).hash k = Hashes.shake.hash k := by
  funext x
  simp only [hb4, Hashes.withTable, hk, ite_false]

/-! ## A session's reads at points -/

/-- Function rows (the PRF view of the ideal cipher). -/
abbrev FR := Blk → Blk

/-- The tables a session's step 1 reads: `H₅` and the cipher. -/
abbrev T5 := Tab5F × Cipher

/-- The shared tables with `H₂³` table `g` and `(H₅, cipher)` tables `t`. -/
def toS (g : Tab2G pP) (t : T5) : ShP FR := (g, t.1, t.2)

/-- A fixed `H₂³` table (step 1 does not read it). -/
def g0 : Tab2G pP := fun _ => 0

/-- A fixed `(H₅, cipher)` pair. -/
def t0 : T5 := (fun _ => 0, fun _ _ => 0)

/-- **A read set**: `H₅` keys and cipher points `(key, input)`. -/
abbrev RdS := Finset (Bytes 37) × (Blk → Blk → Prop)

/-- Two `(H₅, cipher)` pairs agree on a read set. -/
def AgR (r : RdS) (a b : T5) : Prop :=
  (∀ k ∈ r.1, a.1 k = b.1 k) ∧ ∀ k z, r.2 k z → a.2 k z = b.2 k z

/-- `a` on the read set `r`, `b` elsewhere. -/
noncomputable def mixR (r : RdS) (a b : T5) : T5 := by
  classical
  exact (fun k => if k ∈ r.1 then a.1 k else b.1 k, fun k z => if r.2 k z then a.2 k z else b.2 k z)

lemma agR_mixR (r : RdS) (a b : T5) : AgR r a (mixR r a b) := by
  classical
  refine ⟨fun k hk => ?_, fun k z hk => ?_⟩
  · simp only [mixR, hk, ite_true]
  · simp only [mixR, hk, ite_true]

lemma mixR_inv (r : RdS) (a b : T5) : mixR r (mixR r a b) (mixR r b a) = a := by
  classical
  refine Prod.ext (funext fun k => ?_) (funext fun k => funext fun z => ?_)
  · simp only [mixR]; split_ifs <;> rfl
  · simp only [mixR]; split_ifs <;> rfl

/-- **Disjoint read sets**: no common `H₅` key, no common cipher point. -/
def Disj (r r' : RdS) : Prop := (∀ k ∈ r.1, k ∉ r'.1) ∧ ∀ k z, r.2 k z → ¬ r'.2 k z

/-- A reader disjoint from `Q` sees `b` in `mixR Q a b`. -/
lemma agR_mixR_of_disj {r Q : RdS} (h : Disj r Q) (a b : T5) : AgR r b (mixR Q a b) := by
  classical
  refine ⟨fun k hk => ?_, fun k z hk => ?_⟩
  · simp only [mixR, h.1 k hk, ite_false]
  · simp only [mixR, h.2 k z hk, ite_false]

lemma AgR.mono {r r' : RdS} {a b : T5} (h : AgR r a b) (h1 : ∀ k ∈ r'.1, k ∈ r.1)
    (h2 : ∀ k z, r'.2 k z → r.2 k z) : AgR r' a b :=
  ⟨fun k hk => h.1 k (h1 k hk), fun k z hk => h.2 k z (h2 k z hk)⟩

variable (Hb : Hashes)

/-- Step 1's `H₅` keys of the session with tape `x`. -/
noncomputable def k5X (x : XR) (t : T5) : Finset (Bytes 37) :=
  step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 (toS g0 t)

/-- Step 1's cipher keys (its tree's nodes). -/
noncomputable def kEX (x : XR) (t : T5) : Finset Blk :=
  step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 (toS g0 t)

/-- The session's `iv` (`H₄` at `iv_pre ‖ µ₁ ‖ 4`; it does not depend on the shared tables). -/
noncomputable def ivX (x : XR) : ByteArray :=
  step1Iv Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 (toS g0 t0)

/-- **What a session's step 1 reads**: its `624` `H₅` keys, and the cipher at its tree's nodes on
the CTR blocks of its `iv`. -/
noncomputable def rdX (x : XR) (t : T5) : RdS :=
  (k5X Hb x t, fun k z => k ∈ kEX Hb x t ∧ InY (ivX Hb x) z)

variable {Hb}

lemma step1Iv_eq_ivX (x : XR) (s : ShP FR) :
    step1Iv Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s = ivX Hb x :=
  step1Iv_tables _ _ _ _

/-- **A session's step 1 is a consistent reader of its points.** -/
theorem rdX_cons (hHb : HashesWF Hb) (x : XR) (t t' : T5) (h : AgR (rdX Hb x t) t t') :
    rdX Hb x t' = rdX Hb x t ∧ y1 Hb x (toS g0 t') = y1 Hb x (toS g0 t) := by
  obtain ⟨e5, eE, eS⟩ := step1_consP (R := FR) (Hb := Hb) (st := stOf x.1.2.1)
    (r := toBA (List.ofFn x.1.2.2)) hHb (ba x.1.1) x.2 (toS g0 t) (toS g0 t') h.1 fun k hk =>
      PtsAgree.of_inY fun z hz => h.2 k z ⟨hk, by rw [← step1Iv_eq_ivX x (toS g0 t)]; exact hz⟩
  refine ⟨?_, eS⟩
  have e5' : k5X Hb x t' = k5X Hb x t := e5
  have eE' : kEX Hb x t' = kEX Hb x t := eE
  unfold rdX
  rw [e5', eE']

/-- Step 1 does not read `H₂³`. -/
lemma y1_g (hHb : HashesWF Hb) (x : XR) (g : Tab2G pP) (t : T5) :
    y1 Hb x (toS g t) = y1 Hb x (toS g0 t) :=
  (step1_consP (R := FR) (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) hHb
    (ba x.1.1) x.2 (toS g0 t) (toS g t) (fun _ _ => rfl) fun _ _ => fun _ _ => rfl).2.2

/-- Step 2 of a session reads neither `H₅` nor the cipher. -/
lemma sessOf_tables (pk : UOVKey) (msg : Bytes) (x : XR) (y : Prover.Pending) (g : Tab2G pP)
    (t t' : T5) : sessOf Hb pk msg x y (toS g t) = sessOf Hb pk msg x y (toS g t') := by
  have hA : (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t.1).AgreeOff .h5
      (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t'.1) :=
    recHp_agreeOff_h5 (p := pP) (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) x.2 g t.1 t'.1
  simp only [sessOf, toS, proveCommit_agreeOff_h5 hA]

/-- **A session on two tables that agree on its read set is the same session.** -/
theorem sessX_congr (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (x : XR) (g : Tab2G pP)
    (t t' : T5) (h : AgR (rdX Hb x t) t t') :
    sessX Hb pk msg x (toS g t') = sessX Hb pk msg x (toS g t) := by
  rw [sessX_eq, sessX_eq, y1_g hHb x g t', y1_g hHb x g t, (rdX_cons hHb x t t' h).2,
    sessOf_tables pk msg x _ g t' t]

/-! ## The further sessions as one reader -/

section Further

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (Hb) in
/-- **The further sessions' read set**: the union of their step-1 reads. -/
noncomputable def QX (c : ι → XR) (t : T5) : RdS :=
  (univ.biUnion fun j => (rdX Hb (c j) t).1, fun k z => ∃ j, (rdX Hb (c j) t).2 k z)

variable (Hb) in
/-- The further sessions' step-1 states. -/
noncomputable def YX (c : ι → XR) (t : T5) : ι → Prover.Pending := fun j => y1 Hb (c j) (toS g0 t)

/-- **The further sessions are a consistent reader of their points.** -/
theorem QX_cons (hHb : HashesWF Hb) (c : ι → XR) (t t' : T5) (h : AgR (QX Hb c t) t t') :
    QX Hb c t' = QX Hb c t ∧ YX Hb c t' = YX Hb c t := by
  have hj : ∀ j, rdX Hb (c j) t' = rdX Hb (c j) t ∧ y1 Hb (c j) (toS g0 t') = y1 Hb (c j) (toS g0 t) :=
    fun j => rdX_cons hHb (c j) t t' (h.mono (fun k hk => mem_biUnion.2 ⟨j, mem_univ _, hk⟩)
      fun k z hk => ⟨j, hk⟩)
  refine ⟨?_, funext fun j => (hj j).2⟩
  unfold QX
  simp only [fun j => (hj j).1]

/-- A read set that meets the further sessions' meets one of them. -/
lemma exists_of_not_disj_QX {r : RdS} {c : ι → XR} {t : T5} (h : ¬ Disj r (QX Hb c t)) :
    ∃ j, ¬ Disj r (rdX Hb (c j) t) := by
  by_contra hc0
  have hc : ∀ j, Disj r (rdX Hb (c j) t) := fun j => by
    by_contra hj
    exact hc0 ⟨j, hj⟩
  refine h ⟨fun k hk hk' => ?_, fun k z hk ⟨j, hj⟩ => (hc j).2 k z hk hj⟩
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 hk'
  exact (hc j).1 k hk hj

end Further

/-! ## The reduction: the further sessions on private tables -/

section Red

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (Hb) in
/-- The further sessions' requests from their step-1 states. -/
def txY (A : AdversaryN FR ι) (c : ι → XR) (Y : ι → Prover.Pending) : ι → Bytes :=
  fun j => tOf (keyAdv (R := FR) (A.pkX j)) (A.msgX j) (c j).1.2.1 (c j).1.2.2 ((Y j).proof, (Y j).chal1)

variable (Hb) in
/-- **The Issuer of the two-session game that runs the further sessions from their step-1 states
`Y`**, its guess reading the tables through `φ`. With `Y` the further sessions' step 1 on the
game's tables and `φ = id` it is `A.red c` (`realGameRA_red_iff`); the reduction takes `Y` from
private tables and `φ` the tables patched with them (`AdversaryN.redP`). -/
noncomputable def AdversaryN.redY (A : AdversaryN FR ι) (c : ι → XR) (Y : ι → Prover.Pending)
    (φ : ShP FR → ShP FR) : AdversaryRA FR where
  pk _ _ := A.pk
  msg b _ _ := A.msg b
  respond t₀ t₁ i _ _ := A.respond t₀ t₁ (txY A c Y) i
  guess t₀ t₁ y sl s := A.guess t₀ t₁ (txY A c Y) y
    (fun j => (sessOf Hb (A.pkX j) (A.msgX j) (c j) (Y j) (φ s)).2 (A.respondX t₀ t₁ (txY A c Y) j))
    sl (fun j => (c j).2) (φ s)

/-- The tables patched at the read set `Q` with the private tables `t₁`. -/
noncomputable def patchQ (Q : RdS) (t₁ : T5) (s : ShP FR) : ShP FR := toS s.1 (mixR Q t₁ s.2)

variable (Hb) in
/-- **The reduction**: the further sessions' step 1 on the private tables `t₁`, the guess on the
game's tables patched with `t₁` at the further sessions' reads. Its interaction reads no table. -/
noncomputable def AdversaryN.redP (A : AdversaryN FR ι) (c : ι → XR) (t₁ : T5) : AdversaryRA FR :=
  A.redY Hb c (YX Hb c t₁) (patchQ (QX Hb c t₁) t₁)

lemma realSession_eq_sessX (pk : UOVKey) (msg : Bytes) (x : XR) (s : ShP FR) :
    realSession Layout.labelRows (leanProverRO Hb x.2 s) pk msg x.1 = sessX Hb pk msg x s := rfl

/-- **`A.red c` is `A.redY` of the further sessions' step-1 states on the game's tables.** -/
theorem realGameRA_red_iff (hHb : HashesWF Hb) (A : AdversaryN FR ι) (c : ι → XR) (b : Bool)
    (a : XR × XR) (s : ShP FR) :
    realGameRA Hb (A.red Hb c) b (a, s) ↔ realGameRA Hb (A.redY Hb c (YX Hb c s.2) id) b (a, s) := by
  have hs : ∀ j, sessX Hb (A.pkX j) (A.msgX j) (c j) s =
      sessOf Hb (A.pkX j) (A.msgX j) (c j) (YX Hb c s.2 j) s := fun j => by
    rw [sessX_eq]
    exact congrArg (fun y => sessOf Hb (A.pkX j) (A.msgX j) (c j) y s) (y1_g hHb (c j) s.1 s.2)
  have ht : txOf Hb A c s = txY A c (YX Hb c s.2) := funext fun j => by
    show (sessX Hb (A.pkX j) (A.msgX j) (c j) s).1 = _
    rw [hs j]
    rfl
  unfold realGameRA realGameRO viewS AdversaryRA.at AdversaryN.red AdversaryN.redY
  simp only [ht, hs, id]

/-- **The reduction's game is the resampled game, unless a challenge session reads a point the
further sessions read**: with the challenge sessions' reads on the game's tables `t₂` disjoint from
the further sessions' reads `Q` on the private tables `t₁`, the challenge sessions on the patched
tables are the ones on `t₂`. -/
theorem realGameRA_patch_iff (hHb : HashesWF Hb) (A : AdversaryN FR ι) (c : ι → XR)
    (Y : ι → Prover.Pending) (Q : RdS) (b : Bool) (a : XR × XR) (g : Tab2G pP) (t₁ t₂ : T5)
    (h0 : Disj (rdX Hb a.1 t₂) Q) (h1 : Disj (rdX Hb a.2 t₂) Q) :
    realGameRA Hb (A.redY Hb c Y id) b (a, toS g (mixR Q t₁ t₂)) ↔
      realGameRA Hb (A.redY Hb c Y (patchQ Q t₁)) b (a, toS g t₂) := by
  have e0 : ∀ msg, sessX Hb A.pk msg a.1 (toS g (mixR Q t₁ t₂)) = sessX Hb A.pk msg a.1 (toS g t₂) :=
    fun msg => sessX_congr hHb _ _ _ g t₂ _ (agR_mixR_of_disj h0 t₁ t₂)
  have e1 : ∀ msg, sessX Hb A.pk msg a.2 (toS g (mixR Q t₁ t₂)) = sessX Hb A.pk msg a.2 (toS g t₂) :=
    fun msg => sessX_congr hHb _ _ _ g t₂ _ (agR_mixR_of_disj h1 t₁ t₂)
  unfold realGameRA realGameRO viewS AdversaryRA.at AdversaryN.redY
  simp only [realSession_eq_sessX, e0, e1, id]
  rfl

end Red

/-! ## The reduction's budgets and the step bound -/

section Step

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The reduction's interaction reads no table.** -/
theorem AdversaryN.redP_iBudget (A : AdversaryN FR ι) (c : ι → XR) (u : T5) :
    (A.redP Hb c u).IBudget 0 0 0 where
  k0 _ := SReads.const (R := FR) (p := pP) (A.pk, A.msg false, A.msg true)
  k1 _ := SReads.const (R := FR) (p := pP) (A.pk, A.msg false, A.msg true)
  r0 t₀ t₁ _ := SReads.const (R := FR) (p := pP)
    (A.respond t₀ t₁ (txY A c (YX Hb c u)) false, A.respond t₀ t₁ (txY A c (YX Hb c u)) true)
  r1 t₀ t₁ _ := SReads.const (R := FR) (p := pP)
    (A.respond t₀ t₁ (txY A c (YX Hb c u)) false, A.respond t₀ t₁ (txY A c (YX Hb c u)) true)

/-- **The reduction's guess has the Issuer's budget**: the further sessions run on the private
tables, so their reads cost nothing; the patched tables agree with the game's off the further
sessions' points. -/
theorem AdversaryN.redP_gBudget (A : AdversaryN FR ι) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (c : ι → XR) (u : T5) : (A.redP Hb c u).GBudget q3 q5 qE where
  h30 t₀ t₁ y g₁ s := hA.h30 t₀ t₁ _ y _ g₁ _ _
  h31 t₀ t₁ y g₀ s := hA.h31 t₀ t₁ _ y _ g₀ _ _
  h5 t₀ t₁ y sl := by
    classical
    set Q := QX Hb c u
    set TX := txY A c (YX Hb c u)
    let ox : ShP FR → ι → Except Error (Option Bytes) := fun s j =>
      (sessOf Hb (A.pkX j) (A.msgX j) (c j) (YX Hb c u j) (patchQ Q u s)).2 (A.respondX t₀ t₁ TX j)
    choose K hK hf using fun o => hA.h5 t₀ t₁ TX y o sl (fun j => (c j).2)
    refine ⟨fun s => K (ox s) (patchQ Q u s), fun s => hK _ _, fun s G5 hs => ?_⟩
    have hox : ox (s.1, G5, s.2.2) = ox s := funext fun j => by
      simp only [ox, patchQ]
      rw [sessOf_tables (A.pkX j) (A.msgX j) (c j) (YX Hb c u j) s.1 (mixR Q u (G5, s.2.2))
        (mixR Q u s.2)]
    change A.guess t₀ t₁ TX y (ox (s.1, G5, s.2.2)) sl (fun j => (c j).2) (patchQ Q u (s.1, G5, s.2.2)) =
      A.guess t₀ t₁ TX y (ox s) sl (fun j => (c j).2) (patchQ Q u s)
    rw [hox]
    have hp : patchQ Q u (s.1, G5, s.2.2) =
        ((patchQ Q u s).1, (mixR Q u (G5, s.2.2)).1, (patchQ Q u s).2.2) := rfl
    rw [hp]
    refine hf (ox s) (patchQ Q u s) _ fun k hk => ?_
    show (if k ∈ Q.1 then u.1 k else s.2.1 k) = (if k ∈ Q.1 then u.1 k else G5 k)
    rw [hs k hk]
  hE t₀ t₁ y sl := by
    classical
    set Q := QX Hb c u
    set TX := txY A c (YX Hb c u)
    let ox : ShP FR → ι → Except Error (Option Bytes) := fun s j =>
      (sessOf Hb (A.pkX j) (A.msgX j) (c j) (YX Hb c u j) (patchQ Q u s)).2 (A.respondX t₀ t₁ TX j)
    choose K hK hf using fun o => hA.hE t₀ t₁ TX y o sl (fun j => (c j).2)
    refine ⟨fun s => K (ox s) (patchQ Q u s), fun s => hK _ _, fun s E hs => ?_⟩
    have hox : ox (s.1, s.2.1, E) = ox s := funext fun j => by
      simp only [ox, patchQ]
      rw [sessOf_tables (A.pkX j) (A.msgX j) (c j) (YX Hb c u j) s.1 (mixR Q u (s.2.1, E))
        (mixR Q u s.2)]
    change A.guess t₀ t₁ TX y (ox (s.1, s.2.1, E)) sl (fun j => (c j).2) (patchQ Q u (s.1, s.2.1, E)) =
      A.guess t₀ t₁ TX y (ox s) sl (fun j => (c j).2) (patchQ Q u s)
    rw [hox]
    have hp : patchQ Q u (s.1, s.2.1, E) =
        ((patchQ Q u s).1, (patchQ Q u s).2.1, (mixR Q u (s.2.1, E)).2) := rfl
    rw [hp]
    refine hf (ox s) (patchQ Q u s) _ fun k hk => funext fun z => ?_
    show (if Q.2 k z then u.2 k z else s.2.2 k z) = (if Q.2 k z then u.2 k z else E k z)
    rw [hs k hk]

/-- **The one-pair error with no further session's reads**: `blindnessRA`'s bound at budget
`(q₃, q₅, q_E)` and an interaction that reads nothing. -/
noncomputable def εPair0 (q3 q5 qE : ℕ) : ℝ :=
  4 * εRO q3 (q5 + 1872) (qE + 23035) + 2 * noHitProb + 2 / 2 ^ 128

lemma εPair0_nonneg (q3 q5 qE : ℕ) : 0 ≤ εPair0 q3 q5 qE := by
  have := εRO_nonneg' q3 (q5 + 1872) (qE + 23035)
  have : 0 ≤ noHitProb := pr_nonneg _
  have : (0 : ℝ) ≤ 2 / 2 ^ 128 := by norm_num
  unfold εPair0
  linarith

/-- The bad event of the step: a challenge session's step 1, on the game's tables `z.2`, reads a
point that the further sessions' step 1 reads on the private tables `z.1.2`. -/
def badQ (Hb : Hashes) (c : ι → XR) (z : (((XR × XR) × Tab2G pP) × T5) × T5) : Prop :=
  ¬ Disj (rdX Hb z.1.1.1.1 z.2) (QX Hb c z.1.2) ∨ ¬ Disj (rdX Hb z.1.1.1.2 z.2) (QX Hb c z.1.2)

/-- The game's coins split into the challenge tapes and `H₂³`, and the `(H₅, cipher)` pair. -/
def splitT : (XR × XR) × ShP FR ≃ ((XR × XR) × Tab2G pP) × T5 where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun w := (w.1.1, toS w.1.2 w.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The resampled coins regrouped: the private tables first. -/
def regroupT : (((XR × XR) × Tab2G pP) × T5) × T5 ≃ T5 × ((XR × XR) × ShP FR) where
  toFun z := (z.1.2, (z.1.1.1, toS z.1.1.2 z.2))
  invFun w := (((w.2.1, w.2.2.1), w.1), w.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **One world of the step**: the game of `A.red c` is the reduction's game, averaged over the
private tables, up to the bad event. -/
theorem red_close_redP (hHb : HashesWF Hb) (A : AdversaryN FR ι) (c : ι → XR) (b : Bool) :
    |pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) b) -
        pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) b w.2)| ≤
      pr ((((XR × XR) × Tab2G pP) × T5) × T5) (badQ Hb c) := by
  classical
  -- the game on the split coins
  have h1 : pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) b) =
      pr (((XR × XR) × Tab2G pP) × T5) (fun w =>
        realGameRA Hb (A.redY Hb c (YX Hb c w.2) id) b (w.1.1, toS w.1.2 w.2)) := by
    rw [← pr_equiv splitT.symm]
    exact pr_congr fun w => realGameRA_red_iff hHb A c b w.1.1 (toS w.1.2 w.2)
  -- lazy sampling of the further sessions' reads
  have h2 := pr_resample (C := (XR × XR) × Tab2G pP) mixR AgR agR_mixR mixR_inv (YX Hb c) (QX Hb c)
    (fun t t' h => QX_cons hHb c t t' h)
    (fun w Y t => realGameRA Hb (A.redY Hb c Y id) b (w.1, toS w.2 t))
  -- the reduction's game
  have h3 : pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) b w.2) =
      pr ((((XR × XR) × Tab2G pP) × T5) × T5) (fun z =>
        realGameRA Hb (A.redY Hb c (YX Hb c z.1.2) (patchQ (QX Hb c z.1.2) z.1.2)) b
          (z.1.1.1, toS z.1.1.2 z.2)) := by
    rw [← pr_equiv regroupT]
    rfl
  rw [h1, h2, h3]
  refine abs_pr_sub_le_of_agree _ _ _ fun z hz => ?_
  simp only [badQ, not_or, not_not] at hz
  exact realGameRA_patch_iff hHb A c _ _ b z.1.1.1 z.1.1.2 z.1.2 z.2 hz.1 hz.2

/-- **The step bound, for fixed further tapes**: the game of `A.red c` (the many-session game with
the further sessions' tapes `c`) changes by at most `εPair0` plus twice the bad event. -/
theorem red_step (hHb : HashesWF Hb) (A : AdversaryN FR ι) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (c : ι → XR) :
    |pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) false) -
        pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) true)| ≤
      εPair0 q3 q5 qE + 2 * pr ((((XR × XR) × Tab2G pP) × T5) × T5) (badQ Hb c) := by
  have h0 := red_close_redP hHb A c false
  have h1 := red_close_redP hHb A c true
  have hm : |pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) false w.2) -
      pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) true w.2)| ≤
      εPair0 q3 q5 qE := by
    refine abs_pr_prod_sub_le _ _ fun u => ?_
    have h := blindnessRA hHb (A.redP Hb c u) (A.redP_gBudget hA c u) (A.redP_iBudget c u)
    have d0 := deltaRA_le hHb (A.redP Hb c u)
    have d1 := deltaRA_le hHb (A.redP Hb c u).swap
    have e : (2 : ℝ) / 2 ^ 128 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by ring
    unfold εPair0
    simp only [Nat.mul_zero, Nat.add_zero] at h
    change _ ≤ 4 * εRO q3 (q5 + 1872) (qE + 23035) + deltaRA Hb (A.redP Hb c u) +
      deltaRA Hb (A.redP Hb c u).swap at h
    linarith
  have := abs_sub_le (pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) false))
    (pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) false w.2))
    (pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) true))
  have := abs_sub_le (pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) false w.2))
    (pr (T5 × ((XR × XR) × ShP FR)) (fun w => realGameRA Hb (A.redP Hb c w.1) true w.2))
    (pr ((XR × XR) × ShP FR) (realGameRA Hb (A.red Hb c) true))
  rw [abs_sub_comm] at h1
  linarith

end Step

/-! ## The sessions' `iv`s, seeds and keys with `H₄` a table -/

section Ident

lemma mu1_size {Hs : Hashes} (hHs : HashesWF Hs) (st : Statement) : (st.mu1 Hs).size = 32 := by
  unfold Statement.mu1 mu
  split_ifs
  · exact hHs _ _
  · exact hHs _ _

/-- The 32 bytes a session's slice answers at its `ρ`. -/
def slX (x : XR) : Bytes 32 := x.2 x.1.1

/-- A session's root seed. -/
def seedB (x : XR) : Blk := (splitSeed (slX x)).1

/-- A session's `iv_pre`. -/
def ivPreB (x : XR) : Bytes 16 := (splitSeed (slX x)).2

/-- A session's `µ₁` (SHAKE; `H₄` is not involved). -/
noncomputable def mu1X (x : XR) : ByteArray := (st1 (stOf x.1.2.1)).mu1 Hashes.shake

/-- **A session's `H₄` input** `iv_pre ‖ µ₁ ‖ 4`. -/
noncomputable def pre4 (x : XR) : Bytes 49 := blk 49 ((ba (ivPreB x) ++ mu1X x).push 4)

lemma pre4_size (x : XR) : ((ba (ivPreB x) ++ mu1X x).push 4).size = 49 := by
  simp only [ByteArray.size_push, ByteArray.size_append, size_ba, mu1X, mu1_size hashesWF_shake]

lemma x_extract (x : XR) :
    (toBA (List.ofFn x.1.2.2)).extract 0 (st1 (stOf x.1.2.1)).params.witnessBytes =
      toBA (List.ofFn x.1.2.2) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  refine Array.extract_eq_self_of_le ?_
  show (toBA (List.ofFn x.1.2.2)).size ≤ _
  rw [size_toBA, List.length_ofFn]
  show 45 ≤ 164
  decide

variable (G4 : Tab4)

lemma h3Seed_hb4 (x : XR) (g : Tab2G pP) (t5 : Tab5F) :
    h3Seed (recH (hb4 G4) (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t5)
      ((st1 (stOf x.1.2.1)).mu1 (recH (hb4 G4) (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t5))
      (toBA (List.ofFn x.1.2.2)) (ba x.1.1) = splitSeed (slX x) := by
  have e := recH_h3Seed (Hb := hb4 G4) (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) x.2 g
    t5 x.1.1
  rw [x_extract] at e
  exact e

lemma mu1_hb4 (x : XR) (g : Tab2G pP) (t5 : Tab5F) :
    (st1 (stOf x.1.2.1)).mu1 (recH (hb4 G4) (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t5) =
      mu1X x := by
  refine (recH_mu1 (Hb := hb4 G4) (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) x.2 g
    t5).trans ?_
  unfold mu1X Statement.mu1 mu
  rw [hb4_ne G4 (k := .mu) (by decide), hb4_ne G4 (k := .muDelayed) (by decide)]

lemma ivPre1_hb4 (x : XR) (g : Tab2G pP) (t5 : Tab5F) :
    ivPre1 (recH (hb4 G4) (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t5) (stOf x.1.2.1)
      (toBA (List.ofFn x.1.2.2)) (ba x.1.1) = ba (ivPreB x) := by
  have e := congrArg Prod.snd (h3Seed_hb4 G4 x g t5)
  simp only [h3Seed] at e
  unfold ivPre1 ivPreB
  rw [← e, ba_blk_of_size]
  rw [ByteArray.size_extract, recH_wf (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2))
    (hb4_wf G4) x.2 g t5]
  rfl

lemma seed1_hb4 (x : XR) (g : Tab2G pP) (t5 : Tab5F) :
    seed1 (recH (hb4 G4) (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 g t5) (stOf x.1.2.1)
      (toBA (List.ofFn x.1.2.2)) (ba x.1.1) = ba (seedB x) := by
  have e := congrArg Prod.fst (h3Seed_hb4 G4 x g t5)
  simp only [h3Seed] at e
  unfold seed1 seedB
  rw [← e, ba_blk_of_size]
  rw [ByteArray.size_extract, recH_wf (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2))
    (hb4_wf G4) x.2 g t5]
  rfl

/-- **With `H₄` a table, a session's `iv` is the table's answer at its `H₄` input.** -/
theorem step1Iv_hb4 (x : XR) (s : ShP FR) :
    step1Iv (hb4 G4) (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s = ba (G4 (pre4 x)) := by
  unfold step1Iv
  rw [recH_hash_ne (k := .h4) (by decide) (by decide) (by decide), ivPre1_hb4, mu1_hb4,
    hb4_h4 G4 (pre4_size x)]
  rfl

theorem ivX_hb4 (x : XR) : ivX (hb4 G4) x = ba (G4 (pre4 x)) := step1Iv_hb4 G4 x _

/-- A session's cipher keys are its tree's nodes, from its seed under its `iv`. -/
theorem mem_kEX_hb4 {x : XR} {t : T5} {κ : Blk} (h : κ ∈ kEX (hb4 G4) x t) :
    ∃ m < nN, κ = blk 16 (@treeNode (icPrg t.2) (ba (seedB x)) (ba (G4 (pre4 x))) m) := by
  unfold kEX step1KeysE at h
  obtain ⟨m, hm, rfl⟩ := mem_image.1 h
  refine ⟨m, mem_range.1 hm, ?_⟩
  have e := step1Iv_hb4 G4 x (toS g0 t)
  unfold step1Iv at e
  rw [seed1_hb4, e]
  rfl

/-- The gate inputs begin with the `iv`. -/
lemma gateInputsOff_get (p : Params) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64))
    (off : W128) (hiv : iv.size = 16) :
    ∀ u ∈ Prover.gateInputsOff p T iv cols off, ∀ i < 16, u.get! i = iv.get! i := by
  intro u hu i hi
  simp only [Prover.gateInputsOff, List.mem_map] at hu
  obtain ⟨e, -, rfl⟩ := hu
  have s0 : i < iv.size := by omega
  have s1 : i < (AES.pushLE32 iv e.toUInt32).size := by rw [size_pushLE32]; omega
  have s2 : i < (AES.pushLE32 iv e.toUInt32 ++ ((W128.rowMul (fun c => wbit T.g[c]! e) 120
      ((Array.range 120).map fun c => ⟨wordAt cols[c]! p.labelRowOffset,
        wordAt cols[c]! (p.labelRowOffset + 64)⟩)).xor off).toBytes).size := by
    rw [ByteArray.size_append]; omega
  simp only [get!_push, s2, get!_append, s1, get!_pushLE32, s0, ite_true]

/-- **A session's `H₅` keys begin with its `iv`.** -/
theorem k5X_iv {Hb : Hashes} (hHb : HashesWF Hb) {x : XR} {t : T5} {k : Bytes 37}
    (h : k ∈ k5X Hb x t) (i : ℕ) (hi : i < 16) : k ⟨i, by omega⟩ = (ivX Hb x).get! i := by
  unfold k5X step1Keys5 at h
  obtain ⟨u, hu, rfl⟩ := mem_image.1 h
  rw [List.mem_toFinset] at hu
  rw [get_blk]
  simp only [vgIn5, List.mem_append] at hu
  rw [← step1Iv_eq_ivX x (toS g0 t)]
  rcases hu with hu | hu
  · refine (gateInputsOff_get _ _ _ _ _ ?_ u hu i hi).trans rfl
    exact recH_wf (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) hHb x.2 _ _ .h4 _
  · refine (gateInputsOff_get _ _ _ _ _ ?_ u hu i hi).trans rfl
    exact recH_wf (st := st1 (stOf x.1.2.1)) (w := toBA (List.ofFn x.1.2.2)) hHb x.2 _ _ .h4 _

end Ident

/-! ## Small probability lemmas -/

section ProbLemmas

lemma pr_le_of_snd' {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] {P : α × β → Prop} {ε : ℝ}
    (h : ∀ b, pr α (fun a => P (a, b)) ≤ ε) : pr (α × β) P ≤ ε := by
  rw [← pr_equiv (Equiv.prodComm β α)]
  exact pr_le_of_fst fun b => h b

/-- **A conjunction of an event of the first coordinate and a conditionally rare one.** -/
lemma pr_and_le_mul {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (M : α → Prop)
    (K : α → β → Prop) {δ : ℝ} (h : ∀ a, pr β (K a) ≤ δ) :
    pr (α × β) (fun z => M z.1 ∧ K z.1 z.2) ≤ pr α M * δ := by
  classical
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hα]
  have e : pr α M * δ * Fintype.card α = ∑ a, if M a then δ else 0 := by
    rw [pr_def, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [e]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hM : M a
  · simp only [hM, true_and, ite_true]; exact h a
  · simp only [hM, false_and, ite_false]
    exact le_of_eq (by rw [pr_def]; simp)

/-- One half of a uniform slice answer takes a given value with probability `2⁻¹²⁸`. -/
lemma pr_split2_eq_le (ρ v : Bytes 16) : pr Tab3 (fun g => (splitSeed (g ρ)).2 = v) ≤ 1 / 2 ^ 128 := by
  classical
  have h := IC.pr_mem_reset_le (α := Tab3) (K := Bytes 16) (fun g => (splitSeed (g ρ)).2)
    (fun g k => Function.update g ρ (joinSeed ((splitSeed (g ρ)).1, k)))
    (fun g k => by simp only [Function.update_self, splitSeed_joinSeed])
    (fun g k k' => by simp only [Function.update_self, splitSeed_joinSeed, Function.update_idem])
    (fun g => by
      simp only [Prod.mk.eta]
      rw [show joinSeed (splitSeed (g ρ)) = g ρ from splitEquiv.left_inv _, Function.update_eq_self])
    (fun _ => {v}) (fun _ _ => rfl) (q := 1) (fun _ => (Finset.card_singleton v).le)
  refine le_trans (le_of_eq (pr_congr fun g => ?_)) (h.trans (le_of_eq ?_))
  · rw [Finset.mem_singleton]
  · rw [show Fintype.card (Bytes 16) = 2 ^ 128 from card_blk]; norm_num

lemma pr_split1_eq_le (ρ v : Bytes 16) : pr Tab3 (fun g => (splitSeed (g ρ)).1 = v) ≤ 1 / 2 ^ 128 := by
  classical
  have h := IC.pr_mem_reset_le (α := Tab3) (K := Bytes 16) (fun g => (splitSeed (g ρ)).1)
    (fun g k => Function.update g ρ (joinSeed (k, (splitSeed (g ρ)).2)))
    (fun g k => by simp only [Function.update_self, splitSeed_joinSeed])
    (fun g k k' => by simp only [Function.update_self, splitSeed_joinSeed, Function.update_idem])
    (fun g => by
      simp only [Prod.mk.eta]
      rw [show joinSeed (splitSeed (g ρ)) = g ρ from splitEquiv.left_inv _, Function.update_eq_self])
    (fun _ => {v}) (fun _ _ => rfl) (q := 1) (fun _ => (Finset.card_singleton v).le)
  refine le_trans (le_of_eq (pr_congr fun g => ?_)) (h.trans (le_of_eq ?_))
  · rw [Finset.mem_singleton]
  · rw [show Fintype.card (Bytes 16) = 2 ^ 128 from card_blk]; norm_num

/-- A uniform function's values at two different points coincide with probability `1/|β|`. -/
lemma pr_fn_eq_other_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    [DecidableEq β] {a a' : α} (h : a ≠ a') :
    pr (α → β) (fun g => g a = g a') ≤ 1 / Fintype.card β := by
  have hr := IC.pr_mem_reset_le (α := α → β) (K := β) (fun g => g a) (fun g k => Function.update g a k)
    (fun g k => Function.update_self _ _ _) (fun g k k' => Function.update_idem _ _ _)
    (fun g => Function.update_eq_self _ _) (fun g => {g a'})
    (fun g k => by rw [Function.update_of_ne h.symm]) (q := 1) (fun _ => (Finset.card_singleton _).le)
  refine le_trans (le_of_eq (pr_congr fun g => ?_)) (by exact_mod_cast hr)
  rw [Finset.mem_singleton]

/-- The second lane of a 16-byte block, as a word. -/
def lane (u : Bytes 16) : UInt32 := AES.getLE32 (ba u) 4

lemma lane_toNat (u : Bytes 16) :
    (lane u).toNat = (u 4).toNat + 2 ^ 8 * (u 5).toNat + 2 ^ 16 * (u 6).toNat + 2 ^ 24 * (u 7).toNat := by
  unfold lane AES.getLE32
  rw [toNat_le32]
  simp only [get!_ba _ (show 4 < 16 by norm_num), get!_ba _ (show 4 + 1 < 16 by norm_num),
    get!_ba _ (show 4 + 2 < 16 by norm_num), get!_ba _ (show 4 + 3 < 16 by norm_num)]
  rfl

/-- The bytes of a block other than its second lane. -/
def idx12 (i : Fin 12) : Fin 16 := if h : i.val < 4 then ⟨i.val, by omega⟩ else ⟨i.val + 4, by omega⟩

set_option linter.constructorNameAsVariable false in
/-- **At most `2⁹⁶` blocks have a given second lane.** -/
lemma card_lane_le (L : UInt32) : (univ.filter fun u : Bytes 16 => lane u = L).card ≤ 2 ^ 96 := by
  classical
  let φ : Bytes 16 → Bytes 12 := fun u i => u (idx12 i)
  have hinj : Set.InjOn φ (univ.filter fun u : Bytes 16 => lane u = L) := by
    intro u hu u' hu' he
    simp only [coe_filter, mem_univ, true_and] at hu hu'
    have hu1 : lane u = L := hu
    have hu2 : lane u' = L := hu'
    have hl := congrArg UInt32.toNat (hu1.trans hu2.symm)
    rw [lane_toNat, lane_toNat] at hl
    have hb : ∀ i : Fin 12, u (idx12 i) = u' (idx12 i) := fun i => congrFun he i
    funext j
    obtain ⟨jv, hjv⟩ := j
    by_cases hj : jv < 4
    · have := hb ⟨jv, by omega⟩
      simpa only [idx12, hj, ↓reduceDIte] using this
    by_cases hj' : jv < 8
    · have h4 := (u 4).toNat_lt; have h5 := (u 5).toNat_lt; have h6 := (u 6).toNat_lt
      have h7 := (u 7).toNat_lt; have h4' := (u' 4).toNat_lt; have h5' := (u' 5).toNat_lt
      have h6' := (u' 6).toNat_lt; have h7' := (u' 7).toNat_lt
      have e4 : (u 4).toNat = (u' 4).toNat := by omega
      have e5 : (u 5).toNat = (u' 5).toNat := by omega
      have e6 : (u 6).toNat = (u' 6).toNat := by omega
      have e7 : (u 7).toNat = (u' 7).toNat := by omega
      have : jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact UInt8.toNat_inj.1 e4
      · exact UInt8.toNat_inj.1 e5
      · exact UInt8.toNat_inj.1 e6
      · exact UInt8.toNat_inj.1 e7
    · have := hb ⟨jv - 4, by omega⟩
      have hn : ¬ (jv - 4 < 4) := by omega
      simp only [idx12, hn, ↓reduceDIte] at this
      have hj4 : (⟨jv - 4 + 4, by omega⟩ : Fin 16) = ⟨jv, hjv⟩ := Fin.ext (by simp only; omega)
      rwa [hj4] at this
  have h := Finset.card_le_card_of_injOn φ (fun u _ => mem_univ (φ u)) hinj
  rw [Finset.card_univ, Prob.card_bytes] at h
  exact h.trans (le_of_eq (by norm_num))

/-- Two independent uniform blocks share their second lane with probability `≤ 2⁻³²`. -/
lemma pr_fn_lane_le {α : Type*} [Fintype α] [DecidableEq α] {a a' : α} (h : a ≠ a') :
    pr (α → Bytes 16) (fun g => lane (g a) = lane (g a')) ≤ 1 / 2 ^ 32 := by
  classical
  have hr := IC.pr_mem_reset_le (α := α → Bytes 16) (K := Bytes 16) (fun g => g a)
    (fun g k => Function.update g a k)
    (fun g k => Function.update_self _ _ _) (fun g k k' => Function.update_idem _ _ _)
    (fun g => Function.update_eq_self _ _) (fun g => univ.filter fun u => lane u = lane (g a'))
    (fun g k => by rw [Function.update_of_ne h.symm]) (q := 2 ^ 96) (fun g => card_lane_le _)
  refine le_trans (le_of_eq (pr_congr fun g => ?_)) (hr.trans (le_of_eq ?_))
  · simp
  · rw [show Fintype.card (Bytes 16) = 2 ^ 128 from card_blk]; norm_num

end ProbLemmas

/-! ## One challenge session against one further session -/

section Core

variable (G4 : Tab4)

/-- A node of a session's tree on the cipher `E` (with `H₄` the table `G4`). -/
noncomputable def nodeB (x : XR) (E : Cipher) (n : ℕ) : Blk :=
  blk 16 (@treeNode (icPrg E) (ba (seedB x)) (ba (G4 (pre4 x))) n)

/-- **The bad event for one challenge session `x` (on the tables `t`) and one further session `x'`
(on the tables `t'`)**: their step-1 reads meet. -/
def Bp (x x' : XR) (t t' : T5) : Prop := ¬ Disj (rdX (hb4 G4) x t) (rdX (hb4 G4) x' t')

variable {G4}

lemma pre4_get (x : XR) {i : ℕ} (hi : i < 16) : (pre4 x) ⟨i, by omega⟩ = ivPreB x ⟨i, hi⟩ := by
  have s1 : i < (ba (ivPreB x)).size := by rw [size_ba]; exact hi
  have s2 : i < (ba (ivPreB x) ++ mu1X x).size := by rw [ByteArray.size_append]; omega
  simp only [pre4, get_blk, get!_push, s2, get!_append, s1, ite_true, get!_ba _ hi]

lemma ivPreB_of_pre4 {x x' : XR} (h : pre4 x = pre4 x') : ivPreB x = ivPreB x' := by
  funext i
  have := congrFun h ⟨i.val, by omega⟩
  rwa [pre4_get x i.isLt, pre4_get x' i.isLt] at this

lemma ba_eq_of_get {u v : ByteArray} (hu : u.size = 16) (hv : v.size = 16)
    (h : ∀ i < 16, u.get! i = v.get! i) : u = v :=
  blk16_inj hu hv (funext fun i => by rw [get_blk, get_blk, h i i.isLt])

lemma nodeB_zero (x : XR) (E : Cipher) : nodeB G4 x E 0 = seedB x := by
  unfold nodeB
  rw [@treeNode.eq_1 (icPrg E), blk_ba]

/-- **The cases of the bad event**: equal `iv_pre`s, an `H₄` collision, equal root seeds, or a
collision of the second lanes of the `iv`s together with a collision of two tree nodes that are
not both roots. -/
theorem Bp_cases {x x' : XR} {t t' : T5} (h : Bp G4 x x' t t') :
    ivPreB x = ivPreB x' ∨ (pre4 x ≠ pre4 x' ∧ G4 (pre4 x) = G4 (pre4 x')) ∨ seedB x = seedB x' ∨
      (pre4 x ≠ pre4 x' ∧ lane (G4 (pre4 x)) = lane (G4 (pre4 x')) ∧
        ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧ nodeB G4 x t.2 n = nodeB G4 x' t'.2 m) := by
  classical
  have hiv := ivX_hb4 G4 x
  have hiv' := ivX_hb4 G4 x'
  have hpre : pre4 x = pre4 x' ∨ pre4 x ≠ pre4 x' := em _
  unfold Bp Disj at h
  rcases not_and_or.1 h with h5 | hE
  · -- a common `H₅` key: the `iv`s are equal
    push Not at h5
    obtain ⟨k, hk, hk'⟩ := h5
    have he : ivX (hb4 G4) x = ivX (hb4 G4) x' := by
      refine ba_eq_of_get (by rw [hiv, size_ba]) (by rw [hiv', size_ba]) fun i hi => ?_
      rw [← k5X_iv (hb4_wf G4) hk i hi, ← k5X_iv (hb4_wf G4) hk' i hi]
    rw [hiv, hiv'] at he
    rcases hpre with hp | hp
    · exact Or.inl (ivPreB_of_pre4 hp)
    · exact Or.inr (Or.inl ⟨hp, ba_injective he⟩)
  · -- a common cipher point
    push Not at hE
    obtain ⟨k, z, ⟨hk, c, tw, rfl⟩, hk', c', tw', hz⟩ := hE
    have hl := lane1_of_ctrBlock_eq hz
    rw [hiv, hiv'] at hl
    rcases hpre with hp | hp
    · exact Or.inl (ivPreB_of_pre4 hp)
    obtain ⟨n, hn, rfl⟩ := mem_kEX_hb4 G4 hk
    obtain ⟨m, hm, hm'⟩ := mem_kEX_hb4 G4 hk'
    by_cases h00 : n = 0 ∧ m = 0
    · obtain ⟨rfl, rfl⟩ := h00
      refine Or.inr (Or.inr (Or.inl ?_))
      have := hm'
      rw [@treeNode.eq_1 (icPrg t.2), @treeNode.eq_1 (icPrg t'.2), blk_ba, blk_ba] at this
      exact this
    · refine Or.inr (Or.inr (Or.inr ⟨hp, hl, ⟨n, hn⟩, ⟨m, hm⟩, ?_, hm'⟩))
      by_contra hc
      push Not at hc
      exact h00 hc

end Core

/-! ## The probability of the bad event for one pair of sessions -/

section CoreProb

lemma pr_false_le {α : Type*} [Fintype α] (ε : ℝ) (hε : 0 ≤ ε) : pr α (fun _ => False) ≤ ε := by
  classical
  rw [pr_def, Finset.filter_false_of_mem fun _ _ h => h, Finset.card_empty, Nat.cast_zero, zero_div]
  exact hε

lemma pr_E1 : pr (Tab4 × ((XR × XR) × (T5 × T5))) (fun z => ivPreB z.2.1.1 = ivPreB z.2.1.2) ≤
    1 / 2 ^ 128 :=
  pr_le_of_fst fun _ => pr_le_of_snd' fun _ => pr_le_of_snd' fun x' => pr_le_of_fst fun c3 =>
    pr_split2_eq_le c3.1 (ivPreB x')

lemma pr_E3 : pr (Tab4 × ((XR × XR) × (T5 × T5))) (fun z => seedB z.2.1.1 = seedB z.2.1.2) ≤
    1 / 2 ^ 128 :=
  pr_le_of_fst fun _ => pr_le_of_snd' fun _ => pr_le_of_snd' fun x' => pr_le_of_fst fun c3 =>
    pr_split1_eq_le c3.1 (seedB x')

lemma pr_E2 : pr (Tab4 × ((XR × XR) × (T5 × T5))) (fun z =>
    pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧ z.1 (pre4 z.2.1.1) = z.1 (pre4 z.2.1.2)) ≤ 1 / 2 ^ 128 := by
  refine pr_le_of_snd' fun y => ?_
  by_cases hp : pre4 y.1.1 = pre4 y.1.2
  · exact (pr_mono fun _ h => (h.1 hp).elim).trans (pr_false_le _ (by norm_num))
  · refine (pr_mono fun G4 h => h.2).trans ((pr_fn_eq_other_le hp).trans (le_of_eq ?_))
    rw [show Fintype.card (Bytes 16) = 2 ^ 128 from card_blk]; norm_num

lemma pr_M : pr (Tab4 × (XR × XR)) (fun a =>
    pre4 a.2.1 ≠ pre4 a.2.2 ∧ lane (a.1 (pre4 a.2.1)) = lane (a.1 (pre4 a.2.2))) ≤ 1 / 2 ^ 32 := by
  refine pr_le_of_snd' fun y => ?_
  by_cases hp : pre4 y.1 = pre4 y.2
  · exact (pr_mono fun _ h => (h.1 hp).elim).trans (pr_false_le _ (by norm_num))
  · exact (pr_mono fun G4 h => h.2).trans (pr_fn_lane_le hp)

/-- Two nodes of two sessions' trees, on independent uniform ciphers, not both roots, coincide
with probability `≤ 2⁻¹²⁸`. -/
lemma pr_node_pair (G4 : Tab4) (x x' : XR) (n m : Fin nN) :
    pr (T5 × T5) (fun tt => (n.val ≠ 0 ∨ m.val ≠ 0) ∧ nodeB G4 x tt.1.2 n = nodeB G4 x' tt.2.2 m) ≤
      1 / 2 ^ 128 := by
  by_cases hm : m.val ≠ 0
  · refine pr_le_of_fst fun t => pr_le_of_fst fun _ => ?_
    have key := pr_treeNode_eq_le (ba (seedB x')) (ba (G4 (pre4 x'))) (size_ba _) hm m.isLt
      (nodeB G4 x t.2 n)
    refine (pr_mono fun E h => ?_).trans key
    exact h.2.symm
  · by_cases hn : n.val ≠ 0
    · refine pr_le_of_snd' fun t' => pr_le_of_fst fun _ => ?_
      have key := pr_treeNode_eq_le (ba (seedB x)) (ba (G4 (pre4 x))) (size_ba _) hn n.isLt
        (nodeB G4 x' t'.2 m)
      refine (pr_mono fun E h => ?_).trans key
      exact h.2
    · refine (pr_mono fun tt h => ?_).trans (pr_false_le _ (by norm_num))
      rcases h.1 with h1 | h1
      · exact hn h1
      · exact hm h1

lemma pr_K (G4 : Tab4) (x x' : XR) :
    pr (T5 × T5) (fun tt => ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
      nodeB G4 x tt.1.2 n = nodeB G4 x' tt.2.2 m) ≤ 4607 * 4607 / 2 ^ 128 := by
  have e : (fun tt : T5 × T5 => ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
      nodeB G4 x tt.1.2 n = nodeB G4 x' tt.2.2 m) = fun tt => ∃ q : Fin nN × Fin nN,
        (q.1.val ≠ 0 ∨ q.2.val ≠ 0) ∧ nodeB G4 x tt.1.2 q.1 = nodeB G4 x' tt.2.2 q.2 := by
    funext tt
    exact propext ⟨fun ⟨n, m, h⟩ => ⟨(n, m), h⟩, fun ⟨q, h⟩ => ⟨q.1, q.2, h⟩⟩
  rw [e]
  refine (pr_exists_le_sum _).trans ?_
  refine (Finset.sum_le_sum fun q _ => pr_node_pair G4 x x' q.1 q.2).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [nN_eq]
  push_cast
  ring

/-- **The bad event for one challenge session and one further session has probability
`≤ 4·2⁻¹²⁸`**, over `H₄`, both sessions' tapes (their slices) and both pairs of tables:
`2⁻¹²⁸` each for equal `iv_pre`s, an `H₄` collision and equal root seeds, and
`2⁻³²·4607²·2⁻¹²⁸ ≤ 2⁻¹²⁸` for a collision of the `iv`s' second lanes together with a node
collision. -/
theorem pr_Bp_le : pr (Tab4 × ((XR × XR) × (T5 × T5)))
    (fun z => Bp z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) ≤ 4 / 2 ^ 128 := by
  have h4 : pr (Tab4 × ((XR × XR) × (T5 × T5))) (fun z =>
      pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧ lane (z.1 (pre4 z.2.1.1)) = lane (z.1 (pre4 z.2.1.2)) ∧
        ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
          nodeB z.1 z.2.1.1 z.2.2.1.2 n = nodeB z.1 z.2.1.2 z.2.2.2.2 m) ≤ 1 / 2 ^ 128 := by
    rw [← pr_equiv (Equiv.prodAssoc Tab4 (XR × XR) (T5 × T5))]
    have h := pr_and_le_mul (α := Tab4 × (XR × XR)) (β := T5 × T5)
      (fun a => pre4 a.2.1 ≠ pre4 a.2.2 ∧ lane (a.1 (pre4 a.2.1)) = lane (a.1 (pre4 a.2.2)))
      (fun a tt => ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
        nodeB a.1 a.2.1 tt.1.2 n = nodeB a.1 a.2.2 tt.2.2 m) (δ := 4607 * 4607 / 2 ^ 128)
      fun a => pr_K a.1 a.2.1 a.2.2
    refine (le_of_eq (pr_congr fun z => ?_)).trans (h.trans ?_)
    · simp only [Equiv.prodAssoc_apply, and_assoc]
    · have hM := pr_M
      have hδ : (0 : ℝ) ≤ 4607 * 4607 / 2 ^ 128 := by norm_num
      calc pr (Tab4 × (XR × XR)) (fun a => pre4 a.2.1 ≠ pre4 a.2.2 ∧
            lane (a.1 (pre4 a.2.1)) = lane (a.1 (pre4 a.2.2))) * (4607 * 4607 / 2 ^ 128)
          ≤ 1 / 2 ^ 32 * (4607 * 4607 / 2 ^ 128) := mul_le_mul_of_nonneg_right hM hδ
        _ ≤ 1 / 2 ^ 128 := by norm_num
  have hc := pr_mono (α := Tab4 × ((XR × XR) × (T5 × T5))) (fun z (h : Bp z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) =>
    Bp_cases h)
  have o1 := pr_or_le (α := Tab4 × ((XR × XR) × (T5 × T5))) (fun z => ivPreB z.2.1.1 = ivPreB z.2.1.2)
    (fun z => (pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧ z.1 (pre4 z.2.1.1) = z.1 (pre4 z.2.1.2)) ∨
      seedB z.2.1.1 = seedB z.2.1.2 ∨ (pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧
        lane (z.1 (pre4 z.2.1.1)) = lane (z.1 (pre4 z.2.1.2)) ∧ ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
          nodeB z.1 z.2.1.1 z.2.2.1.2 n = nodeB z.1 z.2.1.2 z.2.2.2.2 m))
  have o2 := pr_or_le (α := Tab4 × ((XR × XR) × (T5 × T5)))
    (fun z => pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧ z.1 (pre4 z.2.1.1) = z.1 (pre4 z.2.1.2))
    (fun z => seedB z.2.1.1 = seedB z.2.1.2 ∨ (pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧
        lane (z.1 (pre4 z.2.1.1)) = lane (z.1 (pre4 z.2.1.2)) ∧ ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
          nodeB z.1 z.2.1.1 z.2.2.1.2 n = nodeB z.1 z.2.1.2 z.2.2.2.2 m))
  have o3 := pr_or_le (α := Tab4 × ((XR × XR) × (T5 × T5))) (fun z => seedB z.2.1.1 = seedB z.2.1.2)
    (fun z => pre4 z.2.1.1 ≠ pre4 z.2.1.2 ∧
        lane (z.1 (pre4 z.2.1.1)) = lane (z.1 (pre4 z.2.1.2)) ∧ ∃ n m : Fin nN, (n.val ≠ 0 ∨ m.val ≠ 0) ∧
          nodeB z.1 z.2.1.1 z.2.2.1.2 n = nodeB z.1 z.2.1.2 z.2.2.2.2 m)
  have := pr_E1; have := pr_E2; have := pr_E3
  have e : (4 : ℝ) / 2 ^ 128 = 1 / 2 ^ 128 + 1 / 2 ^ 128 + 1 / 2 ^ 128 + 1 / 2 ^ 128 := by ring
  linarith

end CoreProb

/-! ## The bad event over the whole game -/

section BadAll

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The marginal of a coordinate projection. -/
lemma pr_comp_eq {Ω Ω' W : Type*} [Fintype Ω] [Fintype Ω'] [Fintype W] [Nonempty W] (e : Ω ≃ Ω' × W)
    (f : Ω → Ω') (hf : ∀ z, (e z).1 = f z) (P : Ω' → Prop) :
    pr Ω (fun z => P (f z)) = pr Ω' P := by
  rw [← pr_prod_fst (β := W) P, ← pr_equiv e]
  exact pr_congr fun z => by rw [hf]

/-- The coins of the step's bad event regrouped around one challenge session (the first) and one
further session `j`. -/
def regroupB (j : ι) :
    (Tab4 × (XR × ({j' // j' ≠ j} → XR))) × ((((XR × XR) × Tab2G pP) × T5) × T5) ≃
      (Tab4 × ((XR × XR) × (T5 × T5))) × (({j' // j' ≠ j} → XR) × (XR × Tab2G pP)) where
  toFun z := ((z.1.1, ((z.2.1.1.1.1, z.1.2.1), (z.2.2, z.2.1.2))), (z.1.2.2, (z.2.1.1.1.2, z.2.1.1.2)))
  invFun w := ((w.1.1, (w.1.2.1.2, w.2.1)), ((((w.1.2.1.1, w.2.2.1), w.2.2.2), w.1.2.2.2), w.1.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The challenge session `i` first. -/
def selB : Bool → XR × XR ≃ XR × XR
  | false => Equiv.refl _
  | true => Equiv.prodComm _ _

/-- The coordinates of one pair of sessions. -/
noncomputable def margB (i : Bool) (j : ι) :
    (Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5) ≃
      (Tab4 × ((XR × XR) × (T5 × T5))) × (({j' // j' ≠ j} → XR) × (XR × Tab2G pP)) :=
  ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Tab4) (Equiv.funSplitAt j XR))
    (Equiv.prodCongr (Equiv.prodCongr (Equiv.prodCongr (selB i) (Equiv.refl _)) (Equiv.refl _))
      (Equiv.refl _)))).trans (regroupB j)

lemma margB_fst (i : Bool) (j : ι) (z : (Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5)) :
    (margB i j z).1 = (z.1.1, (((bif i then z.2.1.1.1.2 else z.2.1.1.1.1), z.1.2 j), (z.2.2, z.2.1.2))) := by
  cases i <;> simp [margB, regroupB, selB, Equiv.funSplitAt, Equiv.piSplitAt]

/-- **The step's bad event over all its coins**: `≤ 2·|ι|·4·2⁻¹²⁸` (two challenge sessions, `|ι|`
further sessions, `pr_Bp_le` for each pair). -/
theorem pr_badQ_le :
    pr ((Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5))
      (fun z => badQ (hb4 z.1.1) z.1.2 z.2) ≤ 2 * Fintype.card ι * (4 / 2 ^ 128) := by
  classical
  have himp : ∀ z : (Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5),
      badQ (hb4 z.1.1) z.1.2 z.2 → ∃ q : Bool × ι,
        Bp z.1.1 (bif q.1 then z.2.1.1.1.2 else z.2.1.1.1.1) (z.1.2 q.2) z.2.2 z.2.1.2 := by
    intro z h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := exists_of_not_disj_QX h
      exact ⟨(false, j), hj⟩
    · obtain ⟨j, hj⟩ := exists_of_not_disj_QX h
      exact ⟨(true, j), hj⟩
  refine (pr_mono himp).trans ((pr_exists_le_sum _).trans ?_)
  have hq : ∀ q : Bool × ι, pr ((Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5)) (fun z =>
      Bp z.1.1 (bif q.1 then z.2.1.1.1.2 else z.2.1.1.1.1) (z.1.2 q.2) z.2.2 z.2.1.2) ≤ 4 / 2 ^ 128 := by
    intro q
    have e := pr_comp_eq (margB q.1 q.2)
      (fun z => (z.1.1, (((bif q.1 then z.2.1.1.1.2 else z.2.1.1.1.1), z.1.2 q.2), (z.2.2, z.2.1.2))))
      (margB_fst q.1 q.2) (fun w => Bp w.1 w.2.1.1 w.2.1.2 w.2.2.1 w.2.2.2)
    rw [show (fun z : (Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5) =>
        Bp z.1.1 (bif q.1 then z.2.1.1.1.2 else z.2.1.1.1.1) (z.1.2 q.2) z.2.2 z.2.1.2) =
        fun z => (fun w : Tab4 × ((XR × XR) × (T5 × T5)) => Bp w.1 w.2.1.1 w.2.1.2 w.2.2.1 w.2.2.2)
          (z.1.1, (((bif q.1 then z.2.1.1.1.2 else z.2.1.1.1.1), z.1.2 q.2), (z.2.2, z.2.1.2))) from rfl, e]
    exact pr_Bp_le
  refine (Finset.sum_le_sum fun q _ => hq q).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

end BadAll

/-! ## Many sessions and `N` pairs with `H₄` a table -/

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The many-session game with `H₄` a table** (`realGameN` with the base record `hb4 G4`, the
table drawn uniformly). -/
noncomputable def realGameNH (A : Tab4 → AdversaryN FR ι) (b : Bool)
    (z : Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) : Prop :=
  realGameN (hb4 z.1) (A z.1) b z.2

/-- The coins of `realGameNH` with `H₄` and the further sessions' tapes first. -/
def tapeNH : (Tab4 × (ι → XR)) × ((XR × XR) × ShP FR) ≃ Tab4 × (((XR × XR) × (ι → XR)) × ShP FR) where
  toFun z := (z.1.1, ((z.2.1, z.1.2), z.2.2))
  invFun z := ((z.1, z.2.1.2), (z.2.1.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma abs_pr_prod_sub_le_avg' {α β β' : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype β']
    (P : α × β → Prop) (Q : α × β' → Prop) (f : α → ℝ)
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ f a) :
    |pr (α × β) P - pr (α × β') Q| ≤ (∑ a, f a) / Fintype.card α := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => h a)

/-- **PomFRIT blindness with many sessions and `H₄` a table, with no per-session cipher charge**:
with `m = |ι|` further honest sessions,

    |Pr[W₀] − Pr[W₁]| ≤ εPair0(q₃, q₅, q_E) + 16·m·2⁻¹²⁸,

`εPair0 = 4·εRO(q₃, q₅ + 1872, q_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸` the two-session bound with an
interaction that reads nothing. The further sessions' step 1 is moved to private tables by lazy
sampling (`red_close_redP`), at the cost of the event that a challenge session reads one of their
points (`pr_badQ_le`). -/
theorem blindnessNH_lean (A : Tab4 → AdversaryN FR ι) {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE) :
    |pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A false) -
        pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A true)| ≤
      εPair0 q3 q5 qE + 16 * Fintype.card ι / 2 ^ 128 := by
  rw [← pr_equiv tapeNH, ← pr_equiv tapeNH]
  have h := abs_pr_prod_sub_le_avg' (α := Tab4 × (ι → XR)) (β := (XR × XR) × ShP FR)
    (β' := (XR × XR) × ShP FR) (fun z => realGameNH A false (tapeNH z))
    (fun z => realGameNH A true (tapeNH z))
    (fun a => εPair0 q3 q5 qE + 2 * pr ((((XR × XR) × Tab2G pP) × T5) × T5) (badQ (hb4 a.1) a.2))
    fun a => red_step (hb4_wf a.1) (A a.1) (hA a.1) a.2
  refine h.trans ?_
  set g : Tab4 × (ι → XR) → ℝ := fun a => pr ((((XR × XR) × Tab2G pP) × T5) × T5) (badQ (hb4 a.1) a.2)
  have hc : (0 : ℝ) < Fintype.card (Tab4 × (ι → XR)) := by exact_mod_cast Fintype.card_pos
  have e1 : (∑ a, (εPair0 q3 q5 qE + 2 * g a)) / Fintype.card (Tab4 × (ι → XR)) =
      εPair0 q3 q5 qE + 2 * ((∑ a, g a) / Fintype.card (Tab4 × (ι → XR))) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
      add_div, mul_div_cancel_left₀ _ hc.ne', mul_div_assoc]
  have e2 : (∑ a, g a) / Fintype.card (Tab4 × (ι → XR)) =
      pr ((Tab4 × (ι → XR)) × ((((XR × XR) × Tab2G pP) × T5) × T5))
        (fun z => badQ (hb4 z.1.1) z.1.2 z.2) :=
    (pr_prod (α := Tab4 × (ι → XR)) (β := (((XR × XR) × Tab2G pP) × T5) × T5)
      (fun z => badQ (hb4 z.1.1) z.1.2 z.2)).symm
  rw [e1, e2]
  have hb := pr_badQ_le (ι := ι)
  have e3 : 2 * (2 * (Fintype.card ι : ℝ) * (4 / 2 ^ 128)) = 16 * Fintype.card ι / 2 ^ 128 := by ring
  linarith

end Main

/-! ## `N` challenge pairs, and the numbers -/

section Pairs

variable {N : ℕ}

/-- **The game with `N` challenge pairs and `H₄` a table** (`realGameP` with the base record
`hb4 G4`, the table drawn uniformly). -/
noncomputable def realGamePH (A : Tab4 → AdversaryP FR N) (w : Fin N → Bool)
    (z : Tab4 × ((Fin N → XR × XR) × ShP FR)) : Prop :=
  realGameP (hb4 z.1) (A z.1) w z.2

/-- **PomFRIT blindness with `N` challenge pairs and `H₄` a table**: any two worlds differ by at
most `N·(εPair0 + 16·2(N − 1)·2⁻¹²⁸)` (the hybrid over the pairs; each step is
`blindnessNH_lean` with the other pairs' `2(N − 1)` sessions as further sessions). -/
theorem blindnessPH_lean (A : Tab4 → AdversaryP FR N) {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE)
    (w w' : Fin N → Bool) :
    |pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w) -
        pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w')| ≤
      N * (εPair0 q3 q5 qE + 16 * ((N - 1) * 2 : ℕ) / 2 ^ 128) := by
  let mix : ℕ → Fin N → Bool := fun k j => if j.val < k then w' j else w j
  let P : ℕ → ℝ := fun k => pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A (mix k))
  have h0 : mix 0 = w := funext fun j => by simp [mix]
  have hN : mix N = w' := funext fun j => by simp [mix, j.isLt]
  have hε : 0 ≤ εPair0 q3 q5 qE + 16 * ((N - 1) * 2 : ℕ) / 2 ^ 128 := by
    have := εPair0_nonneg q3 q5 qE
    have : (0 : ℝ) ≤ 16 * ((N - 1) * 2 : ℕ) / 2 ^ 128 := by positivity
    linarith
  have key := abs_sub_le_mul_of_steps P (εPair0 q3 q5 qE + 16 * ((N - 1) * 2 : ℕ) / 2 ^ 128) N
    fun k hk => by
    let kk : Fin N := ⟨k, hk⟩
    have e : ∀ v : Fin N → Bool, pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A v) =
        pr (Tab4 × (((XR × XR) × (Oth kk → XR)) × ShP FR))
          (realGameNH (fun G4 => (A G4).hop kk fun j => v j.1) (v kk)) := fun v => by
      rw [← pr_equiv ((Equiv.refl Tab4).prodCongr ((splitP kk).prodCongr (Equiv.refl (ShP FR))))]
      exact pr_congr fun z => realGameP_iff (hb4 z.1) (A z.1) v kk z.2
    have hv : (fun j : {j : Fin N // j ≠ kk} => mix k j.1) = fun j => mix (k + 1) j.1 := by
      funext ⟨j, hj⟩
      have : j.val ≠ k := fun h => hj (Fin.ext h)
      simp only [mix]
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    have m0 : mix k kk = w kk := by simp [mix, kk]
    have m1 : mix (k + 1) kk = w' kk := by simp [mix, kk]
    show |pr _ (realGamePH A (mix k)) - pr _ (realGamePH A (mix (k + 1)))| ≤ _
    rw [e, e, ← hv, m0, m1]
    have hb := blindnessNH_lean (fun G4 => (A G4).hop kk fun j => mix k j.1)
      (fun G4 => AdversaryP.hop_budget (hA G4) kk _)
    rw [card_oth] at hb
    rcases hw : w kk <;> rcases hw' : w' kk
    · simpa using hε
    · exact hb
    · rw [abs_sub_comm]; exact hb
    · simpa using hε
  simpa only [P, h0, hN] using key

/-- **`εPair0` in numbers**: `≤ 2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`. -/
lemma εPair0_le (q3 q5 qE : ℕ) :
    εPair0 q3 q5 qE ≤ 1 / 2 ^ 103 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have hn := noHitProb_le_128
  unfold εPair0 εRO
  push_cast
  linarith

/-- **The many-session bound in numbers** (one challenge pair, `m = |ι|` further sessions):
`≤ 2⁻¹⁰³ + 16·m·2⁻¹²⁸ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`. -/
theorem blindnessNH_lean_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Tab4 → AdversaryN FR ι)
    {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE) :
    |pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A false) -
        pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A true)| ≤
      1 / 2 ^ 103 + 16 * Fintype.card ι / 2 ^ 128 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessNH_lean A hA
  have := εPair0_le q3 q5 qE
  linarith

/-- **`2³²` sessions, one challenge pair** (`m ≤ 2³²` further sessions): `≤ 2⁻⁹¹` plus the guess's
budget terms (the key-level bound `blindnessN_lean_2pow32` gives `2⁻⁷¹`). -/
theorem blindnessNH_lean_2pow32 {ι : Type} [Fintype ι] [DecidableEq ι] (A : Tab4 → AdversaryN FR ι)
    {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE) (hm : Fintype.card ι ≤ 2 ^ 32) :
    |pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A false) -
        pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A true)| ≤
      1 / 2 ^ 91 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessNH_lean_le A hA
  have hm' : (Fintype.card ι : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hm
  have : (1 : ℝ) / 2 ^ 103 + 16 * Fintype.card ι / 2 ^ 128 ≤ 1 / 2 ^ 91 := by linarith
  linarith

/-- **`2²⁰` sessions, one challenge pair** (`m ≤ 2²⁰` further sessions): `≤ 2⁻¹⁰²` plus the
guess's budget terms (the key-level `blindnessN_lean_2pow20` gives `2⁻⁸³`). -/
theorem blindnessNH_lean_2pow20 {ι : Type} [Fintype ι] [DecidableEq ι] (A : Tab4 → AdversaryN FR ι)
    {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE) (hm : Fintype.card ι ≤ 2 ^ 20) :
    |pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A false) -
        pr (Tab4 × (((XR × XR) × (ι → XR)) × ShP FR)) (realGameNH A true)| ≤
      1 / 2 ^ 102 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessNH_lean_le A hA
  have hm' : (Fintype.card ι : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hm
  have : (1 : ℝ) / 2 ^ 103 + 16 * Fintype.card ι / 2 ^ 128 ≤ 1 / 2 ^ 102 := by linarith
  linarith

/-- **`N` pairs in numbers**: `≤ N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸ + N·4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`, i.e.
`n·2⁻¹⁰⁴ + n²·2⁻¹²⁵` for `n = 2N` sessions plus `N` times the budget terms. -/
theorem blindnessPH_lean_le (A : Tab4 → AdversaryP FR N) {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE)
    (w w' : Fin N → Bool) :
    |pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w) -
        pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w')| ≤
      N / 2 ^ 103 + 32 * (N : ℝ) ^ 2 / 2 ^ 128 + N * (4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  have h := blindnessPH_lean A hA w w'
  have he := εPair0_le q3 q5 qE
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hm : (((N - 1) * 2 : ℕ) : ℝ) ≤ 2 * N := by
    have : (N - 1) * 2 ≤ 2 * N := by omega
    exact_mod_cast this
  have h1 : (N : ℝ) * (εPair0 q3 q5 qE + 16 * ((N - 1) * 2 : ℕ) / 2 ^ 128) ≤
      N * (1 / 2 ^ 103 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 16 * (2 * N) / 2 ^ 128) := by
    refine mul_le_mul_of_nonneg_left ?_ hN0
    have : 16 * (((N - 1) * 2 : ℕ) : ℝ) / 2 ^ 128 ≤ 16 * (2 * N) / 2 ^ 128 := by gcongr
    linarith
  refine h.trans (h1.trans (le_of_eq ?_))
  ring

/-- **`2²⁰` sessions in `N` pairs**: `≤ 2⁻⁸³` plus `N` times the guess's budget terms (the
key-level bound `blindnessP_lean_2pow20` gives `2⁻⁶⁴`). -/
theorem blindnessPH_lean_2pow20 (A : Tab4 → AdversaryP FR N) {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE)
    (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 20) :
    |pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w) -
        pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w')| ≤
      1 / 2 ^ 83 + N * (4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  have h := blindnessPH_lean_le A hA w w'
  have h1 : (N : ℝ) ≤ 2 ^ 19 := by
    have : N ≤ 2 ^ 19 := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsq : (N : ℝ) ^ 2 ≤ 2 ^ 38 := by
    have := mul_le_mul h1 h1 h0 (by positivity)
    nlinarith
  have h2 : (N : ℝ) / 2 ^ 103 + 32 * (N : ℝ) ^ 2 / 2 ^ 128 ≤ 1 / 2 ^ 83 := by linarith
  linarith

/-- **`2³²` sessions in `N` pairs**: `≤ 2⁻⁶⁰` plus `N` times the guess's budget terms (the
key-level bound `blindnessP_lean_2pow32` gives `2⁻⁴⁰`). The remaining quadratic part,
`32·N²·2⁻¹²⁸`, is the birthday bound of the sessions' 128-bit `iv`s and root seeds. -/
theorem blindnessPH_lean_2pow32 (A : Tab4 → AdversaryP FR N) {q3 q5 qE : ℕ} (hA : ∀ G4, (A G4).Budget q3 q5 qE)
    (w w' : Fin N → Bool) (hN : 2 * N ≤ 2 ^ 32) :
    |pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w) -
        pr (Tab4 × ((Fin N → XR × XR) × ShP FR)) (realGamePH A w')| ≤
      1 / 2 ^ 60 + N * (4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128) := by
  have h := blindnessPH_lean_le A hA w w'
  have h1 : (N : ℝ) ≤ 2 ^ 31 := by
    have : N ≤ 2 ^ 31 := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsq : (N : ℝ) ^ 2 ≤ 2 ^ 62 := by
    have := mul_le_mul h1 h1 h0 (by positivity)
    nlinarith
  have h2 : (N : ℝ) / 2 ^ 103 + 32 * (N : ℝ) ^ 2 / 2 ^ 128 ≤ 1 / 2 ^ 60 := by linarith
  linarith

end Pairs

end VoleMole.Privacy.PomFRIT
