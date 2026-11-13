import VoleMole.Privacy.PomFRITMany
import VoleMole.Privacy.PomFRITRAH

/-!
# PomFRIT blindness with adaptively scheduled sessions

`Privacy/PomFRITMany.lean` has any number of further honest sessions in one concurrent schedule:
their requests come before the Issuer's first answer, their outcomes are seen only by the guess.
Here the Issuer **starts further sessions after seeing earlier sessions' outcomes**: before the
challenge, between the challenge requests and the challenge responses, and after the challenge
outcome, each further session's key and message, and the Issuer's response to it, are chosen from
everything seen so far (all earlier requests and outcomes).

## A whole session is a consistent table reader

A further session run to the end (`fullX`: the request, then the Client's checks and step 2 on the
Issuer's response `ρ(request)`) reads `H₅` at its `624` gate inputs and the cipher at its tree's
`4607` nodes (step 1, `step1_cons`), and `H₂³` at the `nGrind = 2³²` grinding points of its
two-phase prefix if the response passes the Client's checks, and not at all otherwise
(`realRun2_h23_congr`, through `sigOf_oR` for the Issuer `respAdv` that answers `ρ`); the prefix
is read off step 1's keys (`pre2_cons`). So `fullX` is `SReads` with `(0, nGrind, 624, 4607)`
(`fullX_sreads`): **PomFRIT's step 2 is a consistent reader**. Sessions run one after the other,
each chosen from the earlier ones (`runSeq`), compose (`runSeq_sreads`), and a reader of the shared
tables is a joint reader of both challenge slices (`SReadsP.of_shared`).

## The game and the reduction

`AdversaryAd`, `realGameAd`: `m₁` further sessions before the challenge, then the challenge key and
messages from them, the two challenge requests, `m₂` further sessions, the challenge responses, the
challenge outcome (the signatures in message order if both complete), `m₃` further sessions, the
guess. For each tape `c` of the further sessions the game is the two-session game with an Issuer
whose interaction reads every table, `H₂³` included (`Privacy/PomFRITRAH.lean`), for the Issuer
`A.red c` that runs the further sessions in its key stage, its response stage and its guess
(`realGameAd_iff`, `Iff.rfl`): interaction budget `IBudgetH 0 ((m₁+m₂)·2³²) ((m₁+m₂)·624)
((m₁+m₂)·4607)` (`red_iBudgetH`), guess budget `(q₃, q₅ + (m₁+m₂+m₃)·624, q_E + (m₁+m₂+m₃)·4607)`
(`red_gBudget`).

## The bound

`blindnessRAH_lean_numG` for every `c`, averaged over `c`: `blindnessAd_lean_numG` (every row type),
`blindnessAd_lean_num` (function rows), `blindnessAd_lean_num_perm`; in numbers
(`blindnessAd_lean_le`) `≤ n·2⁻⁹² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` for `n = m₁ + m₂ + m₃ + 2` sessions
in all: `≤ 2⁻⁷²` for `n ≤ 2²⁰` (`blindnessAd_lean_2pow20`), `≤ 2⁻⁶⁰` for `n ≤ 2³²`
(`blindnessAd_lean_2pow32`). The per-session term (`≈ 2⁻⁹³`) is the `RAH` collision term's charge
per `H₂³` key the interaction reads, `2³²` per session run inside it. Counting the reads' prefixes
instead of their keys (one per session) gives `n·2⁻¹⁰²`: `Privacy/PomFRITAdaptivePfx.lean`
(`blindnessAd_lean_le_pfx`; `lean/docs/zk.md` §10.8).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## A whole further session -/

section Full

variable (Hb : Hashes)

/-- **The Issuer of one further session**, answering `ρ` to its request. -/
def respAdv (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) : AdversaryRO R :=
  ⟨pk, fun _ => msg, fun t₀ _ _ => ρ t₀, fun _ _ _ _ _ => True⟩

/-- **A further session run to the end**: its request, and its outcome on the Issuer's response
`ρ` to that request. -/
noncomputable def fullX (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) (s : ShP R) :
    Bytes × Except Error (Option Bytes) :=
  ((sessX Hb pk msg x s).1, (sessX Hb pk msg x s).2 (ρ (sessX Hb pk msg x s).1))

variable {Hb}

@[simp] lemma respAdv_respond (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (t₀ t₁ : Bytes) (i : Bool) :
    (respAdv (R := R) pk msg ρ).respond t₀ t₁ i = ρ t₀ := rfl

lemma sessX_eq_tR (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) (s : ShP R) :
    sessX Hb pk msg x s = (tR Hb (respAdv pk msg ρ) msg x s, fun resp =>
      finish pk (tR Hb (respAdv pk msg ρ) msg x s) (sigR Hb (respAdv pk msg ρ) msg x s resp) resp) :=
  realSession_eq Hb (respAdv pk msg ρ) msg x s

/-- `finish` does not read the signature when the response fails the Client's checks. -/
lemma finish_of_not_valid (A : AdversaryRO R) (t sig sig' resp : Bytes) (h : validB A resp t = false) :
    finish A.pk t sig resp = finish A.pk t sig' resp := by
  have h' : ¬ (resp.length = uovN ∧ A.pk.eval resp = t) := fun hc =>
    absurd ((validB_iff A resp t).2 hc) (by rw [h]; exact Bool.false_ne_true)
  unfold finish
  by_cases hl : resp.length = uovN
  · have he : A.pk.eval resp ≠ t := fun he => h' ⟨hl, he⟩
    simp [hl, he]
  · simp [hl]

/-- The grinding prefix of a session's two-phase run, at the tables `s`. -/
noncomputable def preX (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) (s : ShP R) : ByteArray :=
  @pre2 (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
    (kOf (respAdv (R := R) pk msg ρ) msg x.1.2.1 x.1.2.2 false (tR Hb (respAdv pk msg ρ) msg x s))
    (splitSeed (x.2 x.1.1))

/-- **The keys a whole session reads**: step 1's `H₅` and cipher keys, and the grinding points of
its prefix if the response passes the Client's checks. -/
noncomputable def fullKeys (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) (s : ShP R) : RS pP :=
  (∅, if validB (respAdv (R := R) pk msg ρ) (ρ (tR Hb (respAdv pk msg ρ) msg x s))
      (tR Hb (respAdv pk msg ρ) msg x s) then univ.image (key2 pP (preX (Hb := Hb) pk msg ρ x s)) else ∅,
    step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s,
    step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s)

/-- Step 1 on the record of the tables is `pendAt` on the `H₅` record at the slice's seed. -/
lemma pendAt_step1 [HasPrg] (hHb : HashesWF Hb) {st : Statement} {r : ByteArray}
    (hr : r.extract 0 (st1 st).params.witnessBytes = r) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F) (ρ : Bytes 16) :
    pendAt (rec5 Hb G5) CrtGen.tables (st1 st) r (splitSeed (G3 ρ)) =
      step1 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r (ba ρ) := by
  rw [step1_eq_pendAt (recH_wf (st := st1 st) (w := r) hHb G3 G2 G5)]
  have e := recH_h3Seed (Hb := Hb) (st := st1 st) (w := r) G3 G2 G5 ρ
  rw [hr] at e
  rw [e]
  exact (recH_eq_rec5 (fun H => pendAt H CrtGen.tables (st1 st) r (splitSeed (G3 ρ)))
    (fun _ _ _ hu h => pendAt_agreeOff hu h CrtGen.tables (st1 st) r (splitSeed (G3 ρ))) Hb (st1 st) r
    G3 G2 G5).symm

/-- **Step 1 is read off its keys**: a table agreeing on step 1's `H₅` and cipher keys has the
same keys, step-1 state and request. -/
lemma full_step1 (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR)
    (s s' : ShP R)
    (h5 : ∀ k ∈ step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s, s.2.2 k = s'.2.2 k) :
    step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s' =
        step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s ∧
      step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s' =
        step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s ∧
      @step1 (icPrg (rowFn s'.2.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s'.1 s'.2.1)
          CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) =
        @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
          CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) ∧
      tR Hb (respAdv pk msg ρ) msg x s' = tR Hb (respAdv pk msg ρ) msg x s := by
  obtain ⟨e5, eE, eS⟩ := step1_cons (R := R) (Hb := Hb) (st := stOf x.1.2.1)
    (r := toBA (List.ofFn x.1.2.2)) hHb (ba x.1.1) x.2 s s' h5 hE
  refine ⟨e5, eE, eS, ?_⟩
  unfold tR s1R
  rw [eS]

/-- **The prefix is read off step 1's keys.** -/
lemma preX_cons (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR)
    (s s' : ShP R)
    (h5 : ∀ k ∈ step1Keys5 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ step1KeysE Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) x.2 s, s.2.2 k = s'.2.2 k) :
    preX (Hb := Hb) pk msg ρ x s' = preX (Hb := Hb) pk msg ρ x s := by
  obtain ⟨-, -, eS, eT⟩ := full_step1 hHb pk msg ρ x s s' h5 hE
  have hr := (hyp2_kOf (R := R) (respAdv pk msg ρ) msg x.1.2.1 x.1.2.2 false
    (tR Hb (respAdv pk msg ρ) msg x s)).extract
  have hP : @pendAt (icPrg (rowFn s'.2.2)) (rec5 Hb s'.2.1) CrtGen.tables (st1 (stOf x.1.2.1))
      (toBA (List.ofFn x.1.2.2)) (splitSeed (x.2 x.1.1)) =
      @pendAt (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables (st1 (stOf x.1.2.1))
      (toBA (List.ofFn x.1.2.2)) (splitSeed (x.2 x.1.1)) := by
    rw [@pendAt_step1 Hb (icPrg (rowFn s'.2.2)) hHb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) hr x.2 s'.1
      s'.2.1 x.1.1, @pendAt_step1 Hb (icPrg (rowFn s.2.2)) hHb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
      hr x.2 s.1 s.2.1 x.1.1]
    exact eS
  unfold preX pre2
  simp only [eT, hP]
  exact realPre_h5 (rec5_agreeOff s'.2.1 s.2.1) _


/-- **The signature is read off step 1 and `H₂³`**: with step 1 unchanged, changing `H₅` and the
cipher does not change it. -/
lemma sigR_tables (hHb : HashesWF Hb) (A : AdversaryRO R) (msg : Bytes) (x : XR) (s s' : ShP R)
    (eS : @step1 (icPrg (rowFn s'.2.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s'.1 s'.2.1)
          CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1) =
        @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s.1 s.2.1)
          CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (ba x.1.1))
    (resp : Bytes) :
    sigR Hb A msg x s' resp = sigR Hb A msg x (s'.1, s.2) resp := by
  have eS2 := (step1_cons (R := R) (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) hHb
    (ba x.1.1) x.2 s (s'.1, s.2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2
  have hA : (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s'.1 s'.2.1).AgreeOff .h5
      (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 s'.1 s.2.1) :=
    recHp_agreeOff_h5 (p := pP) (Hb := Hb) (st := st1 (stOf x.1.2.1))
      (w := toBA (List.ofFn x.1.2.2)) x.2 s'.1 s'.2.1 s.2.1
  unfold sigR s1R
  dsimp only at eS2 ⊢
  rw [eS, eS2, proveCommit_agreeOff_h5 hA]

/-- **The signature reads `H₂³` only at the grinding points of the prefix**, when the response
passes the Client's checks. -/
lemma sigR_h23 (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR)
    (G2 G2' : Tab2G pP) (s₂ : Tab5F × (Blk → R))
    (hv : validB (respAdv (R := R) pk msg ρ) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂)))
      (tR Hb (respAdv pk msg ρ) msg x (G2, s₂)) = true)
    (h2 : ∀ κ ∈ univ.image (key2 pP (preX (Hb := Hb) pk msg ρ x (G2, s₂))), G2 κ = G2' κ) :
    sigR Hb (respAdv pk msg ρ) msg x (G2', s₂) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂))) =
      sigR Hb (respAdv pk msg ρ) msg x (G2, s₂) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂))) := by
  have eT0 : tR Hb (respAdv (R := R) pk msg ρ) msg x (G2', s₂) =
      tR Hb (respAdv (R := R) pk msg ρ) msg x (G2, s₂) := by
    have := (step1_cons (R := R) (Hb := Hb) (st := stOf x.1.2.1) (r := toBA (List.ofFn x.1.2.2)) hHb
      (ba x.1.1) x.2 (G2, s₂) (G2', s₂) (fun _ _ => rfl) (fun _ _ => rfl)).2.2
    unfold tR s1R; rw [this]
  generalize ht : tR Hb (respAdv (R := R) pk msg ρ) msg x (G2, s₂) = t at hv eT0 ⊢
  have hB : ∀ G : Tab2G pP, tR Hb (respAdv (R := R) pk msg ρ) msg x (G, s₂) = t →
      bothOK (respAdv (R := R) pk msg ρ)
        (bif false then (fun _ => t) (G, s₂) else tR Hb (respAdv pk msg ρ) msg x (G, s₂))
        (bif false then tR Hb (respAdv pk msg ρ) msg x (G, s₂) else (fun _ => t) (G, s₂)) = true := by
    intro G hG
    simp only [Bool.cond_false, hG, bothOK, respAdv_respond, hv, Bool.and_self]
  have e0 := sigOf_oR Hb (respAdv (R := R) pk msg ρ) msg false x (fun _ => t) (G2, s₂) (hB G2 ht)
  have e1 := sigOf_oR Hb (respAdv (R := R) pk msg ρ) msg false x (fun _ => t) (G2', s₂) (hB G2' eT0)
  simp only [Bool.cond_false, respAdv_respond] at e0 e1
  rw [ht] at e0
  rw [eT0] at e1
  rw [← e0, ← e1]
  refine congrArg (sigOf x.1.2.1) ?_
  rw [oR_fix (Hb := Hb) _ msg false x (fun _ => t) s₂ G2 G2' rfl,
    oR_fix (Hb := Hb) _ msg false x (fun _ => t) s₂ G2 G2 rfl]
  refine @realRun2_h23_congr (icPrg (rowFn s₂.2)) Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) _ hHb
    (hyp2_kOf _ _ _ _ _ _) x.2 G2 G2' s₂.1 x.1.1 fun _ c => (h2 _ (mem_image.2 ⟨c, mem_univ _, ?_⟩)).symm
  unfold preX
  rw [ht]
  rfl

/-- **A whole further session is a consistent reader** of `H₅` (`624` keys), the cipher (`4607`)
and `H₂³` (the `nGrind` grinding points of its prefix, if its response passes the checks), and of
no slice key (its own slice is fixed). -/
theorem fullX_sreads (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) :
    SReads pP (fun t : Tb R pP => fullX Hb pk msg ρ x t.2) 0 nGrind 624 4607 := by
  classical
  refine ⟨fun t => fullKeys (Hb := Hb) pk msg ρ x t.2, fun t t' h => ?_, fun t => ⟨by simp [fullKeys], ?_,
    (s1Keys_card (Hb := Hb) x t.2).1, (s1Keys_card (Hb := Hb) x t.2).2⟩⟩
  · obtain ⟨-, h2, h5, hE⟩ := h
    obtain ⟨g, G2, s₂⟩ := t
    obtain ⟨g', G2', s₂'⟩ := t'
    dsimp only at h2 h5 hE ⊢
    obtain ⟨e5, eE, eS, eT⟩ := full_step1 hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
    have eP := preX_cons hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
    refine ⟨?_, ?_⟩
    · unfold fullKeys
      rw [eT, eP, e5, eE]
    · unfold fullX
      rw [sessX_eq_tR pk msg ρ x (G2', s₂'), sessX_eq_tR pk msg ρ x (G2, s₂)]
      dsimp only
      rw [eT]
      refine Prod.ext rfl ?_
      dsimp only
      cases hv : validB (respAdv (R := R) pk msg ρ) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂)))
          (tR Hb (respAdv pk msg ρ) msg x (G2, s₂))
      · exact finish_of_not_valid (respAdv pk msg ρ) _ _ _ _ hv
      · rw [sigR_tables hHb _ msg x (G2, s₂) (G2', s₂') eS]
        dsimp only
        rw [sigR_h23 hHb pk msg ρ x G2 G2' s₂ hv fun κ hκ => h2 κ (by
          unfold fullKeys; rw [hv]; exact hκ)]
  · show (fullKeys (Hb := Hb) pk msg ρ x t.2).2.1.card ≤ nGrind
    unfold fullKeys
    split_ifs
    · exact card_image_le.trans (by rw [card_univ, Fintype.card_fin])
    · simp


end Full

/-! ## Sequential further sessions -/

section Seq

variable (Hb : Hashes)

/-- What the Issuer has seen of a finished further session: its request and its outcome. -/
abbrev Hist := Bytes × Except Error (Option Bytes)

/-- **Further sessions one after the other**: each one's key and message (`next`) and the Issuer's
response to its request (`resp`) are chosen from the sessions before it (`H`), each session runs to
the end on the tables with its own tape. -/
noncomputable def runSeq (next : List Hist → UOVKey × Bytes) (resp : List Hist → Bytes → Bytes) :
    List XR → List Hist → ShP R → List Hist
  | [], H, _ => H
  | x :: cs, H, s => runSeq next resp cs (H ++ [fullX Hb (next H).1 (next H).2 (resp H) x s]) s

variable {Hb}

/-- **Sequential sessions are a consistent reader**: `|cs|` times a session's keys. -/
theorem runSeq_sreads (hHb : HashesWF Hb) (next : List Hist → UOVKey × Bytes)
    (resp : List Hist → Bytes → Bytes) (cs : List XR) :
    ∀ H, SReads pP (fun t : Tb R pP => runSeq Hb next resp cs H t.2) 0 (cs.length * nGrind)
      (cs.length * 624) (cs.length * 4607) := by
  induction cs with
  | nil => intro H; simpa [runSeq] using SReads.const (R := R) (p := pP) H
  | cons x cs ih =>
    intro H
    have h := (fullX_sreads (R := R) hHb (next H).1 (next H).2 (resp H) x).bind
      (g := fun y (t : Tb R pP) => runSeq Hb next resp cs (H ++ [y]) t.2) fun y => ih (H ++ [y])
    refine (h.mono le_rfl ?_ ?_ ?_)
    · simp only [List.length_cons]; rw [Nat.succ_mul]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

/-- A consistent reader of the shared tables alone is a joint consistent reader of both challenge
slices and the shared tables (it reads no slice key). -/
lemma SReadsP.of_shared {X : Type*} {f : ShP R → X} {a2 a5 aE : ℕ}
    (h : SReads pP (fun t : Tb R pP => f t.2) 0 a2 a5 aE) (a3 : ℕ) :
    SReadsP (fun t : TbP R => f t.2) a3 a2 a5 aE := by
  obtain ⟨Q, hQ, hc⟩ := h
  refine ⟨fun t => ((∅, ∅), (Q (default, t.2)).2), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨-, -, h2, h5, hE⟩ := h
    obtain ⟨e1, e2⟩ := hQ (default, t.2) (default, t'.2) ⟨fun _ _ => rfl, h2, h5, hE⟩
    exact ⟨by simp only [e1], e2⟩
  · obtain ⟨-, c2, c5, cE⟩ := hc (default, t.2)
    exact ⟨by simp, by simp, c2, c5, cE⟩

end Seq

/-! ## The adaptive game -/

section Game

variable {m₁ m₂ m₃ : ℕ}

/-- **The Issuer of the adaptive game**: before the challenge, `m₁` further sessions one after the
other (`next₁`, `resp₁`: each session's key, message and response from the earlier sessions'
requests and outcomes); then the challenge key and messages from all of them; after the two
challenge requests, `m₂` further sessions (`next₂`, `resp₂`, also seeing the challenge requests);
the challenge responses from everything so far; after the challenge outcome, `m₃` further sessions
(`next₃`, `resp₃`); and a guess that sees everything, the challenge slices and the tables. The
interaction does not read the tables itself (the further sessions it runs do). -/
structure AdversaryAd (R : Type) where
  next₁ : List Hist → UOVKey × Bytes
  resp₁ : List Hist → Bytes → Bytes
  pk : List Hist → UOVKey
  msg : List Hist → Bool → Bytes
  next₂ : List Hist → Bytes → Bytes → List Hist → UOVKey × Bytes
  resp₂ : List Hist → Bytes → Bytes → List Hist → Bytes → Bytes
  respond : List Hist → Bytes → Bytes → List Hist → Bool → Bytes
  next₃ : List Hist → Bytes → Bytes → List Hist → Option (Bytes × Bytes) → List Hist → UOVKey × Bytes
  resp₃ : List Hist → Bytes → Bytes → List Hist → Option (Bytes × Bytes) → List Hist → Bytes → Bytes
  guess : List Hist → Bytes → Bytes → List Hist → Option (Bytes × Bytes) → List Hist → SlP → ShP R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryAd.Budget (A : AdversaryAd R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ H₁ t₀ t₁ H₂ y H₃ (g₁ : Tab3) s, Rd3 (fun g => A.guess H₁ t₀ t₁ H₂ y H₃ (g, g₁) s) q3
  h31 : ∀ H₁ t₀ t₁ H₂ y H₃ (g₀ : Tab3) s, Rd3 (fun g => A.guess H₁ t₀ t₁ H₂ y H₃ (g₀, g) s) q3
  h5 : ∀ H₁ t₀ t₁ H₂ y H₃ sl, Rd5 (A.guess H₁ t₀ t₁ H₂ y H₃ sl) q5
  hE : ∀ H₁ t₀ t₁ H₂ y H₃ sl, RdE (A.guess H₁ t₀ t₁ H₂ y H₃ sl) qE

/-- The further sessions' tapes, stage by stage. -/
abbrev TapesAd (m₁ m₂ m₃ : ℕ) := (Fin m₁ → XR) × (Fin m₂ → XR) × (Fin m₃ → XR)

variable (Hb : Hashes)

namespace AdversaryAd

variable (A : AdversaryAd R) (c : TapesAd m₁ m₂ m₃)

/-- The sessions before the challenge. -/
noncomputable def hist₁ (s : ShP R) : List Hist := runSeq Hb A.next₁ A.resp₁ (List.ofFn c.1) [] s

/-- The sessions between the challenge requests and the challenge responses. -/
noncomputable def hist₂ (t₀ t₁ : Bytes) (s : ShP R) : List Hist :=
  runSeq Hb (A.next₂ (A.hist₁ Hb c s) t₀ t₁) (A.resp₂ (A.hist₁ Hb c s) t₀ t₁) (List.ofFn c.2.1) [] s

/-- The sessions after the challenge outcome. -/
noncomputable def hist₃ (t₀ t₁ : Bytes) (y : Option (Bytes × Bytes)) (s : ShP R) : List Hist :=
  runSeq Hb (A.next₃ (A.hist₁ Hb c s) t₀ t₁ (A.hist₂ Hb c t₀ t₁ s) y)
    (A.resp₃ (A.hist₁ Hb c s) t₀ t₁ (A.hist₂ Hb c t₀ t₁ s) y) (List.ofFn c.2.2) [] s

/-- **The reduction**: the two-session Issuer with a table-reading interaction that runs the
further sessions itself, with their tapes `c` fixed. Its key stage runs the sessions before the
challenge, its response stage also those between the challenge requests and responses, its guess
also those after the challenge outcome. -/
noncomputable def red : AdversaryRA R where
  pk _ s := A.pk (A.hist₁ Hb c s)
  msg b _ s := A.msg (A.hist₁ Hb c s) b
  respond t₀ t₁ i _ s := A.respond (A.hist₁ Hb c s) t₀ t₁ (A.hist₂ Hb c t₀ t₁ s) i
  guess t₀ t₁ y sl s := A.guess (A.hist₁ Hb c s) t₀ t₁ (A.hist₂ Hb c t₀ t₁ s) y (A.hist₃ Hb c t₀ t₁ y s) sl s

end AdversaryAd

/-- **The adaptive game** in world `b`: the further sessions before the challenge, the challenge
requests (the first session on `µ_b`, the second on `µ_{¬b}`, the Lean prover on the shared
tables), the further sessions in between, the challenge responses and outcome (the signatures in
message order if both complete), the further sessions after, and the guess. -/
noncomputable def realGameAd (A : AdversaryAd R) (b : Bool)
    (z : ((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R) : Prop :=
  let H₁ := A.hist₁ Hb z.1.2 z.2
  let S₀ := sessX Hb (A.pk H₁) (A.msg H₁ b) z.1.1.1 z.2
  let S₁ := sessX Hb (A.pk H₁) (A.msg H₁ !b) z.1.1.2 z.2
  let H₂ := A.hist₂ Hb z.1.2 S₀.1 S₁.1 z.2
  let y := outcome b (S₀.2 (A.respond H₁ S₀.1 S₁.1 H₂ false)) (S₁.2 (A.respond H₁ S₀.1 S₁.1 H₂ true))
  A.guess H₁ S₀.1 S₁.1 H₂ y (A.hist₃ Hb z.1.2 S₀.1 S₁.1 y z.2) (z.1.1.1.2, z.1.1.2.2) z.2

/-- **The adaptive game is the two-session game of the reduction**, tape by tape. -/
theorem realGameAd_iff (A : AdversaryAd R) (b : Bool) (x : XR × XR) (c : TapesAd m₁ m₂ m₃) (s : ShP R) :
    realGameAd Hb A b ((x, c), s) ↔ realGameRA Hb (A.red Hb c) b (x, s) :=
  Iff.rfl

variable {Hb}

/-- **The reduction's interaction budget**: the key stage runs the `m₁` sessions before the
challenge, the response stage also the `m₂` sessions in between. -/
theorem AdversaryAd.red_iBudgetH (hHb : HashesWF Hb) (A : AdversaryAd R) (c : TapesAd m₁ m₂ m₃) :
    (A.red Hb c).IBudgetH 0 ((m₁ + m₂) * nGrind) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) where
  k := by
    have h := (runSeq_sreads (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).map
      fun H => (A.pk H, A.msg H false, A.msg H true)
    simp only [List.length_ofFn] at h
    exact SReadsP.of_shared (f := fun s => (A.red Hb c).keyOf (default, default) s)
      ((h.mono le_rfl (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))) 0
  r t₀ t₁ := by
    have h := (runSeq_sreads (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).bind
      (g := fun H₁ (t : Tb R pP) =>
        (A.respond H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] t.2) false,
          A.respond H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] t.2) true))
      fun H₁ => (runSeq_sreads (R := R) hHb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) []).map
        fun H₂ => (A.respond H₁ t₀ t₁ H₂ false, A.respond H₁ t₀ t₁ H₂ true)
    simp only [List.length_ofFn] at h
    exact SReadsP.of_shared (f := fun s => (A.red Hb c).respOf t₀ t₁ (default, default) s)
      ((h.mono le_rfl (by rw [Nat.add_mul]) (by rw [Nat.add_mul]) (by rw [Nat.add_mul]))) 0

/-- **The reduction's guess budget**: the Issuer's plus all further sessions' `H₅` and cipher
reads. -/
theorem AdversaryAd.red_gBudget (hHb : HashesWF Hb) (A : AdversaryAd R) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (c : TapesAd m₁ m₂ m₃) :
    (A.red Hb c).GBudget q3 ((m₁ + m₂ + m₃) * 624 + q5) ((m₁ + m₂ + m₃) * 4607 + qE) where
  h30 t₀ t₁ y g₁ s := hA.h30 _ _ _ _ _ _ g₁ s
  h31 t₀ t₁ y g₀ s := hA.h31 _ _ _ _ _ _ g₀ s
  h5 t₀ t₁ y sl := by
    have r1 := (runSeq_sreads (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).rd5 default
    have h := Rd5.bindEq (m := fun s => runSeq Hb A.next₁ A.resp₁ (List.ofFn c.1) [] s)
      (f := fun H₁ s => A.guess H₁ t₀ t₁
        (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y
        (runSeq Hb (A.next₃ H₁ t₀ t₁
            (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y)
          (A.resp₃ H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y)
          (List.ofFn c.2.2) [] s) sl s)
      (F := fun s => (A.red Hb c).guess t₀ t₁ y sl s) (fun _ => rfl) r1 fun H₁ =>
        Rd5.bindEq (m := fun s => runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s)
          (f := fun H₂ s => A.guess H₁ t₀ t₁ H₂ y
            (runSeq Hb (A.next₃ H₁ t₀ t₁ H₂ y) (A.resp₃ H₁ t₀ t₁ H₂ y) (List.ofFn c.2.2) [] s) sl s)
          (fun _ => rfl) ((runSeq_sreads (R := R) hHb _ _ (List.ofFn c.2.1) []).rd5 default) fun H₂ =>
            Rd5.bindEq (m := fun s => runSeq Hb (A.next₃ H₁ t₀ t₁ H₂ y) (A.resp₃ H₁ t₀ t₁ H₂ y)
                (List.ofFn c.2.2) [] s)
              (f := fun H₃ s => A.guess H₁ t₀ t₁ H₂ y H₃ sl s)
              (fun _ => rfl) ((runSeq_sreads (R := R) hHb _ _ (List.ofFn c.2.2) []).rd5 default)
              fun H₃ => hA.h5 _ _ _ _ _ _ _
    simp only [List.length_ofFn] at h
    exact h.mono (by rw [Nat.add_mul, Nat.add_mul]; omega)
  hE t₀ t₁ y sl := by
    have r1 := (runSeq_sreads (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).rdE default
    have h := RdE.bindEq (m := fun s => runSeq Hb A.next₁ A.resp₁ (List.ofFn c.1) [] s)
      (f := fun H₁ s => A.guess H₁ t₀ t₁
        (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y
        (runSeq Hb (A.next₃ H₁ t₀ t₁
            (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y)
          (A.resp₃ H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s) y)
          (List.ofFn c.2.2) [] s) sl s)
      (F := fun s => (A.red Hb c).guess t₀ t₁ y sl s) (fun _ => rfl) r1 fun H₁ =>
        RdE.bindEq (m := fun s => runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] s)
          (f := fun H₂ s => A.guess H₁ t₀ t₁ H₂ y
            (runSeq Hb (A.next₃ H₁ t₀ t₁ H₂ y) (A.resp₃ H₁ t₀ t₁ H₂ y) (List.ofFn c.2.2) [] s) sl s)
          (fun _ => rfl) ((runSeq_sreads (R := R) hHb _ _ (List.ofFn c.2.1) []).rdE default) fun H₂ =>
            RdE.bindEq (m := fun s => runSeq Hb (A.next₃ H₁ t₀ t₁ H₂ y) (A.resp₃ H₁ t₀ t₁ H₂ y)
                (List.ofFn c.2.2) [] s)
              (f := fun H₃ s => A.guess H₁ t₀ t₁ H₂ y H₃ sl s)
              (fun _ => rfl) ((runSeq_sreads (R := R) hHb _ _ (List.ofFn c.2.2) []).rdE default)
              fun H₃ => hA.hE _ _ _ _ _ _ _
    simp only [List.length_ofFn] at h
    exact h.mono (by rw [Nat.add_mul, Nat.add_mul]; omega)

/-- The adaptive tape, with the further sessions' tapes first. -/
def tapeAd : TapesAd m₁ m₂ m₃ × ((XR × XR) × ShP R) ≃ ((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game


/-! ## The bound -/

section Bound

variable {m₁ m₂ m₃ : ℕ}

/-- **PomFRIT blindness with adaptively scheduled further sessions, for every type of cipher
rows** (`ZKRow R`, `ZK2ARow R`; SHAKE as the base record): with `m₁` further sessions before the
challenge, `m₂` between the challenge requests and responses and `m₃` after the challenge outcome,
each started after the Issuer has seen the earlier ones' outcomes,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃, q₅ + (m₁+m₂+m₃)·624 + 6(m₁+m₂)·624 + 1872,
                                  q_E + (m₁+m₂+m₃)·4607 + 6(m₁+m₂)·4607 + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(0, (m₁+m₂)·2³², (m₁+m₂)·624, (m₁+m₂)·4607)

(`blindnessRAH_lean_numG` for the reduction that runs the further sessions, averaged over their
tapes). -/
theorem blindnessAd_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryAd R) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R) (realGameAd Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H R 0 ((m₁ + m₂) * nGrind) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) := by
  rw [← pr_equiv tapeAd, ← pr_equiv tapeAd]
  exact abs_pr_prod_sub_le _ _ fun c =>
    blindnessRAH_lean_numG (A.red Hashes.shake c) (A.red_gBudget hashesWF_shake hA c)
      (A.red_iBudgetH hashesWF_shake c)

/-- **PomFRIT blindness with adaptively scheduled further sessions** (function rows). -/
theorem blindnessAd_lean_num (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      4 * εRO (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if (m₁ + m₂) * nGrind = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * 0) (6 * ((m₁ + m₂) * 624) + 2184) (6 * ((m₁ + m₂) * 4607) + 18428) +
            ((m₁ + m₂) * nGrind + (m₁ + m₂) * nGrind : ℕ) / 2 ^ 128)) :=
  blindnessAd_lean_numG A hA

/-- **PomFRIT blindness with adaptively scheduled further sessions and AES as uniformly random
permutations.** -/
theorem blindnessAd_lean_num_perm (A : AdversaryAd (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Equiv.Perm Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Equiv.Perm Blk)) (realGameAd Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H (Equiv.Perm Blk) 0 ((m₁ + m₂) * nGrind) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) :=
  blindnessAd_lean_numG A hA

/-- **The adaptive bound in numbers**: with `n = m₁ + m₂ + m₃ + 2` sessions in all,

    |Pr[W₀] − Pr[W₁]| ≤ n·2⁻⁹² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸.

The per-session term is dominated by the collision term's `H₂³` reads (`8·2³²·2⁻¹²⁸ = 2⁻⁹³` for each
session run inside the interaction, which reads `2³²` grinding points). -/
theorem blindnessAd_lean_le (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      (m₁ + m₂ + m₃ + 2 : ℕ) / 2 ^ 92 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_num (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have hn := noHitProb_le_128
  have hG : (nGrind : ℝ) = 2 ^ 32 := by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat]
  have e : ∀ x : ℝ, x / 2 ^ 92 = x * 68719476736 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have h1 : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ m₃ := Nat.cast_nonneg _
  unfold εRO at h
  split_ifs at h with h0
  · push_cast at h ⊢
    rw [e]
    linarith
  · push_cast at h ⊢
    rw [hG] at h
    rw [e]
    nlinarith

/-- **`2²⁰` sessions**: `≤ 2⁻⁷²` plus the guess's budget terms. -/
theorem blindnessAd_lean_2pow20 (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 20) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      1 / 2 ^ 72 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_le (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 92 ≤ 1 / 2 ^ 72 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` sessions**: `≤ 2⁻⁶⁰` plus the guess's budget terms. -/
theorem blindnessAd_lean_2pow32 (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 32) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      1 / 2 ^ 60 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_le (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 92 ≤ 1 / 2 ^ 60 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound


end VoleMole.Privacy.PomFRIT
