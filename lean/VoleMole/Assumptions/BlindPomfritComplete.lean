import VoleMole.Assumptions.BlindPomfritGrind
import VoleMole.ROM.OneMoreLemmaP

/-!
# Theorem 6 at PomFRIT for the Lean client: the completeness term is at most `(ℓ + 1)·2⁻¹¹³`

`lean/docs/security/pomfrit.md` §6.4, G9; `uov-assumptions.md` §5.6. `pomfrit_T6`
(`Assumptions/BlindPomfrit.lean`) bounds `Adv^{ompr}(B)` by PomFRIT's one-more forgery
probability plus the client's completeness failure `compFail`. Here `compFail` is bounded for the
Lean client (`leanClient`, `Assumptions/PomClientLean.lean`), with faest-arch-opt's CRT tables.

**The argument.** For a fixed key, `B`'s and the client's coins (cipher table `E`, seed) and target
stream, the game's run is the lazy random oracle's run of one computation over the world (`B`'s
oracle and the hashes; `OneMore.realImpl_run_eq`). Table by table (`ROM/ExtractReduce.lean`):
* *`B`'s phase* (`B` with the sessions' step 1 and the target oracle, collapsed into one handler,
  `combH`) keeps an invariant (`InvH`): every hint in the target oracle's table is `0`, the
  programmed targets are the table's answers, and each session of the forger's state has its
  label's answer cached with hint `0`, its label and state those of the client's step 1 at this
  table (`eval_start`).
* *The finishing phase* (the client's step 2 of the claimed sessions, then PomFRIT's verification
  `flagV`) does not change the target oracle's entries at cached labels (`post_keep`), so the
  claims' programmed targets are the sessions' answers, and `B`'s win gives `P(σ) = H_T(x)` for
  each claimed session. If no claimed session's grinding answers are `GrindBad`, each signature
  verifies (`verOne_ok`: the verifier recomputes `chal1`, `chal1Pre_honest`; the `hash_to_target`
  input is the label, `tgtIn_final`; the verifier accepts, `pom_complete`) and the messages are
  distinct, so the flag is `true` (`flag_true`).
* So a completeness failure at a table implies `GrindBad` of the grinding answers of one of the
  `ℓ + 1` claimed sessions (`fail_table`), each the output of a computation that reaches its prefix
  without `H₂³` queries (`pfxB`, `allQ_pfxB`). Each has probability `≤ 2⁻¹¹³`
  (`prEvent_grindBad_le`).

**Theorems.**
* **`compFail_le`**: `compFail ≤ (ℓ + 1)·2⁻¹¹³` for the Lean client, every OMPR adversary `B` (with
  a finite random oracle) and every key generation and Issuer.
* **`pomfrit_T6_lean`**: `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger (leanClient …) n B)] +
  (ℓ + 1)·2⁻¹¹³`, the forger running the Lean client; **`pomfrit_T6_lean_bound`**: with `B`'s
  target budget `Q` and `Q + ℓ + 1` targets.

The Issuer's `derive_preimage` abort does not enter: `compFail` is conditioned on `B`'s claims
being preimages (`relP`), and the client never calls the Issuer itself.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
  VoleMole.Assumptions.Blind VoleMole.Assumptions.UOV
open scoped ENNReal

namespace VoleMole.Assumptions.BlindPomfrit

/-! ## Evaluation of the game's layers at a table -/

section EvalLayers

variable {DR : Type} {AR : DR → Type} (G : (d : DR ⊕ Dom) → WB AR d)

/-- The hashes' part of a world table. -/
def gHof : Table := fun d => G (.inr d)

variable (pre' : TG → SIss)

/-- The target oracle and the Issuer on the reduced state (`htW` at PomFRIT's types, hints the
blindings). -/
noncomputable abbrev htH := htW (AR := WB AR) (X := ByteArray) (Hn := TG) (G := TG) (S := SIss) addHint pre'

lemma eval_htH_liftC {α : Type} (oc : OracleComp (specR Ans) α) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (simulateQ
      (liftC (AR := AR) (X := ByteArray) (G := TG) (S := SIss)) oc)).run s) =
      (evalWithAnswerFn (QueryImpl.ofFn (gHof G)) oc, s) := by
  induction oc using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    erw [simulateQ_spec_query]
    simp only [htW]
    erw [evalWithAnswerFn_map, evalWithAnswerFn_liftM_query]
    exact ih _ s

lemma eval_htH_liftV_toV {α : Type} (oc : OracleComp spec α) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (simulateQ
      (liftV (AR := AR) (S := SIss)) (toV oc))).run s) =
      (evalWithAnswerFn (QueryImpl.ofFn (gHof G)) oc, s) := by
  rw [liftV_toV]
  induction oc using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    erw [simulateQ_spec_query]
    simp only [htW]
    erw [evalWithAnswerFn_map, evalWithAnswerFn_liftM_query]
    exact ih _ s

lemma eval_htH_tq {β : Type} (x : ByteArray) (h : TG)
    (k : TG × TG → OracleComp (specA (WB AR) ByteArray TG TG SIss) β) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre')
      (liftM ((specA (WB AR) ByteArray TG TG SIss).query (.inr (.inl (x, h)))) >>= k)).run s) =
      evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (k (tStep addHint x h s).1)).run
        (tStep addHint x h s).2) := by
  erw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]

lemma eval_logImpl_fst (gH : Table) (E : CTable) {α : Type} (oc : OracleComp specIC α)
    (L : QueryLog specIC) :
    (evalWithAnswerFn (QueryImpl.ofFn gH) ((simulateQ (logImpl E) oc).run L)).1 =
      evalWithAnswerFn (QueryImpl.ofFn (join gH E)) oc := by
  induction oc using OracleComp.inductionOn generalizing L with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    rcases t with d | x
    · simp only [logImpl, StateT.run_mk]
      erw [evalWithAnswerFn_map, evalWithAnswerFn_liftM_query]
      exact ih _ _
    · simp only [logImpl, StateT.run_mk, evalWithAnswerFn_pure]
      exact ih _ _

end EvalLayers

/-! ## The target oracle's step -/

section TStep

variable (x : ByteArray) (h : TG) (s : HTS)

lemma tStep_cached {a : TG × TG} (hx : s.1 x = some a) : tStep addHint x h s = (a, s) := by
  simp [tStep, hx]

lemma tStep_self : (tStep addHint x h s).2.1 x = some (tStep addHint x h s).1 := by
  unfold tStep
  cases hx : s.1 x with
  | some a => simp [hx]
  | none => cases s.2.1 <;> simp

lemma tStep_keep {y : ByteArray} {v : TG × TG} (hy : s.1 y = some v) :
    (tStep addHint x h s).2.1 y = some v := by
  unfold tStep
  cases hx : s.1 x with
  | some a => simp [hy]
  | none =>
    have hne : y ≠ x := by rintro rfl; simp [hx] at hy
    cases s.2.1 <;> simp [Function.update_of_ne hne, hy]

lemma tStep_tg_keep {y : ByteArray} (hy : s.1 y ≠ none) :
    (tStep addHint x h s).2.2.2.1 y = s.2.2.1 y := by
  unfold tStep
  cases hx : s.1 x with
  | some a => simp
  | none =>
    have hne : y ≠ x := by rintro rfl; exact hy hx
    cases s.2.1 <;> simp [Function.update_of_ne hne]

/-- The target oracle's table holds only hint `0`, and its programmed targets are its answers. -/
def HInv (s : HTS) : Prop :=
  (∀ y a, s.1 y = some a → a.2 = 0) ∧ ∀ y v, s.2.2.1 y = some v → s.1 y = some v

lemma tStep_hinv (hs : HInv s) : HInv (tStep addHint x 0 s).2 ∧ (tStep addHint x 0 s).1.2 = 0 := by
  obtain ⟨h1, h2⟩ := hs
  unfold tStep
  cases hx : s.1 x with
  | some a => exact ⟨⟨h1, h2⟩, h1 x a hx⟩
  | none =>
    cases hr : s.2.1 with
    | nil =>
      refine ⟨⟨fun y a ha => ?_, fun y v hv => ?_⟩, rfl⟩
      · by_cases hyx : y = x
        · subst hyx; simp at ha; rw [← ha]
        · simp [Function.update_of_ne hyx] at ha; exact h1 y a ha
      · by_cases hyx : y = x
        · subst hyx; have := h2 y v hv; simp [hx] at this
        · simp [Function.update_of_ne hyx]; exact h2 y v hv
    | cons u r =>
      refine ⟨⟨fun y a ha => ?_, fun y v hv => ?_⟩, rfl⟩
      · by_cases hyx : y = x
        · subst hyx; simp at ha; rw [← ha]
        · simp [Function.update_of_ne hyx] at ha; exact h1 y a ha
      · by_cases hyx : y = x
        · subst hyx; simp [addHint] at hv ⊢; exact hv
        · simp [Function.update_of_ne hyx] at hv ⊢; exact h2 y v hv

end TStep

/-! ## `B`'s phase as one handler, and its invariant at a table -/

section BPhase

variable {DR : Type} {AR : DR → Type} (pre' : TG → SIss) (T : CrtTables) (lr : Bool) (ℓ : ℕ)
  {Cn St : Type} (cl : PomClient Cn St) {X' Hn' : Type} [DecidableEq X'] (n : ℕ) (pk : UovPk)
  (κ : CTable × Cn)

/-- The forger's state and the target oracle's state. -/
abbrev BS (St X' Hn' : Type) := BSt ByteArray TG Hn' (ℕ × St) X' (QueryLog specIC) × HTS

/-- **`B`'s phase as one handler**: the blinding forger's handler (with the client `toClient`)
followed by the target oracle and the Issuer on the reduced state. -/
noncomputable def combH : QueryImpl (specB AR X' Hn' TG SIss)
    (StateT (BS St X' Hn') (OracleComp (ofFn (WB AR)))) :=
  fun q => StateT.mk fun p => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (htH (AR := AR) pre') ((blindImpl (toClient T lr ℓ cl) n pk κ q).run p.1)).run p.2

theorem collapseH {α : Type} (oa : OracleComp (specB AR X' Hn' TG SIss) α)
    (s : BSt ByteArray TG Hn' (ℕ × St) X' (QueryLog specIC)) (c : HTS) :
    (simulateQ (htH (AR := AR) pre') ((simulateQ (blindImpl (toClient T lr ℓ cl) n pk κ) oa).run
      s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combH pre' T lr ℓ cl n pk κ) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

variable (G : (d : DR ⊕ Dom) → WB AR d)

/-- The client's step 1 of session `k` at the table. -/
def soOf (k : ℕ) : ByteArray × ByteArray × St :=
  evalWithAnswerFn (QueryImpl.ofFn (join (gHof G) κ.1)) (cl.start pk κ.2 k)

/-- **The invariant of `B`'s phase at a table.** -/
def InvH (p : BS St X' Hn') : Prop :=
  HInv p.2 ∧ ∀ x' e, p.1.ses x' = some e →
    p.2.1 e.x = some (e.u, 0) ∧ e.r = 0 ∧
    e.x = label pk lr e.idx (soOf cl pk κ G e.idx).1 (soOf cl pk κ G e.idx).2.1 ∧
    e.st = (e.idx, (soOf cl pk κ G e.idx).2.2)

lemma eval_start_toClient (k : ℕ) (L : QueryLog specIC) :
    (evalWithAnswerFn (QueryImpl.ofFn (gHof G)) ((toClient T lr ℓ cl).start pk κ L k)).1 =
      (label pk lr k (soOf cl pk κ G k).1 (soOf cl pk κ G k).2.1, 0, (k, (soOf cl pk κ G k).2.2)) := by
  simp only [toClient, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_logImpl_fst]
  rfl

theorem invH_step (q : DR ⊕ ((X' × Hn') ⊕ TG)) (p : BS St X' Hn')
    (hp : InvH lr cl pk κ G p) :
    InvH lr cl pk κ G (evalWithAnswerFn (QueryImpl.ofFn G)
      ((combH pre' T lr ℓ cl n pk κ q).run p)).2 := by
  obtain ⟨bs, s⟩ := p
  rcases q with d | ⟨x', hB⟩ | t
  · simp only [combH, blindImpl, StateT.run_mk]
    erw [simulateQ_map, StateT.run_map, evalWithAnswerFn_map, evalWithAnswerFn_map]
    erw [simulateQ_spec_query]
    simp only [htW]
    erw [evalWithAnswerFn_map]
    exact hp
  · by_cases hk : bs.k < n
    · simp only [combH, blindImpl, StateT.run_mk, hk, ite_true]
      rw [evalWithAnswerFn_map, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind,
        eval_htH_liftC]
      have hog := eval_start_toClient T lr ℓ cl pk κ G bs.k bs.cs
      generalize evalWithAnswerFn (QueryImpl.ofFn (gHof G))
        ((toClient T lr ℓ cl).start pk κ bs.cs bs.k) = og at hog ⊢
      obtain ⟨og1, og2⟩ := og
      dsimp only at hog
      subst hog
      erw [eval_htH_tq]
      simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
      set lab := label pk lr bs.k (soOf cl pk κ G bs.k).1 (soOf cl pk κ G bs.k).2.1 with hlab
      obtain ⟨hinv, hses⟩ := hp
      obtain ⟨hinv', ha0⟩ := tStep_hinv lab s hinv
      refine ⟨hinv', fun y' e he => ?_⟩
      by_cases hy : y' = x'
      · subst hy
        simp only [Function.update_self, Option.some.injEq] at he
        subst he
        refine ⟨?_, rfl, rfl, rfl⟩
        rw [tStep_self]
        exact congrArg some (Prod.ext rfl ha0)
      · simp only [Function.update_of_ne hy] at he
        obtain ⟨h1, h2, h3, h4⟩ := hses y' e he
        exact ⟨tStep_keep _ _ _ h1, h2, h3, h4⟩
    · simp only [combH, blindImpl, StateT.run_mk, hk, ite_false, simulateQ_pure, StateT.run_pure,
        map_pure, evalWithAnswerFn_pure]
      exact hp
  · simp only [combH, blindImpl, StateT.run_mk]
    erw [simulateQ_map, StateT.run_map, evalWithAnswerFn_map, evalWithAnswerFn_map]
    erw [simulateQ_spec_query]
    simp only [htW]
    exact hp

end BPhase

end VoleMole.Assumptions.BlindPomfrit
