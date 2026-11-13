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

/-- **`B`'s phase keeps the invariant at every table.** -/
theorem invH_run (b : OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))) (L : List TG) :
    InvH lr cl pk κ G (evalWithAnswerFn (QueryImpl.ofFn G)
      ((simulateQ (combH pre' T lr ℓ cl n pk κ) b).run
        (bs0 (toClient T lr ℓ cl).init, ((fun _ => none), (L, fun _ => none, 0))))).2 :=
  eval_run_inv G _ _ (fun q p hp => invH_step pre' T lr ℓ cl n pk κ G q p hp) b _
    ⟨⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩, fun _ _ h => by simp [bs0] at h⟩

end BPhase

/-! ## The finishing phase at a table -/

section Post

variable {DR : Type} {AR : DR → Type} (G : (d : DR ⊕ Dom) → WB AR d) (pre' : TG → SIss)

lemma eval_htH_liftV_toV_bind {α β : Type} (oc : OracleComp spec α)
    (k : α → OracleComp (specV Ans ByteArray TG) β) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre') (simulateQ
      (liftV (AR := AR) (S := SIss)) (toV oc >>= k))).run s) =
      evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (simulateQ
        (liftV (AR := AR) (S := SIss)) (k (evalWithAnswerFn (QueryImpl.ofFn (gHof G)) oc)))).run s) := by
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind,
    eval_htH_liftV_toV]

lemma eval_htH_liftV_tq {β : Type} (x : ByteArray) (h : TG)
    (k : TG × TG → OracleComp (specV Ans ByteArray TG) β) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre') (simulateQ
      (liftV (AR := AR) (S := SIss))
        (liftM ((specV Ans ByteArray TG).query (.inr (x, h))) >>= k))).run s) =
      evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (simulateQ
        (liftV (AR := AR) (S := SIss)) (k (tStep addHint x h s).1))).run (tStep addHint x h s).2) := by
  rfl

lemma eval_htH_liftV_pure {β : Type} (a : β) (s : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre') (simulateQ
      (liftV (AR := AR) (S := SIss)) (pure a : OracleComp (specV Ans ByteArray TG) β))).run s) =
      (a, s) := rfl

variable (T : CrtTables) (lr : Bool) (E : CTable) (pk : UovPk)

/-- **One verification at a table accepts** if the signature's parts are a proof and the
refresher with its commitment, the verifier's `chal1` gives the input `x`, `x`'s answer is cached
as `(u, 0)` and the verifier accepts with the target `u`; the target oracle's state is unchanged. -/
theorem verOne_ok (L : QueryLog specIC) (msg proof b1 b2 c1 : ByteArray) (u : TG) (s : HTS)
    (hp : proof.size = (pomfritParams lr).proofBytes) (hb1 : b1.size = 32) (hb2 : b2.size = 32)
    (hcom : toBA (Spec.PomFRIT.commitRefresher (toL b2)) = b1)
    (hc1 : evalWithAnswerFn (QueryImpl.ofFn (gHof G)) (@chal1Pre (icPrg E.cipher)
      (pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr) proof) = some c1)
    (hx : s.1 (tgtIn pk lr (proof ++ b1 ++ b2) msg c1) = some (u, 0))
    (hacc : (@verify (icPrg E.cipher) (Hashes.ofTable (gHof G)) T
      (pomfritRedeemT pk (fun _ => encT u) b1 b2 lr) proof).accept = true) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre') (simulateQ
      (liftV (AR := AR) (S := SIss)) (verOneV T lr E pk L msg (proof ++ b1 ++ b2)))).run s) =
      (true, s) := by
  obtain ⟨e0, e1, e2⟩ := Privacy.PomFRIT.sig_parts hp hb1 hb2
  unfold verOneV
  dsimp only
  rw [e0, e1, e2, hcom]
  have hne : (b1 != b1) = false := by
    show (!(ByteArray.beq b1 b1)) = false
    simp [ByteArray.beq]
  rw [hne, if_neg (by simp)]
  rw [eval_htH_liftV_toV_bind, hc1]
  dsimp only
  rw [eval_htH_liftV_toV_bind]
  erw [eval_htH_liftV_tq]
  rw [tStep_cached _ _ _ hx]
  rw [eval_htH_liftV_toV_bind, eval_htH_liftV_toV_bind, @evalWithAnswerFn_verifyQ (icPrg E.cipher)]
  dsimp only
  rw [eval_htH_liftV_pure, hacc]

/-- `flagV`'s verifications all accept, the state unchanged, if each one does. -/
theorem verAll_ok (L : QueryLog specIC) (s : HTS) :
    ∀ sigs : List (ByteArray × ByteArray),
      (∀ p ∈ sigs, evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre')
        (simulateQ (liftV (AR := AR) (S := SIss)) (verOneV T lr E pk L p.1 p.2))).run s) =
          (true, s)) →
      ∃ vs, (∀ v ∈ vs, v = true) ∧ evalWithAnswerFn (QueryImpl.ofFn G)
        ((simulateQ (htH (AR := AR) pre') (simulateQ (liftV (AR := AR) (S := SIss))
          (verAllV T lr E pk L sigs))).run s) = (vs, s)
  | [], _ => ⟨[], by simp, rfl⟩
  | (m, sg) :: rest, h => by
    obtain ⟨vs, hvs, he⟩ := verAll_ok L s rest fun p hp => h p (List.mem_cons_of_mem _ hp)
    refine ⟨true :: vs, fun v hv => ?_, ?_⟩
    · rcases List.mem_cons.1 hv with rfl | hv
      · rfl
      · exact hvs v hv
    · simp only [verAllV, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]
      rw [h (m, sg) List.mem_cons_self]
      dsimp only
      rw [he]
      rfl

end Post

section FinLog

variable {Cn St : Type} (cl : PomClient Cn St) (pk : UovPk) (κ : CTable × Cn)

/-- **The claimed sessions' signatures at a table**: each is the client's step 2 at the table. -/
theorem eval_finLog (gH : Table) :
    ∀ (cs : List (ByteArray × TG × (ℕ × St) × TG × SIss)) (L : QueryLog specIC),
      (evalWithAnswerFn (QueryImpl.ofFn gH) ((finLog cl pk κ cs).run L)).1 =
        cs.map fun e => (msgOf e.2.2.1.1, evalWithAnswerFn (QueryImpl.ofFn (join gH κ.1))
          (cl.finish pk κ.2 e.2.2.1.1 e.2.2.1.2 e.2.2.2.1 e.2.2.2.2))
  | [], L => rfl
  | e :: cs, L => by
    have ih := eval_finLog gH cs
    simp only [finLog, List.mapM_cons, StateT.run_bind, evalWithAnswerFn_bind, StateT.run_map,
      evalWithAnswerFn_map, StateT.run_pure, evalWithAnswerFn_pure, List.map_cons] at ih ⊢
    rw [ih, eval_logImpl_fst]

end FinLog

section Keep

variable {DR : Type} {AR : DR → Type} (G : (d : DR ⊕ Dom) → WB AR d) (pre' : TG → SIss)

/-- **The finishing phase keeps the target oracle's entries at cached inputs.** -/
theorem post_keep {β : Type} (oc : OracleComp (specV Ans ByteArray TG) β) (s : HTS) (y : ByteArray)
    (hy : s.1 y ≠ none) :
    (evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre')
        (simulateQ (liftV (AR := AR) (S := SIss)) oc)).run s)).2.1 y = s.1 y ∧
      (evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH (AR := AR) pre')
        (simulateQ (liftV (AR := AR) (S := SIss)) oc)).run s)).2.2.2.1 y = s.2.2.1 y := by
  rw [← QueryImpl.simulateQ_compose]
  refine eval_run_inv G _ (fun s' : HTS => s'.1 y = s.1 y ∧ s'.2.2.1 y = s.2.2.1 y)
    (fun q s' hs' => ?_) oc s ⟨rfl, rfl⟩
  rw [QueryImpl.apply_compose]
  rcases q with d | ⟨x, h⟩
  · simp only [liftV]
    erw [simulateQ_spec_query]
    simp only [htW]
    erw [evalWithAnswerFn_map]
    exact hs'
  · simp only [liftV]
    erw [simulateQ_spec_query]
    simp only [htW]
    show (tStep addHint x h s').2.1 y = s.1 y ∧ (tStep addHint x h s').2.2.2.1 y = s.2.2.1 y
    have hy' : s'.1 y ≠ none := hs'.1 ▸ hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy'
    exact ⟨(tStep_keep x h s' hv).trans (hv.symm.trans hs'.1),
      (tStep_tg_keep x h s' hy').trans hs'.2⟩

end Keep

/-! ## Sizes -/

lemma sessOf_sizes (pk : UovPk) (κ : Prob.Bytes 32) (k : ℕ) :
    (sessOf pk κ k).2.1.size = 32 ∧ (sessOf pk κ k).2.2.size = 32 := by
  refine ⟨?_, ?_⟩
  · simp only [sessOf, Privacy.size_toBA, Spec.PomFRIT.length_commitRefresher]
  · simp only [sessOf, Privacy.size_toBA, (Spec.PomFRIT.length_expandSeed _ _ _).2.1]

lemma proveCommit_size [HasPrg] {Hs : Hashes} {st : Statement} {wSuffix : ByteArray}
    {s : Prover.Pending} {proof : ByteArray} (h : Prover.proveCommit Hs st wSuffix s = .ok proof) :
    proof.size = s.params.proofBytes := by
  obtain ⟨-, check, aT, ctr, delta, opening, -, -, hproof⟩ := proveCommit_inv h
  rw [hproof]
  exact (fields_assemble _ _).2.2.2.2.2.2.2.2.2

/-! ## The game at a table -/

section Game

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} (lr : Bool) (ℓ n : ℕ) {X' Hn' : Type}
  [DecidableEq X'] (pk : UovPk) (pre' : TG → SIss) (κ : CTable × Prob.Bytes 32)
  (b : OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))) (L : List TG)

/-- The Lean client as a blind-preimage client. -/
noncomputable abbrev CC := toClient CrtGen.tables lr ℓ (leanClient CrtGen.tables lr)

/-- The target oracle's initial reduced state. -/
def s0 : HTS := (fun _ => none, (L, fun _ => none, 0))

/-- **The blinding forger's composed computation** (`blindAdv`'s, for fixed coins). -/
noncomputable def gameA : OracleComp (specA (WB AR) ByteArray TG TG SIss) (List (ByteArray × SIss) × Bool) := do
  let z ← (simulateQ (blindImpl (CC lr ℓ) n pk κ) b).run (bs0 (CC lr ℓ).init)
  let f ← simulateQ liftV ((CC lr ℓ).post pk κ z.2.cs (claimed z))
  pure ((claimed z).map fun e => (e.1, e.2.2.2.2), f)

/-- `B`'s phase with the target oracle, one handler. -/
noncomputable def phaseB : OracleComp (ofFn (WB AR)) (List (X' × SIss) × BS PSt X' Hn') :=
  (simulateQ (combH pre' CrtGen.tables lr ℓ (leanClient CrtGen.tables lr) n pk κ) b).run
    (bs0 (CC lr ℓ).init, s0 L)

/-- A hash query in the game's world. -/
def toW : QueryImpl spec (OracleComp (ofFn (WB AR))) := fun d => liftM ((ofFn (WB AR)).query (.inr d))

/-- **The grinding prefix of the `p`-th claimed session**, reached without `H₂³` queries: `B`'s
phase, then step 2's prefix (`preGQ`) of that session with `B`'s preimage. -/
noncomputable def pfxB (p : ℕ) : OracleComp (ofFn (WB AR)) ByteArray := do
  let r ← phaseB lr ℓ n pk pre' κ b L
  match (claimed (r.1, r.2.1))[p]? with
  | none => pure ByteArray.empty
  | some e => simulateQ toW (preGQ (pomStmt pk lr e.2.2.2.1 e.2.2.1.2.2.1 e.2.2.1.2.2.2)
      e.2.2.1.2.1 (zeroPre ++ toBA (e.2.2.2.2.getD [])))

omit [DecidableEq DR] in
lemma eval_toW (G : (d : DR ⊕ Dom) → WB AR d) {α : Type} (oc : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn G) (simulateQ toW oc) =
      evalWithAnswerFn (QueryImpl.ofFn (gHof G)) oc := by
  induction oc using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind]
    erw [evalWithAnswerFn_liftM_query]
    exact ih _

omit [DecidableEq DR] in
lemma eval_gameW (G : (d : DR ⊕ Dom) → WB AR d) :
    evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (gameA lr ℓ n pk κ b)).run (s0 L)) =
      let r := evalWithAnswerFn (QueryImpl.ofFn G) (phaseB lr ℓ n pk pre' κ b L)
      let r' := evalWithAnswerFn (QueryImpl.ofFn G) ((simulateQ (htH pre') (simulateQ
        (liftV (AR := AR) (S := SIss)) ((CC lr ℓ).post pk κ r.2.1.cs (claimed (r.1, r.2.1))))).run r.2.2)
      (((claimed (r.1, r.2.1)).map fun e => (e.1, e.2.2.2.2), r'.1), r'.2) := by
  simp only [gameA, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]
  rw [collapseH]
  simp only [evalWithAnswerFn_map, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, phaseB]

end Game

end VoleMole.Assumptions.BlindPomfrit
