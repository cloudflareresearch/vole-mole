import VoleMole.ROM.OneMoreClsOrder

/-!
# A failed forgery of U1^cls is a bad event of the derived game, table by table

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). `pfail_events` (`ROM/OneMoreLemmaPFail.lean`)
with the class extractor: for the hint `E₁^cls` (`e1C`) and a forger whose log covers the decoder
(`CovL`; the wrapped forger `wrapE` has one, `eval_wrapE`), a failed forgery `i` gives, in the
adaptive game of the derived prover `proverP … i`, one of: the verifier accepts, the prover's log
covers the decoder and Lemma P^cls's extraction fails (`ClsCovered`, `ClsExtracted`: the event of
`pomfritT_accept_le_cls`); Post; the verifier's `H₂³` input unqueried; a chain hit or an order hit
(`clsFail_events`). The proof is `pfail_events`'s with the ordering step `e1C_eq_cls`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-- **Covering the decoder is prefix-closed.** -/
lemma CovL_prefix (lr : Bool) (E : CTable) (g : Table) {L Pfx : QueryLog specIC} (h : CovL lr E g L)
    (hP : Pfx <+: L) : CovL lr E g Pfx := by
  intro x1 hx inp hinp
  obtain ⟨V, hV⟩ := hP
  have hm : (.inl (.h21, x1) : DomIC) ∈ Pfx.map Sigma.fst := mem_hashLog.1 hx
  have hlb : logBefore (.inl (.h21, x1)) L = logBefore (.inl (.h21, x1)) Pfx := by
    rw [← hV, logBefore_append_of_mem _ hm]
  have hxL : ((.h21, x1) : Dom) ∈ hashLog L := by
    rw [← hV]; unfold hashLog; rw [List.filterMap_append]; exact List.mem_append_left _ hx
  have := h x1 hxL inp (by rw [hlb]; exact hinp)
  rwa [hlb] at this

section Fail

variable (g : Table) (lr : Bool) (E : CTable) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (ℓ i : ℕ)

set_option maxHeartbeats 1600000 in
/-- **A failed forgery of U1^cls is a bad event of the derived prover's game, table by table**
(`E₁^cls`, a 32-byte key digest, a forger whose log covers the decoder), for any failure event `cf`
outside which `KeysPre` holds (Post: the PRF view's `PostOut` in `clsFail_events`, the point-tied
`PostPOut` in the permutation model): the verifier accepts, the prover's log covers the decoder and
Lemma P^cls's extraction fails (the event of `pomfritT_accept_le_cls`); `cf`; the verifier's `H₂³`
input unqueried; a chain hit or an order hit. -/
theorem clsFail_events_of
    (cf : Out (((TG × ByteArray × ByteArray) × AuxP) × QueryLog specIC) → Prop)
    (hcf : ∀ s g', ¬cf (evalWithAnswerFn (QueryImpl.ofFn g')
        (gameIC CrtGen.tables (stG lr pk s) (proverP lr pk pre A Lst i) E)) →
      KeysPre (stG lr pk s) E (jOf g' (proverP lr pk pre A Lst i) E)
        (gLog CrtGen.tables (stG lr pk s) (proverP lr pk pre A Lst i) E g') g')
    (hd : pk.digest.size = 32)
    (hcovA : CovL lr E g (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst)))) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i)
    (r.2.2.accept = true ∧ ClsCovered E (stG lr pk (stOut r)) CrtGen.tables r ∧
      ¬ClsExtracted E (stG lr pk (stOut r)) CrtGen.tables (witKT pk hG (some (stOut r))) r) ∨
    cf r ∨
    (r.2.2.accept = true ∧ ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2) ∨
    ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i) g,
      chainHitL cbP (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g ∨
        orderHitL (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g := by
  classical
  intro r
  let _ : HasPrg := icPrg E.cipher
  set T := CrtGen.tables
  set P := proverP lr pk pre A Lst i with hPdef
  set PI := proverI T lr E (e1C lr E) pk pre A Lst i with hPIdef
  obtain ⟨haccI, hnp⟩ := pfail_table g T lr E (e1C lr E) pk pre A Lst ℓ i h
  set rI := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T (stG lr pk) PI E) with hrI
  -- the two derived provers
  obtain ⟨ep1, ep2, ep3⟩ := eval_proverP g T lr E (e1C lr E) pk pre A Lst i
  set p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) P with hp
  set q := evalWithAnswerFn (QueryImpl.ofFn (join g E)) PI with hq
  obtain ⟨o1, o2, o3⟩ := gameA_out T (stG lr pk) P E g
  obtain ⟨oI1, oI2, oI3⟩ := gameA_out T (stG lr pk) PI E g
  have hr1 : r.1 = rI.1 := by rw [o1, oI1]; exact ep1
  have hst : stOut r = stOut rI := by rw [o2, oI2]; exact ep2
  have hsA : sA g P E = sA g PI E := ep2
  have hπ : πOf g P E = πOf g PI E := ep1
  have hr3 : r.2.2 = rI.2.2 := by rw [o3, oI3, ep1, ep2]
  set st := stG lr pk (sA g P E) with hstdef
  -- by contradiction
  by_contra hcon
  simp only [not_or, not_and, not_not, not_exists] at hcon
  obtain ⟨hmaj, hpost, hzq, hhit⟩ := hcon
  have hacc : r.2.2.accept = true := by rw [hr3]; exact haccI
  have hmaj := hmaj hacc
  have hz := hzq hacc
  -- the fixed game
  have hrg : r = evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) := evalWithAnswerFn_gameA _ _ _ _ _
  have hlogA : tableQueryLog (gameDP lr E pk pre A Lst i) g = gLog T st P E g :=
    tableQueryLog_gameA _ _ _ _ _
  have hh : NoHit (gameIC T st P E) (chainHit T st P E) g := by
    intro e he hc
    exact (hhit e (by rw [hlogA]; exact he)).1 (by
      show (g e.1).ba ∈ hitTargets cbP (logBefore e.1 (tableQueryLog (gameDP lr E pk pre A Lst i) g))
        e.1.1
      rw [hlogA]; exact hc)
  have hkp : KeysPre st E (jOf g P E) (gLog T st P E g) g :=
    hcf _ g (by rw [← hrg]; exact hpost)
  have haccv : (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true := by
    have h' := hacc
    rw [o3] at h'
    exact h'
  obtain ⟨hf, leaves, hrec, -⟩ := (accept_iff _ T st (πOf g P E)).1 haccv
  have hrec' : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E)
      (Proof.opening ⟨st.params, πOf g P E⟩) (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves :=
    hrec
  -- the logs
  set b0 := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb0
  set b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr (e1C lr E) pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb
  have hinv0 : InvH (e1C lr E) (hs0 Lst) (hs0 Lst) (fun _ => none) :=
    ⟨SameT.refl _, fun x a e hx => by simp [hs0] at hx⟩
  obtain ⟨-, eL, -, -⟩ := eval_wrapIC_hint g E lr (e1C lr E) pre (A pk) [] _ _ _ hinv0
  set L := b0.2.1 with hLdef
  set V := tableQueryLog (contP lr pk i b0) (join g E) with hVdef
  have hJ : jOf g P E = L ++ V := log_proverP g lr E pk pre A Lst i
  have hLJ : L <+: jOf g P E := ⟨V, hJ.symm⟩
  -- the verifier's `H₂³` input, then its `H₂¹` input, are in the forger's log
  have hzL : ((.h23, runZ st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves
      (fun _ _ => ByteArray.empty))) : Dom) ∈ hashLog L := by
    have hz' : ((.h23, zOut st r) : Dom) ∈ hashLog (jOf g P E) := by
      have := hz
      rw [o2, show r.2.1.aux.2 = jOf g P E from by rw [hrg]; exact aux_gameIC T st P E g] at this
      exact this
    have hze : zOut st r = runZ st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (fun _ _ => ByteArray.empty)) := by
      rw [hrg, gameIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map,
        evalWithAnswerFn_verifyQ, proverIC_fst]
      exact zOut_eq_runZ _ T st _ _ haccv hrec _
    rw [hze, hJ] at hz'
    unfold hashLog at hz'
    rw [List.filterMap_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · exact hz'
    · exact absurd hz' (not_mem_hashLog_contP lr pk i b0 (join g E) _)
  have hx1L := mem_x_of_mem_z T st P E g hh _ haccv hrec' hLJ hzL
  set x1 := runX (Hashes.ofTable g) st (πOf g P E) leaves with hx1def
  -- the extraction from the forger's log is the derived game's
  obtain ⟨hkeysL, hknownL⟩ := keysOf_knownOf_prefix T st P E g hh hkp haccv hrec' hLJ hx1L
  have hcI : cipherLog (jOf g PI E) = cipherLog L := by
    rw [jOf, cipherLog_proverI, ← hb, eL]
  have hivI : ivE g (stG lr pk (sA g PI E)) PI E = ivE g st P E := by
    simp only [ivE, hstdef, hsA, hπ]
  obtain ⟨kP, nP⟩ := gameA_keys_known g T E (stG lr pk) P
  obtain ⟨kI, nI⟩ := gameA_keys_known g T E (stG lr pk) PI
  have hkI : rI.2.1.keys = r.2.1.keys := by
    rw [kI, kP, hcI, hivI, ← hsA, ← hπ, ← hkeysL]
  have hnI : rI.2.1.known = r.2.1.known := by
    rw [nI, nP, hcI, hivI, ← hsA, ← hπ, ← hknownL]
  -- the alive trees are known
  have hx1J : ((.h21, x1) : Dom) ∈ hashLog (jOf g P E) := by
    rw [hJ]; unfold hashLog; rw [List.filterMap_append]; exact List.mem_append_left _ hx1L
  have halk : aliveR E r ⊆ r.2.1.known := by
    rw [hrg]
    exact aliveR_subset_known_of T st P E g cf (hcf _) hh (by rw [← hrg]; exact hpost)
      (by rw [← hrg]; exact hacc) hrec' hx1J
  -- the `i`-th forgery's data
  set ms := b0.1.getD i (ByteArray.empty, ByteArray.empty) with hms
  obtain ⟨hout1, hout2⟩ := out_proverP g lr E pk pre A Lst i
  obtain ⟨haux0, haux⟩ := aux_proverP g lr E pk pre A Lst i
  have hπms : πOf g P E = sProof lr ms.2 := hout1
  have h2 : p.2.1.2 = (sB1 lr ms.2, sB2 lr ms.2) := hout2
  have hb1 : st.binder1 = sB1 lr ms.2 := by
    rw [hstdef, stG_binder1]
    have h3 : (sA g P E).2.1 = p.2.1.2.1 := rfl
    rw [h3, h2]
  have e0 : r.2.2 = verify (Hashes.ofTable g) T st (πOf g P E) := o3
  have hc1T : c1T g lr E pk ms.2 = some r.2.2.chal1 := by
    rw [e0]
    unfold c1T
    rw [← hπms]
    exact chal1Pre_of_accept (st := st)
      (st' := pomfritRedeemT pk (fun _ => ByteArray.empty) (sB1 lr ms.2) (sB2 lr ms.2) lr) g T
      (by rw [pomfritRedeemT_params, hstdef, stG_params])
      (by rw [mu1_pomfritRedeemT, hstdef, stG_mu1])
      (by rw [hb1, pomfritRedeemT_binder1]) haccv
  obtain ⟨x, Lx, hpx⟩ : ∃ x Lx, p.2.2 = some (x, Lx) := by
    cases hpa : p.2.2 with
    | none => rw [haux0 hpa] at hc1T; cases hc1T
    | some xl => exact ⟨xl.1, xl.2, rfl⟩
  obtain ⟨c1, Pfx, hc1, hx, hLx, hpre⟩ := haux x Lx hpx
  rw [hc1T] at hc1
  cases hc1
  have hc1s : r.2.2.chal1.size = 136 := by
    rw [e0]
    obtain ⟨-, hc1v⟩ := verify_iv_chal1 _ T st (πOf g P E) haccv hrec
    rw [hc1v]
    exact Prob.Bytes.size_ba _
  have hsz : (ms.2.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes := by
    have := size_of_checkFormat hf
    rwa [hπms] at this
  have hxc : xChal1 x = r.2.2.chal1 := by rw [hx]; exact xChal1_tgtIn hd hc1s
  have hxd : xDpre x = (Proof.correction ⟨st.params, πOf g P E⟩).extract 0 45 := by
    rw [hx, xDpre_tgtIn hd hc1s hsz, hπms]; rfl
  -- the hint the game stored at `x`
  have he : rI.2.1.aux.1.2 = e1C lr E Lx x := by
    rw [hrI, gameA_aux, ← hq, ep3, hpx]; rfl
  have hPfxJ : Pfx <+: jOf g P E := by
    rcases hpre with h1 | h1
    · exact (hLx ▸ List.prefix_append Pfx _).trans (h1.trans hLJ)
    · rw [h1]; exact hLJ
  -- the forger's log in the game's log
  obtain ⟨rest, hG0⟩ := gLog_eq_hashEnt_append T st P E g
  have hGL : gLog T st P E g = hashEnt L ++ (hashEnt V ++ rest) := by
    rw [hG0, hJ, hashEnt_append, List.append_assoc]
  have hcons : ∀ e ∈ gLog T st P E g, e = ⟨e.1, g e.1⟩ := gLog_answer T st P E g
  have hx1H : ((.h21, x1) : Dom) ∈ (hashEnt L).map Sigma.fst := mem_hashEnt_iff.2 hx1L
  have hc1g : xChal1 x = (g (.h21, x1)).ba := by
    rw [hxc, e0]
    obtain ⟨-, hc1v⟩ := verify_iv_chal1 _ T st (πOf g P E) haccv hrec
    rw [hc1v]
    rfl
  -- the ordering step
  have hord : (.h21, x1) ∈ hashLog Pfx := by
    cases hxo : x1Of Pfx x with
    | some w =>
      obtain ⟨e, he, he1, hea⟩ := firstIn_some hxo
      have heG : e ∈ gLog T st P E g := by
        rw [hGL]
        obtain ⟨R, hR⟩ := hPfxJ
        have : e ∈ hashEnt (jOf g P E) := by
          rw [← hR, hashEnt_append]; exact List.mem_append_left _ he
        rw [hJ, hashEnt_append] at this
        rw [← List.append_assoc]
        exact List.mem_append_left _ this
      have hwG : ((.h21, w) : Dom) ∈ (gLog T st P E g).map Sigma.fst :=
        List.mem_map.2 ⟨e, heG, he1⟩
      have hxG : ((.h21, x1) : Dom) ∈ (gLog T st P E g).map Sigma.fst := by
        rw [hGL, List.map_append]; exact List.mem_append_left _ hx1H
      have hans : (g (.h21, w)).ba = (g (.h21, x1)).ba := by
        rw [← hc1g, ← hea]
        have := hcons e heG
        obtain ⟨⟨k, w'⟩, u⟩ := e
        simp only [Prod.mk.injEq] at he1
        obtain ⟨rfl, rfl⟩ := he1
        rw [this]
      have hwx := cell_eq_of_noHit T st P E hh hwG hxG rfl (Or.inr (Or.inl rfl)) hans
      have : w = x1 := congrArg Prod.snd hwx
      subst this
      exact mem_hashEnt_iff.1 (List.mem_map.2 ⟨e, he, he1⟩)
    | none =>
      exfalso
      have hnP : ((.h21, x1) : Dom) ∉ hashLog Pfx := by
        intro hP
        have := firstIn_isSome (k := .h21) (ok := fun _ => true) (a := xChal1 x)
          (e := ⟨(.h21, x1), g (.h21, x1)⟩)
          (exists_entry (fun e he => hcons e (by
            rw [hGL]; obtain ⟨R, hR⟩ := hPfxJ
            have : e ∈ hashEnt (jOf g P E) := by
              rw [← hR, hashEnt_append]; exact List.mem_append_left _ he
            rw [hJ, hashEnt_append] at this
            rw [← List.append_assoc]
            exact List.mem_append_left _ this)) (mem_hashEnt_iff.2 hP)) rfl rfl hc1g.symm
        have hx' : x1Of Pfx x = firstIn .h21 (fun _ => true) (xChal1 x) (hashEnt Pfx) := rfl
        rw [← hx', hxo] at this
        simp at this
      rcases hpre with hpre | hpre
      · -- the forger asked `H_T(x)` before `x₁`: an order hit
        obtain ⟨R, hR⟩ := hpre
        have hR' : L = Lx ++ R := hR.symm
        have hnA : ((.h21, x1) : Dom) ∉ (hashEnt (axT g lr Pfx x)).map Sigma.fst := by
          rw [axT_of_none g lr hxo]; simp [hashEnt, muCell]
        have hnLx : ((.h21, x1) : Dom) ∉ (hashEnt Lx).map Sigma.fst := by
          rw [hLx, hashEnt_append, List.map_append, List.mem_append, not_or]
          exact ⟨fun h' => hnP (mem_hashEnt_iff.1 h'), hnA⟩
        have hmark : ((.h3, x) : Dom) ∈ (hashEnt Lx).map Sigma.fst := by
          rw [hLx, hashEnt_append, List.map_append, axT_of_none g lr hxo]
          simp [hashEnt]
        have hbef : ((.h3, x) : Dom) ∈ (logBefore (.h21, x1) (gLog T st P E g)).map Sigma.fst := by
          rw [hGL, logBefore_append_of_mem _ hx1H, hR', hashEnt_append,
            logBefore_append_of_not_mem _ hnLx, List.map_append]
          exact List.mem_append_left _ hmark
        have hxG : ((.h21, x1) : Dom) ∈ (gLog T st P E g).map Sigma.fst := by
          rw [hGL, List.map_append]; exact List.mem_append_left _ hx1H
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hxG
        refine (hhit e (by rw [hlogA]; exact he)).2 ⟨by rw [he1], ?_⟩
        rw [hlogA, he1, ← hc1g]
        exact List.mem_map.2 ⟨x, mem_kindIns hbef, rfl⟩
      · -- the target query at a verification: `Pfx` is the whole forger's log
        exact hnP (hpre ▸ hx1L)
  -- the hint is the class extractor's output, and the prover's log covers the decoder
  have hsz' : (πOf g P E).size = (pomfritParams lr).proofBytes := by
    rw [hπms]; exact hsz
  have hxu : xU x = Proof.voleCheck ⟨st.params, πOf g P E⟩ := by
    rw [hx, xU_tgtIn hd hc1s hsz, hπms]; rfl
  have hPfxL : Pfx <+: L := by
    rcases hpre with h1 | h1
    · exact (hLx ▸ List.prefix_append Pfx _).trans h1
    · exact h1 ▸ List.prefix_refl _
  have hcovP : CovL lr E g Pfx := CovL_prefix lr E g hcovA hPfxL
  obtain ⟨hme, hcovr⟩ := e1C_eq_cls lr pk P E g (sA g P E) hh hkp (by rw [← hrg]; exact hacc) hrec'
    hPfxJ hord hcovP (by rw [← hrg]; exact hxc) (by rw [hxd]) hxu
  rw [← hrg, ← hLx] at hme
  rw [← hrg] at hcovr
  -- Lemma P^cls's extraction gives a preimage of the programmed target: the claim is good
  have hso : stOut r = sA g P E := o2
  have hcls := hmaj (by rw [hso]; exact hcovr)
  rw [hso, clsExtracted_iff] at hcls
  obtain ⟨t, ht, hwit, hclst⟩ := hcls
  have hcand : @candOut (icPrg E.cipher) _ (stG lr pk (stOut rI)) rI t =
      @candOut (icPrg E.cipher) _ (stG lr pk (stOut r)) r t := by
    unfold candOut outChain
    rw [hst, hr1, hkI, hr3]
  have he' : rI.2.1.aux.1.2 = toTG (preB (@candOut (icPrg E.cipher) _ (stG lr pk (stOut r)) r t)) := by
    rw [he, hme, hso, hclst, Option.getD_some]
    rfl
  refine hnp t (hnI ▸ halk ht) ?_
  rw [hcand, ← hst]
  have hrel := pomRel_of_wit pk (encT (stOut r).1) (encT_size _) _ (by rw [hso]; exact hwit)
  obtain ⟨hlr, -, hls, heval⟩ := hrel
  refine ⟨hls, ?_⟩
  erw [heval]
  rw [he']
  exact (toL_encT_add_toTG _ _ hlr).symm

/-- **A failed forgery of U1^cls is a bad event of the derived prover's game, table by table**
(`E₁^cls`, a 32-byte key digest, a forger whose log covers the decoder): the verifier accepts, the
prover's log covers the decoder and Lemma P^cls's extraction fails (the event of
`pomfritT_accept_le_cls`); Post; the verifier's `H₂³` input unqueried; a chain hit or an order
hit. -/
theorem clsFail_events (hd : pk.digest.size = 32)
    (hcovA : CovL lr E g (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst)))) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i)
    (r.2.2.accept = true ∧ ClsCovered E (stG lr pk (stOut r)) CrtGen.tables r ∧
      ¬ClsExtracted E (stG lr pk (stOut r)) CrtGen.tables (witKT pk hG (some (stOut r))) r) ∨
    PostOut E r ∨
    (r.2.2.accept = true ∧ ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2) ∨
    ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i) g,
      chainHitL cbP (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g ∨
        orderHitL (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g :=
  clsFail_events_of g lr E pk pre A Lst ℓ i (PostOut E)
    (fun _ g' h => keysPre_of_not_postOut CrtGen.tables _ _ E g' h) hd hcovA h

end Fail

end VoleMole.ROM.OneMore.Pomfrit
