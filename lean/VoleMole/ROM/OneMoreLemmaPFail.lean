import VoleMole.ROM.OneMoreLemmaPOrder
import VoleMole.ROM.OneMoreLemmaPQueries

/-!
# A failed forgery is a bad event of the derived prover's adaptive game, table by table

`lean/docs/security/pomfrit.md` §6.4 (gap G8). For Lemma P's `E₁` (`e1P`): if forgery `i` of the
one-more game (at a hash table `g`, cipher table `E`, key and target stream) is accepted and its
claim is not a preimage of its programmed target (`PFail`), then in the adaptive extraction game of
the derived prover `proverP … i` (`ROM/OneMoreLemmaPIC.lean`, which reaches the cipher only by
queries) at the same tables one of these holds (`pfail_events`):

* the verifier accepts and Lemma P's extraction fails (`MajorExtracted`, the event of
  `pomfritT_accept_le_major`);
* Post (`PostOut`), a cipher query of the prover that hits an earlier commitment target;
* the verifier accepts, but its `H₂³` input is not in the prover's log (`prEvent_zUnqueried_le_A`);
* a query of the game's log is a chain hit (`chainHitL`) or an **order hit** (`orderHitL`): an
  `H₂¹` answer that equals the `chal1` field of an earlier marker query `H₃(x)` of the reduction,
  i.e. the forger queried `H_T(x)` before the `H₂¹` query whose answer is `x`'s `chal1` (Lemma P's
  ordering step fails).

The proof: the derived prover outputs the forgery's proof and statement (`eval_proverP`); its log is
the forger's log followed by the verification queries (`log_proverP`), which make no `H₂³` query
(`not_mem_hashLog_contP`). If the verifier's `H₂³` input is in the prover's log it is in the
forger's, and so is the verifier's `H₂¹` input (`mem_x_of_mem_z`, no hits); then the game's
extraction from the forger's log is the derived game's (`keysOf_knownOf_prefix`, no Post), the alive
trees are known (`aliveR_subset_known`), and the hint is the widest group's prefix (`e1P_eq_major`)
unless the forger asked `H_T(x)` first (an order hit). Lemma P's extraction then gives a preimage of
the programmed target, so the claim is good.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The order hit -/

/-- **An order hit at the `H₂¹` cell `t`**: its answer is the `chal1` field of an earlier marker
query `H₃(x)` in the log `Lg g`. -/
def orderHitL (Lg : Table → QueryLog spec) (t : Dom) (g : Table) : Prop :=
  t.1 = .h21 ∧ (g t).ba ∈ (kindIns .h3 ((logBefore t (Lg g)).map Sigma.fst)).map xChal1

/-- The combination of PomFRIT's statements (the hits' `chal2` targets). -/
def cbP : Option (ℕ × ByteArray) := some (45, dstP)

lemma pomfritRedeemT_binder1 (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (lr : Bool) : (pomfritRedeemT pk h b1 b2 lr).binder1 = b1 := rfl

lemma stG_binder1 (lr : Bool) (pk : UovPk) (s : TG × ByteArray × ByteArray) :
    (stG lr pk s).binder1 = s.2.1 := rfl

lemma stG_params (lr : Bool) (pk : UovPk) (s : TG × ByteArray × ByteArray) :
    (stG lr pk s).params = pomfritParams lr := rfl

lemma stG_mu1 (lr : Bool) (pk : UovPk) (s : TG × ByteArray × ByteArray) (Hs : Hashes) :
    (stG lr pk s).mu1 Hs = Hs.hash .muDelayed muCell.2 :=
  mu1_pomfritRedeemT pk _ _ _ lr Hs

/-! ## `chal1` of an accepted proof -/

/-- **An accepted proof's `chal1` is the verifier's steps up to `chal1`** (`chal1Pre`), at any
statement with the same parameters, `mu₁` and `binder₁`. -/
lemma chal1Pre_of_accept [HasPrg] (g : Table) (T : CrtTables) {st st' : Statement}
    (hp : st'.params = st.params) (hmu : st'.mu1 (Hashes.ofTable g) = st.mu1 (Hashes.ofTable g))
    (hb : st'.binder1 = st.binder1) {π : ByteArray}
    (hacc : (verify (Hashes.ofTable g) T st π).accept = true) :
    evalWithAnswerFn (QueryImpl.ofFn g) (chal1Pre st' π) =
      some (verify (Hashes.ofTable g) T st π).chal1 := by
  obtain ⟨hf, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨-, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  rw [evalWithAnswerFn_chal1Pre, hp, hmu, hb]
  rw [hf]
  simp only [Bool.true_eq_false, ite_false]
  rw [hr, hc1]
  rfl

/-! ## The outputs of the two derived provers -/

section Outputs

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (i : ℕ)

/-- `proverI`'s cipher log is the forger's. -/
lemma cipherLog_proverI :
    cipherLog (tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)) =
      cipherLog (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1 := by
  unfold proverI
  rw [tableQueryLog_bind, tableQueryLog_map', cipherLog_append, cipherLog_htIC, List.append_nil,
    log_forger, List.nil_append]

/-- The extractor's keys and known trees of an adaptive game's output. -/
lemma gameA_keys_known {ι β : Type} (stF : ι → Statement) (P : OracleComp specIC (ByteArray × (ι × β))) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).2.1.keys =
        keysOf (cipherLog (jOf g P E)) E (ivE g (stF (sA g P E)) P E)
          (Proof.opening ⟨(stF (sA g P E)).params, πOf g P E⟩)
          (Proof.delta ⟨(stF (sA g P E)).params, πOf g P E⟩) ∧
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).2.1.known =
        knownOf (cipherLog (jOf g P E)) E (ivE g (stF (sA g P E)) P E)
          (Proof.opening ⟨(stF (sA g P E)).params, πOf g P E⟩) := by
  rw [evalWithAnswerFn_gameA]
  exact ⟨gameIC_keys T _ P E g, gameIC_known T _ P E g⟩

/-- The derived prover outputs the `i`-th forgery's proof and binders. -/
lemma out_proverP :
    let b0 := evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none))
    let ms := b0.1.getD i (ByteArray.empty, ByteArray.empty)
    let p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre A Lst i)
    p.1 = sProof lr ms.2 ∧ p.2.1.2 = (sB1 lr ms.2, sB2 lr ms.2) := by
  intro b0 ms p
  have hp : p = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk b0.2.1 ms
      (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        (verPreAll lr pk b0.2.1 (b0.1.take i) (b0.2.2.1, b0.2.2.2)))) := by
    simp only [p, proverP, evalWithAnswerFn_bind]
    rfl
  rw [hp]
  unfold verLastIC
  simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
  cases c1T g lr E pk ms.2 with
  | none => simp
  | some c1 => simp

/-- The auxiliary output of an adaptive game is the prover's. -/
lemma gameA_aux {ι β : Type} (stF : ι → Statement) (P : OracleComp specIC (ByteArray × (ι × β))) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).2.1.aux.1 =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2 := by
  rw [evalWithAnswerFn_gameA]
  simp only [gameIC, evalWithAnswerFn_game]
  rw [proverIC_aux]

end Outputs

/-! ## The per-table implication -/

section Fail

variable (g : Table) (lr : Bool) (E : CTable) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (ℓ i : ℕ)

/-- The derived prover's adaptive game. -/
noncomputable abbrev gameP : OracleComp spec (Out (((TG × ByteArray × ByteArray) × AuxP) ×
    QueryLog specIC)) :=
  gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst i) E

set_option maxHeartbeats 1600000 in
/-- **A failed forgery is a bad event of the derived prover's game, table by table** (Lemma P's
`E₁`, a 32-byte key digest). -/
theorem pfail_events (hd : pk.digest.size = 32)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1P lr E) tgts1 pk ℓ A)).run (hs0 Lst)))) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameP lr E pk pre A Lst i)
    (r.2.2.accept = true ∧ ¬MajorExtracted E (stG lr pk (stOut r))
      (witKT pk hG (some (stOut r))) r) ∨
    PostOut E r ∨
    (r.2.2.accept = true ∧ ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2) ∨
    ∃ e ∈ tableQueryLog (gameP lr E pk pre A Lst i) g,
      chainHitL cbP (tableQueryLog (gameP lr E pk pre A Lst i)) e.1 g ∨
        orderHitL (tableQueryLog (gameP lr E pk pre A Lst i)) e.1 g := by
  classical
  intro r
  let _ : HasPrg := icPrg E.cipher
  set T := CrtGen.tables
  set P := proverP lr pk pre A Lst i with hPdef
  set PI := proverI T lr E (e1P lr E) pk pre A Lst i with hPIdef
  obtain ⟨haccI, hnp⟩ := pfail_table g T lr E (e1P lr E) pk pre A Lst ℓ i h
  set rI := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T (stG lr pk) PI E) with hrI
  -- the two derived provers
  obtain ⟨ep1, ep2, ep3⟩ := eval_proverP g T lr E (e1P lr E) pk pre A Lst i
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
  have hlogA : tableQueryLog (gameP lr E pk pre A Lst i) g = gLog T st P E g :=
    tableQueryLog_gameA _ _ _ _ _
  have hh : NoHit (gameIC T st P E) (chainHit T st P E) g := by
    intro e he hc
    exact (hhit e (by rw [hlogA]; exact he)).1 (by
      show (g e.1).ba ∈ hitTargets cbP (logBefore e.1 (tableQueryLog (gameP lr E pk pre A Lst i) g))
        e.1.1
      rw [hlogA]; exact hc)
  have hkp : KeysPre st E (jOf g P E) (gLog T st P E g) g :=
    keysPre_of_not_postOut T st P E g (by rw [← hrg]; exact hpost)
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
    ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb0
  set b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr (e1P lr E) pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb
  have hinv0 : InvH (e1P lr E) (hs0 Lst) (hs0 Lst) (fun _ => none) :=
    ⟨SameT.refl _, fun x a e hx => by simp [hs0] at hx⟩
  obtain ⟨-, eL, -, -⟩ := eval_wrapIC_hint g E lr (e1P lr E) pre (A pk) [] _ _ _ hinv0
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
    exact aliveR_subset_known T st P E g hh (by rw [← hrg]; exact hpost) (by rw [← hrg]; exact hacc)
      hrec' hx1J
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
  have he : rI.2.1.aux.1.2 = e1P lr E Lx x := by
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
  -- the hint is the widest group's prefix
  have hme := e1P_eq_major T st lr P E g (stG_params lr pk _) (stG_mu1 lr pk _) hh hkp
    (by rw [← hrg]; exact hacc) hrec' hPfxJ hord (by rw [← hrg]; exact hxc)
    (by rw [hxd])
  rw [← hrg, ← hLx] at hme
  -- Lemma P's extraction gives a preimage of the programmed target: the claim is good
  have hso : stOut r = sA g P E := o2
  obtain ⟨t, ht, hwit, hmajt⟩ := hmaj
  have hcand : @candOut (icPrg E.cipher) _ (stG lr pk (stOut rI)) rI t =
      @candOut (icPrg E.cipher) _ (stG lr pk (stOut r)) r t := by
    unfold candOut outChain
    rw [hst, hr1, hkI, hr3]
  have he' : rI.2.1.aux.1.2 = toTG (preB (@candOut (icPrg E.cipher) _ (stG lr pk (stOut r)) r t)) := by
    rw [he, hme, hso]
    rw [hso] at hmajt
    rw [hmajt, Option.getD_some]
  refine hnp t (hnI ▸ halk ht) ?_
  rw [hcand, ← hst]
  have hrel := pomRel_of_wit pk (encT (stOut r).1) (encT_size _) _ hwit
  obtain ⟨hlr, -, hls, heval⟩ := hrel
  refine ⟨hls, ?_⟩
  rw [heval, he']
  exact (toL_encT_add_toTG _ _ hlr).symm

end Fail

end VoleMole.ROM.OneMore.Pomfrit
