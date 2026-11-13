import VoleMole.ROM.OneMoreShiftTable
import VoleMole.ROM.LemmaPSome

/-!
# U2's shift rule, and a failed forgery of U2 as a bad event of the derived game, table by table

`lean/docs/security/pomfrit.md` §6.2, §6.4 (gap G8). Theorem U2's reduction submits, with each
target request at `x`, the prefixes of **all** alive trees as shifts (the paper's `{r^{(i)}}`).

* **The shift rule** (`shP`, `hintS`): from the log at `x`'s first target query, as Lemma P's
  `E₁` (`e1P`): the first `H₂¹` preimage `x₁` of `x`'s `chal1`, the trees with no committed dead
  leaf at `x₁` and their candidates' prefixes `u ⊕ d`, in tree order; at most `17`
  (`hintS = hint2 17 shP`).
* **The ordering step** (`shP_eq_alive`): if the log before `x`'s first target query holds the
  verifier's `H₂¹` input, the shifts are the prefixes of the alive trees at the end, with the
  extractor's candidates (the proof of `e1P_eq_major`, with the list of all prefixes in place of the
  widest group's).
* **The per-table implication** (`shiftFail_events`): if forgery `i` of U2's game fails
  (`ShiftFailZ`: accepted, but its claim is a preimage of no shifted target), then in the adaptive
  game of the derived prover `proverP … i` (the same as for U1: it reads neither hints nor targets)
  one of these holds: the verifier accepts and **no alive tree extracts** (`SomeExtracted`, the
  event of `pomfritT_accept_le_some`, with no `Shift` term); Post; the verifier's `H₂³` input
  unqueried; a chain hit or an order hit. The proof is `pfail_events`'s, with `ver_tableG` for the
  game's side.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The shift rule -/

section Shift

/-- **U2's shift rule** on the log `L` at the target input `x` (`pomfrit.md` §6.2): the first `H₂¹`
preimage `x₁` of `x`'s `chal1` in `L` (no shift if none); the data committed at `x₁` (as `e1P`);
the trees with no committed dead leaf; their candidates' prefixes (`u ⊕ d`, `d[0..M)` from `x`), in
tree order. -/
noncomputable def shP (lr : Bool) (E : CTable) (L : QueryLog specIC) (x : ByteArray) : List TG :=
  match x1Of L x with
  | none => []
  | some x1 =>
    letI : HasPrg := VoleMole.ZK.Sim.icPrg E.cipher
    let Gx := logBefore (.h21, x1) (hashEnt L)
    let Jx := logBefore (.inl (.h21, x1)) L
    let pc := preCore (stE lr) E Gx Jx x1 (tableOfLog (hashEnt L))
    let alive := Finset.univ.filter fun i => deadPre E Gx Jx pc.iv x1 i = ∅
    let pcd : Verifier.Bridge.Chain :=
      { pc with proof := pc.proof ++ zerosBA 64 ++ xDpre x ++ zerosBA 119 }
    ((List.finRange BAVC.tau).filter (· ∈ alive)).map fun i =>
      toTG (preB (EndToEnd.candidate (F := GF128) (pcd.u (stE lr)) (pcd.dc (stE lr)) i))

lemma length_shP_le (lr : Bool) (E : CTable) (L : QueryLog specIC) (x : ByteArray) :
    (shP lr E L x).length ≤ BAVC.tau := by
  unfold shP
  split
  · simp
  · simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)

/-- **U2's hint rule**: the shifts of `shP`, at most `τ = 17` (one per tree). -/
noncomputable abbrev hintS (lr : Bool) : CTable → QueryLog specIC → ByteArray → List TG :=
  hint2 BAVC.tau (shP lr)

lemma hintS_eq (lr : Bool) (E : CTable) (L : QueryLog specIC) (x : ByteArray) :
    hintS lr E L x = shP lr E L x :=
  List.take_of_length_le (length_shP_le lr E L x)

end Shift

/-! ## The ordering step for the shifts -/

section Order

variable {β : Type} (T : CrtTables) (st : Statement) (lr : Bool)
  (P : OracleComp specIC (ByteArray × β)) (E : CTable) (g : Table)

/-- **The ordering step for U2**: if the log `Pfx` before `x`'s first target query (a prefix of
`P`'s log) contains the verifier's `H₂¹` input, the shifts computed from `Pfx` and the reduction's
queries at `x` are the prefixes of the output's alive trees at the end, in tree order, with the
extractor's candidates. For any statement with PomFRIT's parameters and `mu₁`. -/
theorem shP_eq_alive (hstp : st.params = pomfritParams lr)
    (hmu : ∀ Hs : Hashes, st.mu1 Hs = Hs.hash .muDelayed muCell.2)
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hkp : KeysPre st E (jOf g P E) (gLog T st P E g) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E)
      (Proof.opening ⟨st.params, πOf g P E⟩) (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves)
    {Pfx : QueryLog specIC} (hP : Pfx <+: jOf g P E)
    (hx1 : ((.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) : Dom) ∈ hashLog Pfx)
    {x : ByteArray}
    (hxc : xChal1 x = (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.chal1)
    (hxd : xDpre x = (Proof.correction ⟨st.params, πOf g P E⟩).extract 0 45) :
    shP lr E (Pfx ++ axT g lr Pfx x) x =
      ((List.finRange BAVC.tau).filter
          (· ∈ aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))).map
        fun t => toTG (preB (@candOut (icPrg E.cipher) _ st
          (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) t)) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) with hrdef
  set Hs := Hashes.ofTable g
  set π := πOf g P E
  set J := jOf g P E
  have hr2 : r.2.2 = verify Hs T st π := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hJ : r.2.1.aux.2 = J := aux_gameIC T st P E g
  have hacc' : (verify Hs T st π).accept = true := by rw [← hr2]; exact hacc
  obtain ⟨hf, leaves', hrec, -⟩ := (accept_iff _ T st π).1 hacc'
  have hrec' : BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves' := hrec
  rw [hr] at hrec'
  cases hrec'
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc' hrec
  have hHs : ∀ k w, (Hs.hash k w).size = k.outLen := fun k w => by simp [Hs]
  set x1 := runX Hs st π leaves with hx1def
  -- the logs
  obtain ⟨rest, hG0⟩ := gLog_eq_hashEnt_append T st P E g
  have hG : gLog T st P E g = hashEnt J ++ rest := hG0
  obtain ⟨V, hV⟩ := hP
  have hJV : J = Pfx ++ V := hV.symm
  have hsubG : ∀ e ∈ hashEnt Pfx, e ∈ gLog T st P E g := fun e he => by
    rw [hG, hJV, hashEnt_append]
    exact List.mem_append_left _ (List.mem_append_left _ he)
  have hx1H : ((.h21, x1) : Dom) ∈ (hashEnt Pfx).map Sigma.fst := mem_hashEnt_iff.2 hx1
  have hx1J : ((.h21, x1) : Dom) ∈ (hashEnt J).map Sigma.fst := by
    rw [hJV, hashEnt_append, List.map_append]; exact List.mem_append_left _ hx1H
  have hc1x : xChal1 x = (g (.h21, x1)).ba := by rw [hxc, hr2, hc1]; rfl
  have hfirstP : firstIn .h21 (fun _ => true) (xChal1 x) (hashEnt Pfx) = some x1 := by
    rw [hc1x]
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inl rfl)) (d := (.h21, x1)) rfl hsubG hx1H rfl
  have hx1Of : x1Of Pfx x = some x1 := hfirstP
  have hx1Of' : x1Of (Pfx ++ axT g lr Pfx x) x = some x1 := by
    unfold x1Of; rw [hashEnt_append]; exact firstIn_append_of_some hfirstP
  have hGx : logBefore (.h21, x1) (hashEnt (Pfx ++ axT g lr Pfx x)) =
      logBefore (.h21, x1) (gLog T st P E g) := by
    rw [hashEnt_append, logBefore_append_of_mem _ hx1H, hG, hJV, hashEnt_append,
      List.append_assoc, logBefore_append_of_mem _ hx1H]
  have hx1L : (.inl (.h21, x1) : DomIC) ∈ Pfx.map Sigma.fst := mem_hashLog.1 hx1
  have hJx : logBefore (.inl (.h21, x1)) (Pfx ++ axT g lr Pfx x) =
      logBefore (.inl (.h21, x1)) J := by
    rw [logBefore_append_of_mem _ hx1L, hJV, logBefore_append_of_mem _ hx1L]
  -- `iv`
  have hcons : ∀ e ∈ hashEnt Pfx, e = ⟨e.1, g e.1⟩ := fun e he =>
    gLog_answer T st P E g e (hsubG e he)
  have hivX : ivX st x1 g = ivE g st P E := by
    simp only [x1, ivX, ivE, ivOf, runX]
    rw [xIvPre_chal1Input hf (size_mu1 _ hHs st) (hHs _ _)]
  have hivq : ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = r.2.2.iv := by
    rw [ivX_tableOfLog g lr hx1Of hcons, ivX_stE_of st lr g hstp hmu, hivX, hr2, hiv]; rfl
  -- the alive trees
  have hfirst : firstIn .h21 (fun _ => true) r.2.2.chal1 (hashEnt r.2.1.aux.2) = some x1 := by
    rw [hJ, ← hxc, hc1x]
    have hsubJ : ∀ e ∈ hashEnt J, e ∈ gLog T st P E g := fun e he => by
      rw [hG]; exact List.mem_append_left _ he
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inl rfl)) (d := (.h21, x1)) rfl hsubJ hx1J rfl
  have hGJ : logBefore (.h21, x1) (hashEnt J) = logBefore (.h21, x1) (gLog T st P E g) := by
    rw [hG, logBefore_append_of_mem _ hx1J]
  have halive : aliveR E r = univ.filter fun i =>
      deadPre E (logBefore (.h21, x1) (gLog T st P E g)) (logBefore (.inl (.h21, x1)) J)
        r.2.2.iv x1 i = ∅ := by
    unfold aliveR
    rw [hfirst]
    dsimp only
    rw [hJ, hGJ]
  -- unfold `E₁`
  unfold shP
  rw [hx1Of']
  dsimp only
  rw [hGx, hJx, halive]
  -- the committed keys are the extractor's
  obtain ⟨hcom, hwH, -⟩ := chain_ident T st P E g hh (fun _ _ => ByteArray.empty) hacc' hrec
  have hxmu : x1.extract 0 32 = st.mu1 (Hashes.ofTable g) := by
    simp only [x1, runX]
    exact extract_mu_chal1Input (size_mu1 _ hHs st)
  have hivE : ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = ivE g st P E := by
    rw [ivX_tableOfLog g lr hx1Of hcons, ivX_stE_of st lr g hstp hmu, hivX]
  have hkeys : keyPre E (logBefore (.h21, x1) (gLog T st P E g)) (logBefore (.inl (.h21, x1)) J)
      (ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)))) x1 = r.2.1.keys := by
    rw [hrdef, gameIC_keys, hivE]
    funext i j
    unfold keyPre
    split_ifs with hv
    · rw [hcom i hv.1 j hv.2]
      simp only
      rw [keysOf_of_reconstruct hr hv.1 hv.2, ← hivX, hkp x1 hxmu i hv.1 j hv.2 _
        (hcom i hv.1 j hv.2) (fun hxJ => hwH hxJ i hv.1 j hv.2)]
    · rw [keysOf_of_not_valid _ _ _ _ _ hv]
  -- the proof fields
  have hπs : π.size = st.params.o₇ + 20 := size_bytes hf
  have hxPre : xPre st.params x1 = π.extract 0 st.params.o₂ := by
    simp only [x1, runX]
    exact xPre_chal1Input hf (size_mu1 _ hHs st) (hHs _ _)
  have hiv' : (preCore (stE lr) E (logBefore (.h21, x1) (gLog T st P E g))
      (logBefore (.inl (.h21, x1)) J) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)))).iv =
      r.2.2.iv := hivq
  rw [hiv']
  refine List.map_congr_left fun t _ => congrArg toTG (preB_congr fun n hn => ?_)
  have hn' : n < st.params.witnessBits := by rw [hstp]; simp [pomfritParams, Params.witnessBits]; omega
  have hnE : n < (stE lr).params.witnessBits := by
    simp [stE, pomfritParams, Params.witnessBits]; omega
  refine (candidate_chain_eq (stE lr) _ t hnE).trans (Eq.trans ?_
    (candidate_chain_eq st (outChain r) t hn').symm)
  have hr1 : r.1 = π := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hpo : xPre (pomfritParams lr) x1 = π.extract 0 (pomfritParams lr).o₂ := by
    rw [← hstp]; exact hxPre
  have hπo : (pomfritParams lr).o₄ ≤ π.size := by
    rw [hπs, ← hstp]; unfold Params.o₇ Params.o₅; omega
  have keyU : ∀ ch : Bridge.Chain,
      ch.proof = xPre (pomfritParams lr) x1 ++ zerosBA 64 ++ xDpre x ++ zerosBA 119 →
      ch.keys = r.2.1.keys → ch.iv = r.2.2.iv →
      Bridge.uBit (stE lr).params ch.iv (ch.corr (stE lr)) ch.keys t n =
        Bridge.uBit st.params (outChain r).iv ((outChain r).corr st) (outChain r).keys t n := by
    intro ch hp hk hi
    have hc : ch.corr (stE lr) = (outChain r).corr st := by
      funext i
      unfold Bridge.Chain.corr Bridge.Chain.pf
      have h1 : (⟨(stE lr).params, ch.proof⟩ : Proof).corrections =
          (⟨st.params, (outChain r).proof⟩ : Proof).corrections := by
        show (⟨pomfritParams lr, ch.proof⟩ : Proof).corrections =
          (⟨st.params, r.1⟩ : Proof).corrections
        rw [hp, hstp, hr1, ByteArray.append_assoc, ByteArray.append_assoc]
        exact corrections_pcd hpo (by unfold Params.o₄ at hπo; omega) _
      rw [h1, hstp]
      rfl
    rw [hc, hk, hi, hstp]
    rfl
  have keyC : ∀ ch : Bridge.Chain,
      ch.proof = xPre (pomfritParams lr) x1 ++ zerosBA 64 ++ xDpre x ++ zerosBA 119 →
      Bridge.corrBit (ch.pf (stE lr)) n = Bridge.corrBit ((outChain r).pf st) n := by
    intro ch hp
    show Bridge.corrBit ⟨pomfritParams lr, ch.proof⟩ n = Bridge.corrBit ⟨st.params, r.1⟩ n
    rw [hp, hstp, hr1]
    refine corrBit_pcd ?_ hπo (by simp [pomfritParams]) ?_ hn
    · rw [hpo, ByteArray.size_extract]; unfold Params.o₄ at hπo; omega
    · rw [hxd, hstp]
  exact congrArg₂ (fun a b => SeedExtraction.bit a + SeedExtraction.bit b)
    (keyU _ rfl hkeys rfl) (keyC _ rfl)


end Order

/-! ## A failed forgery of U2, table by table -/

section Fail

variable (g : Table) (E : CTable)

/-- The game's extraction at a statement, on a proof and a log: the proof, and the keys and known
trees the extractor computes from the log's cipher entries and the verifier's `iv`. -/
lemma extractIC_keys_known (st : Statement) {β : Type} (π : ByteArray) (b : β)
    (J : QueryLog specIC) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((π, b), J))).1 = π ∧
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((π, b), J))).2.keys =
      keysOf (cipherLog J) E (ivOf (Hashes.ofTable g) ⟨st.params, π⟩ (st.mu1 (Hashes.ofTable g)))
        (Proof.opening ⟨st.params, π⟩) (Proof.delta ⟨st.params, π⟩) ∧
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((π, b), J))).2.known =
      knownOf (cipherLog J) E (ivOf (Hashes.ofTable g) ⟨st.params, π⟩ (st.mu1 (Hashes.ofTable g)))
        (Proof.opening ⟨st.params, π⟩) := by
  simp only [extractIC, evalWithAnswerFn_bind, evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_pure]
  refine ⟨trivial, ?_, ?_⟩ <;> rfl

variable (pk : UovPk)

/-- **The claim is a preimage of one of the targets** if some candidate is. -/
lemma rel_pick {ts : List TG} {cs : List Spec.Bytes}
    (h : ∃ c ∈ cs, ∃ t ∈ ts, c.length = 119 ∧ pk.toSpec.eval c = toL (encT t)) :
    ∃ t ∈ ts, relP pk (pick pk ts cs) t := by
  obtain ⟨c, hc, t, ht, hct⟩ := h
  unfold pick
  obtain ⟨c', hc'⟩ : ∃ c', cs.find? (fun σ => decide (σ.length = 119 ∧
      ∃ t' ∈ ts, pk.toSpec.eval σ = toL (encT t'))) = some c' :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨c, hc, by simpa using ⟨hct.1, t, ht, hct.2⟩⟩)
  have hp := List.find?_some hc'
  simp only [decide_eq_true_eq] at hp
  obtain ⟨t', ht', he⟩ := hp.2
  exact ⟨t', ht', c', by rw [hc'], hp.1, he⟩

/-- **U2's failure for forgery `i`** on the game's reduced output (`ShiftFail` with `τ = 17`). -/
def ShiftFailZ (i : ℕ) (z : (List (ByteArray × SIss) × Bool) × HTSG (List TG)) : Prop :=
  z.1.2 = true ∧ ∃ x σ, z.1.1[i]? = some (x, σ) ∧
    ¬∃ a δs, z.2.1 x = some (a, δs) ∧ δs.length ≤ BAVC.tau ∧ ∃ δ ∈ δs, relP pk σ (a + δ)

variable (lr : Bool) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ i : ℕ)

set_option maxHeartbeats 1600000 in
/-- **A failed forgery of U2 is a bad event of the derived prover's game, table by table** (U2's
shift rule `hintS`, a 32-byte key digest): the verifier accepts and no alive tree extracts, Post,
the verifier's `H₂³` input unqueried, a chain hit or an order hit. -/
theorem shiftFail_events (hd : pk.digest.size = 32)
    (h : ShiftFailZ pk i (runG g CrtGen.tables lr E noHint (hintS lr E) tgts2 pk pre A Lst ℓ)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i)
    (r.2.2.accept = true ∧ ¬SomeExtracted E (stG lr pk (stOut r))
      (witKT pk hG (some (stOut r))) r) ∨
    PostOut E r ∨
    (r.2.2.accept = true ∧ ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2) ∨
    ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i) g,
      chainHitL cbP (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g ∨
        orderHitL (tableQueryLog (gameDP lr E pk pre A Lst i)) e.1 g := by
  classical
  intro r
  let _ : HasPrg := icPrg E.cipher
  set T := CrtGen.tables
  set P := proverP lr pk pre A Lst i with hPdef
  obtain ⟨hacc0, x, σ, hcl, hnr⟩ := h
  obtain ⟨-, -, -, hp1, hp2, Lx, hpx, htab, htacc, hσ⟩ :=
    ver_tableG g T lr E noHint (hintS lr E) tgts2 pk pre A Lst ℓ i hacc0 hcl
  set b0 := forgerOut g lr E pk pre A Lst with hb0
  set ms := b0.1.getD i (ByteArray.empty, ByteArray.empty) with hms
  set p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) P with hp
  obtain ⟨o1, o2, o3⟩ := gameA_out T (stG lr pk) P E g
  have hπ : πOf g P E = sProof lr ms.2 := hp1
  set st := stG lr pk (sA g P E) with hstdef
  have hstp : st = stG lr pk p.2.1 := rfl
  -- by contradiction
  by_contra hcon
  simp only [not_or, not_and, not_not, not_exists] at hcon
  obtain ⟨hsome, hpost, hzq, hhit⟩ := hcon
  have e0 : r.2.2 = verify (Hashes.ofTable g) T st (πOf g P E) := o3
  have hacc : r.2.2.accept = true := by rw [e0, hπ]; exact htacc
  have hsome := hsome hacc
  have hz := hzq hacc
  -- the fixed game
  have hrg : r = evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) :=
    evalWithAnswerFn_gameA _ _ _ _ _
  have hlogA : tableQueryLog (gameDP lr E pk pre A Lst i) g = gLog T st P E g :=
    tableQueryLog_gameA _ _ _ _ _
  have hh : NoHit (gameIC T st P E) (chainHit T st P E) g := by
    intro e he hc
    exact (hhit e (by rw [hlogA]; exact he)).1 (by
      show (g e.1).ba ∈ hitTargets cbP (logBefore e.1 (tableQueryLog (gameDP lr E pk pre A Lst i) g))
        e.1.1
      rw [hlogA]; exact hc)
  have hkp : KeysPre st E (jOf g P E) (gLog T st P E g) g :=
    keysPre_of_not_postOut T st P E g (by rw [← hrg]; exact hpost)
  have haccv : (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true := by
    rw [← e0]; exact hacc
  obtain ⟨hf, leaves, hrec, -⟩ := (accept_iff _ T st (πOf g P E)).1 haccv
  have hrec' : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E)
      (Proof.opening ⟨st.params, πOf g P E⟩) (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves :=
    hrec
  -- the logs
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
  -- the game's extraction from the forger's log is the derived game's
  obtain ⟨hkeysL, hknownL⟩ := keysOf_knownOf_prefix T st P E g hh hkp haccv hrec' hLJ hx1L
  set ex := evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((sProof lr ms.2, ()), L)) with hexd
  obtain ⟨ex1, exk, exn⟩ := extractIC_keys_known g E st (sProof lr ms.2) () L
  have hiv : ivOf (Hashes.ofTable g) ⟨st.params, sProof lr ms.2⟩ (st.mu1 (Hashes.ofTable g)) =
      ivE g st P E := by rw [ivE, hπ]
  obtain ⟨kP, nP⟩ := gameA_keys_known g T E (stG lr pk) P
  have hk : ex.2.keys = r.2.1.keys := by
    rw [exk, kP, hiv, ← hπ, hkeysL]
  have hn : ex.2.known = r.2.1.known := by
    rw [exn, nP, hiv, ← hπ, hknownL]
  -- the alive trees are known
  have hx1J : ((.h21, x1) : Dom) ∈ hashLog (jOf g P E) := by
    rw [hJ]; unfold hashLog; rw [List.filterMap_append]; exact List.mem_append_left _ hx1L
  have halk : aliveR E r ⊆ r.2.1.known := by
    rw [hrg]
    exact aliveR_subset_known T st P E g hh (by rw [← hrg]; exact hpost) (by rw [← hrg]; exact hacc)
      hrec' hx1J
  -- the `i`-th forgery's data
  obtain ⟨haux0, haux⟩ := aux_proverP g lr E pk pre A Lst i
  have hb1 : st.binder1 = sB1 lr ms.2 := by
    rw [hstdef, stG_binder1]
    have h3 : (sA g P E).2.1 = p.2.1.2.1 := rfl
    rw [h3, hp2]
  have hc1T : c1T g lr E pk ms.2 = some r.2.2.chal1 := by
    rw [e0]
    unfold c1T
    rw [← hπ]
    exact chal1Pre_of_accept (st := st)
      (st' := pomfritRedeemT pk (fun _ => ByteArray.empty) (sB1 lr ms.2) (sB2 lr ms.2) lr) g T
      (by rw [pomfritRedeemT_params, hstdef, stG_params])
      (by rw [mu1_pomfritRedeemT, hstdef, stG_mu1])
      (by rw [hb1, pomfritRedeemT_binder1]) haccv
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
    rwa [hπ] at this
  have hxc : xChal1 x = r.2.2.chal1 := by rw [hx]; exact xChal1_tgtIn hd hc1s
  have hxd : xDpre x = (Proof.correction ⟨st.params, πOf g P E⟩).extract 0 45 := by
    rw [hx, xDpre_tgtIn hd hc1s hsz, hπ]; rfl
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
  -- the shifts are the alive trees' prefixes
  have hsh := shP_eq_alive T st lr P E g (stG_params lr pk _) (stG_mu1 lr pk _) hh hkp
    (by rw [← hrg]; exact hacc) hrec' hPfxJ hord (by rw [← hrg]; exact hxc) (by rw [hxd])
  rw [← hrg, ← hLx] at hsh
  -- some alive tree extracts: its decoded candidate is a preimage of a shifted target
  have hso : stOut r = p.2.1 := o2
  obtain ⟨t, ht, hwit⟩ := hsome
  apply hnr
  refine ⟨p.2.1.1, hintS lr E Lx x, htab, List.length_take_le _ _, ?_⟩
  rw [hσ]
  set w := @candOut (icPrg E.cipher) _ (stG lr pk (stOut r)) r t
  have hw : w = @candOut (icPrg E.cipher) _ (stG lr pk p.2.1) r t := by
    simp only [w]; rw [hso]
  have htr : @verify (icPrg E.cipher) (Hashes.ofTable g) T (stG lr pk p.2.1) (sProof lr ms.2) =
      r.2.2 := by
    rw [e0, hπ]; rfl
  have hr1 : ex.1 = r.1 := ex1.trans (hp1.symm.trans o1.symm)
  have hout : outChain (ex.1, ex.2,
      @verify (icPrg E.cipher) (Hashes.ofTable g) T (stG lr pk p.2.1) (sProof lr ms.2)) =
      outChain r := by
    simp only [outChain]
    rw [hr1, hk, htr]
  have hcand : (EndToEnd.candidate (F := GF128) ((outChain (ex.1, ex.2,
      @verify (icPrg E.cipher) (Hashes.ofTable g) T (stG lr pk p.2.1) (sProof lr ms.2))).u
        (stG lr pk p.2.1))
      ((outChain (ex.1, ex.2, @verify (icPrg E.cipher) (Hashes.ofTable g) T (stG lr pk p.2.1)
        (sProof lr ms.2))).dc (stG lr pk p.2.1)) t) = w := by
    rw [hout, hw]; rfl
  have hex : ∃ c ∈ candidates E (stG lr pk p.2.1) (ex.1, ex.2,
      @verify (icPrg E.cipher) (Hashes.ofTable g) T (stG lr pk p.2.1) (sProof lr ms.2)),
      ∃ t' ∈ tgts2 (p.2.1.1, hintS lr E Lx x),
        c.length = 119 ∧ pk.toSpec.eval c = toL (encT t') := by
    refine ⟨bytesOf (bitsOf w) 45 119, ?_, p.2.1.1 + toTG (preB w), ?_, ?_⟩
    · unfold candidates
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      refine ⟨t, ?_, by rw [hcand]⟩
      rw [hn]; exact halk ht
    · simp only [tgts2, List.mem_map]
      refine ⟨toTG (preB w), ?_, rfl⟩
      rw [hintS_eq, hsh]
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      exact ⟨t, ht, by rw [hw, hstp]⟩
    · have hrel := pomRel_of_wit pk (encT (stOut r).1) (encT_size _) _ hwit
      obtain ⟨hlr, -, hls, heval⟩ := hrel
      refine ⟨hls, ?_⟩
      rw [heval, hso]
      exact (toL_encT_add_toTG _ _ hlr).symm
  obtain ⟨δ, hδ, hrel⟩ := rel_pick pk hex
  simp only [tgts2, List.mem_map] at hδ
  obtain ⟨δ', hδ', rfl⟩ := hδ
  exact ⟨δ', hδ', hrel⟩

end Fail

end VoleMole.ROM.OneMore.Pomfrit
