import VoleMole.ROM.OneMoreClsTable

/-!
# The ordering step for `E₁^cls`

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). The analogue of `e1P_eq_major`
(`ROM/OneMoreLemmaPOrder.lean`) for the class extractor: if the log `Pfx` before `x`'s first target
query holds the verifier's `H₂¹` input and covers the decoder (`CovL`), then `E₁^cls(x)` computed
from `Pfx` and the reduction's queries is the class extractor's output at the end of the run, on
the output's chain with the gate hash read off the prover's log (the prefix of `GoalC`, Lemma
P^cls's goal), and the prover's log covers the decoder (`ClsCovered`).

* `xU_tgtIn`: `ũ` at bytes `175 … 239` of `hash_to_target`'s input.
* `pre_ident`: the data committed at the first `H₂¹` preimage `x₁` of `x`'s `chal1`, read off
  `Pfx` and the reduction's queries, are the output's (`e1P_eq_major`'s first half).
* Chain congruences (`clsKey`, `clsPts`, `gateIns`, `chKos` read the chain through `iv`, the keys,
  the proof's first `o₂` bytes, `ũ`, `chal1` and `H₅` at the gate inputs).
* **`e1C_eq_cls`**, **`clsCovered_of_covL`**.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim VoleMole.Verifier.Bridge
open VoleMole.PomFRIT

/-! ## `ũ` in `hash_to_target`'s input -/

/-- **`ũ` in `hash_to_target`'s input**, for a 32-byte key digest, a 136-byte `chal1` and a proof of
the right length. -/
lemma xU_tgtIn {pk : UovPk} {lr : Bool} {sg m c1 : ByteArray} (hd : pk.digest.size = 32)
    (hc : c1.size = 136)
    (hs : (sg.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes) :
    xU (tgtIn pk lr sg m c1) =
      ({ params := pomfritParams lr, bytes := sg.extract 0 (pomfritParams lr).proofBytes } :
        Proof).voleCheck := by
  refine toL_injective ?_
  rw [xU, tgtIn, toL_extract_toBA]
  simp only [Spec.PomFRIT.targetInput, List.append_assoc]
  have h1 : (Spec.PomFRIT.targetDst ++ toL pk.digest ++ toL c1).length = 175 := by
    simp only [List.length_append, targetDst_length, VoleMole.Privacy.length_toL, hd, hc]
  rw [← List.append_assoc, ← List.append_assoc, List.drop_left' h1]
  rw [List.take_left' (by rw [VoleMole.Privacy.length_toL, size_voleCheck hs])]

/-! ## The proof bytes of `E₁^cls`'s chain -/

section Pcd

variable {p : Params} {π A U D : ByteArray}

/-- `c_mult` of `E₁^cls`'s chain (the first `o₂` bytes, then anything) is the proof's. -/
lemma cmult_pcd (hA : A = π.extract 0 p.o₂) (hπ : p.o₂ ≤ π.size) (R : ByteArray) :
    (⟨p, A ++ R⟩ : Proof).cmult = (⟨p, π⟩ : Proof).cmult := by
  have hAs : A.size = p.o₂ := by rw [hA, ByteArray.size_extract]; omega
  rw [cmult_eq, cmult_eq]
  simp only
  rw [extract_append_of_le (by omega), hA, ByteArray.extract_extract]
  rw [Nat.zero_add, Nat.zero_add, Nat.min_self]

/-- `ũ` of `E₁^cls`'s chain is the 64 bytes after the first `o₂`. -/
lemma voleCheck_pcd (hA : A.size = p.o₂) (hU : U.size = 64) (R : ByteArray) :
    (⟨p, A ++ U ++ R⟩ : Proof).voleCheck = U := by
  rw [voleCheck_eq]
  exact extract_append3 hA.symm (by rw [hA, hU])

/-- **The correction bits `j < 360` of `E₁^cls`'s chain** are the proof's (`corrBit_pcd` with any
64 bytes for `ũ`). -/
lemma corrBit_pcdU (hA : A.size = p.o₂) (hU : U.size = 64) (hπ : p.o₄ ≤ π.size)
    (hw : 45 ≤ p.witnessBytes) (hD : D = (⟨p, π⟩ : Proof).correction.extract 0 45) {j : ℕ}
    (hj : j < 360) :
    Bridge.corrBit ⟨p, A ++ U ++ D ++ zerosBA 119⟩ j = Bridge.corrBit ⟨p, π⟩ j := by
  have hcs : (⟨p, π⟩ : Proof).correction.size = p.witnessBytes := by
    rw [correction_eq, ByteArray.size_extract]
    simp only
    unfold Params.o₄ at hπ ⊢
    omega
  have hDs : D.size = 45 := by
    rw [hD, ByteArray.size_extract, hcs]
    omega
  have key : (⟨p, A ++ U ++ D ++ zerosBA 119⟩ : Proof).correction.get! (j / 8) =
      (⟨p, π⟩ : Proof).correction.get! (j / 8) := by
    rw [correction_eq]
    simp only
    rw [ByteArray.append_assoc, extract_append_right' (by rw [ByteArray.size_append, hA, hU])]
    rw [ByteArray.size_append, hA, hU, Nat.sub_self,
      get!_extract_zero (by unfold Params.o₄; omega), get!_append_left (by rw [hDs]; omega), hD,
      get!_extract_zero (by omega)]
  unfold Bridge.corrBit
  rw [key]

end Pcd

/-! ## The data committed at `x₁`, read off the log at the target query -/

section Ident

variable {β : Type} (T : CrtTables) (st : Statement) (lr : Bool)
  (P : OracleComp specIC (ByteArray × β)) (E : CTable) (g : Table)

set_option maxHeartbeats 800000 in
/-- **The data at the target query are the output's** (`e1P_eq_major`'s first half): if the log
`Pfx` before `x`'s first target query (a prefix of `P`'s log) holds the verifier's `H₂¹` input `x₁`,
then `x₁` is the first `H₂¹` preimage of `x`'s `chal1` there, the logs before `x₁` are the prover's,
`iv` read off the log is the verifier's, the committed keys are the extractor's, the alive trees and
dead leaves are the output's, and the proof's first `o₂` bytes are parsed from `x₁`. -/
theorem pre_ident (hstp : st.params = pomfritParams lr)
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
    (hxc : xChal1 x = (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.chal1) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)
    let x1 := runX (Hashes.ofTable g) st (πOf g P E) leaves
    let J := jOf g P E
    let Gx := logBefore (.h21, x1) (hashEnt J)
    let Jx := logBefore (.inl (.h21, x1)) J
    x1Of (Pfx ++ axT g lr Pfx x) x = some x1 ∧
      logBefore (.h21, x1) (hashEnt (Pfx ++ axT g lr Pfx x)) = Gx ∧
      logBefore (.inl (.h21, x1)) (Pfx ++ axT g lr Pfx x) = Jx ∧
      logBefore (.inl (.h21, x1)) Pfx = Jx ∧
      ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = r.2.2.iv ∧
      ivX (stE lr) x1 g = r.2.2.iv ∧
      keyPre E Gx Jx r.2.2.iv x1 = r.2.1.keys ∧
      aliveR E r = univ.filter (fun i => deadPre E Gx Jx r.2.2.iv x1 i = ∅) ∧
      deadR E r = deadPre E Gx Jx r.2.2.iv x1 ∧
      xPre (pomfritParams lr) x1 = r.1.extract 0 (pomfritParams lr).o₂ ∧
      r.1.size = (pomfritParams lr).o₇ + 20 ∧
      r.2.2.chal1 = (g (.h21, x1)).ba := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro r x1' J Gx' Jx'
  set Hs := Hashes.ofTable g
  set π := πOf g P E
  have hr2 : r.2.2 = verify Hs T st π := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hr1 : r.1 = π := by
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
      logBefore (.h21, x1) (hashEnt J) := by
    rw [hashEnt_append, logBefore_append_of_mem _ hx1H, hJV, hashEnt_append,
      logBefore_append_of_mem _ hx1H]
  have hx1L : (.inl (.h21, x1) : DomIC) ∈ Pfx.map Sigma.fst := mem_hashLog.1 hx1
  have hJx : logBefore (.inl (.h21, x1)) (Pfx ++ axT g lr Pfx x) =
      logBefore (.inl (.h21, x1)) J := by
    rw [logBefore_append_of_mem _ hx1L, hJV, logBefore_append_of_mem _ hx1L]
  have hJxP : logBefore (.inl (.h21, x1)) Pfx = logBefore (.inl (.h21, x1)) J := by
    rw [hJV, logBefore_append_of_mem _ hx1L]
  -- `iv`
  have hcons : ∀ e ∈ hashEnt Pfx, e = ⟨e.1, g e.1⟩ := fun e he =>
    gLog_answer T st P E g e (hsubG e he)
  have hivX : ivX st x1 g = ivE g st P E := by
    simp only [x1, ivX, ivE, ivOf, runX]
    rw [xIvPre_chal1Input hf (size_mu1 _ hHs st) (hHs _ _)]
  have hivg : ivX (stE lr) x1 g = r.2.2.iv := by
    rw [ivX_stE_of st lr g hstp hmu, hivX, hr2, hiv]; rfl
  have hivq : ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = r.2.2.iv := by
    rw [ivX_tableOfLog g lr hx1Of hcons, hivg]
  -- the alive trees
  have hfirst : firstIn .h21 (fun _ => true) r.2.2.chal1 (hashEnt r.2.1.aux.2) = some x1 := by
    rw [hJ, ← hxc, hc1x]
    have hsubJ : ∀ e ∈ hashEnt J, e ∈ gLog T st P E g := fun e he => by
      rw [hG]; exact List.mem_append_left _ he
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inl rfl)) (d := (.h21, x1)) rfl hsubJ hx1J rfl
  have halive : aliveR E r = univ.filter fun i =>
      deadPre E (logBefore (.h21, x1) (hashEnt J)) (logBefore (.inl (.h21, x1)) J)
        r.2.2.iv x1 i = ∅ := by
    unfold aliveR
    rw [hfirst]
    dsimp only
    rw [hJ]
  have hdead : deadR E r = deadPre E (logBefore (.h21, x1) (hashEnt J))
      (logBefore (.inl (.h21, x1)) J) r.2.2.iv x1 := by
    unfold deadR
    rw [hfirst]
    dsimp only
    rw [hJ]
  -- the committed keys are the extractor's
  obtain ⟨hcom, hwH, -⟩ := chain_ident T st P E g hh (fun _ _ => ByteArray.empty) hacc' hrec
  have hxmu : x1.extract 0 32 = st.mu1 (Hashes.ofTable g) := by
    simp only [x1, runX]
    exact extract_mu_chal1Input (size_mu1 _ hHs st)
  have hGJ : logBefore (.h21, x1) (hashEnt J) = logBefore (.h21, x1) (gLog T st P E g) := by
    rw [hG, logBefore_append_of_mem _ hx1J]
  have hkeys : keyPre E (logBefore (.h21, x1) (hashEnt J)) (logBefore (.inl (.h21, x1)) J)
      r.2.2.iv x1 = r.2.1.keys := by
    rw [gameIC_keys, ← hivg, ivX_stE_of st lr g hstp hmu, hivX, hGJ]
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
  refine ⟨hx1Of', hGx, hJx, hJxP, hivq, hivg, hkeys, halive, hdead, ?_, ?_, ?_⟩
  · rw [hr1, ← hstp]; exact hxPre
  · rw [hr1, ← hstp]; exact hπs
  · rw [hr2, hc1]; rfl

end Ident

/-! ## What the class extractor reads off a chain -/

section Core

variable [HasPrg] (st : Statement) (T : CrtTables)

/-- **Two chains with the same core**: `iv`, keys and corrections. -/
structure CoreEq (ch ch' : Chain) : Prop where
  iv : ch.iv = ch'.iv
  keys : ch.keys = ch'.keys
  corr : (ch.pf st).corrections = (ch'.pf st).corrections

variable {st} {ch ch' : Chain}

omit [HasPrg] in
lemma CoreEq.symm (h : CoreEq st ch ch') : CoreEq st ch' ch := ⟨h.iv.symm, h.keys.symm, h.corr.symm⟩

omit [HasPrg] in
lemma CoreEq.corr' (h : CoreEq st ch ch') : ch.corr st = ch'.corr st := by
  funext i; simp only [Chain.corr, h.corr]

lemma CoreEq.u (h : CoreEq st ch ch') : ch.u st = ch'.u st := by
  funext i j; simp only [Chain.u, h.iv, h.keys, h.corr']

lemma CoreEq.lab (h : CoreEq st ch ch') : ch.lab st = ch'.lab st := by
  funext i j; simp only [Chain.lab, h.iv, h.keys, h.corr']

lemma CoreEq.clsKey (h : CoreEq st ch ch') : clsKey st ch = clsKey st ch' := by
  funext i; simp only [PomFRIT.clsKey, h.u, h.lab]

lemma CoreEq.clsPts (h : CoreEq st ch ch') (S : Finset (Fin BAVC.tau)) (hd : Blocks)
    (i : Fin BAVC.tau) : clsPts st ch S hd i = clsPts st ch' S hd i := by
  simp only [PomFRIT.clsPts, h.clsKey, h.lab]

lemma CoreEq.gateIns (h : CoreEq st ch ch') (Δ : Blocks) :
    gateIns st ch T Δ = gateIns st ch' T Δ := by
  simp only [IC.gateIns, h.iv, h.keys, h.corr]

lemma CoreEq.clsCertK (h : CoreEq st ch ch') (K : Blocks → Fin 4 → GF128)
    (S : Finset (Fin BAVC.tau)) (hd : Blocks) (i : Fin BAVC.tau) :
    clsCertK K st ch S hd i ↔ clsCertK K st ch' S hd i := by
  simp only [PomFRIT.clsCertK, h.clsKey, h.lab]

/-- **The check value reads the core, `c_mult`, `ũ`, `chal1` and `H₅` at the gate inputs.** -/
lemma chKos_congr (h : CoreEq st ch ch') (hcm : (ch.pf st).cmult = (ch'.pf st).cmult)
    (hvc : (ch.pf st).voleCheck = (ch'.pf st).voleCheck) (hc1 : ch.chal1 = ch'.chal1) (Δ : Blocks)
    (h5 : ∀ inp ∈ gateIns st ch T Δ, ch.h5 inp = ch'.h5 inp) :
    chKos st ch T Δ = chKos st ch' T Δ := by
  rw [← chKos_withH5 st ch' T ch.h5 Δ fun inp hinp => h5 inp (by rw [h.gateIns T]; exact hinp)]
  set c' := withH5 ch' ch.h5
  have hr : ∀ Δ, c'.resp st T Δ = ch.resp st T Δ := fun Δ => by
    show respAt ch.h5 T st.params (ch'.pf st).corrections (ch'.pf st).cmult ch'.iv ch'.keys Δ =
      respAt ch.h5 T st.params (ch.pf st).corrections (ch.pf st).cmult ch.iv ch.keys Δ
    rw [← h.corr, ← hcm, ← h.iv, ← h.keys]
  have hQ : c'.kosQ st T = ch.kosQ st T := by
    funext Δ k; simp only [Chain.kosQ]; rw [hr]
  have hD : c'.kosD st T = ch.kosD st T := by
    funext Δ k; simp only [Chain.kosD]; rw [hr]
  have hU : c'.kosU st = ch.kosU st := by
    funext j
    show gfOfBytes (ch'.pf st).voleCheck (16 * j) = gfOfBytes (ch.pf st).voleCheck (16 * j)
    rw [hvc]
  have hC : c'.kosCh = ch.kosCh := by
    show Bridge.chOf gfId mem_shortKeys ch'.chal1 = Bridge.chOf gfId mem_shortKeys ch.chal1
    rw [hc1]
  simp only [chKos]
  rw [hQ, hD, hU, hC]

end Core

/-! ## The ordering step -/

section Main

lemma hashEnt_logBefore (d : Dom) (L : QueryLog specIC) :
    hashEnt (logBefore (.inl d) L) = logBefore d (hashEnt L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d' =>
      by_cases h : d' = d
      · subst h
        simp only [hashEnt]
        rw [logBefore_cons_self]
        exact (logBefore_cons_self (R := Ans) d' u (hashEnt L)).symm
      · rw [logBefore_cons_of_ne _ _ (by simpa using h)]
        simp only [hashEnt]
        rw [logBefore_cons_of_ne _ _ (by simpa using h), ih]
    | inr c =>
      rw [logBefore_cons_of_ne _ _ (by simp)]
      simp only [hashEnt, ih]

/-- The tree that the class extractor decodes is one that `decIns` covers, when trees of one class
have one prefix. -/
lemma clsTarget_mem_wideOther {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]
    {S : Finset (Fin 17)} {key : Fin 17 → Kt} {p : Fin 17 → P}
    (hkp : ∀ a b, key a = key b → p a = p b) {i : Fin 17} (h : clsTarget S key p = some i) :
    i ∈ wideOther S key := by
  unfold clsTarget at h
  unfold wideOther
  rcases hm : majTree S key with _ | i₁
  · simp [hm] at h
  · simp only [hm, Option.bind_some] at h ⊢
    by_cases hw : 51 ≤ grpW S key (key i₁)
    · rw [ite_eq_left hw] at h
      rw [ite_eq_left hw]
      by_cases hne : (clsCand S key p i₁).Nonempty
      · rw [dite_eq_left hne] at h
        have hi : (clsCand S key p i₁).min' hne = i := Option.some.inj h
        subst hi
        have hmem := Finset.mem_filter.1 ((clsCand S key p i₁).min'_mem hne)
        exact Finset.mem_filter.2 ⟨hmem.1, fun hk => hmem.2.1 (hkp _ _ hk), hmem.2.2⟩
      · rw [dite_eq_right hne] at h; cases h
    · rw [ite_eq_right hw] at h; cases h

lemma clsExt_congr_all {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]
    {S : Finset (Fin 17)} {key key' : Fin 17 → Kt} {p p' : Fin 17 → P}
    {cert cert' : Fin 17 → Prop} [DecidablePred cert] [DecidablePred cert']
    (hk : key = key') (hp : p = p') (hc : ∀ i, clsTarget S key p = some i → (cert i ↔ cert' i)) :
    clsExt S key p cert = clsExt S key' p' cert' := by
  subst hk hp
  exact clsExt_congr_cert hc

variable {β : Type} (lr : Bool) (pk : UovPk) (P : OracleComp specIC (ByteArray × β)) (E : CTable)
  (g : Table)

lemma mem_decIns {Lb : QueryLog specIC} {x1 iv inp : ByteArray} :
    letI : HasPrg := icPrg E.cipher
    inp ∈ decIns lr E Lb x1 iv ↔
      ∃ i ∈ wideOther (aliveOf E Lb x1 iv) (clsKey (stE lr) (pcOf lr E Lb x1 iv)),
        ∃ Δ ∈ clsPts (stE lr) (pcOf lr E Lb x1 iv) (aliveOf E Lb x1 iv)
            (hdOf (deadPre E (hashEnt Lb) Lb iv x1)) i,
          inp ∈ gateIns (stE lr) (pcOf lr E Lb x1 iv) CrtGen.tables Δ := by
  simp only [decIns, List.mem_flatMap, Finset.mem_toList]

open Classical in
/-- **The class extractor's output at the end of the run**: `clsExt` on the output's alive trees,
with the classes, prefixes and certificates of the output's chain (gate hash read off the prover's
log) and dead leaves: the prefix that `ClsExtracted` asks of a tree. -/
noncomputable def clsOut (st : Statement) (r : Out (β × QueryLog specIC)) : Option Spec.Bytes :=
  letI : HasPrg := icPrg E.cipher
  clsExt (aliveR E r) (clsKey st (outChainL r))
    (fun i => preB (candidate (F := GF128) ((outChainL r).u st) ((outChainL r).dc st) i))
    (fun i => clsCert st (outChainL r) CrtGen.tables (aliveR E r) (hdOf (deadR E r)) i)

lemma clsExtracted_iff (st : Statement) (wit : ByteArray → (ℕ → GF128) → Prop)
    (r : Out (β × QueryLog specIC)) :
    letI : HasPrg := icPrg E.cipher
    ClsExtracted E st CrtGen.tables wit r ↔
      ∃ i ∈ aliveR E r, wit r.2.2.chal1
          (candidate (F := GF128) ((outChainL r).u st) ((outChainL r).dc st) i) ∧
        clsOut E st r =
          some (preB (candidate (F := GF128) ((outChainL r).u st) ((outChainL r).dc st) i)) := by
  unfold ClsExtracted GoalC clsOut
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
/-- **The ordering step for `E₁^cls`**: if the log `Pfx` before `x`'s first target query (a prefix
of `P`'s log) holds the verifier's `H₂¹` input and covers the decoder, then `E₁^cls(x)`, computed
from `Pfx` and the reduction's queries, is the class extractor's output at the end of the run
(`clsOut`), and the prover's log covers the decoder (`ClsCovered`). PomFRIT's statements. -/
theorem e1C_eq_cls (s0 : TG × ByteArray × ByteArray)
    (hh : NoHit (gameIC CrtGen.tables (stG lr pk s0) P E) (chainHit CrtGen.tables (stG lr pk s0) P E) g)
    (hkp : KeysPre (stG lr pk s0) E (jOf g P E) (gLog CrtGen.tables (stG lr pk s0) P E g) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIC CrtGen.tables (stG lr pk s0) P E)).2.2.accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g (stG lr pk s0) P E)
      (Proof.opening ⟨(stG lr pk s0).params, πOf g P E⟩)
      (Proof.delta ⟨(stG lr pk s0).params, πOf g P E⟩) = some leaves)
    {Pfx : QueryLog specIC} (hP : Pfx <+: jOf g P E)
    (hx1 : ((.h21, runX (Hashes.ofTable g) (stG lr pk s0) (πOf g P E) leaves) : Dom) ∈ hashLog Pfx)
    (hcov : CovL lr E g Pfx)
    {x : ByteArray}
    (hxc : xChal1 x = (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIC CrtGen.tables (stG lr pk s0) P E)).2.2.chal1)
    (hxd : xDpre x = (Proof.correction ⟨(stG lr pk s0).params, πOf g P E⟩).extract 0 45)
    (hxu : xU x = Proof.voleCheck ⟨(stG lr pk s0).params, πOf g P E⟩) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables (stG lr pk s0) P E)
    e1C lr E (Pfx ++ axT g lr Pfx x) x = toTG ((clsOut E (stG lr pk s0) r).getD []) ∧
      ClsCovered E (stG lr pk s0) CrtGen.tables r := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro r
  set st := stG lr pk s0 with hst
  set T := CrtGen.tables
  obtain ⟨hx1Of', hGx', hJx', hJxP, hivq, hivg, hkeys, halive, hdead, hxPre, hπs, hc1⟩ :=
    pre_ident T st lr P E g (stG_params lr pk s0) (stG_mu1 lr pk s0) hh hkp hacc hr hP hx1 hxc
  set x1 := runX (Hashes.ofTable g) st (πOf g P E) leaves with hx1def
  set J := jOf g P E with hJdef
  set Gx := logBefore (.h21, x1) (hashEnt J)
  set Jx := logBefore (.inl (.h21, x1)) J
  set tbl := tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))
  set pr := pomfritParams lr
  have hr1 : r.1 = πOf g P E := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hJ : r.2.1.aux.2 = J := aux_gameIC T st P E g
  have ho2 : pr.o₂ ≤ r.1.size := by rw [hπs]; unfold Params.o₇ Params.o₅ Params.o₄; omega
  have ho4 : pr.o₄ ≤ r.1.size := by rw [hπs]; unfold Params.o₇ Params.o₅; omega
  have hAs : (xPre pr x1).size = pr.o₂ := by
    rw [hxPre, ByteArray.size_extract, Nat.min_eq_left ho2, Nat.sub_zero]
  have hUs : (xU x).size = 64 := by
    rw [hxu, voleCheck_eq, ByteArray.size_extract]
    show min (pr.o₂ + 64) (πOf g P E).size - pr.o₂ = 64
    rw [← hr1, Nat.min_eq_left (by unfold Params.o₄ at ho4; omega)]
    omega
  -- the three chains: `E₁^cls`'s, the output's, the decoder's
  set chE : Chain := Chain.mk (xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119)
    (keyPre E Gx Jx r.2.2.iv x1) r.2.2.iv ((Hashes.ofTable tbl).hash .h5) (xChal1 x) #[] 0
    ByteArray.empty (fun _ => []) with hchE
  set chO := outChainL r with hchO
  set ch0 := pcOf lr E Jx x1 r.2.2.iv with hch0
  have hcEO : CoreEq st chE chO := by
    refine ⟨rfl, hkeys, ?_⟩
    show (⟨pr, xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119⟩ : Proof).corrections =
      (⟨pr, r.1⟩ : Proof).corrections
    rw [ByteArray.append_assoc, ByteArray.append_assoc]
    exact corrections_pcd hxPre ho2 _
  have hc0O : CoreEq st ch0 chO := by
    refine ⟨rfl, ?_, ?_⟩
    · show keyPre E (hashEnt Jx) Jx r.2.2.iv x1 = r.2.1.keys
      rw [hashEnt_logBefore]; exact hkeys
    · show (⟨pr, xPre pr x1⟩ : Proof).corrections = (⟨pr, r.1⟩ : Proof).corrections
      have h := corrections_pcd (R := ByteArray.empty) hxPre ho2
      rwa [ByteArray.append_empty] at h
  have hS0 : aliveOf E Jx x1 r.2.2.iv = aliveR E r := by
    rw [halive]; unfold aliveOf; rw [hashEnt_logBefore]
  have hd0 : deadPre E (hashEnt Jx) Jx r.2.2.iv x1 = deadR E r := by
    rw [hdead, hashEnt_logBefore]
  -- trees of one class have one prefix
  have hkp' : ∀ a b, clsKey st chO a = clsKey st chO b →
      preB (candidate (F := GF128) (chO.u st) (chO.dc st) a) =
        preB (candidate (F := GF128) (chO.u st) (chO.dc st) b) := by
    intro a b hab
    have hu : chO.u st a = chO.u st b := congrArg Prod.fst hab
    simp only [candidate, hu]
  -- the decoder's inputs are in the log
  have hcovO : ∀ i ∈ wideOther (aliveR E r) (clsKey st chO),
      ∀ Δ ∈ clsPts st chO (aliveR E r) (hdOf (deadR E r)) i, ∀ inp ∈ gateIns st chO T Δ,
        ((.h5, inp) : Dom) ∈ hashLog Pfx := by
    intro i hi Δ hΔ inp hinp
    have hmem := hcov x1 hx1 inp (by
      rw [hJxP, hivg, mem_decIns, hS0, hd0]
      have hk0 : clsKey (stE lr) ch0 = clsKey st chO := hc0O.clsKey
      have hp0 : clsPts (stE lr) ch0 (aliveR E r) (hdOf (deadR E r)) i =
          clsPts st chO (aliveR E r) (hdOf (deadR E r)) i := hc0O.clsPts _ _ _
      have hg0 : gateIns (stE lr) ch0 T Δ = gateIns st chO T Δ := hc0O.gateIns T Δ
      refine ⟨i, by rw [hk0]; exact hi, Δ, by rw [hp0]; exact hΔ, ?_⟩
      rw [hg0]; exact hinp)
    rw [mem_hashLog] at hmem ⊢
    obtain ⟨e, he, he1⟩ := List.mem_map.1 hmem
    exact List.mem_map.2 ⟨e, mem_of_mem_logBefore he, he1⟩
  have hPJ : ∀ d, d ∈ hashLog Pfx → (d : Dom) ∈ (hashEnt J).map Sigma.fst := by
    intro d hd
    obtain ⟨V, hV⟩ := hP
    rw [← hV, hashEnt_append, List.map_append]
    exact List.mem_append_left _ (mem_hashEnt_iff.2 hd)
  refine ⟨?_, fun i hi Δ hΔ inp hinp => ?_⟩
  swap
  · have hi' : tgtC st chO (aliveR E r) = some i := by
      rw [hchO, outChainL, tgtC_withH5]; exact hi
    have hΔ' : Δ ∈ clsPts st chO (aliveR E r) (hdOf (deadR E r)) i := by
      rw [hchO, outChainL, clsPts_withH5]; exact hΔ
    have hinp' : inp ∈ gateIns st chO T Δ := by
      rw [hchO, outChainL, gateIns_withH5]; exact hinp
    rw [hJ]
    exact hPJ _ (hcovO i (clsTarget_mem_wideOther hkp' hi') Δ hΔ' inp hinp')
  -- unfold `E₁^cls`
  unfold e1C
  rw [hx1Of']
  dsimp only
  rw [hGx', hJx']
  have hpc : pcdC (preCore (stE lr) E Gx Jx x1 tbl) x = chE := by
    simp only [pcdC, preCore, hchE, hivq]
    rfl
  rw [show (preCore (stE lr) E Gx Jx x1 tbl).iv = r.2.2.iv from hivq, hpc, ← halive, ← hdead]
  refine congrArg (fun m => toTG (Option.getD m [])) ?_
  -- the prefixes
  have hp : (fun i => preB (candidate (F := GF128) (chE.u (stE lr)) (chE.dc (stE lr)) i)) =
      fun i => preB (candidate (F := GF128) (chO.u st) (chO.dc st) i) := by
    funext t
    refine preB_congr fun n hn => ?_
    have hn' : n < st.params.witnessBits := by
      simp [hst, stG, pomfritRedeemT, pomfritParams, Params.witnessBits]; omega
    refine (candidate_chain_eq (stE lr) _ t hn').trans (Eq.trans ?_
      (candidate_chain_eq st chO t hn').symm)
    have hU : Bridge.uBit (stE lr).params chE.iv (chE.corr (stE lr)) chE.keys t n =
        Bridge.uBit st.params chO.iv (chO.corr st) chO.keys t n := by
      have := congrFun (congrFun hcEO.u t) ⟨n, hn'⟩
      exact this
    have hC : Bridge.corrBit (chE.pf (stE lr)) n = Bridge.corrBit (chO.pf st) n := by
      show Bridge.corrBit ⟨pr, xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119⟩ n =
        Bridge.corrBit ⟨pr, r.1⟩ n
      exact corrBit_pcdU hAs hUs ho4 (by simp [pr, pomfritParams]) (by rw [hxd, hr1]; rfl) hn
    rw [hU, hC]
  have hk : clsKey (stE lr) chE = clsKey st chO := hcEO.clsKey
  unfold clsOut
  refine clsExt_congr_all hk hp fun i hi => ?_
  have hi2 : clsTarget (aliveR E r) (clsKey st chO)
      (fun i => preB (candidate (F := GF128) (chO.u st) (chO.dc st) i)) = some i :=
    (congrArg₂ (fun k q => clsTarget (aliveR E r) k q) hk hp).symm.trans hi
  have hiw := clsTarget_mem_wideOther hkp' hi2
  show clsCertK (chKos st chE T) st chE (aliveR E r) (hdOf (deadR E r)) i ↔
    clsCertK (chKos st chO T) st chO (aliveR E r) (hdOf (deadR E r)) i
  refine (hcEO.clsCertK (chKos st chE T) (aliveR E r) (hdOf (deadR E r)) i).trans ?_
  refine (clsCertK_congr st chO (aliveR E r) (hdOf (deadR E r)) i fun Δ hΔ => ?_).symm
  refine chKos_congr T hcEO.symm ?_ ?_ ?_ Δ fun inp hinp => ?_
  · show (⟨pr, r.1⟩ : Proof).cmult = (⟨pr, xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119⟩ : Proof).cmult
    rw [ByteArray.append_assoc, ByteArray.append_assoc]
    exact (cmult_pcd hxPre ho2 _).symm
  · show (⟨pr, r.1⟩ : Proof).voleCheck =
      (⟨pr, xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119⟩ : Proof).voleCheck
    rw [show xPre pr x1 ++ xU x ++ xDpre x ++ zerosBA 119 =
      xPre pr x1 ++ xU x ++ (xDpre x ++ zerosBA 119) from ByteArray.append_assoc,
      voleCheck_pcd hAs hUs, hxu, hr1]
    rfl
  · show r.2.2.chal1 = xChal1 x
    rw [hxc]
  · have hin := hcovO i hiw Δ hΔ inp hinp
    show h5Of (hashEnt r.2.1.aux.2) inp = (tbl (.h5, inp)).ba
    rw [hJ, h5Of_eq (hashEnt_jOf_ans T st P E g) (hPJ _ hin)]
    have hcons : ∀ e ∈ hashEnt (Pfx ++ axT g lr Pfx x), e = ⟨e.1, g e.1⟩ := by
      intro e he
      rw [hashEnt_append] at he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨V, hV⟩ := hP
        have heJ : e ∈ hashEnt J := by rw [← hV, hashEnt_append]; exact List.mem_append_left _ he
        obtain ⟨rest, hG⟩ := gLog_eq_hashEnt_append T st P E g
        exact gLog_answer T st P E g e (by rw [hG]; exact List.mem_append_left _ heJ)
      · exact axT_consistent g lr Pfx x e he
    have ht := tableOfLog_eq hcons (d := (.h5, inp)) (by
      rw [hashEnt_append, List.map_append]; exact List.mem_append_left _ (mem_hashEnt_iff.2 hin))
    show (g (.h5, inp)).ba = (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) (.h5, inp)).ba
    rw [ht]

end Main

end VoleMole.ROM.OneMore.Pomfrit
