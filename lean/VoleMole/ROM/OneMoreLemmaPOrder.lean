import VoleMole.ROM.OneMoreLemmaPIdent

/-!
# Lemma P's ordering step: `E₁` at query time is the widest group at the end

`lean/docs/security/pomfrit.md` §5, §6.4 (gap G8). The reduction programs the target at `x` with
`E₁(x)` (`e1P`), computed from the log at `x`'s first target query: the first `H₂¹` preimage `x₁` of
`x`'s `chal1`, the trees with no committed dead leaf at `x₁`, and the widest prefix group of their
candidates computed from the committed keys. Lemma P's extraction (`MajorExtracted`) is about the
end of the run: the trees alive at the verifier's `H₂¹` input and the extractor's keys. This file
shows that they agree when `x₁` was queried before `x` (`e1P_eq_major`), and that otherwise the
answer at `x₁` hits the `chal1` field of an earlier marker query `H₃(x)` (`OrderHit`).

* Byte layout: `hash_to_target`'s input has `chal1` at bytes `39 … 175` and `d[0..45)` at bytes
  `239 … 284` for a 32-byte key digest (`xChal1_tgtIn`, `xDpre_tgtIn`).
* `preB_congr`: a candidate's prefix reads its first 360 bits.
* `tableOfLog_eq`: a table read off a consistent log is the table on the logged cells.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim

/-! ## Byte layout of `hash_to_target`'s input -/

section Bytes

lemma toL_extract_toBA (l : List UInt8) (a b : ℕ) :
    toL ((toBA l).extract a b) = (l.drop a).take (b - a) := by
  simp only [VoleMole.Privacy.toL_eq, ByteArray.data_extract, Array.toList_extract, toBA,
    List.extract_eq_take_drop]

lemma targetDst_length : (Spec.PomFRIT.targetDst).length = 7 := by decide

/-- **`chal1` in `hash_to_target`'s input**, for a 32-byte key digest. -/
lemma xChal1_tgtIn {pk : UovPk} {lr : Bool} {sg m c1 : ByteArray} (hd : pk.digest.size = 32)
    (hc : c1.size = 136) : xChal1 (tgtIn pk lr sg m c1) = c1 := by
  refine toL_injective ?_
  rw [xChal1, tgtIn, toL_extract_toBA]
  simp only [Spec.PomFRIT.targetInput, List.append_assoc]
  have h1 : (Spec.PomFRIT.targetDst ++ toL pk.digest).length = 39 := by
    rw [List.length_append, targetDst_length, VoleMole.Privacy.length_toL, hd]
  rw [← List.append_assoc Spec.PomFRIT.targetDst, List.drop_left' h1]
  rw [List.take_left' (by rw [VoleMole.Privacy.length_toL, hc])]

/-- **`d[0..45)` in `hash_to_target`'s input**, for a 32-byte key digest, a 136-byte `chal1` and a
proof of the right length. -/
lemma xDpre_tgtIn {pk : UovPk} {lr : Bool} {sg m c1 : ByteArray} (hd : pk.digest.size = 32)
    (hc : c1.size = 136)
    (hs : (sg.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes) :
    xDpre (tgtIn pk lr sg m c1) =
      (({ params := pomfritParams lr, bytes := sg.extract 0 (pomfritParams lr).proofBytes } :
        Proof).correction.extract 0 45) := by
  refine toL_injective ?_
  rw [xDpre, tgtIn, toL_extract_toBA]
  simp only [Spec.PomFRIT.targetInput, List.append_assoc]
  have h1 : (Spec.PomFRIT.targetDst ++ toL pk.digest ++ toL c1 ++
      toL ({ params := pomfritParams lr, bytes := sg.extract 0 (pomfritParams lr).proofBytes } :
        Proof).voleCheck).length = 239 := by
    simp only [List.length_append, targetDst_length, VoleMole.Privacy.length_toL, hd, hc,
      size_voleCheck hs]
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.drop_left' h1]
  rw [List.take_left' (by rw [VoleMole.Privacy.length_toL, size_correction hs])]

end Bytes

/-! ## A candidate's prefix reads its first 360 bits -/

section PreB

lemma witByte_congr {w w' : ℕ → Bool} {b : ℕ} (h : ∀ j < 8, w (8 * b + j) = w' (8 * b + j)) :
    Keccak.witByte w b = Keccak.witByte w' b := by
  unfold Keccak.witByte
  congr 3
  refine List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

/-- **`preB` reads the first 360 values.** -/
lemma preB_congr {w w' : ℕ → GF128} (h : ∀ n < 360, w n = w' n) : preB w = preB w' := by
  unfold preB bytesOf
  congr 1
  funext k
  refine witByte_congr fun j hj => ?_
  simp only [bitsOf]
  rw [h _ (by omega)]

end PreB

/-! ## A table read off a consistent log -/

lemma tableOfLog_eq {g : Table} {L : QueryLog spec} (hL : ∀ e ∈ L, e = ⟨e.1, g e.1⟩) {d : Dom}
    (hd : d ∈ L.map Sigma.fst) : tableOfLog L d = g d := by
  classical
  have hex : ∃ u, (⟨d, u⟩ : (t : Dom) × Ans t) ∈ L := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact ⟨e.2, he⟩
  unfold tableOfLog
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have h := hL _ hex.choose_spec
  exact eq_of_heq (Sigma.mk.inj h).2

lemma get!_extract_zero {b : ByteArray} {n k : ℕ} (hk : k < n) :
    (b.extract 0 n).get! k = b.get! k := by
  rw [Bridge.byteArray_get!_eq, Bridge.byteArray_get!_eq, ByteArray.data_extract,
    Array.getElem?_extract]
  by_cases hb : k < b.data.size
  · have hb' : k < b.size := hb
    simp [hk, hb']
  · simp only [Nat.zero_add]
    rw [Array.getElem?_eq_none (by omega)]
    split_ifs <;> simp

/-! ## The log at a target query -/

section Aux

lemma firstIn_append_of_some {k : Kind} {ok : ByteArray → Bool} {a w : ByteArray}
    {A B : QueryLog spec} (h : firstIn k ok a A = some w) : firstIn k ok a (A ++ B) = some w := by
  unfold firstIn at h ⊢
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.find?_append, he]
  rfl

variable (g : Table) (lr : Bool)

/-- The reduction's queries at `x`, when `x`'s `chal1` has the `H₂¹` preimage `x₁` in the log. -/
lemma axT_of_some {L : QueryLog specIC} {x x1 : ByteArray} (h : x1Of L x = some x1) :
    axT g lr L x = [⟨.inl (.h3, x), g (.h3, x)⟩, ⟨.inl muCell, g muCell⟩,
      ⟨.inl (ivCell lr x1 (g muCell).ba), g (ivCell lr x1 (g muCell).ba)⟩] := by
  unfold axT auxSpec
  rw [h]
  simp

/-- The reduction's queries at `x`, when `x`'s `chal1` has no `H₂¹` preimage in the log. -/
lemma axT_of_none {L : QueryLog specIC} {x : ByteArray} (h : x1Of L x = none) :
    axT g lr L x = [⟨.inl (.h3, x), g (.h3, x)⟩, ⟨.inl muCell, g muCell⟩] := by
  unfold axT auxSpec
  rw [h]
  simp

lemma hashEnt_consistent {E : CTable} {J : QueryLog specIC}
    (hJ : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩) : ∀ e ∈ hashEnt J, e = ⟨e.1, g e.1⟩ := by
  induction J with
  | nil => simp [hashEnt]
  | cons e J ih =>
    obtain ⟨t, u⟩ := e
    have ih' := ih fun e he => hJ e (List.mem_cons_of_mem _ he)
    cases t with
    | inl d =>
      intro e he
      simp only [hashEnt, List.mem_cons] at he
      rcases he with rfl | he
      · have h := hJ _ List.mem_cons_self
        have := eq_of_heq (Sigma.mk.inj h).2
        simp only at this ⊢
        rw [this]; rfl
      · exact ih' e he
    | inr x => exact ih'

lemma axT_consistent (L : QueryLog specIC) (x : ByteArray) :
    ∀ e ∈ hashEnt (axT g lr L x), e = ⟨e.1, g e.1⟩ := by
  cases h : x1Of L x with
  | some x1 => rw [axT_of_some g lr h]; simp [hashEnt]
  | none => rw [axT_of_none g lr h]; simp [hashEnt]

end Aux

/-! ## `iv` and `mu₁` of PomFRIT's statements -/

section Iv

lemma mu1_stE (lr : Bool) (Hs : Hashes) : (stE lr).mu1 Hs = Hs.hash .muDelayed muCell.2 := by
  simp only [Statement.mu1, stE, mu, muCell, ite_true]

lemma mu1_pomfritRedeemT (pk : UovPk) (hF : ByteArray → ByteArray) (b1 b2 : ByteArray) (lr : Bool)
    (Hs : Hashes) : (pomfritRedeemT pk hF b1 b2 lr).mu1 Hs = Hs.hash .muDelayed muCell.2 := by
  simp only [Statement.mu1, pomfritRedeemT, mu, muCell, ite_true]

lemma ivX_stE (pk : UovPk) (hF : ByteArray → ByteArray) (b1 b2 : ByteArray) (lr : Bool)
    (x1 : ByteArray) (g : Table) :
    ivX (stE lr) x1 g = ivX (pomfritRedeemT pk hF b1 b2 lr) x1 g := by
  simp only [ivX, mu1_stE, mu1_pomfritRedeemT]
  rfl

/-- **`iv` read off the log at a target query** is the table's, when the reduction's queries put
`mu₁` and `iv` there. -/
lemma ivX_tableOfLog (g : Table) (lr : Bool) {Pfx : QueryLog specIC} {x x1 : ByteArray}
    (hx : x1Of Pfx x = some x1) (hc : ∀ e ∈ hashEnt Pfx, e = ⟨e.1, g e.1⟩) :
    ivX (stE lr) x1 (tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x))) = ivX (stE lr) x1 g := by
  have hcons : ∀ e ∈ hashEnt (Pfx ++ axT g lr Pfx x), e = ⟨e.1, g e.1⟩ := by
    rw [hashEnt_append]
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hc e he
    · exact axT_consistent g lr Pfx x e he
  have hax := axT_of_some g lr hx
  have hmu : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) muCell = g muCell := by
    refine tableOfLog_eq hcons ?_
    rw [hashEnt_append, List.map_append, hax]
    simp [hashEnt]
  have hiv : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) (ivCell lr x1 (g muCell).ba) =
      g (ivCell lr x1 (g muCell).ba) := by
    refine tableOfLog_eq hcons ?_
    rw [hashEnt_append, List.map_append, hax]
    simp [hashEnt]
  have hmu' : tableOfLog (hashEnt (Pfx ++ axT g lr Pfx x)) (Kind.muDelayed, muCell.2) =
      g (Kind.muDelayed, muCell.2) := hmu
  simp only [ivX, mu1_stE, Hashes.ofTable]
  rw [hmu']
  exact congrArg Prob.Bytes.ba hiv

end Iv

/-! ## The chain of `E₁` -/

section Pcd

lemma size_zerosBA (n : ℕ) : (zerosBA n).size = n := by
  simp [zerosBA, ByteArray.size]

variable {p : Params} {π A D : ByteArray}

/-- The corrections of `E₁`'s chain (the first `o₂` bytes, then anything) are the proof's. -/
lemma corrections_pcd (hA : A = π.extract 0 p.o₂) (hπ : p.o₂ ≤ π.size) (R : ByteArray) :
    (⟨p, A ++ R⟩ : Proof).corrections = (⟨p, π⟩ : Proof).corrections := by
  have hAs : A.size = p.o₂ := by rw [hA, ByteArray.size_extract]; omega
  rw [corrections_eq, corrections_eq]
  simp only
  rw [extract_append_of_le (by have := o₂_le p; omega), hA, ByteArray.extract_extract]
  rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (o₂_le p)]

/-- **The correction bits `j < 360` of `E₁`'s chain** are the proof's, when the chain carries
`d[0..45)` after `o₂ + 64` bytes. -/
lemma corrBit_pcd (hA : A.size = p.o₂) (hπ : p.o₄ ≤ π.size) (hw : 45 ≤ p.witnessBytes)
    (hD : D = (⟨p, π⟩ : Proof).correction.extract 0 45) {j : ℕ} (hj : j < 360) :
    Bridge.corrBit ⟨p, A ++ zerosBA 64 ++ D ++ zerosBA 119⟩ j = Bridge.corrBit ⟨p, π⟩ j := by
  have hcs : (⟨p, π⟩ : Proof).correction.size = p.witnessBytes := by
    rw [correction_eq, ByteArray.size_extract]
    simp only
    unfold Params.o₄ at hπ ⊢
    omega
  have hDs : D.size = 45 := by
    rw [hD, ByteArray.size_extract, hcs]
    omega
  have key : (⟨p, A ++ zerosBA 64 ++ D ++ zerosBA 119⟩ : Proof).correction.get! (j / 8) =
      (⟨p, π⟩ : Proof).correction.get! (j / 8) := by
    rw [correction_eq]
    simp only
    rw [ByteArray.append_assoc, extract_append_right' (by rw [ByteArray.size_append, hA,
      size_zerosBA])]
    rw [ByteArray.size_append, hA, size_zerosBA, Nat.sub_self,
      get!_extract_zero (by unfold Params.o₄; omega), get!_append_left (by rw [hDs]; omega), hD,
      get!_extract_zero (by omega)]
  unfold Bridge.corrBit
  rw [key]

end Pcd

/-- A candidate's value at a witness row, through the chain's fields. -/
lemma candidate_chain_eq [HasPrg] (st : Statement) (ch : Bridge.Chain) (t : Fin BAVC.tau) {n : ℕ}
    (hn : n < st.params.witnessBits) :
    candidate (F := GF128) (ch.u st) (ch.dc st) t n =
      SeedExtraction.bit (Bridge.uBit st.params ch.iv (ch.corr st) ch.keys t n) +
        SeedExtraction.bit (Bridge.corrBit (ch.pf st) n) := by
  simp only [candidate, extW, hn, dite_true, Bridge.Chain.u, Bridge.Chain.dc]

/-! ## The ordering step -/

section Order

open VoleMole.Verifier.Bridge

variable {β : Type} (T : CrtTables) (st : Statement) (lr : Bool)
  (P : OracleComp specIC (ByteArray × β)) (E : CTable) (g : Table)

lemma ivX_stE_of (hstp : st.params = pomfritParams lr)
    (hmu : ∀ Hs : Hashes, st.mu1 Hs = Hs.hash .muDelayed muCell.2) (x1 : ByteArray) :
    ivX (stE lr) x1 g = ivX st x1 g := by
  simp only [ivX, mu1_stE, hmu, hstp]
  rfl

/-- **Lemma P's ordering step**: if the log `Pfx` before `x`'s first target query (a prefix of `P`'s
log) contains the verifier's `H₂¹` input, then `E₁(x)`, computed from `Pfx` and the reduction's
queries at `x`, is the prefix of the widest group of the output's alive trees, with the extractor's
candidates: the hint is Lemma P's majority prefix (outside the hits and Post). For any statement
with PomFRIT's parameters and `mu₁`. -/
theorem e1P_eq_major (hstp : st.params = pomfritParams lr)
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
    e1P lr E (Pfx ++ axT g lr Pfx x) x =
      toTG ((PomFRIT.majP (aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
        fun t => preB (@candOut (icPrg E.cipher) _ st
          (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) t)).getD []) := by
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
  unfold e1P
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
  refine congrArg (fun m => toTG (Option.getD m [])) ?_
  refine PomFRIT.majP_congr fun t _ => preB_congr fun n hn => ?_
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

end VoleMole.ROM.OneMore.Pomfrit
