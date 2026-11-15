import VoleMole.Theft.JointProver
import VoleMole.Theft.JointLean

/-!
# The simulator's programming is a point reader confined to its `iv`

`real_sim_leN_lean` (`Theft/JointLean.lean`) asks for the earlier simulators' programmings as
table readers **confined to their `iv`s** (`Conf`, hypothesis `hRpg`). The programming `progRO`
programs `H₂³` at the grinding points of the prefix the verifier recomputes from the simulated
proof (`outPre`, `vPre`). `vPre` was known to read the cipher only at the **keys** of the BAVC
reconstruction (`vPre_ic_congr`, `rdKeys`). Here, at points:

* `reconstruct_ic_congrP`, `rdKeys_ic_congrP`: the BAVC reconstruction from an opening, with `iv`,
  reads the cipher only at the CTR blocks of `iv` of its nodes, and its nodes are then the same;
* **`vPre_ic_congrP`**, `vIn5_ic_congrP`: the recomputed prefix and the verifier's `H₅` inputs read
  the cipher only at those points;
* **`progPtRd`**: the programming's new `H₂³` table as a consistent table reader: no slice key,
  the verifier's `≤ 312` `H₅` gate inputs, the points `(node, CTR block of the proof's iv)` of the
  reconstruction's `≤ 4607` nodes;
* **`progPtRd_conf`**: it is confined to the simulated output's `iv` (`ivV`), within `(312, 4607)`;
  `Conf.of_iv`: and to any `iv` decoder that only returns `ivV`'s value (`ivO` of
  `real_sim_leN_lean`, hypothesis `hiv`), so `lProgRd_conf` is `hRpg`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Arith

/-! ## The BAVC reconstruction at points -/

section Recon

variable {E E' : Cipher} {iv opening delta : ByteArray}

/-- **The tables agree at the reconstruction's points**: at every node key of the reconstruction
(computed with `E`), on every CTR block of `iv`. -/
def RecAgreeP (E E' : Cipher) (iv opening delta : ByteArray) : Prop :=
  ∀ k ∈ rdKeys E iv opening delta, PtsAgree E E' k iv

/-- **The derivation reads the table only at its nodes' points.** -/
theorem derivedN_ic_congrP (h : RecAgreeP E E' iv opening delta) :
    ∀ N ≤ BAVC.numLeaves - 1,
      @derivedN (icPrg E) iv opening delta N = @derivedN (icPrg E') iv opening delta N := by
  have hLN : BAVC.numLeaves - 1 < BAVC.numNodes := by decide
  intro N
  induction N with
  | zero => intro _; exact (@derivN_zero (icPrg E) iv _).trans (@derivN_zero (icPrg E') iv _).symm
  | succ N ih =>
    intro hN
    rewrite [@derivedN_succ (icPrg E), @derivedN_succ (icPrg E'), ← ih (by omega)]
    rcases hA : (@derivedN (icPrg E) iv opening delta N)[N]! with _ | node
    · simp only [BAVC.deriveStep, hA]
    · have hmem : blk 16 node ∈ rdKeys E iv opening delta := by
        have := @mem_rdKeys E iv opening delta N (by omega)
        rwa [@recTree_get (icPrg E) iv opening delta N (by omega) node hA] at this
      have hc : @BAVC.children (icPrg E) iv node N = @BAVC.children (icPrg E') iv node N := by
        unfold BAVC.children
        rw [icPrg_congrP (fun _ => h _ hmem)]
      simp only [BAVC.deriveStep, hA, hc]

theorem recTree_ic_congrP (h : RecAgreeP E E' iv opening delta) :
    @recTree (icPrg E) iv opening delta = @recTree (icPrg E') iv opening delta := by
  unfold recTree
  rewrite [derivedN_ic_congrP h _ le_rfl]
  rfl

/-- **The reconstruction's nodes are the same** for tables that agree at its points. -/
theorem rdKeys_ic_congrP (h : RecAgreeP E E' iv opening delta) :
    rdKeys E' iv opening delta = rdKeys E iv opening delta := by
  unfold rdKeys
  rw [recTree_ic_congrP h]

/-- **The reconstruction reads the table only at its nodes' points.** -/
theorem reconstruct_ic_congrP (h : RecAgreeP E E' iv opening delta) :
    @BAVC.reconstruct (icPrg E) iv opening delta = @BAVC.reconstruct (icPrg E') iv opening delta := by
  have ht := recTree_ic_congrP h
  rewrite [@reconstruct_eq (icPrg E), @reconstruct_eq (icPrg E'), ← ht]
  split_ifs with hb
  · rfl
  · rewrite [@leavesOf_eq (icPrg E), @leavesOf_eq (icPrg E')]
    simp only [Option.some.injEq, BAVC.Leaves.mk.injEq, true_and]
    apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
    refine pieces_congr fun i hi j hj => ?_
    split_ifs
    · rfl
    · exact icPrg_congrP (fun _ => h _ (mem_rdKeys (treePos_lt hi hj))) _ _ _

/-- **The VOLE expansion from the reconstruction reads the table only at its nodes' points.** -/
theorem convertToVole_ic_congrP (h : RecAgreeP E E' iv opening delta) (pf : Proof)
    (hd : pf.delta = delta) {leaves : BAVC.Leaves}
    (hl : @BAVC.reconstruct (icPrg E) iv opening delta = some leaves) :
    @convertToVole (icPrg E) pf iv leaves = @convertToVole (icPrg E') pf iv leaves := by
  unfold convertToVole
  refine convertToVoleAt_ic_congrP _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_
  have := @leafKey_mem_rdKeys E iv opening delta i j hi hj (by rw [← hd]; exact hjd)
  rw [hl, Option.getD_some] at this
  exact this hs

end Recon

/-! ## The recomputed prefix at points -/

section VPre

variable {E E' : Cipher}

/-- The `iv` of a proof under a record. -/
abbrev pfIv (Hs : Hashes) (st : Statement) (b : ByteArray) : ByteArray :=
  ivOf Hs ⟨st.params, b⟩ (st.mu1 Hs)

/-- **The verifier's recomputed prefix reads the cipher only at the reconstruction's points.** -/
theorem vPre_ic_congrP (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : RecAgreeP E E' (pfIv Hs st proof) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta) :
    @vPre (icPrg E) Hs T st proof = @vPre (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congrP h
  show @vPreP (icPrg E) Hs T st pf = @vPreP (icPrg E') Hs T st pf
  unfold vPreP
  rcases hl : @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with _ | leaves
  · rw [← hr, hl]
  · rw [← hr, hl]
    have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves :=
      convertToVole_ic_congrP h pf rfl hl
    simp only [vPreOf, hc]

/-- **The verifier's `H₅` inputs read the cipher only at the reconstruction's points.** -/
theorem vIn5_ic_congrP (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : RecAgreeP E E' (pfIv Hs st proof) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta) :
    @vIn5 (icPrg E) Hs T st proof = @vIn5 (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congrP h
  unfold vIn5
  dsimp only
  rcases hl : @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with _ | leaves
  · rw [← hr, hl]
  · rw [← hr, hl]
    have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves :=
      convertToVole_ic_congrP h pf rfl hl
    exact congrArg (gateInputs st.params T _) hc

/-- The verifier's `H₅` inputs are gate inputs of the proof's `iv`. -/
lemma vIn5_gate {Hs : Hashes} (hHs : HashesWF Hs) {T : CrtTables} {st : Statement} {p : Params}
    (hp : st.params = p) {proof : ByteArray} {x : ByteArray} (hx : x ∈ @vIn5 (icPrg E) Hs T st proof) :
    Gate5 p T (pfIv Hs st proof) (blk 37 x) := by
  unfold vIn5 at hx
  dsimp only at hx
  split at hx
  · simp at hx
  · subst hp
    rw [gateInputs_eq_off] at hx
    have hsz : (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)).size = 16 := by
      unfold ivOf; exact hHs .h4 _
    exact gate5_of_mem hsz hx

end VPre

/-! ## The programming as a confined point reader -/

section Prog

attribute [local irreducible] simulate

variable (p : Params) (Hb : Hashes) (st : Statement)

/-- **The `iv` of an output** (empty for an error). -/
noncomputable def oIv (o : Except String ByteArray) : ByteArray :=
  match o with
  | .ok b => pfIv Hb st b
  | .error _ => .empty

/-- **The cipher points the programming reads**: the reconstruction's nodes at the CTR blocks of
the simulated proof's `iv`. -/
noncomputable def progPtsE (o : Except String ByteArray) (s : Sh p) : Finset (Blk × Blk) :=
  ptsOf (progKeysE Hb st o s) (oIv Hb st o)

variable {p Hb st}

lemma progKeysE_ok (b : ByteArray) (s : Sh p) :
    progKeysE Hb st (.ok b) s = rdKeys s.2.2 (pfIv Hb st b) (⟨st.params, b⟩ : Proof).opening
      (⟨st.params, b⟩ : Proof).delta := by
  simp only [progKeysE, pfIv, ivOf, rec5_h4, rec5_mu1, rowFn_fn]

lemma progKeys5_ok (b : ByteArray) (s : Sh p) :
    progKeys5 Hb st (.ok b) s =
      ((@vIn5 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st b).toFinset).image (blk 37) := by
  unfold progKeys5
  rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ _ (rec5_mu1 _) (rec5_h4 _)]

/-- **The programming reads at points, consistently**: tables with the same `H₂³` that agree with
`s` on its `H₅` keys and at its cipher points give the same new `H₂³` table and the same reads. -/
theorem progPt_cons (c : SimCoins p) (s s' : Sh p) (h2 : s'.1 = s.1)
    (h5 : ∀ k ∈ progKeys5 Hb st (simulate p c) s, s.2.1 k = s'.2.1 k)
    (hE : ∀ kz ∈ progPtsE p Hb st (simulate p c) s, s.2.2 kz.1 kz.2 = s'.2.2 kz.1 kz.2) :
    (progRO p Hb st c s').1 = (progRO p Hb st c s).1 ∧
      progKeys5 Hb st (simulate p c) s' = progKeys5 Hb st (simulate p c) s ∧
      progPtsE p Hb st (simulate p c) s' = progPtsE p Hb st (simulate p c) s := by
  rcases ho : simulate p c with e | b
  · refine ⟨?_, by simp only [progKeys5], by simp only [progPtsE, progKeysE]⟩
    simp only [progRO, outPre, ho, h2]
  -- the cipher agrees at the reconstruction's points
  have hA : RecAgreeP s.2.2 s'.2.2 (pfIv Hb st b) (⟨st.params, b⟩ : Proof).opening
      (⟨st.params, b⟩ : Proof).delta := by
    intro k hk c' t
    refine hE (k, _) ?_
    rw [ho, progPtsE, mem_ptsOf, progKeysE_ok]
    exact ⟨hk, c', t, rfl⟩
  have hA' : RecAgreeP s.2.2 s'.2.2 (pfIv (rec5 Hb s'.2.1) st b) (⟨st.params, b⟩ : Proof).opening
      (⟨st.params, b⟩ : Proof).delta := by
    simpa only [pfIv, ivOf, rec5_h4, rec5_mu1] using hA
  have hI : @vIn5 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st b =
      @vIn5 (icPrg (rowFn s'.2.2)) Hb CrtGen.tables st b := vIn5_ic_congrP Hb CrtGen.tables st b hA
  have k5 : progKeys5 Hb st (.ok b) s' = progKeys5 Hb st (.ok b) s := by
    rw [progKeys5_ok, progKeys5_ok, hI]
  have kE : progKeysE Hb st (.ok b) s' = progKeysE Hb st (.ok b) s := by
    rw [progKeysE_ok, progKeysE_ok, rdKeys_ic_congrP hA]
  refine ⟨?_, k5, by simp only [progPtsE, kE]⟩
  -- the new table: first the cipher, then `H₅`
  have o1 : @vPre (icPrg (rowFn s'.2.2)) (rec5 Hb s'.2.1) CrtGen.tables st b =
      @vPre (icPrg (rowFn s.2.2)) (rec5 Hb s'.2.1) CrtGen.tables st b :=
    (vPre_ic_congrP _ _ _ _ hA').symm
  have o2 : @vPre (icPrg (rowFn s.2.2)) (rec5 Hb s'.2.1) CrtGen.tables st b =
      @vPre (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables st b := by
    have hmu : st.mu1 (rec5 Hb s'.2.1) = st.mu1 (rec5 Hb s.2.1) := by rw [rec5_mu1, rec5_mu1]
    have h4 : (rec5 Hb s'.2.1).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
    have hAg : (rec5 Hb s'.2.1).AgreeOff .h5 (rec5 Hb s.2.1) := by
      intro k hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
    refine @vPre_h5_congr (icPrg (rowFn s.2.2)) _ _ hAg _ _ _ fun x hx => ?_
    rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ _ hmu h4] at hx
    refine withTable_h5_congr _ fun _ => (h5 _ ?_).symm
    rw [ho]
    simp only [progKeys5]
    exact mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩
  simp only [progRO, outPre, ho, h2, o1, o2]

variable (Hb st)

/-- **The simulator's programming as a consistent table point reader**: no slice key, the
verifier's `H₅` gate inputs, the reconstruction's nodes at the CTR blocks of the proof's `iv`. -/
noncomputable def progPtRd (c : SimCoins p) :
    TRd (fun (_ : Tab3) (s : Sh p) => (progRO p Hb st c s).1) where
  Q3 _ _ := ∅
  Q5 _ s := progKeys5 Hb st (simulate p c) s
  QE _ s := progPtsE p Hb st (simulate p c) s
  cons _ s _ s' _ hA := by
    obtain ⟨a, b, c⟩ := progPt_cons c s s' hA.1 hA.2.1 hA.2.2
    exact ⟨a, rfl, b, c⟩

lemma progPtRd_Q5 (c : SimCoins p) (g : Tab3) (s : Sh p) :
    (progPtRd Hb st c).Q5 g s = progKeys5 Hb st (simulate p c) s := rfl

lemma progPtRd_QE (c : SimCoins p) (g : Tab3) (s : Sh p) :
    (progPtRd Hb st c).QE g s = progPtsE p Hb st (simulate p c) s := rfl

variable {Hb st}

/-- **The programming's reader is confined to the simulated output's `iv`**, within `(312, 4607)`. -/
theorem progPtRd_conf (hHb : HashesWF Hb) (hp : st.params = p) (c : SimCoins p) :
    Conf (progPtRd Hb st c) (fun _ => ivV Hb st (simulate p c)) 312 4607 where
  h3 _ _ := rfl
  h5 g s := by
    rw [progPtRd_Q5]
    unfold progKeys5
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
    · simp
  hE g s := by
    rw [progPtRd_QE]
    refine card_fst_ptsOf_le.trans ?_
    unfold progKeysE
    split
    · exact rdKeys_card _ _ _ _
    · simp
  in5 g s v hv k hk := by
    rw [progPtRd_Q5] at hk
    rcases ho : simulate p c with e | b
    · rw [ho] at hv; cases hv
    · rw [ho] at hv hk
      simp only [ivV, Option.some.injEq] at hv
      rw [progKeys5_ok] at hk
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hk
      rw [← hv]
      exact vIn5_gate hHb hp (List.mem_toFinset.1 hx)
  inE g s v hv kz hkz := by
    rw [progPtRd_QE] at hkz
    rcases ho : simulate p c with e | b
    · rw [ho] at hv; cases hv
    · rw [ho] at hv hkz
      simp only [ivV, Option.some.injEq] at hv
      rw [progPtsE, mem_ptsOf] at hkz
      rw [← hv]
      exact hkz.2

/-- **A confined reader is confined to any `iv` that only returns its `iv`.** -/
theorem Conf.of_iv {Y : Type*} {F : Tab3 → Sh p → Y} {R : TRd F} {iv iv' : Sh p → Option ByteArray}
    {a5 aE : ℕ} (hc : Conf R iv a5 aE) (h : ∀ s v, iv' s = some v → iv s = some v) :
    Conf R iv' a5 aE where
  h3 := hc.h3
  h5 := hc.h5
  hE := hc.hE
  in5 g s v hv := hc.in5 g s v (h s v hv)
  inE g s v hv := hc.inE g s v (h s v hv)

end Prog

/-! ## `real_sim_leN_lean`'s hypothesis `hRpg` -/

section Lean

variable {X : Type} {I O : Type*} {p : Params}

/-- **The programmings of a game of Lean proofs as point readers.** -/
noncomputable def lProgRd (Hb : X → Hashes) (stOf : I → Statement) (x : X) (xI : I)
    (c : SimCoins p) : TRd (fun (_ : Tab3) s => (lProg p Hb stOf x xI c s).1) :=
  progPtRd (Hb x) (stOf xI) c

/-- **`real_sim_leN_lean`'s `hRpg`**, with `(m₅, m_E) = (312, 4607)`. -/
theorem lProgRd_conf (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x)) (stOf : I → Statement)
    (hp : ∀ xI, (stOf xI).params = p) (φ : Except String ByteArray → O)
    (ivO : X → I → O → Option ByteArray)
    (hiv : ∀ x xI e v, ivO x xI (φ e) = some v → ivV (Hb x) (stOf xI) e = some v)
    (x : X) (xI : I) (c : SimCoins p) :
    Conf (lProgRd Hb stOf x xI c) (fun _ => ivO x xI (lSim p φ xI c)) 312 4607 :=
  (progPtRd_conf (hHb x) (hp xI) c).of_iv fun _ v h => hiv x xI _ v h

end Lean

end VoleMole.Theft
