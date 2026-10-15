import VoleMole.ZK.HopsROM

/-!
# Which oracle inputs the prover reads (the side conditions of `ZK/HopsROM.lean`)

The random-oracle hops of `ZK/HopsROM.lean` replace one hash domain by a uniform table. Two of
them need to know where the prover reads that domain:

* **Grinding.** `grind_rom` needs the grinding prefix to be a function of the coins, not of the
  `H₂³` table. `realPre_pendAt_congr`: the prefix `realPre … (pendAt …)` (step 1 at the seed and
  `iv_pre`, then `chal2 ‖ qs_check ‖ ã`) is the same for any two hash records that agree off `H₂³`.
  So with `H₂³` a table, the prefix is the base record's (`realPre_withTable_h23`), and
  `grind_rom_prover`, `grind_rom_program_prover` are `grind_rom`, `grind_rom_program` for the
  prover's own prefix, computed with the table.
* **H6.** The ideal-tape prover reads `H₅` only at its *active* gate inputs, the verifier's
  `gateInputs` at the key columns `q` (`proveIdeal_h5_congr`): `c_mult`'s forced gate hashes are
  there (`forcedInput_eq`), and so are the CRT reconstruction's. The sibling input, by contrast,
  is the active label plus `u_pre` (`sibInput_eq`): `L^{1−γ_e}_e = L_e(q) ⊕ u_pre`.

`Hashes.AgreeOff k Hs Hs'`: the records agree on every domain but `k`.
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Records that agree off one domain -/

/-- `Hs` and `Hs'` agree on every domain but `k`. -/
def _root_.VoleMole.Verifier.Hashes.AgreeOff (k : Kind) (Hs Hs' : Hashes) : Prop :=
  ∀ k', k' ≠ k → Hs.hash k' = Hs'.hash k'

lemma _root_.VoleMole.Verifier.Hashes.agreeOff_withTable (Hs : Hashes) (k : Kind) {K : Type}
    (enc : K → ByteArray) (G : K → Bytes k.outLen) : Hs.AgreeOff k (Hs.withTable k enc G) :=
  fun k' hk' => (funext (Hashes.withTable_ne Hs k k' hk' enc G)).symm

section Agree

variable {k : Kind} {Hs Hs' : Hashes} (h : Hs.AgreeOff k Hs')
include h

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.mu1 (h1 : k ≠ .mu) (h2 : k ≠ .muDelayed) (st : Statement) :
    st.mu1 Hs = st.mu1 Hs' := by
  simp only [Statement.mu1, VoleMole.Verifier.mu, h .mu (Ne.symm h1), h .muDelayed (Ne.symm h2)]

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.muDelayed (h1 : k ≠ .mu) (st : Statement) :
    st.muDelayed Hs = st.muDelayed Hs' := by
  funext c
  simp only [Statement.muDelayed, VoleMole.Verifier.mu, h .mu (Ne.symm h1)]

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.combBytes (h1 : ∀ M, k ≠ .comb M) (st : Statement) :
    st.combBytes Hs = st.combBytes Hs' := by
  funext c
  unfold Statement.combBytes
  split
  · rfl
  · rw [h _ (Ne.symm (h1 _))]

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.chal1 (h1 : k ≠ .h21) : VoleMole.Verifier.chal1 Hs = VoleMole.Verifier.chal1 Hs' := by
  funext pf a b c
  simp only [VoleMole.Verifier.chal1, h .h21 (Ne.symm h1)]

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.chal2 (h1 : k ≠ .h22) : VoleMole.Verifier.chal2 Hs = VoleMole.Verifier.chal2 Hs' := by
  funext pf a b c d
  simp only [VoleMole.Verifier.chal2, h .h22 (Ne.symm h1)]

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.pubOf (h1 : k ≠ .mu) (h2 : k ≠ .muDelayed) (h3 : k ≠ .h4) (h4 : k ≠ .h1)
    (st : Statement) : pubOf Hs st = pubOf Hs' st := by
  funext s d
  simp only [Sim.pubOf, h.mu1 h1 h2, h .h4 (Ne.symm h3), h .h1 (Ne.symm h4)]

end Agree

/-! ## The grinding prefix does not read `H₂³` -/

section Grind

variable {Hs Hs' : Hashes} (T : CrtTables) (st : Statement) (w : ByteArray)

/-- Step 1 does not read `H₂³`. -/
lemma pendAt_congr (h : Hs.AgreeOff .h23 Hs') (wPrefix : ByteArray) (x : Bytes 16 × Bytes 16) :
    pendAt Hs T st wPrefix x = pendAt Hs' T st wPrefix x := by
  simp only [pendAt, voleGenAt, h.mu1 (by decide) (by decide), h .h4 (by decide),
    h .h1 (by decide), h .h5 (by decide), h.chal1 (by decide)]

/-- `chal2 ‖ qs_check ‖ ã` does not read `H₂³`. -/
lemma realPre_congr (h : Hs.AgreeOff .h23 Hs') (s : Prover.Pending) :
    realPre Hs st s w = realPre Hs' st s w := by
  simp only [realPre, realC2, h.chal2 (by decide), h.muDelayed (by decide) st,
    h.combBytes (fun _ => nofun) st]

/-- **The grinding prefix does not read `H₂³`**: it is the same for any two hash records that
agree off `H₂³`. -/
theorem realPre_pendAt_congr (h : Hs.AgreeOff .h23 Hs') (wPrefix : ByteArray)
    (x : Bytes 16 × Bytes 16) :
    realPre Hs st (pendAt Hs T st wPrefix x) w = realPre Hs' st (pendAt Hs' T st wPrefix x) w := by
  rw [pendAt_congr T st h, realPre_congr st w h]

end Grind

section GrindROM

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- The prover's grinding prefix, with the base record. -/
def prePrefix (x : Bytes 16 × Bytes 16) : ByteArray :=
  realPre Hs st (pendAt Hs T st (w.extract 0 st.params.witnessBytes) x) w

/-- With `H₂³` a table, the prover's grinding prefix is the base record's. -/
lemma realPre_withTable_h23 (G : GKey → Bytes 16) (x : Bytes 16 × Bytes 16) :
    let Hs' := Hs.withTable .h23 (gEnc (prePrefix Hs T st w)) G
    realPre Hs' st (pendAt Hs' T st (w.extract 0 st.params.witnessBytes) x) w =
      prePrefix Hs T st w x :=
  (realPre_pendAt_congr T st w (Hs.agreeOff_withTable .h23 _ G) _ x).symm

/-- **The grinding hop in the ROM, for the prover's own prefix**: with `H₂³` a uniform table on
the grinding points, the `H₂³` answers at the grinding points of the prover's prefix (computed with
the table) are uniform and independent of the seed and `iv_pre`. This is `GrindHyp` with `ε = 0`
for the record with the table, averaged over the table (`HopHyps.grind`'s prefix). -/
theorem grind_rom_prover :
    Close 0 (fun p : (Bytes 16 × Bytes 16) × (GKey → Bytes 16) =>
        let Hs' := Hs.withTable .h23 (gEnc (prePrefix Hs T st w)) p.2
        (p.1.1, p.1.2, realGrind Hs'
          (realPre Hs' st (pendAt Hs' T st (w.extract 0 st.params.witnessBytes) p.1) w)))
      (id : Bytes 16 × Bytes 16 × Grind → _) :=
  (grind_rom (prePrefix Hs T st w) Hs).congr (fun p => by
    simp only [realPre_withTable_h23]) fun _ => rfl

/-- **Programming `H₂³` at the prover's grinding points is perfect** (`grind_rom_program` for the
prover's own prefix, computed with the table). -/
theorem grind_rom_program_prover
    (A : Bytes 16 × Bytes 16 → Grind → (GKey → Bytes 16) → Prop) :
    pr ((Bytes 16 × Bytes 16) × (GKey → Bytes 16)) (fun p =>
        let Hs' := Hs.withTable .h23 (gEnc (prePrefix Hs T st w)) p.2
        A p.1 (realGrind Hs'
          (realPre Hs' st (pendAt Hs' T st (w.extract 0 st.params.witnessBytes) p.1) w)) p.2) =
      pr ((Bytes 16 × Bytes 16) × ((GKey → Bytes 16) × Grind))
        (fun p => A p.1 p.2.2 (programAt (grindKey (prePrefix Hs T st w) p.1) p.2.2 p.2.1)) := by
  simp only [realPre_withTable_h23]
  exact grind_rom_program (prePrefix Hs T st w) Hs A

end GrindROM

/-! ## The gate inputs on the prover's tags -/

section Gates

variable (p : Params) (T : CrtTables)

/-- `u_pre`: the 128 label rows of `u`. -/
def uPreOf (u : Array UInt64) : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩

/-- The label rows of the first 120 columns, as blocks. -/
def topsOf (cols : Array (Array UInt64)) : Array W128 :=
  (Array.range 120).map fun c => ⟨wordAt cols[c]! p.labelRowOffset, wordAt cols[c]! (p.labelRowOffset + 64)⟩

/-- The label `L_e` of gate `e` from the columns `cols`. -/
def labelOf (cols : Array (Array UInt64)) (e : ℕ) : W128 :=
  W128.rowMul (fun c => wbit T.g[c]! e) 120 (topsOf p cols)

lemma gateInputsOff_getD (iv : ByteArray) (cols : Array (Array UInt64)) (off : W128) {e : ℕ}
    (he : e < 312) : (Prover.gateInputsOff p T iv cols off).getD e .empty =
      (AES.pushLE32 iv e.toUInt32 ++ ((labelOf p T cols e).xor off).toBytes).push 5 := by
  simp only [Prover.gateInputsOff, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show e < p.nMult from he), Option.map_some, Option.getD_some]
  rfl

lemma gateInputs_eq_off (iv : ByteArray) (cols : Array (Array UInt64)) :
    gateInputs p T iv cols = Prover.gateInputsOff p T iv cols W128.zero := by
  simp only [gateInputs, Prover.gateInputsOff]
  congr 1
  funext e
  congr 3
  simp [W128.xor, W128.zero]

/-- On the label rows, the prover's tag columns are `q_c ⊕ Δ_c · u`, word by word. -/
lemma wordAt_tagCols (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (dbit : ℕ → Bool)
    (q : Array (Array UInt64)) (u : Array UInt64) {c : ℕ} (hc : c < 120)
    (hq : p.colBytes / 8 ≤ (q[c]!).size) {o : ℕ} (ho : o + 64 ≤ p.labelRowOffset + 128) :
    wordAt (tagCols dbit q u)[c]! o = wordAt q[c]! o ^^^ (if dbit c then wordAt u o else 0) := by
  have hrl := correctionRows_lt p
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hs : s < 64
  · rw [UInt64.toNat_xor, Nat.testBit_xor, wordAt_testBit _ _ hs, wordAt_testBit _ _ hs,
      tagCols, getElem!_range_map _ _ (by omega)]
    split_ifs with hd
    · rw [wbit_xorWords _ _ (by omega), wordAt_testBit _ _ hs]
    · simp
  · rw [uint64_testBit_lt _ (by omega), uint64_testBit_lt _ (by omega)]

lemma xor_xor_self (a : W128) : a.xor a = W128.zero := by
  simp [W128.xor, W128.zero]

lemma xor_zero' (a : W128) : a.xor W128.zero = a := by
  simp [W128.xor, W128.zero]

lemma zero_xor' (a : W128) : W128.zero.xor a = a := by
  simp [W128.xor, W128.zero]

/-- **The label on the prover's tags**: `L_e(q ⊕ Δ·u) = L_e(q) ⊕ γ_e · u_pre`, `γ = Δ · G`. -/
lemma labelOf_tagCols (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (dbit : ℕ → Bool)
    (q : Array (Array UInt64)) (u : Array UInt64)
    (hq : ∀ c < 120, p.colBytes / 8 ≤ (q[c]!).size) {e : ℕ} (he : e < 312) :
    labelOf p T (tagCols dbit q u) e = (labelOf p T q e).xor
      (if wbit (gammaOf T dbit) e then uPreOf p u else W128.zero) := by
  have htop : ∀ c < 120, ((topsOf p (tagCols dbit q u))[c]!).toGF =
      ((topsOf p q)[c]!).toGF + (if dbit c then (uPreOf p u).toGF else 0) := by
    intro c hc
    rw [topsOf, topsOf, getElem!_range_map _ _ hc, getElem!_range_map _ _ hc,
      wordAt_tagCols p hlab dbit q u hc (hq c hc) (by omega),
      wordAt_tagCols p hlab dbit q u hc (hq c hc) (by omega)]
    split <;> rfl
  apply Bridge.W128.ext_toGF
  rw [labelOf, labelOf, toGF_xor, rowMul_toGF, rowMul_toGF, toGF_ite,
    Finset.sum_congr rfl fun c hc => by rw [htop c (Finset.mem_range.1 hc)],
    ← CrtCheck.gf2_zb_mul, zb_wbit_gammaOf _ _ (by omega), map_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases wbit T.g[c]! e <;> cases dbit c <;> simp

/-- The prover's gate inputs: offset `off` on its tags is offset `off ⊕ γ_e · u_pre` on `q`. -/
lemma gateInputsOff_tagCols (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (iv : ByteArray)
    (dbit : ℕ → Bool) (q : Array (Array UInt64)) (u : Array UInt64)
    (hq : ∀ c < 120, p.colBytes / 8 ≤ (q[c]!).size) (off : W128) {e : ℕ} (he : e < 312) :
    (Prover.gateInputsOff p T iv (tagCols dbit q u) off).getD e .empty =
      (Prover.gateInputsOff p T iv q
        (off.xor (if wbit (gammaOf T dbit) e then uPreOf p u else W128.zero))).getD e .empty := by
  rw [gateInputsOff_getD p T _ _ _ he, gateInputsOff_getD p T _ _ _ he,
    labelOf_tagCols p T hlab dbit q u hq he]
  congr 3
  apply Bridge.W128.ext_toGF
  simp only [toGF_xor]
  ring

/-- **The forced gate input** (`L^{γ_e}_e`, whose `H₅` answer the prover reads) is the verifier's
`L_e(q)`. -/
lemma forcedInput_eq (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (iv : ByteArray)
    (dbit : ℕ → Bool) (q : Array (Array UInt64)) (u : Array UInt64)
    (hq : ∀ c < 120, p.colBytes / 8 ≤ (q[c]!).size) {e : ℕ} (he : e < 312) :
    (if wbit (gammaOf T dbit) e then Prover.gateInputsOff p T iv (tagCols dbit q u) (uPreOf p u)
      else Prover.gateInputsOff p T iv (tagCols dbit q u) W128.zero).getD e .empty =
      (Prover.gateInputsOff p T iv q W128.zero).getD e .empty := by
  split <;> rename_i hg <;>
    simp only [gateInputsOff_tagCols p T hlab iv dbit q u hq _ he, hg, ↓reduceIte,
      Bool.false_eq_true, xor_xor_self]

/-- **The sibling gate input** (`L^{1−γ_e}_e`) is `L_e(q) ⊕ u_pre`. -/
lemma siblingInput_eq (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (iv : ByteArray)
    (dbit : ℕ → Bool) (q : Array (Array UInt64)) (u : Array UInt64)
    (hq : ∀ c < 120, p.colBytes / 8 ≤ (q[c]!).size) {e : ℕ} (he : e < 312) :
    (if wbit (gammaOf T dbit) e then Prover.gateInputsOff p T iv (tagCols dbit q u) W128.zero
      else Prover.gateInputsOff p T iv (tagCols dbit q u) (uPreOf p u)).getD e .empty =
      (Prover.gateInputsOff p T iv q (uPreOf p u)).getD e .empty := by
  split <;> rename_i hg <;>
    simp only [gateInputsOff_tagCols p T hlab iv dbit q u hq _ he, hg, ↓reduceIte,
      Bool.false_eq_true, zero_xor', xor_zero']

lemma toBytes_injective : Function.Injective W128.toBytes := by
  intro a b h
  have e : ∀ x : W128, x.toBytes = bytesOfWords #[x.lo, x.hi] := fun _ => rfl
  have h2 := congrArg wordsOf ((e a).symm.trans (h.trans (e b)))
  rw [wordsOf_bytesOfWords, wordsOf_bytesOfWords] at h2
  have h0 : a.lo = b.lo := by simpa using congrArg (·[0]!) h2
  have h1 : a.hi = b.hi := by simpa using congrArg (·[1]!) h2
  cases a; cases b
  simp_all

/-- **A gate input determines its gate and its offset.** -/
lemma gateInputsOff_getD_inj (iv : ByteArray) (q : Array (Array UInt64)) {v v' : W128}
    {e e' : Fin 312}
    (h : (Prover.gateInputsOff p T iv q v).getD e .empty =
      (Prover.gateInputsOff p T iv q v').getD e' .empty) : e = e' ∧ v = v' := by
  have h1 := congrArg (fun b => AES.getLE32 b iv.size) h
  simp only [getLE32_gateInput] at h1
  have h2 := congrArg UInt32.toNat h1
  rw [toNat_toUInt32 (by have := e.isLt; omega), toNat_toUInt32 (by have := e'.isLt; omega)] at h2
  have hee : e = e' := Fin.ext h2
  subst hee
  refine ⟨rfl, ?_⟩
  rw [gateInputsOff_getD p T _ _ _ e.isLt, gateInputsOff_getD p T _ _ _ e.isLt] at h
  have h3 := toBytes_injective ((ByteArray.append_right_inj _).1 (push_injective 5 h))
  have h4 := congrArg W128.toGF h3
  simp only [toGF_xor] at h4
  exact Bridge.W128.ext_toGF (add_left_cancel h4)

end Gates

/-! ## The ideal-tape prover reads `H₅` only at the active gate inputs -/

section Reads

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- The verifier's key columns `q` of a tape (from the opening, `Δ` and the corrections). -/
def qcolsTape (s : Shared) (t : Pads st.params) : Array (Array UInt64) :=
  qcolsOf st (pubOf Hs st s (deltaOf s.2.1)) (deltaOf s.2.1)
    (correctionsOf st.params (usOf st.params t))

/-- **The active gate inputs of a tape**: `iv ‖ e ‖ L_e(q) ‖ 5` (the verifier's gate inputs; the
prover's at `L^{γ_e}_e`). -/
def actInputs (s : Shared) (t : Pads st.params) : List ByteArray :=
  Prover.gateInputsOff st.params T (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsTape Hs st s t)
    W128.zero

lemma qcolsOf_size (P : Pub) (delta : Bytes 16) (c : ByteArray) :
    ∀ c' < 120, st.params.colBytes / 8 ≤ ((qcolsOf st P delta c)[c']!).size :=
  fun _ hc => convertToVoleAt_col_size _ _ _ _ _ hc

lemma getD_mem_of_lt {L : List ByteArray} {e : ℕ} (he : e < L.length) : L.getD e .empty ∈ L := by
  rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he

variable {Hs} {Hs' : Hashes}

lemma gateHashesIdeal_congr (gamma : Array UInt64) (b : Bool) (ins : List ByteArray)
    (sib : Fin 312 → Bytes 4)
    (h : ∀ e < 312, wbit gamma e = b →
      Hs.hash .h5 (ins.getD e .empty) = Hs'.hash .h5 (ins.getD e .empty)) :
    gateHashesIdeal Hs gamma b ins sib = gateHashesIdeal Hs' gamma b ins sib := by
  unfold gateHashesIdeal
  congr 1
  refine List.map_congr_left fun e he => ?_
  have he := List.mem_range.1 he
  split
  · rename_i hb; rw [h e he (by simpa using hb)]
  · rfl

/-- `c_mult` reads `H₅` at the forced gate inputs only, which are the verifier's. -/
lemma cmultIdeal_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (P : Pub) (delta : Bytes 16) (qcols : Array (Array UInt64)) (u : Array UInt64)
    (uMask : Array W128) (sib : Fin 312 → Bytes 4)
    (hq : ∀ c < 120, st.params.colBytes / 8 ≤ (qcols[c]!).size)
    (h : ∀ e < 312, Hs.hash .h5 ((Prover.gateInputsOff st.params T P.iv qcols W128.zero).getD e .empty) =
      Hs'.hash .h5 ((Prover.gateInputsOff st.params T P.iv qcols W128.zero).getD e .empty)) :
    cmultIdeal Hs T st P delta qcols u uMask sib = cmultIdeal Hs' T st P delta qcols u uMask sib := by
  have key : ∀ e < 312, (if wbit (gammaOf T (BAVC.deltaBit (ba delta))) e then
      Prover.gateInputsOff st.params T P.iv (tagCols (BAVC.deltaBit (ba delta)) qcols u)
        ⟨wordAt u st.params.labelRowOffset, wordAt u (st.params.labelRowOffset + 64)⟩
      else Prover.gateInputsOff st.params T P.iv (tagCols (BAVC.deltaBit (ba delta)) qcols u)
        W128.zero).getD e .empty =
      (Prover.gateInputsOff st.params T P.iv qcols W128.zero).getD e .empty := fun e he =>
    forcedInput_eq st.params T hlab P.iv _ qcols u hq he
  unfold cmultIdeal
  dsimp only
  rw [gateHashesIdeal_congr (Hs := Hs) (Hs' := Hs') _ false _ _ fun e he hg => by
      have k := key e he
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at k
      rw [k]; exact h e he,
    gateHashesIdeal_congr (Hs := Hs) (Hs' := Hs') _ true _ _ fun e he hg => by
      have k := key e he
      simp only [hg, ↓reduceIte] at k
      rw [k]; exact h e he]

/-- The CRT reconstruction reads `H₅` at the verifier's gate inputs only. -/
lemma tCrt_congr (hoff : Hs.AgreeOff .h5 Hs') (s : Shared) (delta : Bytes 16) (c cm : ByteArray)
    (h : ∀ y ∈ gateInputs st.params T (pubOf Hs st s delta).iv
      (qcolsOf st (pubOf Hs st s delta) delta c), Hs.hash .h5 y = Hs'.hash .h5 y) :
    tCrt Hs T st s delta c cm = tCrt Hs' T st s delta c cm := by
  unfold tCrt crtReconstructAt gateHashes
  rw [← hoff.pubOf (by decide) (by decide) (by decide) (by decide) st, List.map_congr_left h]

/-- The rest of the run reads `H₅` only through the CRT reconstruction. -/
lemma idealTail_congr (hoff : Hs.AgreeOff .h5 Hs') (s : Shared) (ctr : ℕ) (delta : Bytes 16)
    (corrections cmult : ByteArray) (uMask : Array W128) (ubits : Array Bool)
    (correction : ByteArray)
    (htc : tCrt Hs T st s delta corrections cmult = tCrt Hs' T st s delta corrections cmult) :
    idealTail Hs T st w s ctr delta corrections cmult uMask ubits correction =
      idealTail Hs' T st w s ctr delta corrections cmult uMask ubits correction := by
  simp only [idealTail, tVRows, tVMask, tUt, tC1, htc,
    hoff.pubOf (by decide) (by decide) (by decide) (by decide) st, hoff.chal1 (by decide),
    hoff.chal2 (by decide), hoff.muDelayed (by decide) st, hoff.combBytes (fun _ => nofun) st]

/-- **The ideal-tape prover reads `H₅` only at the active gate inputs** `L_e(q)` of its tape: two
hash records that agree off `H₅`, and on `H₅` at `actInputs`, give the same output. -/
theorem proveIdeal_h5_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hoff : Hs.AgreeOff .h5 Hs') (x : IdealTape st.params)
    (h : ∀ y ∈ actInputs Hs T st x.1 x.2, Hs.hash .h5 y = Hs'.hash .h5 y) :
    proveIdeal Hs T st w x = proveIdeal Hs' T st w x := by
  obtain ⟨s, t⟩ := x
  have hP := hoff.pubOf (by decide) (by decide) (by decide) (by decide) st
  unfold proveIdeal
  split
  · rfl
  rcases hg : firstHit s.2.1 with _ | ⟨ctr, delta⟩
  · rfl
  have hdel : deltaOf s.2.1 = delta := by simp only [deltaOf, hg, Option.map_some, Option.getD_some]
  simp only [actInputs, qcolsTape, hdel] at h
  dsimp only
  unfold idealCore
  dsimp only
  rw [← hP]
  have hlen := gateInputsOff_length st.params T (pubOf Hs st s delta).iv
    (qcolsOf st (pubOf Hs st s delta) delta (correctionsOf st.params (usOf st.params t))) W128.zero
  rw [cmultIdeal_congr T st hlab _ _ _ _ _ _ (qcolsOf_size st _ _ _) fun e he =>
    h _ (getD_mem_of_lt (by omega))]
  refine idealTail_congr T st w hoff _ _ _ _ _ _ _ _ (tCrt_congr T st hoff _ _ _ _ fun y hy => ?_)
  rw [gateInputs_eq_off] at hy
  exact h y hy

end Reads

end VoleMole.ZK.Sim
