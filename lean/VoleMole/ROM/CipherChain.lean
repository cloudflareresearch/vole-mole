import VoleMole.ROM.CipherRelations
import VoleMole.ROM.LogPrefix
import VoleMole.ROM.ChainParse

/-!
# The "same chain" step and L2 in the ideal-cipher model (plan M6, `ε_chain`, `ε_dead`)

`ROM/Accept.lean` assumes that the data committed at the verifier's `H₂¹`, `H₂²`, `H₂³` inputs are
those of the accepted proof's chain (`SameChainHyp`, with L2(c)) and that the accepted `Δ` hides the
committed dead leaves (`DeadHiddenHyp`, L2(a)), outside failure events and per-query "hits". Here
both are proved for the joint hash and ideal-cipher game `gameIC`, with concrete chain data read off
the logs:

* **The committed data** (`preOf`, `midOf`, `accOf`, `deadOf`). At an `H₂¹` input `x`: the `com`
  field of `x`, its first `H₁` preimage `cw` (545 bytes) in the game's hash log before the first
  query of `x`, the first preimages `w_i` of the 17 blocks of `cw`, the leaf commitments (32-byte
  blocks of the `w_i`), and for each leaf the first key in `P`'s cipher log before `x` with that
  commitment (Definition B; zero if none): `preCore`. The corrections, `c_mult` and `iv_pre` are
  parsed from `x` (`ROM/ChainParse.lean`). The **committed dead leaves** (`deadPre`) are the leaves
  with no such key. At an `H₂²` input `y`: the first `H₂¹` preimage of its `chal1` field, and
  `preCore` there, with `ũ`, `h_V`, `d` parsed from `y` (`midCore`). At an `H₂³` input `z`: the
  first `H₂²` preimage of its `chal2` field, `midCore` there, `ã` and the check value parsed from
  `z`; the accepted `chal3` are the challenges on that chain hiding its dead leaves (`tailCore`).
  These read the logs only before the query's own cell, so they are committed
  (`preOf_committed`, …: `logBefore_tableQueryLog_update`).
* **The hits** (`chainHit`): a hash answer at a cell `t` that is a target of the log before `t`
  (`hitTargets`): an `H₁` answer equal to a block of an earlier `com` input, to the `com` field of an
  earlier `H₂¹` input, or to an earlier `H₁` answer; an `H₂¹` answer equal to the `chal1` field of
  an earlier `H₂²` input or to an earlier `H₂¹` answer; an `H₂²` answer equal to the `chal2` field
  of an earlier `H₂³` input or to an earlier `H₂²` answer. Without hits, the verifier's chain
  `w_i → cw → x → y → z` was queried in this order and its cells are the first preimages: L1.4's
  ordering, `Coll₁` and the `H₂¹`, `H₂²` collisions (`chain_ident`).
* **Post** (`PostJ`, C3/L2(c) of `L0-L2`): some cipher query of `P` is the first one at both points
  `w`, `w'` of a key `κ`, and the commitment `E_κ(w) ‖ E_κ(w')` (in either order) is a 32-byte block
  of an earlier `H₁` input. Without it, a key found in the full cipher log for a committed leaf was
  already found before `x` (`extractKey_pre_eq`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Searching a log -/

/-- The input of the first entry of kind `k` of the log `L` whose input satisfies `ok` and whose
answer is `a`. -/
def firstIn (k : Kind) (ok : ByteArray → Bool) (a : ByteArray) (L : QueryLog spec) :
    Option ByteArray :=
  (L.find? fun e : (t : Dom) × Ans t => decide (e.1.1 = k) && ok e.1.2 &&
    decide ((e.2 : Ans e.1).ba = a)).map (·.1.2)

/-- **The first preimage is the unique one**: if `(k, w)` is in `L` with answer `a`, and every entry
of kind `k` with an acceptable input and answer `a` is at `(k, w)`, the search returns `w`. -/
lemma firstIn_eq {k : Kind} {ok : ByteArray → Bool} {a : ByteArray} {L : QueryLog spec}
    {w : ByteArray} (hw : ∃ e ∈ L, e.1 = (k, w) ∧ (e.2 : Ans e.1).ba = a)
    (hok : ok w = true)
    (huniq : ∀ e ∈ L, e.1.1 = k → ok e.1.2 = true → (e.2 : Ans e.1).ba = a → e.1.2 = w) :
    firstIn k ok a L = some w := by
  obtain ⟨e, he, hek, hea⟩ := hw
  unfold firstIn
  set p : (t : Dom) × Ans t → Bool := fun e =>
    decide (e.1.1 = k) && ok e.1.2 && decide ((e.2 : Ans e.1).ba = a)
  have hpe : p e = true := by
    simp only [p, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by rw [hek], by rw [hek]; exact hok⟩, hea⟩
  obtain ⟨e₀, hf⟩ : ∃ e₀, L.find? p = some e₀ :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨e, he, hpe⟩)
  have hp0 : p e₀ = true := List.find?_some hf
  simp only [p, Bool.and_eq_true, decide_eq_true_eq] at hp0
  rw [hf, Option.map_some, huniq e₀ (List.mem_of_find?_eq_some hf) hp0.1.1 hp0.1.2 hp0.2]

/-! ## The chain data read off the logs -/

section Data

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable)

/-- The game's hash log. -/
def gLog (g : Table) : QueryLog spec := tableQueryLog (gameIC T st P E) g

/-- The size of a leaf-hash input of tree `i`: `32·2^{k_i} + 1`. -/
def lhSize (i : ℕ) : ℕ := 32 * 2 ^ BAVC.kOf i + 1

/-- **The commitment of leaf `(i, j)` committed at the `H₂¹` input `x`**, read off the hash log
`Gx` before `x`: block `j` of the first preimage of block `i` of the first preimage of `com`. -/
def comPre (Gx : QueryLog spec) (x : ByteArray) (i j : ℕ) : Option ByteArray := do
  let cw ← firstIn .h1 (fun w => w.size == 545) (xCom x) Gx
  let w ← firstIn .h1 (fun w => w.size == lhSize i) (cw.extract (32 * i) (32 * i + 32)) Gx
  pure (w.extract (32 * j) (32 * j + 32))

/-- `iv = H₄(iv_pre ‖ mu₁ ‖ 4)` with `iv_pre` parsed from `x`. -/
def ivX (x : ByteArray) (g : Table) : ByteArray :=
  (Hashes.ofTable g).hash .h4 ((xIvPre st.params x ++ st.mu1 (Hashes.ofTable g)).push 4)

/-- **The leaf key committed at `x`**: the first key of the cipher log `Jx` before `x` with the
committed commitment (zero if none, and outside the leaf indices). -/
def keyPre (Gx : QueryLog spec) (Jx : QueryLog specIC) (iv x : ByteArray) (i j : ℕ) : ByteArray :=
  if i < BAVC.tau ∧ j < 2 ^ BAVC.kOf i then
    match comPre Gx x i j with
    | some c => ((extractKey (cipherLog Jx) E iv i c).map ba).getD BAVC.zeroBlock
    | none => BAVC.zeroBlock
  else BAVC.zeroBlock

/-- **The committed dead leaves at `x`**: the leaves whose committed commitment has no key in the
cipher log before `x`. -/
def deadPre (Gx : QueryLog spec) (Jx : QueryLog specIC) (iv x : ByteArray) (i : Fin BAVC.tau) :
    Finset ℕ :=
  (range (2 ^ BAVC.kOf i)).filter fun j => (match comPre Gx x i j with
    | some c => (extractKey (cipherLog Jx) E iv i c).isNone
    | none => false) = true

/-- **The chain prefix committed at `x`**, from the logs `Gx`, `Jx` before `x`. -/
def preCore (Gx : QueryLog spec) (Jx : QueryLog specIC) (x : ByteArray) (g : Table) : Chain :=
  { proof := xPre st.params x, keys := keyPre E Gx Jx (ivX st x g) x, iv := ivX st x g,
    h5 := (Hashes.ofTable g).hash .h5, chal1 := ByteArray.empty, hV := #[], z := 0,
    chal2 := ByteArray.empty, vals := fun _ => [] }

/-- **The chain data up to `chal2` committed at `y`**, from the logs `Gy`, `Jy` before `y`: the
prefix at the first `H₂¹` preimage `x` of `y`'s `chal1`, with `ũ`, `h_V`, `d` parsed from `y`. -/
def midCore (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray) (g : Table) : Chain :=
  match firstIn .h21 (fun _ => true) (yChal1 y) Gy with
  | some x =>
    let pc := preCore st E (logBefore (.h21, x) Gy) (logBefore (.inl (.h21, x)) Jy) x g
    { pc with proof := pc.proof ++ yVc y ++ yCorr st.params y, chal1 := yChal1 y, hV := yHV y }
  | none => preCore st E [] [] ByteArray.empty g

/-- The committed dead leaves of the chain at `y`. -/
def midDead (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray) (g : Table) :
    Fin BAVC.tau → Finset ℕ :=
  match firstIn .h21 (fun _ => true) (yChal1 y) Gy with
  | some x => deadPre E (logBefore (.h21, x) Gy) (logBefore (.inl (.h21, x)) Jy) (ivX st x g) x
  | none => fun _ => ∅

/-- **The chain committed at `z`** and its dead leaves, from the logs `Gz`, `Jz` before `z`: the
data at the first `H₂²` preimage `y` of `z`'s `chal2`, with `ã`, `chal2`, the check value and
the constraint evaluator. -/
def tailCore (Gz : QueryLog spec) (Jz : QueryLog specIC) (zi : ByteArray) (g : Table) :
    Chain × (Fin BAVC.tau → Finset ℕ) :=
  match firstIn .h22 (fun _ => true) (zChal2 zi) Gz with
  | some y =>
    let mc := midCore st E (logBefore (.h22, y) Gz) (logBefore (.inl (.h22, y)) Jz) y g
    (⟨mc.proof ++ zQs st.params zi, mc.keys, mc.iv, mc.h5, mc.chal1, mc.hV, zCheck zi, zChal2 zi,
        st.values mc.chal1 (st.combBytes (Hashes.ofTable g) (zChal2 zi))⟩,
      midDead st E (logBefore (.h22, y) Gz) (logBefore (.inl (.h22, y)) Jz) y g)
  | none => (preCore st E [] [] ByteArray.empty g, fun _ => ∅)

/-- **The chain prefix committed at an `H₂¹` input.** -/
def preOf (x : ByteArray) (g : Table) : Chain :=
  preCore st E (logBefore (.h21, x) (gLog T st P E g)) (logBefore (.inl (.h21, x)) (jOf g P E)) x g

/-- **The chain data up to `chal2` committed at an `H₂²` input.** -/
def midOf (y : ByteArray) (g : Table) : Chain :=
  midCore st E (logBefore (.h22, y) (gLog T st P E g)) (logBefore (.inl (.h22, y)) (jOf g P E)) y g

/-- **The `chal3` accepted at an `H₂³` input**: those on the chain committed there that hide its
committed dead leaves. -/
def accOf (z : ByteArray) (g : Table) (b : Prob.Bytes 16) : Prop :=
  let tc := tailCore st E (logBefore (.h23, z) (gLog T st P E g))
    (logBefore (.inl (.h23, z)) (jOf g P E)) z g
  deltaBlocks b ∈ @hideSet (icPrg E.cipher) st T tc.1 tc.2

/-- The committed dead leaves at the `H₂¹` input `x`. -/
def deadAtX (x : ByteArray) (g : Table) : Fin BAVC.tau → Finset ℕ :=
  deadPre E (logBefore (.h21, x) (gLog T st P E g)) (logBefore (.inl (.h21, x)) (jOf g P E))
    (ivX st x g) x

/-- **The committed dead leaves of the accepted proof's chain** (at the verifier's `H₂¹` input). -/
def deadOf (g : Table) : Fin BAVC.tau → Finset ℕ :=
  match @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) with
  | some leaves => deadAtX T st P E (runX (Hashes.ofTable g) st (πOf g P E) leaves) g
  | none => fun _ => ∅

/-! ## The data are committed -/

/-- The kinds of the chain's challenge queries. -/
def ChalKind (k : Kind) : Prop := k = .h21 ∨ k = .h22 ∨ k = .h23

/-- The kinds the chain prefix reads besides its logs (`iv`, `mu₁`, the gate hash) are not these. -/
def MidKind (k : Kind) : Prop := k ≠ .h4 ∧ k ≠ .mu ∧ k ≠ .muDelayed ∧ k ≠ .h5

lemma midKind_of_chalKind {k : Kind} (h : ChalKind k) : MidKind k := by
  rcases h with rfl | rfl | rfl <;> simp [MidKind]

lemma midKind_comb (M : ℕ) : MidKind (.comb M) := by simp [MidKind]

lemma ofTable_update_hash' (g : Table) (t : Dom) (u : Ans t) {k : Kind} (hne : k ≠ t.1) :
    (Hashes.ofTable (Function.update g t u)).hash k = (Hashes.ofTable g).hash k := by
  funext w
  exact hash_ofTable_update_of_ne g t u hne w

lemma ofTable_update_hash (g : Table) (t : Dom) (u : Ans t) {k : Kind} (hk : ChalKind t.1)
    (hk' : ¬ChalKind k) : (Hashes.ofTable (Function.update g t u)).hash k =
      (Hashes.ofTable g).hash k :=
  ofTable_update_hash' g t u fun h : k = t.1 => hk' (by rw [h]; exact hk)

lemma mu1_update (g : Table) (t : Dom) (u : Ans t) (hk : MidKind t.1) :
    st.mu1 (Hashes.ofTable (Function.update g t u)) = st.mu1 (Hashes.ofTable g) := by
  simp only [Statement.mu1, mu]
  rw [ofTable_update_hash' (k := .mu) g t u (Ne.symm hk.2.1),
    ofTable_update_hash' (k := .muDelayed) g t u (Ne.symm hk.2.2.1)]

lemma ivX_update (g : Table) (t : Dom) (u : Ans t) (hk : MidKind t.1) (x : ByteArray) :
    ivX st x (Function.update g t u) = ivX st x g := by
  simp only [ivX]
  rw [mu1_update st g t u hk, ofTable_update_hash' (k := .h4) g t u (Ne.symm hk.1)]

lemma combBytes_update (g : Table) (t : Dom) (u : Ans t) (hk : ChalKind t.1) (c : ByteArray) :
    st.combBytes (Hashes.ofTable (Function.update g t u)) c = st.combBytes (Hashes.ofTable g) c := by
  unfold Statement.combBytes
  split
  · rfl
  · rw [ofTable_update_hash (k := .comb _) g t u hk (by simp [ChalKind])]

lemma preCore_update (Gx : QueryLog spec) (Jx : QueryLog specIC) (x : ByteArray) (g : Table)
    (t : Dom) (u : Ans t) (hk : MidKind t.1) :
    preCore st E Gx Jx x (Function.update g t u) = preCore st E Gx Jx x g := by
  simp only [preCore, ivX_update st g t u hk,
    ofTable_update_hash' (k := .h5) g t u (Ne.symm hk.2.2.2)]

lemma midCore_update (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray) (g : Table)
    (t : Dom) (u : Ans t) (hk : MidKind t.1) :
    midCore st E Gy Jy y (Function.update g t u) = midCore st E Gy Jy y g := by
  simp only [midCore]
  split <;> simp only [preCore_update st E _ _ _ g t u hk]

lemma midDead_update (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray) (g : Table)
    (t : Dom) (u : Ans t) (hk : MidKind t.1) :
    midDead st E Gy Jy y (Function.update g t u) = midDead st E Gy Jy y g := by
  simp only [midDead]
  split <;> simp only [ivX_update st g t u hk]

lemma tailCore_update (Gz : QueryLog spec) (Jz : QueryLog specIC) (z : ByteArray) (g : Table)
    (t : Dom) (u : Ans t) (hk : ChalKind t.1) :
    tailCore st E Gz Jz z (Function.update g t u) = tailCore st E Gz Jz z g := by
  simp only [tailCore]
  split <;> simp only [midCore_update st E _ _ _ g t u (midKind_of_chalKind hk),
    midDead_update st E _ _ _ g t u (midKind_of_chalKind hk), combBytes_update st g t u hk,
    preCore_update st E _ _ _ g t u (midKind_of_chalKind hk)]

lemma logBefore_jOf_update (g : Table) (t : Dom) (u : Ans t) :
    logBefore (.inl t) (jOf (Function.update g t u) P E) = logBefore (.inl t) (jOf g P E) :=
  logBefore_tableQueryLog_congr P (join g E) (join (Function.update g t u) E) (.inl t)
    fun _ h => join_update_inl_of_ne g E t u h

lemma logBefore_gLog_update (g : Table) (t : Dom) (u : Ans t) :
    logBefore t (gLog T st P E (Function.update g t u)) = logBefore t (gLog T st P E g) :=
  logBefore_tableQueryLog_update _ g t u

/-- **The prefix committed at `x` does not read `H₂¹(x)`.** -/
theorem preOf_committed (x : ByteArray) (g : Table) (u : Ans (.h21, x)) :
    preOf T st P E x (Function.update g (.h21, x) u) = preOf T st P E x g := by
  simp only [preOf, logBefore_gLog_update, logBefore_jOf_update]
  exact preCore_update st E _ _ _ g _ u (midKind_of_chalKind (Or.inl rfl))

/-- **The data committed at `y` do not read `H₂²(y)`.** -/
theorem midOf_committed (y : ByteArray) (g : Table) (u : Ans (.h22, y)) :
    midOf T st P E y (Function.update g (.h22, y) u) = midOf T st P E y g := by
  simp only [midOf, logBefore_gLog_update, logBefore_jOf_update]
  exact midCore_update st E _ _ _ g _ u (midKind_of_chalKind (Or.inr (Or.inl rfl)))

/-- **The accepted `chal3` at `z` do not read `H₂³(z)`.** -/
theorem accOf_committed (z : ByteArray) (g : Table) (u : Ans (.h23, z)) :
    accOf T st P E z (Function.update g (.h23, z) u) = accOf T st P E z g := by
  funext b
  simp only [accOf, logBefore_gLog_update, logBefore_jOf_update]
  rw [tailCore_update st E _ _ _ g _ u (Or.inr (Or.inr rfl))]

/-- **The chain data of an issue relation (fixed system) are committed.** -/
theorem chainData_committed (cs : System GF128) :
    (ChainData.ofSys (st := st) (preOf T st P E) (midOf T st P E) cs (accOf T st P E)).Committed :=
  ChainData.ofSys_committed _ _ _ _ (preOf_committed T st P E) (midOf_committed T st P E)
    (accOf_committed T st P E)

/-! ## The hits -/

/-- The answers of the entries of kind `k` of a log. -/
def ansOf (k : Kind) (L : QueryLog spec) : List ByteArray :=
  (L.filter fun e => decide (e.1.1 = k)).map fun e => (e.2 : Ans e.1).ba

/-- The `chal2` fields of the earlier combination inputs (of the statement's combination kind). -/
def combTargets (cb : Option (ℕ × ByteArray)) (pre : QueryLog spec) : List ByteArray :=
  match cb with
  | some (M, _) => (kindIns (.comb M) (pre.map Sigma.fst)).map (·.extract 0 56)
  | none => []

/-- The number of combination queries a hit bound must charge. -/
def combCount (cb : Option (ℕ × ByteArray)) (n : Kind → ℕ) : ℕ :=
  match cb with
  | some (M, _) => n (.comb M)
  | none => 0

/-- **The targets of a hit of kind `k`**, given the log `pre` before the hit's cell: the 17 blocks of
the earlier `com` inputs (545 bytes), the `com` fields of the earlier `H₂¹` inputs and the earlier
`H₁` answers (`H₁`); the `chal1` fields of the earlier `H₂²` inputs and the earlier `H₂¹` answers
(`H₂¹`); the `chal2` fields of the earlier `H₂³` inputs and of the earlier combination inputs, and
the earlier `H₂²` answers (`H₂²`). -/
def hitTargets (cb : Option (ℕ × ByteArray)) (pre : QueryLog spec) : Kind → List ByteArray
  | .h1 => ((kindIns .h1 (pre.map Sigma.fst)).filter (·.size == 545)).flatMap
        (fun w => (List.range 17).map fun i => w.extract (32 * i) (32 * i + 32)) ++
      (kindIns .h21 (pre.map Sigma.fst)).map xCom ++ ansOf .h1 pre
  | .h21 => (kindIns .h22 (pre.map Sigma.fst)).map yChal1 ++ ansOf .h21 pre
  | .h22 => (kindIns .h23 (pre.map Sigma.fst)).map zChal2 ++ ansOf .h22 pre ++ combTargets cb pre
  | _ => []

/-- **A hit**: the answer at the cell `t` is a target of the game's log before `t`. -/
def chainHit (t : Dom) (g : Table) : Prop :=
  (g t).ba ∈ hitTargets st.comb (logBefore t (gLog T st P E g)) t.1

/-- The bound of a hit of each kind, for a game with `n k` queries of kind `k` and `nc`
combination queries. -/
noncomputable def hitEps (n : Kind → ℕ) (nc : ℕ) : Kind → ℝ≥0∞
  | .h1 => ((18 * n .h1 + n .h21 : ℕ) : ℝ≥0∞) / 2 ^ 256
  | .h21 => ((n .h22 + n .h21 : ℕ) : ℝ≥0∞) / 2 ^ 1088
  | .h22 => ((n .h23 + n .h22 + nc : ℕ) : ℝ≥0∞) / 2 ^ 448
  | _ => 0

lemma hitEps_eq_zero (n : Kind → ℕ) (nc : ℕ) : ∀ k ∉ hitKinds, hitEps n nc k = 0 := by
  intro k hk
  cases k <;> simp_all [hitKinds, hitEps]

lemma length_kindIns_le_of_sublist {k : Kind} {L L' : List Dom} (h : L.Sublist L') :
    (kindIns k L).length ≤ (kindIns k L').length := by
  unfold kindIns
  rw [List.length_map, List.length_map]
  exact (h.filter _).length_le

lemma logBefore_sublist {D : Type} {R : D → Type} [DecidableEq D] (d : D)
    (L : QueryLog (ofFn R)) : (logBefore d L).Sublist L :=
  List.takeWhile_sublist _

lemma length_ansOf (k : Kind) (L : QueryLog spec) :
    (ansOf k L).length = (kindIns k (L.map Sigma.fst)).length := by
  unfold ansOf kindIns
  rw [List.length_map, List.length_map, List.filter_map, List.length_map]
  rfl

/-- **The queries of each kind of a computation's log** are within its budget. -/
theorem length_kindIns_tableQueryLog_le {α : Type} (oa : OracleComp spec α) {q : Kind → ℕ}
    (hq : IsKindQueryBound oa q) (g : Table) (k : Kind) :
    (kindIns k ((tableQueryLog oa g).map Sigma.fst)).length ≤ q k := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => simp [kindIns]
  | query_bind t k' ih =>
    obtain ⟨h0, hk⟩ := isKindQueryBound_query_bind_iff.1 hq
    rw [tableQueryLog_query_bind, List.map_cons, kindIns_cons]
    have h := ih (g t) (hk (g t))
    by_cases hkt : t.1 = k
    · subst hkt
      simp only [↓reduceIte, List.length_cons]
      rw [Function.update_self] at h
      omega
    · simp only [hkt, ↓reduceIte]
      rwa [Function.update_of_ne (Ne.symm hkt)] at h

lemma length_combTargets_le (cb : Option (ℕ × ByteArray)) (pre : QueryLog spec) (n : Kind → ℕ)
    (hn : ∀ k, (kindIns k (pre.map Sigma.fst)).length ≤ n k) :
    (combTargets cb pre).length ≤ combCount cb n := by
  rcases cb with _ | ⟨M, dst⟩
  · simp [combTargets, combCount]
  · simp only [combTargets, combCount, List.length_map]
    exact hn _

lemma length_hitTargets_le (cb : Option (ℕ × ByteArray)) (pre : QueryLog spec) (n : Kind → ℕ)
    (hn : ∀ k, (kindIns k (pre.map Sigma.fst)).length ≤ n k) (k : Kind) :
    ((hitTargets cb pre k).length : ℝ≥0∞) / 2 ^ (8 * k.outLen) ≤ hitEps n (combCount cb n) k := by
  cases k
  case h1 =>
    have h1 := hn .h1
    have h21 := hn .h21
    have hf : (((kindIns .h1 (pre.map Sigma.fst)).filter (·.size == 545)).flatMap
        (fun w => (List.range 17).map fun i => w.extract (32 * i) (32 * i + 32))).length ≤
          17 * n .h1 := by
      rw [List.length_flatMap]
      simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate,
        smul_eq_mul]
      have := (List.filter_sublist (p := fun w : ByteArray => w.size == 545)
        (l := kindIns .h1 (pre.map Sigma.fst))).length_le
      nlinarith
    have hl : (hitTargets cb pre .h1).length ≤ 18 * n .h1 + n .h21 := by
      simp only [hitTargets, List.length_append, List.length_map, length_ansOf]
      omega
    simp only [hitEps, Kind.outLen]
    gcongr
  case h21 =>
    have hl : (hitTargets cb pre .h21).length ≤ n .h22 + n .h21 := by
      simp only [hitTargets, List.length_append, List.length_map, length_ansOf]
      have := hn .h22; have := hn .h21; omega
    simp only [hitEps, Kind.outLen]
    gcongr
  case h22 =>
    have hl : (hitTargets cb pre .h22).length ≤ n .h23 + n .h22 + combCount cb n := by
      simp only [hitTargets, List.length_append, List.length_map, length_ansOf]
      have := hn .h23; have := hn .h22; have := length_combTargets_le cb pre n hn; omega
    simp only [hitEps, Kind.outLen]
    gcongr
  all_goals simp [hitTargets, hitEps]

/-- **A hit has probability `≤ hitEps n` when its cell alone is resampled**, for a game with at
most `n k` queries of each kind: the log before the cell, hence the targets, do not depend on the
cell. -/
theorem prEvent_chainHit_le (n : Kind → ℕ) (hn : IsKindQueryBound (gameIC T st P E) n)
    (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[chainHit T st P E t (Function.update g t u)] ≤
      hitEps n (combCount st.comb n) t.1 := by
  have h : ∀ u : Ans t, chainHit T st P E t (Function.update g t u) ↔
      u.ba ∈ hitTargets st.comb (logBefore t (gLog T st P E g)) t.1 := fun u => by
    simp only [chainHit, Function.update_self, logBefore_gLog_update]
  simp_rw [h]
  refine (prEvent_ba_mem_le t.1.outLen _).trans
    (length_hitTargets_le st.comb _ n (fun k => ?_) t.1)
  exact (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
    (length_kindIns_tableQueryLog_le _ hn g k)

end Data

/-! ## Post: a committed leaf commitment hit by a later key (C3) -/

section Post

/-- **The commitments a Post query can hit**: the pairs of blocks of the 32-byte blocks `jj < 256`
of the `H₁` inputs of a joint-log prefix, in both orders. -/
noncomputable def postTargets (pre : QueryLog specIC) : Finset (Blk × Blk) :=
  ((kindIns .h1 (hashLog pre)).flatMap fun w => (List.range 256).flatMap fun jj =>
    [split32 (w.extract (32 * jj) (32 * jj + 32)),
      (split32 (w.extract (32 * jj) (32 * jj + 32))).swap]).toFinset

lemma card_postTargets_le (pre : QueryLog specIC) :
    #(postTargets pre) ≤ 512 * (kindIns .h1 (hashLog pre)).length := by
  unfold postTargets
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  rw [List.length_flatMap]
  simp only [List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- **Post** (`L0-L2` C3, in the PRF view): some cipher query of the joint log `J`, at a point `w`
of a key `κ`, is the first query of `κ` at `w` and at a neighbour `w'` of `w`, and the blocks
`E_κ(w)`, `E_κ(w')` form (in some order) a 32-byte block of an earlier `H₁` input. -/
def PostJ (E : CTable) (J : QueryLog specIC) : Prop :=
  ∃ pre e post, J = pre ++ e :: post ∧ ∃ κ w, e.1 = .inr (κ, w) ∧ ∃ w' ∈ adj w,
    (.inr (κ, w) : DomIC) ∉ pre.map Sigma.fst ∧ (.inr (κ, w') : DomIC) ∉ pre.map Sigma.fst ∧
    (E (κ, w), E (κ, w')) ∈ postTargets pre

/-- Post, for the game's output (the joint log is in `aux`). -/
def PostOut {β : Type} (E : CTable) (r : Out (β × QueryLog specIC)) : Prop := PostJ E r.2.1.aux.2

/-- The prefix of a joint log before its `k`-th cipher entry. -/
def beforeCipher : ℕ → QueryLog specIC → QueryLog specIC
  | _, [] => []
  | k, ⟨.inl d, u⟩ :: L => ⟨.inl d, u⟩ :: beforeCipher k L
  | 0, ⟨.inr _, _⟩ :: _ => []
  | k + 1, ⟨.inr x, u⟩ :: L => ⟨.inr x, u⟩ :: beforeCipher k L

/-- The cell of the `k`-th cipher entry of a joint log. -/
def kthCell : ℕ → QueryLog specIC → Option Cell
  | _, [] => none
  | k, ⟨.inl _, _⟩ :: L => kthCell k L
  | 0, ⟨.inr x, _⟩ :: _ => some x
  | k + 1, ⟨.inr _, _⟩ :: L => kthCell k L

lemma beforeCipher_kthCell {pre : QueryLog specIC} {e : (t : DomIC) × AnsIC t}
    {post : QueryLog specIC} {x : Cell} (he : e.1 = .inr x) :
    beforeCipher (cipherLog pre).length (pre ++ e :: post) = pre ∧
      kthCell (cipherLog pre).length (pre ++ e :: post) = some x := by
  obtain ⟨t, u⟩ := e
  simp only at he
  subst he
  induction pre with
  | nil => exact ⟨rfl, rfl⟩
  | cons p pre ih =>
    obtain ⟨t', u'⟩ := p
    cases t' with
    | inl d =>
      have hc : cipherLog (⟨Sum.inl d, u'⟩ :: pre) = cipherLog pre := rfl
      rw [hc, List.cons_append]
      exact ⟨by simp only [beforeCipher]; rw [ih.1], by simp only [kthCell]; exact ih.2⟩
    | inr y =>
      have hc : (cipherLog (⟨Sum.inr y, u'⟩ :: pre)).length = (cipherLog pre).length + 1 := by
        show (⟨y, u'⟩ :: cipherLog pre).length = _
        rfl
      rw [hc, List.cons_append]
      exact ⟨by simp only [beforeCipher]; rw [ih.1], by simp only [kthCell]; exact ih.2⟩

lemma sublist_hashLog_of_append {pre post : QueryLog specIC} :
    (hashLog pre).Sublist (hashLog (pre ++ post)) := by
  induction pre with
  | nil => exact List.nil_sublist _
  | cons p pre ih =>
    obtain ⟨t, u⟩ := p
    cases t with
    | inl d =>
      show (d :: hashLog pre).Sublist (d :: hashLog (pre ++ post))
      exact ih.cons_cons d
    | inr x => exact ih

/-- **`P`'s cipher queries** are within its budget. -/
theorem length_cipherLog_le {α : Type} (P : OracleComp specIC α) {n : ℕ}
    (hn : IsQueryBoundP P (fun t => t.isRight = true) n) (f : (t : DomIC) → AnsIC t) :
    (cipherLog (tableQueryLog P f)).length ≤ n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [tableQueryLog_query_bind]
    cases t with
    | inl d =>
      simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false] at hn
      exact ih _ (hn.2 _)
    | inr x =>
      simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true] at hn
      have := ih _ (hn.2 (f (.inr x)))
      show (⟨x, f (.inr x)⟩ :: cipherLog (tableQueryLog (k (f (.inr x))) f)).length ≤ n
      rw [List.length_cons]
      omega

variable {β : Type} (P : OracleComp specIC (ByteArray × β))

/-- `w'`, the neighbour of `w` selected by `b`. -/
def adjB (b : Bool) (w : Blk) : Blk := if b then nxt w else prv w

lemma adjB_ne (b : Bool) (w : Blk) : adjB b w ≠ w := by
  cases b
  · exact prv_ne w
  · exact nxt_ne w

/-- Post at the `k`-th cipher query, with the neighbour `adjB b`. -/
def PostAt (h : Table) (k : ℕ) (b : Bool) (E : CTable) : Prop :=
  ∃ pre e post, jOf h P E = pre ++ e :: post ∧ (cipherLog pre).length = k ∧ ∃ κ w,
    e.1 = .inr (κ, w) ∧ (.inr (κ, w) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, adjB b w) : DomIC) ∉ pre.map Sigma.fst ∧ (E (κ, w), E (κ, adjB b w)) ∈ postTargets pre

/-- **Post at a fixed query and neighbour** has probability `≤ 512·q₁·2⁻²⁵⁶` (two fresh cells
hitting at most `512 q₁` targets, `prEvent_two_cells_le`). -/
theorem prEvent_postAt_le (h : Table) (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) (k : ℕ)
    (b : Bool) :
    Pr{let E ← $ᵗ CTable}[PostAt P h k b E] ≤ ((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  let c₁ : CTable → Cell := fun E => (kthCell k (jOf h P E)).getD default
  let c₂ : CTable → Cell := fun E => ((c₁ E).1, adjB b (c₁ E).2)
  let T : CTable → Finset (Blk × Blk) := fun E => postTargets (beforeCipher k (jOf h P E))
  -- The data of an occurrence.
  have hdat : ∀ E, PostAt P h k b E → ∃ pre e post κ w, jOf h P E = pre ++ e :: post ∧
      (cipherLog pre).length = k ∧ e.1 = .inr (κ, w) ∧ c₁ E = (κ, w) ∧
      beforeCipher k (jOf h P E) = pre ∧ (.inr (κ, w) : DomIC) ∉ pre.map Sigma.fst ∧
      (.inr (κ, adjB b w) : DomIC) ∉ pre.map Sigma.fst ∧
      (E (κ, w), E (κ, adjB b w)) ∈ postTargets pre := by
    rintro E ⟨pre, e, post, hJ, hk, κ, w, he, h1, h2, h3⟩
    have hs := beforeCipher_kthCell (pre := pre) (post := post) he
    rw [hk, ← hJ] at hs
    exact ⟨pre, e, post, κ, w, hJ, hk, he, by simp only [c₁, hs.2, Option.getD_some], hs.1, h1,
      h2, h3⟩
  refine (prEvent_two_cells_le (PostAt P h k b) c₁ c₂ T (512 * q .h1) ?_ ?_ ?_ ?_).trans le_rfl
  · intro E hE
    obtain ⟨pre, e, post, κ, w, -, -, -, hc, -⟩ := hdat E hE
    simp only [c₂, hc]
    intro heq
    exact adjB_ne b w (congrArg Prod.snd heq).symm
  · intro E hE w₀
    obtain ⟨pre, e, post, κ, w, hJ, hk, he, hc, hb, h1, h2, -⟩ := hdat E hE
    have hc₂ : c₂ E = (κ, adjB b w) := by simp only [c₂, hc]
    set E' := upd2 E (c₁ E) (c₂ E) w₀
    have hag : ∀ t ∈ pre.map Sigma.fst, join h E' t = join h E t := by
      intro t ht
      cases t with
      | inl d => rfl
      | inr x =>
        show E' x = E x
        refine upd2_apply_of_ne E (fun hx => h1 ?_) (fun hx => h2 ?_) w₀
        · rw [← hc, ← hx]; exact ht
        · rw [← hc₂, ← hx]; exact ht
    obtain ⟨post', hJ'⟩ := tableQueryLog_prefix_congr P (join h E) (join h E') pre e post hJ hag
    have hs := beforeCipher_kthCell (pre := pre) (post := post')
      (e := ⟨e.1, join h E' e.1⟩) he
    rw [hk] at hs
    have hJ'' : jOf h P E' = pre ++ ⟨e.1, join h E' e.1⟩ :: post' := hJ'
    have hc' : c₁ E' = c₁ E := by
      simp only [c₁, hJ'', hs.2, Option.getD_some, hc]
    refine ⟨hc', by simp only [c₂, hc'], ?_⟩
    simp only [T, hJ'', hs.1, hb]
  · intro E hE
    obtain ⟨pre, e, post, κ, w, hJ, -, -, -, hb, -⟩ := hdat E hE
    simp only [T, hb]
    refine (card_postTargets_le pre).trans (Nat.mul_le_mul_left _ ?_)
    have h1 := length_kindIns_le_of_sublist (k := .h1) (sublist_hashLog_of_append (pre := pre)
      (post := e :: post))
    rw [← hJ] at h1
    exact h1.trans (length_kindIns_hashLog_le P hq (join h E) .h1)
  · intro E hE
    obtain ⟨pre, e, post, κ, w, -, -, -, hc, hb, -, -, h3⟩ := hdat E hE
    simp only [T, hb, c₂, hc]
    exact h3

/-- **Post has probability `≤ 1024·q_E·q₁·2⁻²⁵⁶`** over the cipher table, at every hash table. -/
theorem prEvent_postJ_le (h : Table) (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable}[PostJ E (jOf h P E)] ≤
      ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  classical
  refine (prEvent_mono _ _ (fun E => ∃ i ∈ (range qE ×ˢ (univ : Finset Bool)), PostAt P h i.1 i.2 E)
    fun E hE => ?_).trans ?_
  · obtain ⟨pre, e, post, hJ, κ, w, he, w', hw', h1, h2, h3⟩ := hE
    have hlen : (cipherLog pre).length < qE := by
      have := length_cipherLog_le P hqE (join h E)
      have hJ' : tableQueryLog P (join h E) = pre ++ e :: post := hJ
      obtain ⟨t, u⟩ := e
      simp only at he
      subst he
      rw [hJ'] at this
      have hcl : cipherLog (pre ++ ⟨.inr (κ, w), u⟩ :: post) =
          cipherLog pre ++ ⟨(κ, w), u⟩ :: cipherLog post := by
        simp [cipherLog, List.filterMap_append]
      rw [hcl, List.length_append, List.length_cons] at this
      omega
    have hb : w' = adjB (decide (w' = nxt w)) w := by
      rcases mem_adj.1 hw' with h' | h'
      · simp [adjB, h']
      · by_cases hn : w' = nxt w
        · simp [adjB, hn]
        · simp [adjB, h']
    refine ⟨((cipherLog pre).length, decide (w' = nxt w)), Finset.mem_product.2
      ⟨Finset.mem_range.2 hlen, Finset.mem_univ _⟩, pre, e, post, hJ, rfl, κ, w, he, h1, ?_, ?_⟩
    · rw [← hb]; exact h2
    · rw [← hb]; exact h3
  · have hc := prEvent_exists_finset_le_card_mul (range qE ×ˢ (univ : Finset Bool))
      ($ᵗ CTable) (fun (i : ℕ × Bool) E => PostAt P h i.1 i.2 E)
      (ε := ((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)
      fun i _ => prEvent_postAt_le P h q hq i.1 i.2
    refine hc.trans (le_of_eq ?_)
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool]

/-- **Post in the joint experiment**: `≤ 1024·q_E·q₁·2⁻²⁵⁶`. -/
theorem prEvent_joint_postOut_le (T : CrtTables) (st : Statement) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        PostOut E r] ≤
      ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  have h := prEvent_joint_le_add (gameIC T st P) (fun E r => PostOut E r) (fun _ _ => False)
    (((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostOut, gameIC_aux]
      exact prEvent_postJ_le P g qE hqE q hq
  rwa [prEvent_joint_false, add_zero] at h

end Post

end VoleMole.ROM.IC
