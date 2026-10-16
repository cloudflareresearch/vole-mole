import VoleMole.ROM.AdaptComb

/-!
# Adaptively chosen statements: PomFRIT (delayed instance binding)

PomFRIT binds its instance late: `iv` and `chal1` use `mu₁ = H₂⁴(DST ‖ 12)`, and the instance
enters `chal2`'s input through `μ = H₂⁰(dig(pk) ‖ h(chal1) ‖ DST ‖ 8)`, with
`h(chal1) = hash_to_target(pk, chal1, sig, msg)` (`pomfritRedeem`). Compared with
`ROM/AdaptChain.lean`, `ROM/AdaptComb.lean`:

* **The statement is committed at `H₂²`**, by the `μ` field of the `H₂²` input (`yMu`, bytes
  `264 … 296`, after `chal1 ‖ ũ ‖ h_V`). `stmtAtD`: at an `H₂²` input `y`, the decoding at
  `chal1 = yChal1 y` of the first `H₂⁰` preimage of `yMu y` in the log before `y`; at an `H₂³`
  input, that at the first `H₂²` preimage of its `chal2`; at an `H₂¹` input, a fixed *reference*
  statement (`none`): nothing there depends on the instance. Statement hits (`stmtHitD`): an `H₂⁰`
  answer equal to the `μ` field of an earlier `H₂²` input or to an earlier `H₂⁰` answer.
* **The decoding recovers the target, not the statement**: it returns some statement whose
  instance encoding at that `chal1` is the preimage (`decD`), so some `(sig', msg')` with
  `h'(chal1) = h(chal1)`; the system and the relation read only the target, and the chain-level
  functions read the statement only through `params` (and `delayed`, `dst`). Two transports
  make this usable: of `chainBad`/`combBad` between statements with equal `params`
  (`chainBad_transport`, `combBad_transport`: destructure, `subst`, `Iff.rfl`), and of the chain
  data between statements with equal `params`, `delayed = true`, `dst`, and (for the accepted
  `chal3`) equal values at the chain's `chal1` (`preCore_congrD`, `midCore_congrD`,
  `tailCore_congrD`, `hideSet_transport`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Transport between statements with the same parameters -/

/-- **`chainBad` reads the statement only through its parameters.** -/
theorem chainBad_transport {st st' : Statement} (h : st.params = st'.params) (C : ChainData st)
    [HasPrg] (T : CrtTables) (S : Finset Blocks) (N : ℕ) (t : Dom) (g : Table) :
    chainBad C T S N t g ↔
      chainBad (st := st') ⟨C.preOf, C.midOf, C.csOf, C.accOf⟩ T S N t g := by
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  obtain ⟨p', d', dl', b1', b2', ie', cb', v'⟩ := st'
  simp only at h
  subst h
  exact Iff.rfl

/-- **`combBad` reads the statement only through its parameters.** -/
theorem combBad_transport {st st' : Statement} {M : ℕ} (h : st.params = st'.params)
    (C : CombData st M) [HasPrg] (T : CrtTables) (S : Finset Blocks) (N : ℕ) (t : Dom)
    (g : Table) :
    combBad C T S N t g ↔ combBad (st := st')
      ⟨C.preOf, C.midOf, C.sysOf, C.witOf, C.accOf, C.dst, C.pre⟩ T S N t g := by
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  obtain ⟨p', d', dl', b1', b2', ie', cb', v'⟩ := st'
  simp only at h
  subst h
  exact Iff.rfl

/-- `hideSet` reads the statement only through its parameters. -/
theorem hideSet_transport {st st' : Statement} (h : st.params = st'.params) [HasPrg]
    (T : CrtTables) (ch : Chain) (dead : Fin BAVC.tau → Finset ℕ) :
    hideSet st T ch dead = hideSet st' T ch dead := by
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  obtain ⟨p', d', dl', b1', b2', ie', cb', v'⟩ := st'
  simp only at h
  subst h
  rfl

/-! ## The chain data of delayed statements -/

lemma mu1_of_delayed {st : Statement} (h : st.delayed = true) (Hs : Hashes) :
    st.mu1 Hs = mu Hs none st.dst := by
  simp [Statement.mu1, h]

section Congr

variable {st st' : Statement} (hp : st.params = st'.params) (hd : st.delayed = true)
  (hd' : st'.delayed = true) (hdst : st.dst = st'.dst)
include hp hd hd' hdst

lemma ivX_congrD (x : ByteArray) (g : Table) : ivX st x g = ivX st' x g := by
  simp only [ivX, mu1_of_delayed hd, mu1_of_delayed hd', hp, hdst]

lemma preCore_congrD (E : CTable) (Gx : QueryLog spec) (Jx : QueryLog specIC) (x : ByteArray)
    (g : Table) : preCore st E Gx Jx x g = preCore st' E Gx Jx x g := by
  simp only [preCore, ivX_congrD hp hd hd' hdst, hp]

lemma midCore_congrD (E : CTable) (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray)
    (g : Table) : midCore st E Gy Jy y g = midCore st' E Gy Jy y g := by
  unfold midCore
  split <;> simp only [preCore_congrD hp hd hd' hdst, hp]

omit hp hd hd' hdst in
/-- The `chal1` of the data at `y`, when `y`'s `chal1` has an `H₂¹` preimage in the log. -/
lemma midCore_chal1 (E : CTable) {Gy : QueryLog spec} (Jy : QueryLog specIC) {y x : ByteArray}
    (g : Table) (h : firstIn .h21 (fun _ => true) (yChal1 y) Gy = some x) :
    (midCore st E Gy Jy y g).chal1 = yChal1 y := by
  simp only [midCore, h]

lemma midDead_congrD (E : CTable) (Gy : QueryLog spec) (Jy : QueryLog specIC) (y : ByteArray)
    (g : Table) : midDead st E Gy Jy y g = midDead st' E Gy Jy y g := by
  unfold midDead
  split <;> simp only [ivX_congrD hp hd hd' hdst]

/-- **The chain at `z` of two delayed statements with one set of parameters and the same values at
the chain's `chal1`.** -/
lemma tailCore_congrD (hcomb : st.comb = st'.comb) (E : CTable) {Gz : QueryLog spec}
    (Jz : QueryLog specIC) {z y x : ByteArray} (g : Table)
    (hy : firstIn .h22 (fun _ => true) (zChal2 z) Gz = some y)
    (hx : firstIn .h21 (fun _ => true) (yChal1 y) (logBefore (.h22, y) Gz) = some x)
    (hv : st.values (yChal1 y) = st'.values (yChal1 y)) :
    tailCore st E Gz Jz z g = tailCore st' E Gz Jz z g := by
  have hc : ∀ c, st.combBytes (Hashes.ofTable g) c = st'.combBytes (Hashes.ofTable g) c := by
    intro c; simp only [Statement.combBytes, hcomb]
  simp only [tailCore, hy, midCore_chal1 E _ g hx, hv, hc, midCore_congrD hp hd hd' hdst,
    midDead_congrD hp hd hd' hdst, hp]

end Congr

/-! ## Congruence of the bad events at one query -/

/-- `chainBad` at an `H₂¹` input reads the data there only. -/
theorem chainBad_congr_h21 {st : Statement} (C C' : ChainData st) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) (g : Table) (x : ByteArray) (h : C.preOf x g = C'.preOf x g)
    [HasPrg] : chainBad C T S N (.h21, x) g ↔ chainBad C' T S N (.h21, x) g := by
  simp only [chainBad]; rw [h]

/-- `chainBad` at an `H₂³` input reads the data there only. -/
theorem chainBad_congr_h23 {st : Statement} (C C' : ChainData st) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) (g : Table) (z : ByteArray) (h : C.accOf z g = C'.accOf z g)
    [HasPrg] : chainBad C T S N (.h23, z) g ↔ chainBad C' T S N (.h23, z) g := by
  simp only [chainBad]; rw [h]

/-- `combBad` at an `H₂²` input reads the data there only. -/
theorem combBad_congr_h22 {st : Statement} {M : ℕ} (C C' : CombData st M) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) (g : Table) (y : ByteArray) (hmid : C.midOf y g = C'.midOf y g)
    (hsys : C.sysOf y g = C'.sysOf y g) (hwit : C.witOf y g = C'.witOf y g)
    (hdst : C.dst = C'.dst) (hP : C.pre y g = C'.pre y g) [HasPrg] :
    combBad C T S N (.h22, y) g ↔ combBad C' T S N (.h22, y) g := by
  obtain ⟨p1, m1, s1, w1, a1, d1, r1⟩ := C
  obtain ⟨p2, m2, s2, w2, a2, d2, r2⟩ := C'
  simp only at hmid hsys hwit hdst hP
  subst hdst
  simp only [combBad, CombData.qsComb, CombData.wC, ite_true]
  rw [hmid, hsys, hwit, hP]

/-! ## `μ` in the `H₂²` input -/

/-- The `μ` field of an `H₂²` input (delayed binding): bytes `264 … 296`. -/
def yMu (y : ByteArray) : ByteArray := y.extract 264 296

lemma yMu_chal2Input {pf : Proof} (hf : pf.checkFormat = true) {c1 muD b2 : ByteArray}
    (hV : Array GF128) (hc1 : c1.size = 136) (h4 : hV.size = 4) (hmu : muD.size = 32) :
    yMu (chal2Input pf c1 hV muD b2) = muD := by
  have hvc := size_voleCheck hf
  have e4 : hV = #[hV[0]!, hV[1]!, hV[2]!, hV[3]!] := by
    apply Array.ext
    · simp [h4]
    · intro i h1 h2
      simp only [h4] at h1
      interval_cases i <;> simp [getElem!_pos, h4]
  have hbs : (hV.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty).size = 64 := by
    rw [e4]
    show (ByteArray.empty ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _).size = 64
    simp only [ByteArray.size_append, size_gfToBytes]
    rfl
  have hA : (c1 ++ pf.voleCheck ++ hV.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty).size
      = 264 := by
    rw [ByteArray.size_append, ByteArray.size_append, hc1, hvc, hbs]
  simp only [yMu, chal2Input]
  rw [extract_push_of_le _ _ (by simp only [ByteArray.size_append] at hA ⊢; omega),
    show c1 ++ pf.voleCheck ++ hV.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty ++ muD ++
        b2 ++ pf.correction =
      (c1 ++ pf.voleCheck ++ hV.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty) ++ muD ++
        (b2 ++ pf.correction) by
        simp only [ByteArray.append_assoc]]
  exact extract_append3 hA.symm (by rw [hA, hmu])

/-- The delayed `H₂⁰` input of a statement at `chal1`: `inst(chal1) ‖ DST ‖ 8`. -/
def muInD (st : Statement) (c1 : ByteArray) : ByteArray := (st.instEnc c1 ++ st.dst).push 8

lemma muDelayed_ofTable {st : Statement} (hd : st.delayed = true) (g : Table) (c1 : ByteArray) :
    st.muDelayed (Hashes.ofTable g) c1 = (g (.mu, muInD st c1)).ba := by
  simp [Statement.muDelayed, hd, mu, muInD]

/-- **On an accepted proof of a delayed statement, the verifier's `H₂⁰` query is in its log**, at
`inst(chal1) ‖ DST ‖ 8` for its run's `chal1`. -/
theorem inLog_verifyQ_muD [HasPrg] (g : Table) (T : CrtTables) (st : Statement)
    (hd : st.delayed = true) (proof : ByteArray)
    (h : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves) (keys : ℕ → ℕ → ByteArray) :
    InLog (verifyQ T st proof) g
      (.mu, muInD st (runChain (Hashes.ofTable g) T st proof leaves keys).chal1) := by
  obtain ⟨hf, leaves', hr', h0, -⟩ := (accept_iff _ T st proof).1 h
  rw [hr] at hr'
  cases hr'
  simp only [ivOf, crtReconstruct, crtReconstructAt, gateHashes] at hr h0
  unfold InLog verifyQ runChain
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, tableQueryLog_bind,
    evalWithAnswerFn_mu1Q, tableQueryLog_hashQ, evalWithAnswerFn_hashQ, hr,
    evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_combBytesQ, List.map_append, List.map_cons,
    List.mem_append, List.mem_cons, beq_iff_eq, h0, chal1, BAVC.check, true_or, or_true,
    muDelayedQ, hd, ite_true, muInD]

/-! ## The statement committed at a chain query, delayed binding -/

section StmtD

variable {κ : Type} (dec : ByteArray → ByteArray → Option κ) (r₀ : κ)

/-- The statement committed at an `H₂²` input `y`: the decoding at `y`'s `chal1` of the first
`H₂⁰` preimage of `yMu y` in the log `G` before `y`. -/
def sYD (G : QueryLog spec) (y : ByteArray) : Option κ :=
  (firstIn .mu (fun _ => true) (yMu y) G).bind (dec (yChal1 y))

/-- The statement committed at an `H₂³` input `z`: that at the first `H₂²` preimage of its
`chal2`. -/
def sZD (G : QueryLog spec) (z : ByteArray) : Option κ :=
  match firstIn .h22 (fun _ => true) (zChal2 z) G with
  | some y => sYD dec (logBefore (.h22, y) G) y
  | none => none

/-- **The statement committed at the query `t`**, delayed binding: the reference `r₀` at `H₂¹`,
`sYD` at `H₂²`, `sZD` at `H₂³`, read off the log `L` before `t`. -/
def stmtAtD (L : QueryLog spec) (t : Dom) : Option κ :=
  match t.1 with
  | .h21 => some r₀
  | .h22 => sYD dec (logBefore t L) t.2
  | .h23 => sZD dec (logBefore t L) t.2
  | _ => none

theorem stmtAtD_update {α : Type} (oa : OracleComp spec α) (g : Table) (t : Dom) (u : Ans t) :
    stmtAtD dec r₀ (tableQueryLog oa (Function.update g t u)) t =
      stmtAtD dec r₀ (tableQueryLog oa g) t := by
  unfold stmtAtD
  rw [logBefore_tableQueryLog_update]

lemma stmtAtD_congr {L L' : QueryLog spec} {t : Dom} (h : logBefore t L = logBefore t L') :
    stmtAtD dec r₀ L t = stmtAtD dec r₀ L' t := by
  unfold stmtAtD; rw [h]

end StmtD

/-! ## Statement hits, delayed binding -/

/-- The targets of a statement hit (delayed binding): the `μ` fields of the earlier `H₂²` inputs
and the earlier `H₂⁰` answers. -/
def stmtTargetsD (pre : QueryLog spec) : List ByteArray :=
  (kindIns .h22 (pre.map Sigma.fst)).map yMu ++ ansOf .mu pre

/-- **A statement hit** (delayed binding). -/
def stmtHitD (L : Table → QueryLog spec) (t : Dom) (g : Table) : Prop :=
  t.1 = .mu ∧ (g t).ba ∈ stmtTargetsD (logBefore t (L g))

/-- The bound of a statement hit (delayed binding). -/
noncomputable def stmtEpsD (n : Kind → ℕ) : Kind → ℝ≥0∞
  | .mu => ((n .h22 + n .mu : ℕ) : ℝ≥0∞) / 2 ^ 256
  | _ => 0

theorem prEvent_stmtHitD_le {α : Type} (oa : OracleComp spec α) (n : Kind → ℕ)
    (hn : IsKindQueryBound oa n) (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[stmtHitD (tableQueryLog oa) t (Function.update g t u)] ≤
      stmtEpsD n t.1 := by
  obtain ⟨k, x⟩ := t
  by_cases hk : k = .mu
  · subst hk
    have h : ∀ u : Ans (.mu, x), stmtHitD (tableQueryLog oa) (.mu, x)
        (Function.update g (.mu, x) u) ↔
        u.ba ∈ stmtTargetsD (logBefore (.mu, x) (tableQueryLog oa g)) := fun u => by
      simp only [stmtHitD, Function.update_self, logBefore_tableQueryLog_update, true_and]
    simp_rw [h]
    refine (prEvent_ba_mem_le Kind.mu.outLen _).trans ?_
    have hc : ∀ k, (kindIns k ((logBefore (.mu, x) (tableQueryLog oa g)).map Sigma.fst)).length ≤
        n k := fun k =>
      (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
        (length_kindIns_tableQueryLog_le _ hn g k)
    have hl : (stmtTargetsD (logBefore (.mu, x) (tableQueryLog oa g))).length ≤
        n .h22 + n .mu := by
      simp only [stmtTargetsD, List.length_append, List.length_map, length_ansOf]
      have := hc .h22; have := hc .mu; omega
    simp only [stmtEpsD, Kind.outLen]
    gcongr
  · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hk hu.1).trans ?_
    rw [prEvent_false]
    exact bot_le

/-! ## The identification, delayed binding -/

section IdentD

variable {κ β : Type} (dec : ByteArray → ByteArray → Option κ) (r₀ : κ) (T : CrtTables)
  (st : Statement) (P : OracleComp specIC (ByteArray × β)) (E : CTable) (g : Table)

/-- No statement hit (delayed binding) in the fixed game's log. -/
def NoStmtHitD : Prop := ∀ e ∈ gLog T st P E g, ¬stmtHitD (gLog T st P E) e.1 g

lemma mu_cell_eqD (hs : NoStmtHitD T st P E g) {a b : Dom}
    (ha : a ∈ (gLog T st P E g).map Sigma.fst) (hb : b ∈ (gLog T st P E g).map Sigma.fst)
    (hka : a.1 = .mu) (hkb : b.1 = .mu) (hans : (g a).ba = (g b).ba) : a = b := by
  by_contra hab
  have key : ∀ c d : Dom, d.1 = .mu → c ∈ (logBefore d (gLog T st P E g)).map Sigma.fst →
      c.1 = .mu → (g c).ba = (g d).ba → d ∈ (gLog T st P E g).map Sigma.fst → False := by
    intro c d hd hc hck hcd hdG
    have he := exists_entry (fun e he => gLog_answer T st P E g e (mem_of_mem_logBefore he)) hc
    have hmem : (g d).ba ∈ stmtTargetsD (logBefore d (gLog T st P E g)) := by
      rw [← hcd]
      simp only [stmtTargetsD, List.mem_append]
      exact Or.inr (List.mem_map.2 ⟨_, List.mem_filter.2 ⟨he, by simp [hck]⟩, rfl⟩)
    obtain ⟨e, heG, rfl⟩ := List.mem_map.1 hdG
    exact hs e heG ⟨hd, hmem⟩
  rcases mem_or_mem_logBefore ha hb hab with h | h
  · exact key a b hkb h hka hans hb
  · exact key b a hka h hkb hans.symm ha

/-- **The statement committed at the verifier's `H₂²` input**, without statement hits: the
verifier's `H₂⁰` input precedes `y` and is the first `H₂⁰` preimage of `yMu y` there. -/
theorem sYD_ident {c1 w : ByteArray} {o : κ} (hdec : dec c1 w = some o)
    (hs : NoStmtHitD T st P E g) {y : ByteArray}
    (hyG : ((.h22, y) : Dom) ∈ (gLog T st P E g).map Sigma.fst)
    (hmuG : ((.mu, w) : Dom) ∈ (gLog T st P E g).map Sigma.fst)
    (hymu : yMu y = (g (.mu, w)).ba) (hc1 : yChal1 y = c1) :
    sYD dec (logBefore (.h22, y) (gLog T st P E g)) y = some o := by
  set G := gLog T st P E g
  have hO : ((.mu, w) : Dom) ∈ (logBefore (.h22, y) G).map Sigma.fst := by
    refine (mem_or_mem_logBefore hmuG hyG (by simp)).resolve_right fun h => ?_
    obtain ⟨e, heG, he1⟩ := List.mem_map.1 hmuG
    refine hs e heG ⟨by rw [he1], ?_⟩
    rw [he1, ← hymu]
    simp only [stmtTargetsD, List.mem_append]
    exact Or.inl (List.mem_map.2 ⟨y, mem_kindIns h, rfl⟩)
  have hsub : ∀ e ∈ logBefore (.h22, y) G, e ∈ G := fun e he => mem_of_mem_logBefore he
  have hF : firstIn .mu (fun _ => true) (yMu y) (logBefore (.h22, y) G) = some w := by
    refine firstIn_eq ⟨⟨(.mu, w), g (.mu, w)⟩,
      exists_entry (fun e he => gLog_answer T st P E g e (hsub e he)) hO, rfl, hymu.symm⟩ rfl
      fun e he hek _ hea => ?_
    have heG := hsub e he
    rw [ans_of_mem_gLog T st P E g heG, hymu] at hea
    have := mu_cell_eqD T st P E g hs (List.mem_map.2 ⟨e, heG, rfl⟩) hmuG hek rfl hea
    rw [this]
  rw [sYD, hF, Option.bind_some, hc1, hdec]

/-- **The identification, delayed binding**: in the fixed game at a delayed `st`, on an accepted
proof without chain hits and statement hits, the statement committed at the verifier's `H₂²` and
`H₂³` inputs is the decoding of its `H₂⁰` input at its `chal1`. -/
theorem stmtAtD_ident (hd : st.delayed = true) (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hs : NoStmtHitD T st P E g) (keys : ℕ → ℕ → ByteArray) : letI := icPrg E.cipher
    (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true → ∀ {leaves : BAVC.Leaves},
    BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys
    ∀ {o : κ}, dec ch.chal1 (muInD st ch.chal1) = some o →
    stmtAtD dec r₀ (gLog T st P E g) (.h22, runY (Hashes.ofTable g) st ch) = some o ∧
      stmtAtD dec r₀ (gLog T st P E g) (.h23, runZ st ch) = some o := by
  let _ : HasPrg := icPrg E.cipher
  intro hacc leaves hr
  dsimp only
  intro o hdec
  obtain ⟨-, -, -, hF4, -, hO4⟩ := chain_ident T st P E g hh keys hacc hr
  have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr
  obtain ⟨hf, -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  obtain ⟨-, hyL, -⟩ := inLog_verifyQ g T st (πOf g P E) hacc hr0 keys
  have hyG := inLog_gLog T st P E g hyL
  have hmuG := inLog_gLog T st P E g (inLog_verifyQ_muD g T st hd (πOf g P E) hacc hr0 keys)
  set ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys
  have hc1s : ch.chal1.size = 136 := Prob.Bytes.size_ba _
  have h4 : ch.hV.size = 4 := by
    show (voleHashReceiver _ _ _ _ _ _).size = 4; simp [voleHashReceiver]
  have hmus : (st.muDelayed (Hashes.ofTable g) ch.chal1).size = 32 := by
    rw [muDelayed_ofTable hd]; exact Prob.Bytes.size_ba _
  have hymu : yMu (runY (Hashes.ofTable g) st ch) = (g (.mu, muInD st ch.chal1)).ba := by
    rw [runY, show Chain.pf st ch = ⟨st.params, πOf g P E⟩ from rfl,
      yMu_chal2Input hf _ hc1s h4 hmus, muDelayed_ofTable hd]
  have hyc1 : yChal1 (runY (Hashes.ofTable g) st ch) = ch.chal1 := by
    rw [runY, yChal1_chal2Input _ hc1s]
  have h2 := sYD_ident dec T st P E g hdec hs hyG hmuG hymu hyc1
  refine ⟨h2, ?_⟩
  show sZD dec (logBefore (.h23, runZ st ch) (gLog T st P E g)) (runZ st ch) = some o
  rw [sZD, hF4]
  dsimp only
  rw [logBefore_logBefore hO4]
  exact h2

end IdentD

/-! ## Chain data with a chain-dependent system, and the generic per-query bounds -/

section FamilyD

variable {ι β κ : Type} (T : CrtTables) (stF : ι → Statement)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) {M : ℕ} (stK : κ → Statement)
  (sysK : κ → ByteArray → (Fin M → GF128) → System GF128)
  (witK : κ → ByteArray → (ℕ → GF128) → Prop) (dst : ByteArray)

/-- **The combined data of the statement `stK o`** against the adaptive game's log, with the
system and the relation at the chain's `chal1` (as `pomfritData`). -/
def combDataD (o : κ) : CombData (stK o) M where
  preOf := preOfA T stF P E (stK o)
  midOf := midOfA T stF P E (stK o)
  sysOf y g l := sysK o (midOfA T stF P E (stK o) y g).chal1 l
  witOf y g w := witK o (midOfA T stF P E (stK o) y g).chal1 w
  accOf := accOfA T stF P E (stK o)
  dst := dst
  pre := preCellsA T stF P E

theorem combDataD_committed (o : κ) : (combDataD T stF P E stK sysK witK dst o).Committed where
  pre := preOfA_committed T stF P E (stK o)
  acc := accOfA_committed T stF P E (stK o)
  mid := midOfA_committed T stF P E (stK o)
  midComb y g x v hx := midOfA_comb T stF P E (stK o) M y g x v hx
  sys y g u := by simp only [combDataD, midOfA_committed]
  sysComb y g x v hx := by simp only [combDataD, midOfA_comb T stF P E (stK o) M y g x v hx]
  wit y g u := by simp only [combDataD, midOfA_committed]
  witComb y g x v hx := by simp only [combDataD, midOfA_comb T stF P E (stK o) M y g x v hx]
  preMid := preCellsA_mid T stF P E
  preComb y g x v h := preCellsA_comb T stF P E M y g x v h

end FamilyD

section Generic

variable {ι β κ : Type} (T : CrtTables) (stF : ι → Statement)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) {M : ℕ} (stK : κ → Statement)
  (sysK : κ → ByteArray → (Fin M → GF128) → System GF128)
  (witK : κ → ByteArray → (ℕ → GF128) → Prop) (dst : ByteArray)
  (sel : QueryLog spec → Dom → Option κ)

/-- **A bad query at the statement `sel` commits there** (data `combDataD`). -/
def combBadF (N : ℕ) (t : Dom) (g : Table) : Prop :=
  ∃ o, sel (gLogA T stF P E g) t = some o ∧
    @combBad (icPrg E.cipher) (stK o) M (combDataD T stF P E stK sysK witK dst o) T chal3Blocks
      N t g

variable (hsel : ∀ L L' t, logBefore t L = logBefore t L' → sel L t = sel L' t)
include hsel

lemma sel_update {α : Type} (oa : OracleComp spec α) (g : Table) (t : Dom) (u : Ans t) :
    sel (tableQueryLog oa (Function.update g t u)) t = sel (tableQueryLog oa g) t :=
  hsel _ _ t (logBefore_tableQueryLog_update oa g t u)

/-- **The per-query bound at `H₂¹` and `H₂³`.** -/
theorem prEvent_combBadF_cell_le (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ o, (stK o).params = st₀.params) (N : ℕ) (t : Dom) (ht : t.1 ≠ .h22)
    (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[combBadF T stF P E stK sysK witK dst sel N t (Function.update g t u)] ≤
      chainEps st₀ chal3Blocks 0 N t.1 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  have h : ∀ u, combBadF T stF P E stK sysK witK dst sel N t (Function.update g t u) ↔
      ∃ o, sel (gLogA T stF P E g) t = some o ∧
        chainBad (combDataD T stF P E stK sysK witK dst o).toChainData T chal3Blocks N t
          (Function.update g t u) := fun u => by
    unfold combBadF gLogA
    rw [sel_update sel hsel]
    simp only [combBad, ht, ite_false]
  simp_rw [h]
  rcases hσ : sel (gLogA T stF P E g) t with _ | o
  · simp only [reduceCtorEq, false_and, exists_false]
    rw [prEvent_false]
    exact bot_le
  · have h' : ∀ u, (∃ o', some o = some o' ∧
        chainBad (combDataD T stF P E stK sysK witK dst o').toChainData T chal3Blocks N t
          (Function.update g t u)) ↔
        chainBad (combDataD T stF P E stK sysK witK dst o).toChainData T chal3Blocks N t
          (Function.update g t u) :=
      fun u => ⟨fun ⟨o', ho', hb⟩ => (Option.some.inj ho') ▸ hb, fun hb => ⟨o, rfl, hb⟩⟩
    simp_rw [h']
    refine (prEvent_chainBad_update_le hT _ (CombData.toChainData_committed _
      (combDataD_committed T stF P E stK sysK witK dst o)) chal3Blocks (n := 0)
      (fun _ _ => rfl) N t g).trans_eq ?_
    rw [chainEps_congr (hparams o)]

/-- The statement committed at `y` after setting `H₂²(y)` and a fresh combination cell. -/
lemma sel_two_updates (N : ℕ) (X : Table) {y : ByteArray} (u : Ans (.h22, y))
    (v : Ans (combKey M dst u)) {o : κ}
    (hσ : sel (gLogA T stF P E (Function.update (Function.update X (combKey M dst u) v)
      (.h22, y) u)) (.h22, y) = some o)
    (hb : @combBad (icPrg E.cipher) (stK o) M (combDataD T stF P E stK sysK witK dst o) T
      chal3Blocks N (.h22, y) (Function.update (Function.update X (combKey M dst u) v) (.h22, y) u)) :
    sel (gLogA T stF P E X) (.h22, y) = some o := by
  let _ : HasPrg := icPrg E.cipher
  simp only [combBad, ite_true] at hb
  obtain ⟨-, hfresh⟩ := hb
  rw [Function.update_self] at hfresh
  have hfresh' : combKey M dst u ∉ preCellsA T stF P E y
      (Function.update X (combKey M dst u) v) := by
    intro hm
    refine hfresh ?_
    show combKey M dst u ∈ preCellsA T stF P E y _
    rw [preCellsA_mid]
    exact hm
  have hnot : combKey M dst u ∉ preCellsA T stF P E y X := fun hm =>
    hfresh' (preCellsA_comb T stF P E M y X _ v hm)
  unfold gLogA at hσ ⊢
  rw [sel_update sel hsel] at hσ
  rw [hsel _ _ _ (logBefore_tableQueryLog_congr_of_not_mem _ X _
    (fun t' ht' => Function.update_of_ne ht' _ _) hnot)] at hσ
  exact hσ

set_option exponentiation.threshold 500 in
/-- **The `H₂²` bound** (`prEvent_combBadA_h22_le` with chain-dependent systems and any committed
choice `sel`). -/
theorem prEvent_combBadF_h22_le (N : ℕ) {n' : ℕ} (hn' : ∀ o c1 l, (sysK o c1 l).length = n')
    {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin M → GF128) (fun l => (sysK o c1 l).Holds w ∧ ¬witK o c1 w) ≤ εc)
    (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey M dst u ∈ K)
    {y : ByteArray} (hy : ((.h22, y) : Dom) ∈ K) (c : (ofFn fun d : K => Ans d.val).QueryCache)
    (hc : c ⟨_, hy⟩ = none) {n : ℕ} (hcard : (cachedKeys c).card < n) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      combBadF T stF P E stK sysK witK dst sel N (.h22, y) (extendTable K (completeTable c g))] ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  let t : K := ⟨_, hy⟩
  let p : Ans t.val → K := fun u => ⟨combKey M dst u, hK u⟩
  have hp : Function.Injective p := fun u u' h =>
    combKey_injective M dst (congrArg Subtype.val h)
  refine (prEvent_completeTable_le_two_cells c t p
    (fun G => combBadF T stF P E stK sysK witK dst sel N (.h22, y) (extendTable K G))).trans ?_
  rw [add_comm (ENNReal.ofReal _ + εc)]
  refine add_le_add ?_ ?_
  · refine (prEvent_isSome_le c p hp).trans ?_
    have hcardU : Fintype.card (Ans t.val) = 2 ^ 448 := card_bytes 56
    rw [hcardU, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard.le) _
  · let X : ((d : K) → Ans d.val) → Table := fun g => extendTable K (completeTable c g)
    let σ : ((d : K) → Ans d.val) → Option κ := fun g => sel (gLogA T stF P E (X g)) (.h22, y)
    let CD := combDataD T stF P E stK sysK witK dst
    change Pr{let u ← $ᵗ (Prob.Bytes 56); let v ← $ᵗ (Prob.Bytes (16 * M)); let g ← $ᵗ ((d : K) → Ans d.val)}[
          c (p u) = none ∧ combBadF T stF P E stK sysK witK dst sel N (.h22, y)
          (extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)))] ≤ _
    refine (prEvent_three_mono (Q := fun u v g =>
      (∃ o, σ g = some o ∧ (¬((CD o).sysOf y (X g) (combDec v)).Holds
          ((CD o).wC T chal3Blocks y (X g)) ∧
        Seed.zkHash ((CD o).sysOf y (X g) (combDec v)).length (gfOfBytes u.ba 0)
          (gfOfBytes u.ba 16) (gfOfBytes u.ba 32) ⟨W128.word u.ba 48, 0⟩
          (valVec ((CD o).sysOf y (X g) (combDec v)) ((CD o).wC T chal3Blocks y (X g))) = 0)) ∨
      (∃ o, σ g = some o ∧ (((CD o).sysOf y (X g) (combDec v)).Holds
          ((CD o).wC T chal3Blocks y (X g)) ∧
        ¬(CD o).witOf y (X g) ((CD o).wC T chal3Blocks y (X g))))) ?_).trans ?_
    · intro u v g h
      obtain ⟨hcu, o, hσ, hb⟩ := h
      have hq := combBad_h22_update (CD o) K (combDataD_committed T stF P E stK sysK witK dst o)
        T chal3Blocks N hK hy c hc u v hcu g hb
      have hσ' : σ g = some o := by
        have hX' : extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)) =
            Function.update (Function.update (X g) (combKey M dst u) v) (.h22, y) u :=
          extend_two_updates dst K c hy hc hK u v hcu g
        rw [hX'] at hσ hb
        exact sel_two_updates T stF P E stK sysK witK dst sel hsel N (X g) u v hσ hb
      rcases hq with hq | hq
      · exact Or.inl ⟨o, hσ', hq⟩
      · exact Or.inr ⟨o, hσ', hq⟩
    refine (prEvent_three_or_le _ _).trans (add_le_add ?_ ?_)
    · refine prEvent_three_le_of_first _ fun v g => ?_
      rcases hσ : σ g with _ | o
      · simp only [reduceCtorEq, false_and, exists_false]
        rw [prEvent_false]
        exact bot_le
      · simp only [Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        exact (prU_qs_bad_le _ _).trans_eq (by rw [show ((CD o).sysOf y (X g) (combDec v)).length
          = n' from hn' o _ _])
    · refine prEvent_three_le_of_second (fun v g => ∃ o, σ g = some o ∧
        (((CD o).sysOf y (X g) (combDec v)).Holds ((CD o).wC T chal3Blocks y (X g)) ∧
          ¬(CD o).witOf y (X g) ((CD o).wC T chal3Blocks y (X g)))) fun g => ?_
      rcases hσ : σ g with _ | o
      · simp only [reduceCtorEq, false_and, exists_false]
        rw [prEvent_false]
        exact bot_le
      · simp only [Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        have := hεc o (midOfA T stF P E (stK o) y (X g)).chal1 ((CD o).wC T chal3Blocks y (X g))
        rwa [prU_map_equiv (combEquiv M)] at this

end Generic

/-! ## The deterministic step at the joint game, chain-dependent systems -/

/-- **The per-chain deterministic theorem with a chain-dependent system** `sysC chal1 l` and
relation `witC chal1` (PomFRIT's form of `prEvent_accept_le_comb_terms`' `hdet`). -/
def CombDetD [HasPrg] {M : ℕ} (T : CrtTables) (st : Statement)
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (N : ℕ) (Wit : ByteArray → (ℕ → GF128) → Prop) : Prop :=
  ∀ (ch : Chain) (known : Finset (Fin BAVC.tau)) (acc : Prob.Bytes 16 → Prop)
    (l : Fin M → GF128) (c1 : ByteArray), ch.chal1 = c1 → (∀ w, ch.vals w = (sysC c1 l).values w) →
    ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
    Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      ¬(sysC c1 l).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (sysC c1 l) (wStar uStar (ch.dc st))) ≠ 0) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      (sysC c1 l).Holds (wStar uStar (ch.dc st)) → witC c1 (wStar uStar (ch.dc st))) →
    ChainHyps A known acc →
    (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
      (open Classical in #{x ∈ admissible | acc x} ≤ N)

/-- The fixed game's combined data with a chain-dependent system (`pomfritData`'s form). -/
def combDataFixD {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
    (E : CTable) {M : ℕ} (sysC : ByteArray → (Fin M → GF128) → System GF128)
    (witC : ByteArray → (ℕ → GF128) → Prop) (dst : ByteArray) : CombData st M where
  preOf := preOf T st P E
  midOf := midOf T st P E
  sysOf y g l := sysC (midOf T st P E y g).chal1 l
  witOf y g w := witC (midOf T st P E y g).chal1 w
  accOf := accOf T st P E
  dst := dst
  pre := preCells T st P E

section TraceD

variable {β : Type} {T : CrtTables}

set_option maxRecDepth 4000 in
/-- **The deterministic step at the joint game, chain-dependent systems** (`combBad_trace_ic` with
`combDataFixD`). -/
theorem combBad_trace_icD (hT : liftInvOk T = true) (st : Statement) {M : ℕ}
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (dst : ByteArray) (hcomb : st.comb = some (M, dst)) (N : ℕ)
    (Wit : ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ c1 (v : Prob.Bytes (16 * M)) w, st.values c1 v.ba w = (sysC c1 (combDec v)).values w)
    (P : OracleComp specIC (ByteArray × β)) (E : CTable)
    (hdet : @CombDetD (icPrg E.cipher) M T st sysC witC N Wit) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (hnex : ¬@Extracted (icPrg E.cipher) _ st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnc : ¬PostOut E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnb : ¬@bindFail (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnd : ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) :
    letI := icPrg E.cipher
    ∃ leaves, BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves ∧
      (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true ∧
      let C := combDataFixD T st P E sysC witC dst
      let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
      combBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) g ∨
        combBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
        combBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set C := combDataFixD T st P E sysC witC dst
  have hs := sameChainHyp_ic T st P E g
  have hl := deadHiddenHyp_ic T st P E g
  have hcf := combFreshHyp_ic T st P E hcomb C rfl rfl g
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬PostOut E r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys
    SameChain st T C.preOf C.midOf C.accOf (deadOf T st P E g) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch) ∧
      ∀ i ∉ r.2.1.known, (deadOf T st P E g i).Nonempty at hs
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬PostOut E r → ¬DeadOpenOut st E r →
    NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ i : Fin BAVC.tau, ∀ j ∈ deadOf T st P E g i,
      BAVC.deltaIndex (Proof.delta ⟨st.params, r.1⟩) i = j at hl
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬PostOut E r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let y := runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)
    combKey M C.dst (g (.h22, y)) ∉ C.pre y g at hcf
  change (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.2.accept = true
    at hacc
  change ¬Extracted st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnex
  change ¬PostOut E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnc
  change ¬bindFail st (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnb
  change ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnd
  have hπ : (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 = πOf g P E :=
    proverIC_fst g st E P
  simp only [evalWithAnswerFn_game, hπ] at hs hl hacc hnex hnc hnb hnd
  rw [evalWithAnswerFn_game, hπ] at hcf
  set π := πOf g P E
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  obtain ⟨hsc, hL2c⟩ := hs hacc hnc hh leaves hr'
  have hbad := combBad_of_accept hT C N Wit hcomb (fun _ _ v w => hvals _ v w)
    (fun _ _ ch known acc l hch1 hv A hA hAS hkos hQS hcb hP =>
      hdet ch known acc l _ hch1 hv A hA hAS hkos hQS hcb hP) hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) hsc hL2c (hl hacc hnc hnd hh)
    (hcf hacc hnc hh leaves hr')
    (by
      rintro ⟨i, hi, hw⟩
      refine hnex ⟨i, hi, ?_⟩
      simp only [huc.1, huc.2, hc1]
      exact hw)
  exact ⟨leaves, hr, hacc, hbad⟩

end TraceD

/-! ## PomFRIT: the family, the decoding, and the targets -/

section PomDefs

variable {ι : Type} (pk : UovPk) (sigF msgF : ι → ByteArray) (lr : Bool)

/-- PomFRIT's statements, with the signature and the message chosen by the prover. -/
def stP (s : ι) : Statement := pomfritRedeem pk (sigF s) (msgF s) lr

/-- The reference statement `none` and the family, as one family over `Option ι`. -/
def sigK (o : Option ι) : ByteArray := o.elim ByteArray.empty sigF
def msgK (o : Option ι) : ByteArray := o.elim ByteArray.empty msgF
def stKP (o : Option ι) : Statement := pomfritRedeem pk (sigK sigF o) (msgK msgF o) lr

/-- The system at a combination, at the chain's `chal1`. -/
def sysKP (o : Option ι) (c1 : ByteArray) (l : Fin 45 → GF128) : System GF128 :=
  pomfritRedeemSysL pk (sigK sigF o) (msgK msgF o) lr c1 l

/-- The relation at the target of the chain's `chal1`. -/
def witKP (o : Option ι) (c1 : ByteArray) (w : ℕ → GF128) : Prop :=
  pomfritWit GF256.ofBits 119 45 pk.map
    (fun k => ⟨fnOf (pomfritTarget (pomfritParams lr) pk.digest c1 (sigK sigF o) (msgK msgF o))
      k.val⟩) w

/-- PomFRIT's combination DST. -/
def dstP : ByteArray := toBA (VoleMole.Spec.makeDst "pomf" 0 'l' '0')

/-- **The decoding**: some statement of the family whose `H₂⁰` input at `c1` is `w`. -/
noncomputable def decP (c1 w : ByteArray) : Option (Option ι) := by
  classical
  exact if h : ∃ s, muInD (stP pk sigF msgF lr s) c1 = w then some (some h.choose) else none

lemma decP_spec (c1 : ByteArray) (s : ι) : ∃ s', decP pk sigF msgF lr c1
    (muInD (stP pk sigF msgF lr s) c1) = some (some s') ∧
    muInD (stP pk sigF msgF lr s') c1 = muInD (stP pk sigF msgF lr s) c1 := by
  classical
  have h : ∃ s', muInD (stP pk sigF msgF lr s') c1 = muInD (stP pk sigF msgF lr s) c1 := ⟨s, rfl⟩
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold decP
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- **The `H₂⁰` input at `c1` determines the target at `c1`.** -/
lemma pomfritTarget_eq_of_muInD {sig msg sig' msg' c1 : ByteArray}
    (h : muInD (pomfritRedeem pk sig msg lr) c1 = muInD (pomfritRedeem pk sig' msg' lr) c1) :
    pomfritTarget (pomfritParams lr) pk.digest c1 sig msg =
      pomfritTarget (pomfritParams lr) pk.digest c1 sig' msg' := by
  simp only [muInD, pomfritRedeem] at h
  exact (ByteArray.append_right_inj _).1 ((ByteArray.append_left_inj _).1 (push_inj h))

lemma pomfrit_values_eq {sig msg sig' msg' c1 : ByteArray}
    (h : pomfritTarget (pomfritParams lr) pk.digest c1 sig msg =
      pomfritTarget (pomfritParams lr) pk.digest c1 sig' msg') :
    (pomfritRedeem pk sig msg lr).values c1 = (pomfritRedeem pk sig' msg' lr).values c1 := by
  simp only [pomfritRedeem, h]

end PomDefs

/-! ## PomFRIT: from the chosen statement's bad events to the committed ones -/

section PomConv

variable {ι β : Type} (pk : UovPk) (sigF msgF : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) (N : ℕ) (g : Table)

/-- The fixed game's data at the chosen statement. -/
abbrev cFix : CombData (stP pk sigF msgF lr (sA g P E)) 45 :=
  combDataFixD T (stP pk sigF msgF lr (sA g P E)) P E (sysKP pk sigF msgF lr (some (sA g P E)))
    (witKP pk sigF msgF lr (some (sA g P E))) dstP

/-- The committed data of `o`. -/
abbrev cDP (o : Option ι) : CombData (stKP pk sigF msgF lr o) 45 :=
  combDataD T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr) (sysKP pk sigF msgF lr)
    (witKP pk sigF msgF lr) dstP o

lemma preOf_fix_eq (o : Option ι) (x : ByteArray) :
    preOf T (stP pk sigF msgF lr (sA g P E)) P E x g =
      preOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr o) x g := by
  refine (preOfA_eq T (stP pk sigF msgF lr) P E g x).symm.trans ?_
  unfold preOfA
  exact preCore_congrD (st := stP pk sigF msgF lr (sA g P E)) (st' := stKP pk sigF msgF lr o)
    rfl rfl rfl rfl E _ _ x g

lemma midOf_fix_eq (o : Option ι) (y : ByteArray) :
    midOf T (stP pk sigF msgF lr (sA g P E)) P E y g =
      midOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr o) y g := by
  refine (midOfA_eq T (stP pk sigF msgF lr) P E g y).symm.trans ?_
  unfold midOfA
  exact midCore_congrD (st := stP pk sigF msgF lr (sA g P E)) (st' := stKP pk sigF msgF lr o)
    rfl rfl rfl rfl E _ _ y g

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂¹` input: the reference data's bad event. -/
theorem pomfrit_convX (x : ByteArray) :
    @combBad (icPrg E.cipher) _ _ (cFix pk sigF msgF lr T P E g) T chal3Blocks N (.h21, x) g →
    @combBad (icPrg E.cipher) _ _ (cDP pk sigF msgF lr T P E none) T chal3Blocks N (.h21, x) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  simp only [combBad, reduceCtorEq, ite_false] at hb ⊢
  have h1 := (chainBad_congr_h21 (cFix pk sigF msgF lr T P E g).toChainData
    ⟨(cDP pk sigF msgF lr T P E none).preOf, (cFix pk sigF msgF lr T P E g).midOf, fun _ _ => [],
      (cFix pk sigF msgF lr T P E g).accOf⟩ T chal3Blocks N g x
    (preOf_fix_eq pk sigF msgF lr T P E g none x)).1 hb
  have h2 := (chainBad_transport (st := stP pk sigF msgF lr (sA g P E))
    (st' := stKP pk sigF msgF lr none) rfl _ T chal3Blocks N (.h21, x) g).1 h1
  refine (chainBad_congr_h21 _ _ T chal3Blocks N g x ?_).1 h2
  rfl

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂²` input: the bad event of a statement with the same target at its
`chal1`. -/
theorem pomfrit_convY (y x0 : ByteArray) (s' : ι)
    (hx : firstIn .h21 (fun _ => true) (yChal1 y)
      (logBefore (.h22, y) (gLogA T (stP pk sigF msgF lr) P E g)) = some x0)
    (htgt : pomfritTarget (pomfritParams lr) pk.digest (yChal1 y) (sigF (sA g P E)) (msgF (sA g P E)) =
      pomfritTarget (pomfritParams lr) pk.digest (yChal1 y) (sigF s') (msgF s')) :
    @combBad (icPrg E.cipher) _ _ (cFix pk sigF msgF lr T P E g) T chal3Blocks N (.h22, y) g →
    @combBad (icPrg E.cipher) _ _ (cDP pk sigF msgF lr T P E (some s')) T chal3Blocks N
      (.h22, y) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  have hmid := midOf_fix_eq pk sigF msgF lr T P E g (some s') y
  have hc1 : (midOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr (some s')) y g).chal1 =
      yChal1 y := midCore_chal1 E _ g hx
  have hsys : (cFix pk sigF msgF lr T P E g).sysOf y g =
      (cDP pk sigF msgF lr T P E (some s')).sysOf y g := by
    funext l
    change sysKP pk sigF msgF lr (some (sA g P E))
        (midOf T (stP pk sigF msgF lr (sA g P E)) P E y g).chal1 l =
      sysKP pk sigF msgF lr (some s')
        (midOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr (some s')) y g).chal1 l
    rw [hmid, hc1]
    simp only [sysKP, sigK, msgK, Option.elim, pomfritRedeemSysL, htgt]
  have hwit : (cFix pk sigF msgF lr T P E g).witOf y g =
      (cDP pk sigF msgF lr T P E (some s')).witOf y g := by
    funext w
    change witKP pk sigF msgF lr (some (sA g P E))
        (midOf T (stP pk sigF msgF lr (sA g P E)) P E y g).chal1 w =
      witKP pk sigF msgF lr (some s')
        (midOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr (some s')) y g).chal1 w
    rw [hmid, hc1]
    simp only [witKP, sigK, msgK, Option.elim, htgt]
  have h1 : @combBad (icPrg E.cipher) (stP pk sigF msgF lr (sA g P E)) 45
      (⟨(cDP pk sigF msgF lr T P E (some s')).preOf, (cDP pk sigF msgF lr T P E (some s')).midOf,
        (cDP pk sigF msgF lr T P E (some s')).sysOf, (cDP pk sigF msgF lr T P E (some s')).witOf,
        (cDP pk sigF msgF lr T P E (some s')).accOf, dstP, preCellsA T (stP pk sigF msgF lr) P E⟩ :
        CombData (stP pk sigF msgF lr (sA g P E)) 45) T chal3Blocks N (.h22, y) g := by
    refine (combBad_congr_h22 (cFix pk sigF msgF lr T P E g) _ T chal3Blocks N g y ?_ ?_ ?_ ?_
      ?_).1 hb
    · exact hmid
    · exact hsys
    · exact hwit
    · rfl
    · exact (preCellsA_eq T (stP pk sigF msgF lr) P E g y).symm
  have h2 := (combBad_transport (st := stP pk sigF msgF lr (sA g P E))
    (st' := stKP pk sigF msgF lr (some s')) rfl _ T chal3Blocks N (.h22, y) g).1 h1
  refine (combBad_congr_h22 _ _ T chal3Blocks N g y ?_ ?_ ?_ ?_ ?_).1 h2 <;> rfl

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂³` input: the bad event of a statement with the same target at the
chain's `chal1`. -/
theorem pomfrit_convZ (z y x0 : ByteArray) (s' : ι)
    (hy : firstIn .h22 (fun _ => true) (zChal2 z)
      (logBefore (.h23, z) (gLogA T (stP pk sigF msgF lr) P E g)) = some y)
    (hx : firstIn .h21 (fun _ => true) (yChal1 y)
      (logBefore (.h22, y) (logBefore (.h23, z) (gLogA T (stP pk sigF msgF lr) P E g))) = some x0)
    (htgt : pomfritTarget (pomfritParams lr) pk.digest (yChal1 y) (sigF (sA g P E)) (msgF (sA g P E)) =
      pomfritTarget (pomfritParams lr) pk.digest (yChal1 y) (sigF s') (msgF s')) :
    @combBad (icPrg E.cipher) _ _ (cFix pk sigF msgF lr T P E g) T chal3Blocks N (.h23, z) g →
    @combBad (icPrg E.cipher) _ _ (cDP pk sigF msgF lr T P E (some s')) T chal3Blocks N
      (.h23, z) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  simp only [combBad, reduceCtorEq, ite_false] at hb ⊢
  have hacc : accOf T (stP pk sigF msgF lr (sA g P E)) P E z g =
      accOfA T (stP pk sigF msgF lr) P E (stKP pk sigF msgF lr (some s')) z g := by
    rw [← accOfA_eq]
    funext b
    unfold accOfA
    dsimp only
    rw [tailCore_congrD (st := stP pk sigF msgF lr (sA g P E))
      (st' := stKP pk sigF msgF lr (some s')) rfl rfl rfl rfl rfl E _ g hy hx
      (pomfrit_values_eq pk lr htgt),
      hideSet_transport (st := stP pk sigF msgF lr (sA g P E))
        (st' := stKP pk sigF msgF lr (some s')) rfl]
  have h1 := (chainBad_congr_h23 (cFix pk sigF msgF lr T P E g).toChainData
    ⟨(cFix pk sigF msgF lr T P E g).preOf, (cFix pk sigF msgF lr T P E g).midOf, fun _ _ => [],
      (cDP pk sigF msgF lr T P E (some s')).accOf⟩ T chal3Blocks N g z hacc).1 hb
  have h2 := (chainBad_transport (st := stP pk sigF msgF lr (sA g P E))
    (st' := stKP pk sigF msgF lr (some s')) rfl _ T chal3Blocks N (.h23, z) g).1 h1
  refine (chainBad_congr_h23 _ _ T chal3Blocks N g z ?_).1 h2
  rfl

end PomConv

/-! ## PomFRIT: the adaptive union bound -/

section PomUnion

variable {ι β : Type} (pk : UovPk) (sigF msgF : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The adaptive union bound for PomFRIT, per cipher table**: as
`prEvent_accept_le_adaptive_comb_E`, with the statement committed at `H₂²` (`stmtAtD`) and the
statement hits of delayed binding (`stmtHitD`, `(n₂₂ + n₀)·2⁻²⁵⁶` per `H₂⁰` query). No injectivity
is needed: the `H₂⁰` input determines the target (`pomfritTarget_eq_of_muInD`), which is all the
system and the relation read. -/
theorem prEvent_accept_le_adaptive_pomfrit_E (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKP pk sigF msgF lr o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKP pk sigF msgF lr o c1 l).Holds w ∧ ¬witKP pk sigF msgF lr o c1 w) ≤ εc)
    (hdet : ∀ s, @CombDetD (icPrg E.cipher) 45 T (stP pk sigF msgF lr s)
      (sysKP pk sigF msgF lr (some s)) (witKP pk sigF msgF lr (some s)) N
      (witKP pk sigF msgF lr (some s)))
    (n : ℕ) (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T (stP pk sigF msgF lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stP pk sigF msgF lr (stOut r))
          (witKP pk sigF msgF lr (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        Pr{let r ← (simulateQ randomOracle (gameA T (stP pk sigF msgF lr) P E)).run' ∅}[
          bindFailA (stP pk sigF msgF lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stP pk sigF msgF lr) P E)).run' ∅}[
          deadOpenA (stP pk sigF msgF lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stP pk sigF msgF lr) P E)).run' ∅}[
          PostOut E r] := by
  classical
  intro n''
  let _ : HasPrg := icPrg E.cipher
  set stF := stP pk sigF msgF lr
  set oa := gameA T stF P E
  set mx := (simulateQ randomOracle oa).run' ∅
  set ntot := n + 2 + verifierTotal
  let cb : Option (ℕ × ByteArray) := some (45, dstP)
  let sel : QueryLog spec → Dom → Option (Option ι) := stmtAtD (decP pk sigF msgF lr) none
  have hsel : ∀ L L' t, logBefore t L = logBefore t L' → sel L t = sel L' t :=
    fun L L' t h => stmtAtD_congr _ _ h
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬Extracted (stF (stOut r)) (witKP pk sigF msgF lr (some (stOut r))) r
  let bad : Dom → Table → Prop := fun t g =>
    combBadF T stF P E (stKP pk sigF msgF lr) (sysKP pk sigF msgF lr) (witKP pk sigF msgF lr) dstP
      sel N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨ stmtHitD (tableQueryLog oa) t g
  let combE : Kind → ℝ≥0∞ := fun k => if k = .h22 then
    ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (ntot : ℝ≥0∞) / 2 ^ 448
    else chainEps (stKP pk sigF msgF lr none) chal3Blocks 0 N k
  let ε : Kind → ℝ≥0∞ := fun k => combE k + (hitEps n'' (combCount cb n'') k + stmtEpsD n'' k)
  have hKε : ∀ k ∉ adaptKinds, ε k = 0 := by
    intro k hk
    cases k <;> simp_all [adaptKinds, ε, combE, chainEps, hitEps, stmtEpsD]
  let K : Finset Dom := possibleQueryKeys oa ∪ Finset.univ.image (combKey 45 dstP)
  have hK : ∀ u, combKey 45 dstP u ∈ K := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hS : AllQueriesSatisfy oa (· ∈ K) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d h => Finset.mem_union_left _ h
  let : SampleableType ((d : K) → Ans d.val) := SampleableType.piOfFintype _
  have hq'' := isKindQueryBound_gameA T stF P E hq
  have htrace : ∀ g : Table, (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬PostOut E r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
    intro g h
    simp only [ev, bindFailA, deadOpenA, oa, evalWithAnswerFn_gameA, stOut_gameIC] at h
    obtain ⟨⟨hacc, hnex⟩, hnb, hnd, hnp⟩ := h
    have hlog : tableQueryLog oa g = gLog T (stF (sA g P E)) P E g :=
      tableQueryLog_gameA T stF P E g
    by_cases hh : NoHit (gameIC T (stF (sA g P E)) P E) (chainHit T (stF (sA g P E)) P E) g
    swap
    · simp only [NoHit, not_forall, not_not] at hh
      obtain ⟨e, he, hhit⟩ := hh
      refine ⟨e, hlog ▸ he, Or.inr (Or.inl ?_)⟩
      unfold chainHitL
      rw [hlog]
      exact hhit
    by_cases hs : NoStmtHitD T (stF (sA g P E)) P E g
    swap
    · simp only [NoStmtHitD, not_forall, not_not] at hs
      obtain ⟨e, he, hhit⟩ := hs
      refine ⟨e, hlog ▸ he, Or.inr (Or.inr ?_)⟩
      unfold stmtHitD
      rw [hlog]
      exact hhit
    obtain ⟨leaves, hr, hacc', hbad⟩ := combBad_trace_icD hT (stF (sA g P E))
      (sysKP pk sigF msgF lr (some (sA g P E))) (witKP pk sigF msgF lr (some (sA g P E))) dstP rfl N
      (witKP pk sigF msgF lr (some (sA g P E)))
      (fun c1 v w => by
        show (pomfritRedeem pk (sigF (sA g P E)) (msgF (sA g P E)) lr).values c1 v.ba w = _
        rw [pomfritRedeem_values]; simp only [pomfritRedeemSys, ofArr_combinationOf_ba]; rfl)
      P E (hdet (sA g P E)) g hacc hnex hnp hnb hnd hh
    set keys := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC (stF (sA g P E)) E P)).2.keys
    set ch := runChain (Hashes.ofTable g) T (stF (sA g P E)) (πOf g P E) leaves keys
    obtain ⟨s', hdec, hmuEq⟩ := decP_spec pk sigF msgF lr ch.chal1 (sA g P E)
    obtain ⟨h2, h3⟩ := stmtAtD_ident (decP pk sigF msgF lr) none T (stF (sA g P E)) P E g rfl hh hs
      keys hacc' hr hdec
    obtain ⟨-, -, hF3, hF4, hO3, hO4⟩ := chain_ident T (stF (sA g P E)) P E g hh keys hacc' hr
    have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨(stF (sA g P E)).params, πOf g P E⟩
        ((stF (sA g P E)).mu1 (Hashes.ofTable g))) (Proof.opening ⟨(stF (sA g P E)).params, πOf g P E⟩)
        (Proof.delta ⟨(stF (sA g P E)).params, πOf g P E⟩) = some leaves := hr
    obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T (stF (sA g P E)) (πOf g P E) hacc' hr0 keys
    have hc1s : ch.chal1.size = 136 := Prob.Bytes.size_ba _
    have hyc1 : yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch) = ch.chal1 := by
      rw [runY, yChal1_chal2Input _ hc1s]
    have htgt : pomfritTarget (pomfritParams lr) pk.digest
        (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) (sigF (sA g P E)) (msgF (sA g P E)) =
        pomfritTarget (pomfritParams lr) pk.digest
          (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) (sigF s') (msgF s') := by
      rw [hyc1]; exact (pomfritTarget_eq_of_muInD pk lr hmuEq).symm
    have hgl : gLogA T stF P E g = gLog T (stF (sA g P E)) P E g := gLogA_eq T stF P E g
    have hF3' : firstIn .h21 (fun _ => true)
        (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch))
        (logBefore (.h22, runY (Hashes.ofTable g) (stF (sA g P E)) ch) (gLogA T stF P E g)) =
        some (runX (Hashes.ofTable g) (stF (sA g P E)) (πOf g P E) leaves) := by
      rw [hgl]; exact hF3
    have hF4' : firstIn .h22 (fun _ => true) (zChal2 (runZ (stF (sA g P E)) ch))
        (logBefore (.h23, runZ (stF (sA g P E)) ch) (gLogA T stF P E g)) =
        some (runY (Hashes.ofTable g) (stF (sA g P E)) ch) := by
      rw [hgl]; exact hF4
    have hF3'' : firstIn .h21 (fun _ => true)
        (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch))
        (logBefore (.h22, runY (Hashes.ofTable g) (stF (sA g P E)) ch)
          (logBefore (.h23, runZ (stF (sA g P E)) ch) (gLogA T stF P E g))) =
        some (runX (Hashes.ofTable g) (stF (sA g P E)) (πOf g P E) leaves) := by
      rw [hgl, logBefore_logBefore hO4]; exact hF3
    have hmk : ∀ (t : Dom) (o : Option ι), InLog (verifyQ T (stF (sA g P E)) (πOf g P E)) g t →
        sel (gLog T (stF (sA g P E)) P E g) t = some o →
        @combBad (icPrg E.cipher) _ _ (cDP pk sigF msgF lr T P E o) T chal3Blocks N t g →
        ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
      intro t o ht hst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T (stF (sA g P E)) P E g ht)
      refine ⟨e, hlog ▸ he, Or.inl ⟨o, ?_, hb⟩⟩
      show sel (tableQueryLog oa g) e.1 = some o
      rw [hlog]
      exact hst
    rcases hbad with hb | hb | hb
    · exact hmk _ none hxL (by simp only [sel, stmtAtD]) (pomfrit_convX pk sigF msgF lr T P E N g _ hb)
    · exact hmk _ (some s') hyL h2 (pomfrit_convY pk sigF msgF lr T P E N g _ _ s' hF3' htgt hb)
    · exact hmk _ (some s') hzL h3
        (pomfrit_convZ pk sigF msgF lr T P E N g _ _ _ s' hF4' hF3'' htgt hb)
  have hgood := prEvent_randomOracle_le_of_fresh_bad_queries oa K hS (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound oa adaptKinds ε hKε n'' hq'') ntot
    (isTotalQueryBound_gameA T stF E hn)
    (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r) bad ?_ htrace
  · have hsum : ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k =
        n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF lr none)) +
          n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
            ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
          n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
          hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) +
          n'' .mu * stmtEpsD n'' .mu := by
      simp only [adaptKinds, ε, combE]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [chainEps, hitEps, stmtEpsD, hitSum, reduceCtorEq, ite_true, ite_false, zero_add,
        add_zero, mul_add, ntot]
      ring
    calc Pr{let r ← mx}[ev r]
        ≤ Pr{let r ← mx}[(ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r) ∨
            (bindFailA stF E r ∨ (deadOpenA stF E r ∨ PostOut E r))] :=
          prEvent_mono mx _ _ fun r h => by tauto
      _ ≤ Pr{let r ← mx}[ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬PostOut E r] +
            (Pr{let r ← mx}[bindFailA stF E r] +
              (Pr{let r ← mx}[deadOpenA stF E r] + Pr{let r ← mx}[PostOut E r])) :=
          (prEvent_or_le mx _ _).trans (add_le_add le_rfl ((prEvent_or_le mx _ _).trans
            (add_le_add le_rfl (prEvent_or_le mx _ _))))
      _ ≤ _ := by
          rw [← hsum]
          refine (add_le_add hgood le_rfl).trans_eq ?_
          ring
  · rintro c ⟨⟨k, x⟩, hx⟩ hc hcard
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
      (add_le_add ?_ ?_)))
    · by_cases hk : k = .h22
      · subst hk
        show _ ≤ combE .h22
        simp only [combE, ite_true]
        exact prEvent_combBadF_h22_le T stF P E (stKP pk sigF msgF lr) (sysKP pk sigF msgF lr)
          (witKP pk sigF msgF lr) dstP sel hsel N hn' hεc K hK hx c hc hcard
      · refine prEvent_completeTable_cell_le c _ hc
          (fun t G => combBadF T stF P E (stKP pk sigF msgF lr) (sysKP pk sigF msgF lr)
            (witKP pk sigF msgF lr) dstP sel N t.val (extendTable K G)) _ fun G => ?_
        simp only [extendTable_update]
        show _ ≤ combE k
        rw [show combE k = chainEps (stKP pk sigF msgF lr none) chal3Blocks 0 N k from by
          simp only [combE, hk, ite_false]]
        exact prEvent_combBadF_cell_le T stF P E (stKP pk sigF msgF lr) (sysKP pk sigF msgF lr)
          (witKP pk sigF msgF lr) dstP sel hsel hT _ (fun _ => rfl) N (k, x) hk _
    · refine prEvent_completeTable_cell_le c _ hc
        (fun t G => chainHitL cb (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
      simp only [extendTable_update]
      exact prEvent_chainHitL_le cb oa n'' hq'' _ _
    · refine prEvent_completeTable_cell_le c _ hc
        (fun t G => stmtHitD (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
      simp only [extendTable_update]
      exact prEvent_stmtHitD_le oa n'' hq'' _ _

end PomUnion

/-! ## PomFRIT: the joint experiment and the theorem -/

/-- **The statement-binding term, delayed binding**: `(q₀+3)·(q₂₂+1 + q₀+3)·2⁻²⁵⁶`. -/
noncomputable def stmtBindEpsD (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .mu + 3) * (((q .h22 + 1 + (q .mu + 3) : ℕ) : ℝ≥0∞) / 2 ^ 256)

lemma stmtEpsD_game (q : Kind → ℕ) :
    ((q + extractorQueries + verifierQueries) .mu : ℝ≥0∞) *
        stmtEpsD (q + extractorQueries + verifierQueries) .mu = stmtBindEpsD q := by
  simp only [stmtEpsD, stmtBindEpsD, Pi.add_apply, extractorQueries, verifierQueries, or_true,
    ite_true, reduceCtorEq, or_false, ite_false, add_zero]
  push_cast
  ring_nf

section PomJoint

variable {ι β : Type} (pk : UovPk) (sigF msgF : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β)))

/-- **PomFRIT's adaptive bound in the joint experiment.** -/
theorem prEvent_accept_le_adaptive_pomfrit (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKP pk sigF msgF lr o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKP pk sigF msgF lr o c1 l).Holds w ∧ ¬witKP pk sigF msgF lr o c1 w) ≤ εc)
    (hdet : ∀ (E : CTable) s, @CombDetD (icPrg E.cipher) 45 T (stP pk sigF msgF lr s)
      (sysKP pk sigF msgF lr (some s)) (witKP pk sigF msgF lr (some s)) N
      (witKP pk sigF msgF lr (some s)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameA T (stP pk sigF msgF lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stP pk sigF msgF lr (stOut r))
          (witKP pk sigF msgF lr (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n''
  have hE := fun E => prEvent_accept_le_adaptive_pomfrit_E pk sigF msgF lr T P E hT N hn' hεc
    (hdet E) n hn q hq
  have hdo := prEvent_joint_deadOpen_le_A T (stP pk sigF msgF lr) P (pomfritParams lr)
    (fun _ => rfl) q hq
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA (stP pk sigF msgF lr) E r)
    (fun E r => deadOpenA (stP pk sigF msgF lr) E r) (fun E r => PostOut E r) _ hE).trans ?_
  gcongr
  · exact (prEvent_joint_bindFail_le_A T (stP pk sigF msgF lr) P qE hqE).trans
      (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T (stP pk sigF msgF lr) P qE hqE q hq

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **PomFRIT redemption with an adaptively chosen signature and message**, in the random-oracle
and ideal-cipher model, every term explicit: for the issuer's key `pk`, the prover outputs a
proof and an index `s` of the signature and message `(sig, msg) = (sigF s, msgF s)` it proves
(any family: the delayed `μ` binds the target `h(chal1)`, which is all the relation reads); the
extractor runs at that statement. The verifier accepts and the extractor's candidate is not a
signature witness for the target at the verifier's `chal1` with probability

    ≤ (the bound of `pomfritRedeem_accept_le_full`) + (q₀+3)·(q₂₂+q₀+4)·2⁻²⁵⁶. -/
theorem pomfritRedeem_accept_le_adaptive (sigF msgF : ι → ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => pomfritRedeem pk (sigF s) (msgF s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (pomfritRedeem pk (sigF (stOut r)) (msgF (stOut r)) labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 (sigF (stOut r))
              (msgF (stOut r))) k.val⟩)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 + stmtBindEpsD q := by
  classical
  have h := prEvent_accept_le_adaptive_pomfrit pk sigF msgF labelRows CrtGen.tables P
    liftInvOk_tables 2 (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      intro ch known acc l c1 hch1 hv A hA hAS hkos hQS hcb hP
      subst hch1
      exact pomfritRedeem_extract_chain pk (sigF s) (msgF s) labelRows ch _ l hv hA hAS hkos hP.1
        hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q 45 rfl, stmtEpsD_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF labelRows none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKP, pomfritRedeem, pomfritParams])
      (by norm_num [stKP, pomfritRedeem, pomfritParams])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45 +
          stmtBindEpsD q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

end PomJoint

end VoleMole.ROM.IC
