import VoleMole.ROM.LemmaP
import VoleMole.ROM.LemmaPClassDet

/-!
# Lemma P^cls in the random-oracle and ideal-cipher model

`lean/docs/security/pomfrit-lemmap-tight.md` §6A.3. `ROM/LemmaP.lean` with the class extractor:
the goal reads the chain (label rows, `ũ`, the check value), `chal1` must be good for parallelism
(a new bad event at `H₂¹`), and the `H₂³` term is `2⁵⁰·2⁻¹²⁸ = 2⁻⁷⁸` per query.

* **The parallelism event** (`parEps`, `prU_kos_par_le`, `parEps_le`, `parBad`,
  `prEvent_parBad_update_le`): a uniform 136-byte `chal1` is not good for parallelism on
  `Seed.DisjQuads` (at most `2³⁷⁷` quadruples) for response functions fixed before it with
  probability at most `2⁻¹³⁴`, for at most 1441 hashed rows.
* **The deterministic step with a goal that reads the chain** (`combBad_of_acceptC`, `CombDetC`,
  `combBad_trace_icDC`): `combBad_of_acceptG` and `combBad_trace_icDG`, where the per-chain step
  also gets `KOSPar` and the committed dead leaves that the accepting set hides.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

-- `Finset.univ` over tuples of `Blocks` needs a deeper recursion limit in the unifier.
set_option maxRecDepth 8000

/-! ## The parallelism event at `H₂¹` -/

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Seed

/-- The quadruples of challenges whose two pairs differ on disjoint sets of trees. -/
abbrev DQ : Set (Blocks × Blocks × Blocks × Blocks) :=
  DisjQuads fun i : Fin BAVC.tau => Fin (BAVC.kOf i) → ZMod 2

/-- `ε_par(L) = 2³⁷⁷·(|F|⁴|T| + (L−1)⁵|F|⁴)/(|F|⁸|T|)` at `|F| = 2¹²⁸`, `|T| = 2⁶⁴`. -/
noncomputable def parEps (L : ℕ) : ℝ≥0∞ :=
  ((2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (L - 1) ^ 5 * (2 ^ 128) ^ 4) : ℕ) : ℝ≥0∞) /
    ((2 ^ (8 * 136) : ℕ) : ℝ≥0∞)

/-- **`KOSPar` at the executable encoding**: a uniform 136-byte `chal1`, parsed as `chOf` parses
it, is not good for parallelism on `DisjQuads`, for response functions fixed before it, with
probability at most `parEps L`. -/
theorem prU_kos_par_le (T : CrtTables) {L : ℕ} (Q : Blocks → Fin L → GF128)
    (D : Blocks → Fin 4 → GF128) :
    prU (Bytes 136) (fun b => ¬Seed.KOSPar (chOf gfId mem_shortKeys b.ba) DQ (lift T) Q D) ≤
      parEps L := by
  classical
  let Pq : Finset (Blocks × Blocks × Blocks × Blocks) := Finset.univ.filter (· ∈ DQ)
  have hPq : (Pq : Set (Blocks × Blocks × Blocks × Blocks)) = DQ := by
    ext q; simp [Pq]
  have hcard : #Pq ≤ 2 ^ 377 := by
    refine le_trans (le_of_eq ?_) (pomfrit_disjQuads_le
      (B := fun i : Fin BAVC.tau => Fin (BAVC.kOf i) → ZMod 2) PomFRIT.card_block)
    congr 1
  have h := prU_le_of_card_le _ (Seed.card_not_kosPar_le shortKeys Pq (lift T) Q D)
  rw [hPq, prU_map_equiv chal1Equiv, card_ch, GF128.card_eq, card_shortKeys] at h
  refine h.trans ?_
  unfold parEps
  gcongr

/-- `parEps L ≤ 2⁻¹³⁴` for at most 1441 hashed rows (`pomfrit_par_count`). -/
theorem parEps_le {L : ℕ} (hL : L ≤ 1441) : parEps L ≤ (2 ^ 134 : ℝ≥0∞)⁻¹ := by
  have hN : 2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (L - 1) ^ 5 * (2 ^ 128) ^ 4) ≤ 2 ^ 954 :=
    calc _ ≤ 2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (1441 - 1) ^ 5 * (2 ^ 128) ^ 4) := by
          gcongr
      _ ≤ 2 ^ 954 := pomfrit_par_count
  refine ENNReal.div_le_of_le_mul ?_
  rw [Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) ^ (8 * 136) = 2 ^ 134 * 2 ^ 954 by rw [← pow_add],
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  exact_mod_cast hN

end VoleMole.Prob

namespace VoleMole.ROM

section AcceptC

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction OracleComp OracleSpec

variable {β : Type}

/-- **The parallelism bad query**: at an `H₂¹` query `x`, the answer is not good for parallelism
for the responses committed at `x` (`pre x g`). -/
def parBad (st : Statement) (pre : ByteArray → Table → Chain) (T : CrtTables) :
    Dom → Table → Prop
  | (.h21, x), g => ¬Seed.KOSPar (chOf gfId mem_shortKeys (g (.h21, x)).ba) DQ (lift T)
      ((pre x g).kosQ st T) ((pre x g).kosD st T)
  | _, _ => False

/-- The per-query charge of `parBad`. -/
noncomputable def parEpsK (st : Statement) : Kind → ℝ≥0∞
  | .h21 => parEps (Chain.kosL st)
  | _ => 0

/-- **`parBad` has its single-challenge bound** when only its own cell is resampled, for data
that do not read the query's own answer. -/
theorem prEvent_parBad_update_le (st : Statement) (pre : ByteArray → Table → Chain)
    (hpre : ∀ x (g : Table) u, pre x (Function.update g (.h21, x) u) = pre x g) (T : CrtTables)
    (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[parBad st pre T t (Function.update g t u)] ≤ parEpsK st t.1 := by
  classical
  obtain ⟨k, x⟩ := t
  cases k
  case h21 =>
    have h : ∀ u : Ans (.h21, x), parBad st pre T (.h21, x) (Function.update g (.h21, x) u) ↔
        ¬Seed.KOSPar (chOf gfId mem_shortKeys (u : Bytes 136).ba) DQ (lift T)
          ((pre x g).kosQ st T) ((pre x g).kosD st T) := fun u => by
      simp only [parBad]
      rw [Function.update_self, hpre]
    simp_rw [h]
    exact prEvent_uniformSample_le (α := Bytes 136) (prU_kos_par_le T _ _)
  all_goals
    simp only [parBad]
    exact prEvent_false_le _

/-- `parBad` reads the statement only through its parameters. -/
theorem parBad_transport {st st' : Statement} (h : st.params = st'.params)
    (pre : ByteArray → Table → Chain) (T : CrtTables) (t : Dom) (g : Table) :
    parBad st pre T t g ↔ parBad st' pre T t g := by
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  obtain ⟨p', d', dl', b1', b2', ie', cb', v'⟩ := st'
  simp only at h
  subst h
  exact Iff.rfl

/-- `parBad` at an `H₂¹` input reads the data there only. -/
theorem parBad_congr {st : Statement} (pre pre' : ByteArray → Table → Chain) (T : CrtTables)
    (g : Table) (x : ByteArray) (h : pre x g = pre' x g) :
    parBad st pre T (.h21, x) g ↔ parBad st pre' T (.h21, x) g := by
  simp only [parBad]; rw [h]

set_option maxRecDepth 8000 in
/-- **`combBad_of_acceptG` with a goal that reads the chain**, the parallelism event and the
committed dead leaves. The goal is a predicate of the verifier's chain, the trees `S` and the
committed dead leaves. The per-chain step `hdet` gets, besides `combBad_of_acceptG`'s hypotheses:
`chal1` is good for parallelism (from `¬parBad` at the `H₂¹` input), every challenge of the
accepting set hides every committed dead leaf, and the trees outside `S` have one. -/
theorem combBad_of_acceptC {T : CrtTables} (hT : liftInvOk T = true) {st : Statement} {M : ℕ}
    (C : CombData st M) (N : ℕ)
    (Goal : Chain → Finset (Fin BAVC.tau) → (Fin BAVC.tau → Finset ℕ) → Prop)
    (hcomb : st.comb = some (M, C.dst))
    (hvals : ∀ y g (v : Bytes (16 * M)) w,
      st.values (C.midOf y g).chal1 v.ba w = (C.sysOf y g (combDec v)).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (dead : Fin BAVC.tau → Finset ℕ)
      (acc : Bytes 16 → Prop) (l : Fin M → GF128), ch.chal1 = (C.midOf y g).chal1 →
      (∀ w, ch.vals w = (C.sysOf y g l).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      Seed.KOSPar ch.kosCh DQ (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.sysOf y g l).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.sysOf y g l) (wStar uStar (ch.dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        (C.sysOf y g l).Holds (wStar uStar (ch.dc st)) → C.witOf y g (wStar uStar (ch.dc st))) →
      ChainHyps A known acc →
      (∀ Δ ∈ A, ∀ i : Fin BAVC.tau, ∀ j ∈ dead i, BAVC.hiddenIndex (dbitOf Δ) i = j) →
      (∀ i ∉ known, (dead i).Nonempty) →
      Goal ch known dead ∨ (open Classical in #{x ∈ admissible | acc x} ≤ N))
    {g : Table} {proof : ByteArray} {e : ExtData β}
    (hacc : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves)
    (hbind : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      j ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, proof⟩) i → leafKey leaves i j = e.keys i j)
    {dead : Fin BAVC.tau → Finset ℕ}
    (hsame : SameChain st T C.preOf C.midOf C.accOf dead g
      (runChain (Hashes.ofTable g) T st proof leaves e.keys)
      (runX (Hashes.ofTable g) st proof leaves)
      (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st proof leaves e.keys))
      (runZ st (runChain (Hashes.ofTable g) T st proof leaves e.keys)))
    (S : Finset (Fin BAVC.tau)) (hL2c : ∀ i ∉ S, (dead i).Nonempty)
    (hL2a : ∀ i : Fin BAVC.tau, ∀ j ∈ dead i,
      BAVC.deltaIndex (Proof.delta ⟨st.params, proof⟩) i = j)
    (hfresh : combKey M C.dst (g (.h22, runY (Hashes.ofTable g) st
      (runChain (Hashes.ofTable g) T st proof leaves e.keys))) ∉
        C.pre (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st proof leaves e.keys)) g)
    (hnot : ¬Goal (runChain (Hashes.ofTable g) T st proof leaves e.keys) S dead) :
    let ch := runChain (Hashes.ofTable g) T st proof leaves e.keys
    combBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st proof leaves) g ∨
      parBad st C.preOf T (.h21, runX (Hashes.ofTable g) st proof leaves) g ∨
      combBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
      combBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  intro ch
  set Hs := Hashes.ofTable g
  set x := runX Hs st proof leaves
  set y := runY Hs st ch
  set z := runZ st ch
  have hon := onChain_of_accept Hs T st ch rfl rfl rfl rfl proof hacc
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun leaves' hr' => by
      have : leaves' = leaves := Option.some_injective _ (hr'.symm.trans hr)
      subst this
      exact ⟨hbind, rfl, rfl, rfl⟩
  obtain ⟨hf, -⟩ := (accept_iff Hs T st proof).1 hacc
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨h1, hp, h2, h3⟩ := hno
  have hpre : Chain.SamePrefix st (C.preOf x g) (C.midOf y g) :=
    hsame.pre.trans hsame.mid.1.symm
  have hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba := hsame.mid.2.1.symm
  have hch1 : ch.chal1 = (C.midOf y g).chal1 := hsame.mid.2.1
  have hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba := rfl
  have hv : ∀ w, ch.vals w =
      (C.sysOf y g (combDec (g (combKey M C.dst (g (.h22, y)))))).values w := fun w => by
    change st.values ch.chal1 (st.combBytes Hs ch.chal2) w = _
    rw [show st.combBytes Hs ch.chal2 = _ from combBytes_ofTable hcomb g (g (.h22, y)), hch1]
    exact hvals y g _ w
  have hpar : Seed.KOSPar ch.kosCh DQ (lift T) (ch.kosQ st T) (ch.kosD st T) := by
    simp only [parBad, not_not] at hp
    rw [hsame.mid.kosCh_eq, hsame.mid.1.kosQ_eq, hsame.mid.1.kosD_eq, hpre.kosQ_eq, hpre.kosD_eq,
      Chain.kosCh, hc1]
    exact hp
  have hgood := comb_good_of_not_bad hT C chal3Blocks N hpre hc1 hsame.mid hc2
    (fun A => ChainHyps A S (C.accOf z g) ∧
      ∀ Δ ∈ A, ∀ i : Fin BAVC.tau, ∀ j ∈ dead i, BAVC.hiddenIndex (dbitOf Δ) i = j) _
    (fun A hA hAS hkos hQS hcb hP => hdet y g ch S dead (C.accOf z g) _ hch1 hv A hA hAS hkos
      hpar hQS hcb hP.1 hP.2 hL2c) h1 h2 hfresh (hideSet st T ch dead)
    (hideSet_subset st T ch dead)
    ⟨⟨fun i hi => isFixed_hideSet (hL2c i hi), fun b _ hb => (hsame.acc b).1 hb⟩,
      fun Δ hΔ i j hj => (mem_hideSet.1 hΔ).2 i j hj⟩
  have hd : (g (.h23, z)).ba = Proof.delta ⟨st.params, proof⟩ := hon.2
  have hadm : g (.h23, z) ∈ admissible := by
    have h15 : (Proof.delta ⟨st.params, proof⟩).get! 15 = 0 := by
      simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq] at hf
      exact hf.2
    rw [← hd, Bytes.get!_ba _ (by simp [Kind.outLen])] at h15
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h15⟩
  rcases hgood with hex | hfew
  · exact hnot hex
  · refine h3 ?_
    simp only [combBad, reduceCtorEq, ite_false]
    refine chainBad_h23_of_accept C.toChainData T chal3Blocks N hfew hadm ((hsame.acc _).2 ?_)
    refine mem_hideSet.2 ⟨mem_onSet.2 ⟨Finset.mem_image_of_mem _ hadm, ?_⟩, fun i j hj => ?_⟩
    · rw [deltaBlocks, show (g.chal3 z).ba = _ from hd]
      exact hon.1
    · rw [hiddenIndex_deltaBlocks hd i]
      exact hL2a i j hj

end AcceptC

end VoleMole.ROM

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- **The per-chain deterministic theorem with a goal that reads the chain** (`CombDetG` with
`Goal ch known dead`, the parallelism hypothesis and the committed dead leaves). -/
def CombDetC [HasPrg] {M : ℕ} (T : CrtTables) (st : Statement)
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (N : ℕ) (Goal : Chain → Finset (Fin BAVC.tau) → (Fin BAVC.tau → Finset ℕ) → Prop) : Prop :=
  ∀ (ch : Chain) (known : Finset (Fin BAVC.tau)) (dead : Fin BAVC.tau → Finset ℕ)
    (acc : Prob.Bytes 16 → Prop)
    (l : Fin M → GF128) (c1 : ByteArray), ch.chal1 = c1 → (∀ w, ch.vals w = (sysC c1 l).values w) →
    ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
    Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
    Seed.KOSPar ch.kosCh DQ (lift T) (ch.kosQ st T) (ch.kosD st T) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      ¬(sysC c1 l).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (sysC c1 l) (wStar uStar (ch.dc st))) ≠ 0) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      (sysC c1 l).Holds (wStar uStar (ch.dc st)) → witC c1 (wStar uStar (ch.dc st))) →
    ChainHyps A known acc →
    (∀ Δ ∈ A, ∀ i : Fin BAVC.tau, ∀ j ∈ dead i, BAVC.hiddenIndex (dbitOf Δ) i = j) →
    (∀ i ∉ known, (dead i).Nonempty) →
    Goal ch known dead ∨ (open Classical in #{x ∈ admissible | acc x} ≤ N)

section TraceC

variable {β : Type} {T : CrtTables}

set_option maxRecDepth 8000 in
/-- **`combBad_trace_icDG` with a goal that reads the chain**: the goal is stated for the chain of
the verifier's run (`runChain`, with the table's `H₅`), the trees `S` and the committed dead
leaves `deadOf`; a bad query is then also a `chal1` that is not good for parallelism. -/
theorem combBad_trace_icDC (hT : liftInvOk T = true) (st : Statement) {M : ℕ}
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (dst : ByteArray) (hcomb : st.comb = some (M, dst)) (N : ℕ)
    (Goal : Chain → Finset (Fin BAVC.tau) → (Fin BAVC.tau → Finset ℕ) → Prop)
    (hvals : ∀ c1 (v : Prob.Bytes (16 * M)) w, st.values c1 v.ba w = (sysC c1 (combDec v)).values w)
    (P : OracleComp specIC (ByteArray × β)) (E : CTable)
    (hdet : @CombDetC (icPrg E.cipher) M T st sysC witC N Goal)
    (cf : Out (β × QueryLog specIC) → Prop)
    (hcf' : ∀ g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) →
      KeysPre st E (jOf g P E) (gLog T st P E g) g) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (S : Finset (Fin BAVC.tau)) (hSd : ∀ i ∉ S, (deadOf T st P E g i).Nonempty)
    (hnex : letI := icPrg E.cipher
      ∀ leaves, BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves →
      ¬Goal (runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys) S (deadOf T st P E g))
    (hnc : ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
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
        parBad st C.preOf T (.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) g ∨
        combBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
        combBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set C := combDataFixD T st P E sysC witC dst
  have hs := sameChainHyp_ic_of T st P E cf hcf' g
  have hl := deadHiddenHyp_ic_of T st P E cf hcf' g
  have hcf := combFreshHyp_ic_of T st P E hcomb C rfl rfl cf g
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys
    SameChain st T C.preOf C.midOf C.accOf (deadOf T st P E g) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch) ∧
      ∀ i ∉ r.2.1.known, (deadOf T st P E g i).Nonempty at hs
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → ¬DeadOpenOut st E r →
    NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ i : Fin BAVC.tau, ∀ j ∈ deadOf T st P E g i,
      BAVC.deltaIndex (Proof.delta ⟨st.params, r.1⟩) i = j at hl
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let y := runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)
    combKey M C.dst (g (.h22, y)) ∉ C.pre y g at hcf
  change (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.2.accept = true
    at hacc
  change ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnc
  change ¬bindFail st (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnb
  change ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnd
  have hπ : (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 = πOf g P E :=
    proverIC_fst g st E P
  simp only [evalWithAnswerFn_game, hπ] at hs hl hacc hnc hnb hnd
  rw [evalWithAnswerFn_game, hπ] at hcf
  set π := πOf g P E
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  obtain ⟨hsc, -⟩ := hs hacc hnc hh leaves hr'
  have hbad := combBad_of_acceptC hT C N Goal hcomb (fun _ _ v w => hvals _ v w)
    (fun _ _ ch known dead acc l hch1 hv A hA hAS hkos hpar hQS hcb hP hhide hne =>
      hdet ch known dead acc l _ hch1 hv A hA hAS hkos hpar hQS hcb hP hhide hne) hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) hsc S hSd (hl hacc hnc hnd hh)
    (hcf hacc hnc hh leaves hr') (hnex leaves hr)
  exact ⟨leaves, hr, hacc, hbad⟩

end TraceC

end VoleMole.ROM.IC

/-! ## The class extractor reads its certificate at one tree -/

namespace VoleMole.PomFRIT

section Target

variable {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]

/-- The tree whose class the class extractor decodes, if any: the least tree of a class of width
at least 51 whose prefix differs from the widest class's. -/
def clsTarget (S : Finset (Fin 17)) (key : Fin 17 → Kt) (p : Fin 17 → P) : Option (Fin 17) :=
  (majTree S key).bind fun i₁ =>
    if 51 ≤ grpW S key (key i₁) then
      if h : (clsCand S key p i₁).Nonempty then some ((clsCand S key p i₁).min' h) else none
    else none

/-- `clsExt` reads the certificate at `clsTarget` only. -/
theorem clsExt_congr_cert {S : Finset (Fin 17)} {key : Fin 17 → Kt} {p : Fin 17 → P}
    {cert cert' : Fin 17 → Prop} [DecidablePred cert] [DecidablePred cert']
    (h : ∀ i, clsTarget S key p = some i → (cert i ↔ cert' i)) :
    clsExt S key p cert = clsExt S key p cert' := by
  unfold clsExt
  unfold clsTarget at h
  cases hm : majTree S key with
  | none => rfl
  | some i₁ =>
    rw [hm] at h
    simp only [Option.bind_some] at h ⊢
    split_ifs with hw hne hc hc' hc'
    · rfl
    · exact absurd ((h _ (by simp [hw, hne])).1 hc) hc'
    · exact absurd ((h _ (by simp [hw, hne])).2 hc') hc
    · rfl
    · rfl
    · rfl

end Target

end VoleMole.PomFRIT

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.PomFRIT

/-! ## Lemma P^cls's goal -/

section GoalC

variable [HasPrg]

/-- The blocks that hide the committed dead leaves: for a tree with a dead leaf, the bits of its
least dead leaf. -/
def hdOf (dead : Fin BAVC.tau → Finset ℕ) : Blocks := fun i b =>
  if h : (dead i).Nonempty then zb (((dead i).min' h).testBit b) else 0

omit [HasPrg] in
/-- A challenge that hides every dead leaf has the blocks `hdOf dead` on the trees with one. -/
lemma eq_hdOf_of_hides {dead : Fin BAVC.tau → Finset ℕ} {Δ : Blocks}
    (h : ∀ i : Fin BAVC.tau, ∀ j ∈ dead i, BAVC.hiddenIndex (dbitOf Δ) i = j) {i : Fin BAVC.tau}
    (hi : (dead i).Nonempty) : Δ i = hdOf dead i := by
  funext b
  simp only [hdOf, hi, dite_true]
  rw [← h i _ (Finset.min'_mem _ hi), testBit_hiddenIndex _ _ b.isLt]
  exact (congrFun (congrFun (blocksOf_dbitOf Δ) i) b).symm

/-- The `H₅` inputs the committed response of a chain reads at the challenge `Δ`. -/
def gateIns (st : Statement) (ch : Chain) (T : CrtTables) (Δ : Blocks) : List ByteArray :=
  gateInputs st.params T ch.iv (convertToVoleAt st.params (dbitOf Δ)
    (fun i => (ch.pf st).corrections.extract ((i - 1) * st.params.correctionBytes)
      (i * st.params.correctionBytes)) ch.iv ch.keys)

/-- The chain with another gate hash. -/
def withH5 (ch : Chain) (h5 : ByteArray → ByteArray) : Chain := { ch with h5 := h5 }

/-- The committed response reads `H₅` at `gateIns` only. -/
lemma resp_withH5 (st : Statement) (ch : Chain) (T : CrtTables) (h5 : ByteArray → ByteArray)
    (Δ : Blocks) (h : ∀ inp ∈ gateIns st ch T Δ, h5 inp = ch.h5 inp) :
    (withH5 ch h5).resp st T Δ = ch.resp st T Δ := by
  have hmap : (gateIns st ch T Δ).map h5 = (gateIns st ch T Δ).map ch.h5 :=
    List.map_congr_left h
  simp only [Chain.resp, respAt, crtReconstructAt, gateHashes, withH5, Chain.pf]
  simp only [gateIns, Chain.pf] at hmap
  rw [hmap]

/-- The check value reads `H₅` at `gateIns` only. -/
lemma chKos_withH5 (st : Statement) (ch : Chain) (T : CrtTables) (h5 : ByteArray → ByteArray)
    (Δ : Blocks) (h : ∀ inp ∈ gateIns st ch T Δ, h5 inp = ch.h5 inp) :
    chKos st (withH5 ch h5) T Δ = chKos st ch T Δ := by
  have hr := resp_withH5 st ch T h5 Δ h
  have hQ : (withH5 ch h5).kosQ st T Δ = ch.kosQ st T Δ := by
    funext k; simp only [Chain.kosQ]; rw [hr]
  have hD : (withH5 ch h5).kosD st T Δ = ch.kosD st T Δ := by
    funext k; simp only [Chain.kosD]; rw [hr]
  simp only [chKos, Seed.kosValue_eq]
  rw [hQ, hD]
  rfl

open Classical in
/-- **Lemma P^cls's goal** for the relation `wit`, a chain, the trees `S` and the committed dead
leaves: some tree of `S` whose candidate satisfies `wit` has the prefix that the class extractor
outputs (classes by witness and label rows, certificates of the decoder on the chain's check
value, on the challenges that hide the dead leaves). -/
def GoalC (wit : ByteArray → (ℕ → GF128) → Prop) (st : Statement) (T : CrtTables) (ch : Chain)
    (S : Finset (Fin BAVC.tau)) (dead : Fin BAVC.tau → Finset ℕ) : Prop :=
  ∃ i ∈ S, wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i) ∧
    clsExt S (clsKey st ch) (fun i => preB (candidate (F := GF128) (ch.u st) (ch.dc st) i))
      (fun i => clsCert st ch T S (hdOf dead) i) =
      some (preB (candidate (F := GF128) (ch.u st) (ch.dc st) i))

/-- The tree the class extractor decodes for a chain and the trees `S`. -/
noncomputable def tgtC (st : Statement) (ch : Chain) (S : Finset (Fin BAVC.tau)) : Option (Fin BAVC.tau) :=
  clsTarget S (clsKey st ch) (fun i => preB (candidate (F := GF128) (ch.u st) (ch.dc st) i))

/-- **The goal reads `H₅` at the decoder's evaluations only**: at the gate inputs of the points
`clsPts` of the tree `tgtC`. -/
theorem goalC_withH5 (wit : ByteArray → (ℕ → GF128) → Prop) (st : Statement) (T : CrtTables)
    (ch : Chain) (h5 : ByteArray → ByteArray) (S : Finset (Fin BAVC.tau))
    (dead : Fin BAVC.tau → Finset ℕ)
    (h : ∀ i, tgtC st ch S = some i → ∀ Δ ∈ clsPts st ch S (hdOf dead) i,
      ∀ inp ∈ gateIns st ch T Δ, h5 inp = ch.h5 inp) :
    GoalC wit st T (withH5 ch h5) S dead ↔ GoalC wit st T ch S dead := by
  classical
  unfold GoalC
  have hext : clsExt S (clsKey st (withH5 ch h5))
      (fun i => preB (candidate (F := GF128) ((withH5 ch h5).u st) ((withH5 ch h5).dc st) i))
      (fun i => clsCert st (withH5 ch h5) T S (hdOf dead) i) =
      clsExt S (clsKey st ch) (fun i => preB (candidate (F := GF128) (ch.u st) (ch.dc st) i))
        (fun i => clsCert st ch T S (hdOf dead) i) := by
    refine clsExt_congr_cert (cert := fun i => clsCert st (withH5 ch h5) T S (hdOf dead) i)
      (cert' := fun i => clsCert st ch T S (hdOf dead) i) fun i hi => ?_
    exact clsCertK_congr st ch S (hdOf dead) i fun x hx =>
      chKos_withH5 st ch T h5 x (h i hi x hx)
  rw [hext]
  rfl

/-- The goal reads the dead leaves on the trees outside `S` only, through `hdOf`. -/
theorem goalC_congr_dead (wit : ByteArray → (ℕ → GF128) → Prop) (st : Statement) (T : CrtTables)
    (ch : Chain) (S : Finset (Fin BAVC.tau)) {dead dead' : Fin BAVC.tau → Finset ℕ}
    (h : ∀ i ∉ S, dead i = dead' i) :
    GoalC wit st T ch S dead ↔ GoalC wit st T ch S dead' := by
  have hs : sliceOf S (hdOf dead) = sliceOf S (hdOf dead') := by
    ext Δ
    simp only [sliceOf, Set.mem_ofPred_eq]
    refine forall_congr' fun k => forall_congr' fun hk => ?_
    have : hdOf dead k = hdOf dead' k := by funext b; simp only [hdOf, h k hk]
    rw [this]
  unfold GoalC clsCert clsCertK
  rw [hs]

omit [HasPrg] in
lemma withH5_withH5 (ch : Chain) (a b : ByteArray → ByteArray) :
    withH5 (withH5 ch a) b = withH5 ch b := rfl

omit [HasPrg] in
lemma withH5_h5 (ch : Chain) (a : ByteArray → ByteArray) : (withH5 ch a).h5 = a := rfl

lemma tgtC_withH5 (st : Statement) (ch : Chain) (a : ByteArray → ByteArray)
    (S : Finset (Fin BAVC.tau)) : tgtC st (withH5 ch a) S = tgtC st ch S := rfl

lemma clsPts_withH5 (st : Statement) (ch : Chain) (a : ByteArray → ByteArray)
    (S : Finset (Fin BAVC.tau)) (hd : Blocks) (i : Fin BAVC.tau) :
    clsPts st (withH5 ch a) S hd i = clsPts st ch S hd i := rfl

lemma gateIns_withH5 (st : Statement) (ch : Chain) (a : ByteArray → ByteArray) (T : CrtTables)
    (Δ : Blocks) : gateIns st (withH5 ch a) T Δ = gateIns st ch T Δ := rfl

/-- The goal reads the chain's proof, keys, `iv`, gate hash and `chal1` only. -/
theorem goalC_core (wit : ByteArray → (ℕ → GF128) → Prop) (st : Statement) (T : CrtTables)
    {ch ch' : Chain} (S : Finset (Fin BAVC.tau)) (dead : Fin BAVC.tau → Finset ℕ)
    (h1 : ch'.proof = ch.proof) (h2 : ch'.keys = ch.keys) (h3 : ch'.iv = ch.iv)
    (h4 : ch'.h5 = ch.h5) (h5 : ch'.chal1 = ch.chal1) :
    GoalC wit st T ch' S dead ↔ GoalC wit st T ch S dead := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ch
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := ch'
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  exact Iff.rfl

/-- The goal at the chain of the verifier's run is the goal at the output's chain with the run's
gate hash, for a transcript with the run's `iv` and `chal1`. -/
theorem goalC_run_out {β : Type} (wit : ByteArray → (ℕ → GF128) → Prop) (st : Statement)
    (T : CrtTables) (Hs : Hashes) (π : ByteArray) (leaves : BAVC.Leaves) (e : ExtData β)
    (tr : Transcript) (hiv : tr.iv = ivOf Hs ⟨st.params, π⟩ (st.mu1 Hs))
    (hc1 : tr.chal1 = chal1 Hs ⟨st.params, π⟩ (st.mu1 Hs)
      (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1)
    (S : Finset (Fin BAVC.tau)) (dead : Fin BAVC.tau → Finset ℕ) :
    GoalC wit st T (withH5 (outChain (π, e, tr)) (Hs.hash .h5)) S dead ↔
      GoalC wit st T (runChain Hs T st π leaves e.keys) S dead :=
  goalC_core wit st T S dead rfl rfl hiv rfl hc1

end GoalC

/-! ## The goal on an output of the game -/

section OutC

variable {β : Type}

/-- The gate hash read off a hash log: the answer of the first `H₅` entry at the input. -/
def h5Of (L : QueryLog spec) (inp : ByteArray) : ByteArray :=
  ((L.find? fun e : (t : Dom) × Ans t => decide (e.1 = (Kind.h5, inp))).map
    fun e => (e.2 : Ans e.1).ba).getD ByteArray.empty

/-- On a log whose answers are the table's, `h5Of` is the table's `H₅` at every logged input. -/
lemma h5Of_eq {g : Table} {L : QueryLog spec} (hL : ∀ e ∈ L, (e.2 : Ans e.1) = g e.1)
    {inp : ByteArray} (h : ((Kind.h5, inp) : Dom) ∈ L.map Sigma.fst) :
    h5Of L inp = (g (.h5, inp)).ba := by
  obtain ⟨e₀, he₀, he₀1⟩ := List.mem_map.1 h
  have hsome : (L.find? fun e : (t : Dom) × Ans t => decide (e.1 = (Kind.h5, inp))).isSome :=
    List.find?_isSome.2 ⟨e₀, he₀, by simp [he₀1]⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some he
  simp only [decide_eq_true_eq] at hp
  have hm := List.mem_of_find?_eq_some he
  have ha := hL e hm
  unfold h5Of
  rw [he]
  obtain ⟨⟨k, w⟩, u⟩ := e
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp only [Option.map_some, Option.getD_some]
  rw [show u = g (Kind.h5, w) from ha]

/-- **The committed dead leaves of an output**, read off the prover's log as `aliveR` reads
them: the dead leaves (`deadPre`) at the first `H₂¹` preimage of the output's `chal1`; none if
`chal1` has no preimage there. -/
def deadR (E : CTable) (r : Out (β × QueryLog specIC)) : Fin BAVC.tau → Finset ℕ :=
  match firstIn .h21 (fun _ => true) r.2.2.chal1 (hashEnt r.2.1.aux.2) with
  | some x => deadPre E (logBefore (.h21, x) (hashEnt r.2.1.aux.2))
      (logBefore (.inl (.h21, x)) r.2.1.aux.2) r.2.2.iv x
  | none => fun _ => ∅

/-- The output's chain (`outChain`) with the gate hash read off the prover's log. -/
def outChainL (r : Out (β × QueryLog specIC)) : Chain :=
  withH5 (outChain r) (h5Of (hashEnt r.2.1.aux.2))

/-- **Lemma P^cls's extraction succeeds on an output**: `GoalC` at the output's chain, with the
gate hash read off the prover's log, its alive trees and its committed dead leaves. -/
def ClsExtracted (E : CTable) (st : Statement) (T : CrtTables)
    (wit : ByteArray → (ℕ → GF128) → Prop) (r : Out (β × QueryLog specIC)) : Prop :=
  @GoalC (icPrg E.cipher) wit st T (outChainL r) (aliveR E r) (deadR E r)

/-- **The prover's log covers the decoder**: if the class extractor decodes the class of a tree,
every gate input of the committed response at every point where the decoder evaluates the check
value is an `H₅` query of the prover's log. -/
def ClsCovered (E : CTable) (st : Statement) (T : CrtTables) (r : Out (β × QueryLog specIC)) :
    Prop :=
  letI := icPrg E.cipher
  ∀ i, tgtC st (outChain r) (aliveR E r) = some i →
    ∀ Δ ∈ clsPts st (outChain r) (aliveR E r) (hdOf (deadR E r)) i,
      ∀ inp ∈ gateIns st (outChain r) T Δ,
        ((Kind.h5, inp) : Dom) ∈ (hashEnt r.2.1.aux.2).map Sigma.fst

variable (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (E : CTable)
  (g : Table)

/-- **Without chain hits, the committed dead leaves of the accepted chain are those of the
output**, on the trees that are not alive. -/
theorem deadOf_eq_deadR (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true) :
    ∀ i ∉ aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)),
      deadOf T st P E g i = deadR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) i := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro i hi
  set r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)
  set Hs := Hashes.ofTable g
  set π := πOf g P E
  have hr2 : r.2.2 = verify Hs T st π := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hJ : r.2.1.aux.2 = jOf g P E := aux_gameIC T st P E g
  rw [hr2] at hacc
  obtain ⟨hf, leaves, hrec, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hrec
  have hrec' : BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := hrec
  have hdead : deadOf T st P E g = deadAtX T st P E (runX Hs st π leaves) g := by
    unfold deadOf; rw [hrec']
  rw [hdead]
  unfold aliveR at hi
  unfold deadR
  rw [hJ, hr2] at hi ⊢
  split at hi
  · rename_i x hx
    obtain ⟨rest, hG⟩ := gLog_eq_hashEnt_append T st P E g
    obtain ⟨e, he, he1, hea⟩ := firstIn_some hx
    -- `x` is the verifier's `H₂¹` input.
    obtain ⟨hxL, -, -⟩ := inLog_verifyQ g T st π hacc hrec
      (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
    have hxvG := inLog_gLog T st P E g hxL
    have heG : e ∈ gLog T st P E g := by rw [hG]; exact List.mem_append_left _ he
    have hxG : ((.h21, x) : Dom) ∈ (gLog T st P E g).map Sigma.fst :=
      List.mem_map.2 ⟨e, heG, he1⟩
    have hans : (g (.h21, x)).ba = (g (.h21, runX Hs st π leaves)).ba := by
      have h1 := ans_of_mem_gLog T st P E g heG
      obtain ⟨⟨k, w⟩, u⟩ := e
      simp only [Prod.mk.injEq] at he1
      obtain ⟨rfl, rfl⟩ := he1
      have h2 : (g (.h21, w)).ba = (verify Hs T st π).chal1 := by rw [← h1]; exact hea
      rw [h2, hc1]
      rfl
    have hxx := cell_eq_of_noHit T st P E hh hxG hxvG rfl (Or.inr (Or.inl rfl)) hans
    have hxv : x = runX Hs st π leaves := congrArg Prod.snd hxx
    subst hxv
    have hxH : ((.h21, runX Hs st π leaves) : Dom) ∈ (hashEnt (jOf g P E)).map Sigma.fst :=
      List.mem_map.2 ⟨e, he, he1⟩
    have hlog : logBefore (.h21, runX Hs st π leaves) (gLog T st P E g) =
        logBefore (.h21, runX Hs st π leaves) (hashEnt (jOf g P E)) := by
      rw [hG]; exact logBefore_append_of_mem rest hxH
    have hivX : ivX st (runX Hs st π leaves) g = (verify Hs T st π).iv := by
      rw [hiv]
      unfold ivX ivOf runX
      rw [xIvPre_chal1Input hf]
      · exact size_mu1 Hs (fun k w => by simp [Hs]) st
      · exact Prob.Bytes.size_ba _
    simp only [hx]
    unfold deadAtX
    rw [hlog, hivX]
  · exact absurd (Finset.mem_univ i) hi

include T st in
/-- The hash entries of the prover's log carry the table's answers. -/
lemma hashEnt_jOf_ans : ∀ e ∈ hashEnt (jOf g P E), (e.2 : Ans e.1) = g e.1 := by
  intro e he
  obtain ⟨rest, hG⟩ := gLog_eq_hashEnt_append T st P E g
  exact ans_of_mem_gLog T st P E g (by rw [hG]; exact List.mem_append_left _ he)

set_option maxRecDepth 8000 in
/-- **From the chain of the verifier's run to the output**: without chain hits, for an accepted
proof whose prover's log covers the decoder, Lemma P^cls's goal at the chain of the verifier's
run (with the table's `H₅` and the committed dead leaves `deadOf`) is the goal at the output. -/
theorem clsExtracted_of_goalC (wit : ByteArray → (ℕ → GF128) → Prop)
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (hcov : ClsCovered E st T (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E))) :
    letI := icPrg E.cipher
    ∀ leaves, BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves →
      GoalC wit st T (runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys)
        (aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E))) (deadOf T st P E g) →
      ClsExtracted E st T wit (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro leaves hrec hG
  have hdd := deadOf_eq_deadR T st P E g hh hacc
  have hπ : (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 = πOf g P E :=
    proverIC_fst g st E P
  have hr : evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) =
      (πOf g P E, (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2,
        verify (Hashes.ofTable g) T st (πOf g P E)) := by
    change evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)) = _
    rw [evalWithAnswerFn_game, hπ]
  have hJ : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.aux.2 = jOf g P E :=
    aux_gameIC T st P E g
  generalize evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) = r at hr hJ hacc hcov hdd hG ⊢
  generalize (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2 = e at hr hG
  generalize htr : verify (Hashes.ofTable g) T st (πOf g P E) = tr at hr
  have hacc' : (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true := by
    rw [htr]; rw [hr] at hacc; exact hacc
  have hrec0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hrec
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st (πOf g P E) hacc' hrec0
  rw [htr] at hiv hc1
  -- The dead leaves.
  rw [goalC_congr_dead wit st T _ _ hdd] at hG
  -- The chain of the run and the output's chain have the same proof, keys, `iv` and `chal1`.
  have hcore : GoalC wit st T (withH5 (outChain r) ((Hashes.ofTable g).hash .h5)) (aliveR E r)
      (deadR E r) := by
    have := (goalC_run_out wit st T (Hashes.ofTable g) (πOf g P E) leaves e tr hiv hc1 (aliveR E r)
      (deadR E r)).2 hG
    rw [← hr] at this
    exact this
  -- The gate hash: the log's answers are the table's.
  have hfin : GoalC wit st T (withH5 (withH5 (outChain r) ((Hashes.ofTable g).hash .h5))
      (h5Of (hashEnt r.2.1.aux.2))) (aliveR E r) (deadR E r) := by
    refine (goalC_withH5 wit st T (withH5 (outChain r) ((Hashes.ofTable g).hash .h5))
      (h5Of (hashEnt r.2.1.aux.2)) (aliveR E r) (deadR E r) fun i hi Δ hΔ inp hinp => ?_).2 hcore
    rw [tgtC_withH5] at hi
    rw [clsPts_withH5] at hΔ
    rw [gateIns_withH5] at hinp
    have hmem := hcov i hi Δ hΔ inp hinp
    rw [hJ] at hmem ⊢
    rw [withH5_h5]
    exact h5Of_eq (hashEnt_jOf_ans T st P E g) hmem
  rw [withH5_withH5] at hfin
  exact hfin

end OutC

end VoleMole.ROM.IC
