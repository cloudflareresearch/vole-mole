import VoleMole.ROM.AdaptPomfrit
import VoleMole.ROM.PermPost
import VoleMole.ROM.LemmaPDet
import VoleMole.EndToEnd.SpecRelations

/-!
# Lemma P in the random-oracle and ideal-cipher model: the adaptive bound into the widest group

`lean/docs/security/pomfrit.md` §5, §6.4. PomFRIT redemption with an adaptively chosen statement
whose target is **any function** of `chal1` (`pomfritRedeemT`: for the one-more game, the answer of
the target oracle `H_T`; `pomfritRedeem` is the case `hash_to_target`), and an extraction goal that
is Lemma P's: **some fully alive tree of the widest prefix group has a candidate in the relation**.

* `pomfritRedeemT` (moved here from `ROM/OneMorePomfrit.lean`) and `pomfritRedeemT_values`.
* **Generalized goal** (`combBad_of_acceptG`, `CombDetG`, `combBad_trace_icDG`): the deterministic
  steps of `ROM/Accept.lean` and `ROM/AdaptPomfrit.lean` with the extraction goal any predicate of
  `chal1`, the trees' candidates and a set `S` of trees containing every tree without a committed
  dead leaf (there: `∃ i ∈ known, Wit chal1 (cand i)`). The proofs are those of
  `combBad_of_accept` and `combBad_trace_icD`, which read the goal only through `hdet`.
* **The alive trees of an output** (`aliveR`): the trees with no committed dead leaf at the first
  `H₂¹` preimage of the output's `chal1` in the prover's log (all trees if there is none); it
  contains every tree with no dead leaf of the verifier's chain when there are no chain hits
  (`dead_of_not_mem_aliveR`).
* **Lemma P's goal** (`GoalP`, `MajorExtracted`): a tree of `aliveR` whose candidate satisfies the
  relation at the chosen target and whose prefix (`preB`: witness bytes `[0, 45)`) is that of the
  widest group (`majP`).
* **The adaptive bound** (`prEvent_accept_le_adaptive_pomfritT_E`, `…_pomfritT`,
  `pomfritT_accept_le_major`): as `pomfritRedeem_accept_le_adaptive`, for the target family, with
  Lemma P's goal and the `H₂³` term `(Q₃ + 1)·2⁵⁷·2⁻¹²⁸ = (Q₃ + 1)·2⁻⁷¹`
  (`pomfritT_extract_major_chain` as the per-chain step).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

/-! ## PomFRIT redemption with a given target function -/

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier

/-- **PomFRIT redemption with the target function `h`** (`pomfritRedeem` with `h` in place of
`hash_to_target` at the verifier's `chal1`, and the binders given). -/
def pomfritRedeemT (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (labelRows : Bool) : Statement :=
  { params := pomfritParams labelRows
    dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
    delayed := true
    binder1 := b1
    binder2 := b2
    instEnc := fun c1 => pk.digest ++ h c1
    comb := some (45, toBA (Spec.makeDst "pomf" 0 'l' '0'))
    values := fun c1 lb w =>
      UovEval.pomfritRedeemValues 119 45 pk.map (fun k => ⟨fnOf (h c1) k.val⟩)
        (combinationOf 45 lb) w }

@[simp] lemma pomfritRedeemT_params (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (lr : Bool) : (pomfritRedeemT pk h b1 b2 lr).params = pomfritParams lr := rfl

/-- The constraint evaluator of `pomfritRedeemT` is PomFRIT's system at the target `h(chal1)`. -/
theorem pomfritRedeemT_values (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (lr : Bool) (c1 lb : ByteArray) (x : ℕ → GF128) :
    (pomfritRedeemT pk h b1 b2 lr).values c1 lb x =
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map (fun k => ⟨fnOf (h c1) k.val⟩)
        (ofArr (combinationOf 45 lb))).values x := by
  show UovEval.pomfritRedeemValues 119 45 pk.map _ _ x = _
  rw [UovEval.pomfritRedeemValues_eq, Verifier.Bridge.betaFast_eq]

end VoleMole.ROM.OneMore.Pomfrit

/-! ## The deterministic step with a general extraction goal -/

namespace VoleMole.ROM

section AcceptG

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction OracleComp OracleSpec

variable {β : Type}

/-- The candidates of an output's chain, per tree. -/
noncomputable def candOut (st : Statement) (r : Out β) : Fin BAVC.tau → ℕ → GF128 :=
  fun i => candidate (F := GF128) ((outChain r).u st) ((outChain r).dc st) i


set_option maxRecDepth 4000 in
/-- **`chainBad_of_accept` for the combined relations** (`combBad`, with `l` read from the table
at `chal2 ‖ dst`): the statement's combination is `(M, C.dst)` (`hcomb`) and its evaluator at the
combination bytes `v` is the system at `combDec v` (`hvals`). `hdet` may use that the chain's
`chal1` is the one committed at `y` (PomFRIT's system reads it). -/
theorem combBad_of_acceptG {T : CrtTables} (hT : liftInvOk T = true) {st : Statement} {M : ℕ}
    (C : CombData st M) (N : ℕ)
    (Goal : ByteArray → (Fin BAVC.tau → ℕ → GF128) → Finset (Fin BAVC.tau) → Prop)
    (hcomb : st.comb = some (M, C.dst))
    (hvals : ∀ y g (v : Bytes (16 * M)) w,
      st.values (C.midOf y g).chal1 v.ba w = (C.sysOf y g (combDec v)).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (acc : Bytes 16 → Prop) (l : Fin M → GF128), ch.chal1 = (C.midOf y g).chal1 →
      (∀ w, ch.vals w = (C.sysOf y g l).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.sysOf y g l).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.sysOf y g l) (wStar uStar (ch.dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        (C.sysOf y g l).Holds (wStar uStar (ch.dc st)) → C.witOf y g (wStar uStar (ch.dc st))) →
      ChainHyps A known acc →
      Goal ch.chal1 (fun i => candidate (F := GF128) (ch.u st) (ch.dc st) i) known ∨
        (open Classical in #{x ∈ admissible | acc x} ≤ N))
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
    (hnot : ¬Goal (runChain (Hashes.ofTable g) T st proof leaves e.keys).chal1
      (fun i => candidate (F := GF128) ((runChain (Hashes.ofTable g) T st proof leaves e.keys).u st)
        ((runChain (Hashes.ofTable g) T st proof leaves e.keys).dc st) i) S):
    let ch := runChain (Hashes.ofTable g) T st proof leaves e.keys
    combBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st proof leaves) g ∨
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
  obtain ⟨h1, h2, h3⟩ := hno
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
  have hgood := comb_good_of_not_bad hT C chal3Blocks N hpre hc1 hsame.mid hc2
    (fun A => ChainHyps A S (C.accOf z g)) _
    (fun A hA hAS hkos hQS hcb hP => hdet y g ch S (C.accOf z g) _ hch1 hv A hA hAS hkos
      hQS hcb hP) h1 h2 hfresh (hideSet st T ch dead) (hideSet_subset st T ch dead)
    ⟨fun i hi => isFixed_hideSet (hL2c i hi), fun b _ hb => (hsame.acc b).1 hb⟩
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

end AcceptG

end VoleMole.ROM

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- **The per-chain deterministic theorem with a general goal** (`CombDetD` with
`∃ i ∈ known, Wit chal1 (cand i)` replaced by `Goal chal1 cand known`). -/
def CombDetG [HasPrg] {M : ℕ} (T : CrtTables) (st : Statement)
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (N : ℕ) (Goal : ByteArray → (Fin BAVC.tau → ℕ → GF128) → Finset (Fin BAVC.tau) → Prop) : Prop :=
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
    Goal ch.chal1 (fun i => candidate (F := GF128) (ch.u st) (ch.dc st) i) known ∨
      (open Classical in #{x ∈ admissible | acc x} ≤ N)

section TraceD

variable {β : Type} {T : CrtTables}

set_option maxRecDepth 4000 in
/-- **The deterministic step at the joint game, chain-dependent systems** (`combBad_trace_ic` with
`combDataFixD`). -/
theorem combBad_trace_icDG (hT : liftInvOk T = true) (st : Statement) {M : ℕ}
    (sysC : ByteArray → (Fin M → GF128) → System GF128) (witC : ByteArray → (ℕ → GF128) → Prop)
    (dst : ByteArray) (hcomb : st.comb = some (M, dst)) (N : ℕ)
    (Goal : ByteArray → (Fin BAVC.tau → ℕ → GF128) → Finset (Fin BAVC.tau) → Prop)
    (hvals : ∀ c1 (v : Prob.Bytes (16 * M)) w, st.values c1 v.ba w = (sysC c1 (combDec v)).values w)
    (P : OracleComp specIC (ByteArray × β)) (E : CTable)
    (hdet : @CombDetG (icPrg E.cipher) M T st sysC witC N Goal)
    (cf : Out (β × QueryLog specIC) → Prop)
    (hcf' : ∀ g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) →
      KeysPre st E (jOf g P E) (gLog T st P E g) g) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (S : Finset (Fin BAVC.tau)) (hSd : ∀ i ∉ S, (deadOf T st P E g i).Nonempty)
    (hnex : ¬Goal (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.chal1
      (@candOut (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E))) S)
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
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  obtain ⟨hsc, -⟩ := hs hacc hnc hh leaves hr'
  have hbad := combBad_of_acceptG hT C N Goal hcomb (fun _ _ v w => hvals _ v w)
    (fun _ _ ch known acc l hch1 hv A hA hAS hkos hQS hcb hP =>
      hdet ch known acc l _ hch1 hv A hA hAS hkos hQS hcb hP) hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) hsc S hSd (hl hacc hnc hnd hh)
    (hcf hacc hnc hh leaves hr')
    (fun hG => hnex (by
      have hr : evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) =
          (π, e, verify (Hashes.ofTable g) T st π) := by
        change evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)) = _
        rw [evalWithAnswerFn_game, hπ]
      rw [hr]
      unfold candOut
      simp only [huc.1, huc.2, hc1]
      exact hG))
  exact ⟨leaves, hr, hacc, hbad⟩

end TraceD


/-! ## The target family, the decoding, and the targets -/

section PomTDefs

open VoleMole.ROM.OneMore.Pomfrit

variable {ι : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool)

/-- PomFRIT's statements with the target function and the binders chosen by the prover. -/
def stT (s : ι) : Statement := pomfritRedeemT pk (hF s) (b1F s) (b2F s) lr

/-- The reference statement `none` and the family, as one family over `Option ι`. -/
def hFK (o : Option ι) : ByteArray → ByteArray := o.elim (fun _ => ByteArray.empty) hF
def bK (bF : ι → ByteArray) (o : Option ι) : ByteArray := o.elim ByteArray.empty bF
def stKT (o : Option ι) : Statement := pomfritRedeemT pk (hFK hF o) (bK b1F o) (bK b2F o) lr

/-- A 45-byte string as a target. -/
def tgtOf (b : ByteArray) : Fin 45 → GF256 := fun k => ⟨fnOf b k.val⟩

/-- The system at a combination, at the chain's `chal1`. -/
def sysKT (o : Option ι) (c1 : ByteArray) (l : Fin 45 → GF128) : System GF128 :=
  PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map (tgtOf (hFK hF o c1)) l

/-- The relation at the target of the chain's `chal1`. -/
def witKT (o : Option ι) (c1 : ByteArray) (w : ℕ → GF128) : Prop :=
  pomfritWit GF256.ofBits 119 45 pk.map (tgtOf (hFK hF o c1)) w

/-- **The decoding**: some statement of the family whose `H₂⁰` input at `c1` is `w`. -/
noncomputable def decT (c1 w : ByteArray) : Option (Option ι) := by
  classical
  exact if h : ∃ s, muInD (stT pk hF b1F b2F lr s) c1 = w then some (some h.choose) else none

lemma decT_spec (c1 : ByteArray) (s : ι) : ∃ s', decT pk hF b1F b2F lr c1
    (muInD (stT pk hF b1F b2F lr s) c1) = some (some s') ∧
    muInD (stT pk hF b1F b2F lr s') c1 = muInD (stT pk hF b1F b2F lr s) c1 := by
  classical
  have h : ∃ s', muInD (stT pk hF b1F b2F lr s') c1 = muInD (stT pk hF b1F b2F lr s) c1 :=
    ⟨s, rfl⟩
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold decT
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- **The `H₂⁰` input at `c1` determines the target at `c1`.** -/
lemma target_eq_of_muInD_T {h h' : ByteArray → ByteArray} {b1 b2 b1' b2' c1 : ByteArray}
    (heq : muInD (pomfritRedeemT pk h b1 b2 lr) c1 = muInD (pomfritRedeemT pk h' b1' b2' lr) c1) :
    h c1 = h' c1 := by
  simp only [muInD, pomfritRedeemT] at heq
  exact (ByteArray.append_right_inj _).1 ((ByteArray.append_left_inj _).1 (push_inj heq))

omit pk in
lemma pomfritT_values_eq (pk : UovPk) {h h' : ByteArray → ByteArray} {b1 b2 b1' b2' c1 : ByteArray}
    (heq : h c1 = h' c1) :
    (pomfritRedeemT pk h b1 b2 lr).values c1 = (pomfritRedeemT pk h' b1' b2' lr).values c1 := by
  simp only [pomfritRedeemT, heq]

end PomTDefs

/-! ## Lemma P's goal on an output -/

section Major

/-- The prefix of a candidate: its witness bytes `[0, 45)` (the `r` of `P(s) = h ⊕ r`). -/
noncomputable def preB (w : ℕ → GF128) : Spec.Bytes := SpecRel.bytesOf (SpecRel.bitsOf w) 0 45

/-- **Lemma P's goal** at `chal1`, the trees' candidates `cand` and the trees `S`, for the relation
`wit`: some tree of `S` whose candidate satisfies `wit` lies in the widest prefix group of `S`. -/
def GoalP (wit : ByteArray → (ℕ → GF128) → Prop) (c1 : ByteArray)
    (cand : Fin BAVC.tau → ℕ → GF128) (S : Finset (Fin BAVC.tau)) : Prop :=
  ∃ i ∈ S, wit c1 (cand i) ∧ PomFRIT.majP S (fun i => preB (cand i)) = some (preB (cand i))

variable {β : Type}

/-- **The alive trees of an output**: the trees with no committed dead leaf (`deadPre`) at the
first `H₂¹` preimage `x` of the output's `chal1` in the prover's hash log, with the logs before
`x` and the verifier's `iv`; all trees if `chal1` has no preimage there. -/
def aliveR (E : CTable) (r : Out (β × QueryLog specIC)) : Finset (Fin BAVC.tau) :=
  match firstIn .h21 (fun _ => true) r.2.2.chal1 (hashEnt r.2.1.aux.2) with
  | some x => univ.filter fun i =>
      deadPre E (logBefore (.h21, x) (hashEnt r.2.1.aux.2)) (logBefore (.inl (.h21, x)) r.2.1.aux.2)
        r.2.2.iv x i = ∅
  | none => univ

/-- **Lemma P's extraction succeeds on an output**: `GoalP` at the output's `chal1`, the
candidates of its chain (`candOut`, the extractor's keys) and its alive trees. -/
def MajorExtracted (E : CTable) (st : Statement) (wit : ByteArray → (ℕ → GF128) → Prop)
    (r : Out (β × QueryLog specIC)) : Prop :=
  GoalP wit r.2.2.chal1 (@candOut (icPrg E.cipher) _ st r) (aliveR E r)

lemma firstIn_some {k : Kind} {ok : ByteArray → Bool} {a : ByteArray} {L : QueryLog spec}
    {w : ByteArray} (h : firstIn k ok a L = some w) :
    ∃ e ∈ L, e.1 = (k, w) ∧ (e.2 : Ans e.1).ba = a := by
  unfold firstIn at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨e, List.mem_of_find?_eq_some he, ?_, hp.2⟩
  obtain ⟨⟨k', w'⟩, u⟩ := e
  simp only at hp ⊢
  rw [hp.1.1]

variable (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (E : CTable)
  (g : Table)

/-- The game's hash log starts with `P`'s hash entries. -/
lemma gLog_eq_hashEnt_append : ∃ rest, gLog T st P E g = hashEnt (jOf g P E) ++ rest := by
  unfold gLog gameIC game
  rw [tableQueryLog_bind, proverIC_eq_bind, tableQueryLog_bind, tableQueryLog_runE_eq]
  exact ⟨_, List.append_assoc _ _ _⟩

lemma aux_gameIC :
    (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.aux.2 = jOf g P E := by
  unfold gameIC
  rw [@evalWithAnswerFn_game (icPrg E.cipher)]
  exact congrArg Prod.snd (proverIC_aux g st E P)

/-- **Without chain hits, every tree of the accepted chain with no committed dead leaf is alive in
the output.** -/
theorem dead_of_not_mem_aliveR (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true) :
    ∀ i ∉ aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)),
      (deadOf T st P E g i).Nonempty := by
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
  rw [hJ, hr2] at hi
  split at hi
  · rename_i x hx
    have hne : deadPre E (logBefore (.h21, x) (hashEnt (jOf g P E)))
        (logBefore (.inl (.h21, x)) (jOf g P E)) (verify Hs T st π).iv x i ≠ ∅ := by
      intro h0
      exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
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
    unfold deadAtX
    rw [hlog, hivX]
    exact Finset.nonempty_iff_ne_empty.2 hne
  · exact absurd (Finset.mem_univ i) hi

end Major

/-! ## PomFRIT: from the chosen statement's bad events to the committed ones -/

section PomConvT

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) (N : ℕ) (g : Table)

/-- The fixed game's data at the chosen statement. -/
abbrev cFixT : CombData (stT pk hF b1F b2F lr (sA g P E)) 45 :=
  combDataFixD T (stT pk hF b1F b2F lr (sA g P E)) P E (sysKT pk hF (some (sA g P E)))
    (witKT pk hF (some (sA g P E))) dstP

/-- The committed data of `o`. -/
abbrev cDT (o : Option ι) : CombData (stKT pk hF b1F b2F lr o) 45 :=
  combDataD T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr) (sysKT pk hF)
    (witKT pk hF) dstP o

lemma preOf_fixT_eq (o : Option ι) (x : ByteArray) :
    preOf T (stT pk hF b1F b2F lr (sA g P E)) P E x g =
      preOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr o) x g := by
  refine (preOfA_eq T (stT pk hF b1F b2F lr) P E g x).symm.trans ?_
  unfold preOfA
  exact preCore_congrD (st := stT pk hF b1F b2F lr (sA g P E)) (st' := stKT pk hF b1F b2F lr o)
    rfl rfl rfl rfl E _ _ x g

lemma midOf_fixT_eq (o : Option ι) (y : ByteArray) :
    midOf T (stT pk hF b1F b2F lr (sA g P E)) P E y g =
      midOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr o) y g := by
  refine (midOfA_eq T (stT pk hF b1F b2F lr) P E g y).symm.trans ?_
  unfold midOfA
  exact midCore_congrD (st := stT pk hF b1F b2F lr (sA g P E)) (st' := stKT pk hF b1F b2F lr o)
    rfl rfl rfl rfl E _ _ y g

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂¹` input: the reference data's bad event. -/
theorem pomfritT_convX (x : ByteArray) :
    @combBad (icPrg E.cipher) _ _ (cFixT pk hF b1F b2F lr T P E g) T chal3Blocks N (.h21, x) g →
    @combBad (icPrg E.cipher) _ _ (cDT pk hF b1F b2F lr T P E none) T chal3Blocks N (.h21, x) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  simp only [combBad, reduceCtorEq, ite_false] at hb ⊢
  have h1 := (chainBad_congr_h21 (cFixT pk hF b1F b2F lr T P E g).toChainData
    ⟨(cDT pk hF b1F b2F lr T P E none).preOf, (cFixT pk hF b1F b2F lr T P E g).midOf, fun _ _ => [],
      (cFixT pk hF b1F b2F lr T P E g).accOf⟩ T chal3Blocks N g x
    (preOf_fixT_eq pk hF b1F b2F lr T P E g none x)).1 hb
  have h2 := (chainBad_transport (st := stT pk hF b1F b2F lr (sA g P E))
    (st' := stKT pk hF b1F b2F lr none) rfl _ T chal3Blocks N (.h21, x) g).1 h1
  refine (chainBad_congr_h21 _ _ T chal3Blocks N g x ?_).1 h2
  rfl

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂²` input: the bad event of a statement with the same target at its
`chal1`. -/
theorem pomfritT_convY (y x0 : ByteArray) (s' : ι)
    (hx : firstIn .h21 (fun _ => true) (yChal1 y)
      (logBefore (.h22, y) (gLogA T (stT pk hF b1F b2F lr) P E g)) = some x0)
    (htgt : hF (sA g P E) (yChal1 y) = hF s' (yChal1 y)) :
    @combBad (icPrg E.cipher) _ _ (cFixT pk hF b1F b2F lr T P E g) T chal3Blocks N (.h22, y) g →
    @combBad (icPrg E.cipher) _ _ (cDT pk hF b1F b2F lr T P E (some s')) T chal3Blocks N
      (.h22, y) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  have hmid := midOf_fixT_eq pk hF b1F b2F lr T P E g (some s') y
  have hc1 : (midOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr (some s')) y g).chal1 =
      yChal1 y := midCore_chal1 E _ g hx
  have hsys : (cFixT pk hF b1F b2F lr T P E g).sysOf y g =
      (cDT pk hF b1F b2F lr T P E (some s')).sysOf y g := by
    funext l
    change sysKT pk hF (some (sA g P E))
        (midOf T (stT pk hF b1F b2F lr (sA g P E)) P E y g).chal1 l =
      sysKT pk hF (some s')
        (midOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr (some s')) y g).chal1 l
    rw [hmid, hc1]
    simp only [sysKT, hFK, Option.elim, htgt]
  have hwit : (cFixT pk hF b1F b2F lr T P E g).witOf y g =
      (cDT pk hF b1F b2F lr T P E (some s')).witOf y g := by
    funext w
    change witKT pk hF (some (sA g P E))
        (midOf T (stT pk hF b1F b2F lr (sA g P E)) P E y g).chal1 w =
      witKT pk hF (some s')
        (midOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr (some s')) y g).chal1 w
    rw [hmid, hc1]
    simp only [witKT, hFK, Option.elim, htgt]
  have h1 : @combBad (icPrg E.cipher) (stT pk hF b1F b2F lr (sA g P E)) 45
      (⟨(cDT pk hF b1F b2F lr T P E (some s')).preOf, (cDT pk hF b1F b2F lr T P E (some s')).midOf,
        (cDT pk hF b1F b2F lr T P E (some s')).sysOf, (cDT pk hF b1F b2F lr T P E (some s')).witOf,
        (cDT pk hF b1F b2F lr T P E (some s')).accOf, dstP, preCellsA T (stT pk hF b1F b2F lr) P E⟩ :
        CombData (stT pk hF b1F b2F lr (sA g P E)) 45) T chal3Blocks N (.h22, y) g := by
    refine (combBad_congr_h22 (cFixT pk hF b1F b2F lr T P E g) _ T chal3Blocks N g y ?_ ?_ ?_ ?_
      ?_).1 hb
    · exact hmid
    · exact hsys
    · exact hwit
    · rfl
    · exact (preCellsA_eq T (stT pk hF b1F b2F lr) P E g y).symm
  have h2 := (combBad_transport (st := stT pk hF b1F b2F lr (sA g P E))
    (st' := stKT pk hF b1F b2F lr (some s')) rfl _ T chal3Blocks N (.h22, y) g).1 h1
  refine (combBad_congr_h22 _ _ T chal3Blocks N g y ?_ ?_ ?_ ?_ ?_).1 h2 <;> rfl

set_option maxRecDepth 4000 in
/-- At the verifier's `H₂³` input: the bad event of a statement with the same target at the
chain's `chal1`. -/
theorem pomfritT_convZ (z y x0 : ByteArray) (s' : ι)
    (hy : firstIn .h22 (fun _ => true) (zChal2 z)
      (logBefore (.h23, z) (gLogA T (stT pk hF b1F b2F lr) P E g)) = some y)
    (hx : firstIn .h21 (fun _ => true) (yChal1 y)
      (logBefore (.h22, y) (logBefore (.h23, z) (gLogA T (stT pk hF b1F b2F lr) P E g))) = some x0)
    (htgt : hF (sA g P E) (yChal1 y) = hF s' (yChal1 y)) :
    @combBad (icPrg E.cipher) _ _ (cFixT pk hF b1F b2F lr T P E g) T chal3Blocks N (.h23, z) g →
    @combBad (icPrg E.cipher) _ _ (cDT pk hF b1F b2F lr T P E (some s')) T chal3Blocks N
      (.h23, z) g := by
  let _ : HasPrg := icPrg E.cipher
  intro hb
  simp only [combBad, reduceCtorEq, ite_false] at hb ⊢
  have hacc : accOf T (stT pk hF b1F b2F lr (sA g P E)) P E z g =
      accOfA T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr (some s')) z g := by
    rw [← accOfA_eq]
    funext b
    unfold accOfA
    dsimp only
    rw [tailCore_congrD (st := stT pk hF b1F b2F lr (sA g P E))
      (st' := stKT pk hF b1F b2F lr (some s')) rfl rfl rfl rfl rfl E _ g hy hx
      (pomfritT_values_eq lr pk htgt),
      hideSet_transport (st := stT pk hF b1F b2F lr (sA g P E))
        (st' := stKT pk hF b1F b2F lr (some s')) rfl]
  have h1 := (chainBad_congr_h23 (cFixT pk hF b1F b2F lr T P E g).toChainData
    ⟨(cFixT pk hF b1F b2F lr T P E g).preOf, (cFixT pk hF b1F b2F lr T P E g).midOf, fun _ _ => [],
      (cDT pk hF b1F b2F lr T P E (some s')).accOf⟩ T chal3Blocks N g z hacc).1 hb
  have h2 := (chainBad_transport (st := stT pk hF b1F b2F lr (sA g P E))
    (st' := stKT pk hF b1F b2F lr (some s')) rfl _ T chal3Blocks N (.h23, z) g).1 h1
  refine (chainBad_congr_h23 _ _ T chal3Blocks N g z ?_).1 h2
  rfl

end PomConvT

section PomUnionT

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)

/-- **Lemma P's per-query bad event** for the prover `P` (the bad event of
`prEvent_accept_le_adaptive_pomfritT_E`): at the query `t`, a bad query of the statement committed
there (`combBadF` at `stmtAtD`), a chain hit, or a statement hit of the adaptive game's log. It reads
the log before `t` only. -/
def pomBad (N : ℕ) (t : Dom) (g : Table) : Prop :=
  combBadF T (stT pk hF b1F b2F lr) P E (stKT pk hF b1F b2F lr) (sysKT pk hF) (witKT pk hF) dstP
      (stmtAtD (decT pk hF b1F b2F lr) none) N t g ∨
    chainHitL (some (45, dstP)) (tableQueryLog (gameA T (stT pk hF b1F b2F lr) P E)) t g ∨
    stmtHitD (tableQueryLog (gameA T (stT pk hF b1F b2F lr) P E)) t g

/-- **The per-query charge of `pomBad`** at a query of kind `k`, for a game with `n'' k` queries of
kind `k` (`ntot` bounds the cached cells at an `H₂²` query). -/
noncomputable def pomEps (n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) (n'' : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  (if k = .h22 then ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (ntot : ℝ≥0∞) / 2 ^ 448
    else chainEps (stKT pk hF b1F b2F lr none) chal3Blocks 0 N k) +
    (hitEps n'' (combCount (some (45, dstP)) n'') k + stmtEpsD n'' k)

lemma pomEps_eq_zero (n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) (n'' : Kind → ℕ) (k : Kind)
    (hk : k ∉ adaptKinds) : pomEps pk hF b1F b2F lr n' εc ntot N n'' k = 0 := by
  cases k <;> simp_all [adaptKinds, pomEps, chainEps, hitEps, stmtEpsD]

set_option maxRecDepth 4000 in
/-- **Lemma P's deterministic step, per table** (the trace of
`prEvent_accept_le_adaptive_pomfritT_E`): if the verifier accepts the prover's proof and Lemma P's
extraction fails, without binding failure, opened dead leaf or `cf`, a query of the game's log is
bad (`pomBad`). -/
theorem pomBad_trace (hT : liftInvOk T = true) (N : ℕ)
    (hdet : ∀ s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (GoalP (witKT pk hF (some s))))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (g : Table)
    (h₀ : let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T (stT pk hF b1F b2F lr) P E)
      (r.2.2.accept = true ∧ ¬MajorExtracted E (stT pk hF b1F b2F lr (stOut r))
        (witKT pk hF (some (stOut r))) r) ∧
      ¬bindFailA (stT pk hF b1F b2F lr) E r ∧ ¬deadOpenA (stT pk hF b1F b2F lr) E r ∧ ¬cf r) :
    ∃ e ∈ tableQueryLog (gameA T (stT pk hF b1F b2F lr) P E) g,
      pomBad pk hF b1F b2F lr T P E N e.1 g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  let cb : Option (ℕ × ByteArray) := some (45, dstP)
  let sel : QueryLog spec → Dom → Option (Option ι) := stmtAtD (decT pk hF b1F b2F lr) none
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬MajorExtracted E (stF (stOut r)) (witKT pk hF (some (stOut r))) r
  let bad : Dom → Table → Prop := fun t g =>
    combBadF T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF) (witKT pk hF) dstP
      sel N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨ stmtHitD (tableQueryLog oa) t g
  show ∃ e ∈ tableQueryLog oa g, bad e.1 g
  have h : (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬cf r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) := h₀
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
  obtain ⟨leaves, hr, hacc', hbad⟩ := combBad_trace_icDG hT (stF (sA g P E))
    (sysKT pk hF (some (sA g P E))) (witKT pk hF (some (sA g P E))) dstP rfl N
    (GoalP (witKT pk hF (some (sA g P E))))
    (fun c1 v w => by
      show (OneMore.Pomfrit.pomfritRedeemT pk (hF (sA g P E)) (b1F (sA g P E)) (b2F (sA g P E))
        lr).values c1 v.ba w = _
      rw [OneMore.Pomfrit.pomfritRedeemT_values, ofArr_combinationOf_ba]; rfl)
    P E (hdet (sA g P E)) cf (hcf (sA g P E)) g hacc _
    (dead_of_not_mem_aliveR T (stF (sA g P E)) P E g hh hacc) hnex hnp hnb hnd hh
  set keys := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC (stF (sA g P E)) E P)).2.keys
  set ch := runChain (Hashes.ofTable g) T (stF (sA g P E)) (πOf g P E) leaves keys
  obtain ⟨s', hdec, hmuEq⟩ := decT_spec pk hF b1F b2F lr ch.chal1 (sA g P E)
  obtain ⟨h2, h3⟩ := stmtAtD_ident (decT pk hF b1F b2F lr) none T (stF (sA g P E)) P E g rfl hh hs
    keys hacc' hr hdec
  obtain ⟨-, -, hF3, hF4, hO3, hO4⟩ := chain_ident T (stF (sA g P E)) P E g hh keys hacc' hr
  have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨(stF (sA g P E)).params, πOf g P E⟩
      ((stF (sA g P E)).mu1 (Hashes.ofTable g))) (Proof.opening ⟨(stF (sA g P E)).params, πOf g P E⟩)
      (Proof.delta ⟨(stF (sA g P E)).params, πOf g P E⟩) = some leaves := hr
  obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T (stF (sA g P E)) (πOf g P E) hacc' hr0 keys
  have hc1s : ch.chal1.size = 136 := Prob.Bytes.size_ba _
  have hyc1 : yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch) = ch.chal1 := by
    rw [runY, yChal1_chal2Input _ hc1s]
  have htgt : hF (sA g P E) (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) =
      hF s' (yChal1 (runY (Hashes.ofTable g) (stF (sA g P E)) ch)) := by
    rw [hyc1]; exact (target_eq_of_muInD_T pk lr hmuEq).symm
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
      @combBad (icPrg E.cipher) _ _ (cDT pk hF b1F b2F lr T P E o) T chal3Blocks N t g →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
    intro t o ht hst hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T (stF (sA g P E)) P E g ht)
    refine ⟨e, hlog ▸ he, Or.inl ⟨o, ?_, hb⟩⟩
    show sel (tableQueryLog oa g) e.1 = some o
    rw [hlog]
    exact hst
  rcases hbad with hb | hb | hb
  · exact hmk _ none hxL (by simp only [sel, stmtAtD]) (pomfritT_convX pk hF b1F b2F lr T P E N g _ hb)
  · exact hmk _ (some s') hyL h2 (pomfritT_convY pk hF b1F b2F lr T P E N g _ _ s' hF3' htgt hb)
  · exact hmk _ (some s') hzL h3
      (pomfritT_convZ pk hF b1F b2F lr T P E N g _ _ _ s' hF4' hF3'' htgt hb)

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **Lemma P's per-query bound** (cache form): over the uncached cells of a cache with fewer than
`ntot` keys, a fresh query `t` is bad (`pomBad`) with probability at most `pomEps` at its kind, for
a prover with `q k` hash queries of kind `k` and any finite key set `K` containing the combination
cells. -/
theorem prEvent_pomBad_le (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) (K : Finset Dom)
    [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey 45 dstP u ∈ K) (ntot : ℕ)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      pomBad pk hF b1F b2F lr T P E N t.val (extendTable K (completeTable c g))] ≤
      pomEps pk hF b1F b2F lr n' εc ntot N (q + extractorQueries + verifierQueries) t.val.1 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  set n'' := q + extractorQueries + verifierQueries
  let cb : Option (ℕ × ByteArray) := some (45, dstP)
  let sel : QueryLog spec → Dom → Option (Option ι) := stmtAtD (decT pk hF b1F b2F lr) none
  have hsel : ∀ L L' t, logBefore t L = logBefore t L' → sel L t = sel L' t :=
    fun L L' t h => stmtAtD_congr _ _ h
  have hq'' := isKindQueryBound_gameA T stF P E hq
  rcases t with ⟨⟨k, x⟩, hx⟩
  unfold pomBad pomEps
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ ?_)))
  · by_cases hk : k = .h22
    · subst hk
      simp only [ite_true]
      exact prEvent_combBadF_h22_le T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF)
        (witKT pk hF) dstP sel hsel N hn' hεc K hK hx c hc hcard
    · refine prEvent_completeTable_cell_le c _ hc
        (fun t G => combBadF T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF)
          (witKT pk hF) dstP sel N t.val (extendTable K G)) _ fun G => ?_
      simp only [extendTable_update]
      simp only [hk, ite_false]
      exact prEvent_combBadF_cell_le T stF P E (stKT pk hF b1F b2F lr) (sysKT pk hF)
        (witKT pk hF) dstP sel hsel hT _ (fun _ => rfl) N (k, x) hk _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => chainHitL cb (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_chainHitL_le cb oa n'' hq'' _ _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => stmtHitD (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_stmtHitD_le oa n'' hq'' _ _

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The adaptive union bound for PomFRIT, per cipher table**: as
`prEvent_accept_le_adaptive_comb_E`, with the statement committed at `H₂²` (`stmtAtD`) and the
statement hits of delayed binding (`stmtHitD`, `(n₂₂ + n₀)·2⁻²⁵⁶` per `H₂⁰` query). No injectivity
is needed: the `H₂⁰` input determines the target (`pomfritTarget_eq_of_muInD`), which is all the
system and the relation read. -/
theorem prEvent_accept_le_adaptive_pomfritT_E (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (GoalP (witKT pk hF (some s))))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stT pk hF b1F b2F lr s) P E)) →
      KeysPre (stT pk hF b1F b2F lr s) E (jOf g P E) (gLog T (stT pk hF b1F b2F lr s) P E g) g)
    (n : ℕ) (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬MajorExtracted E (stT pk hF b1F b2F lr (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          bindFailA (stT pk hF b1F b2F lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          deadOpenA (stT pk hF b1F b2F lr) E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
          cf r] := by
  classical
  intro n''
  set stF := stT pk hF b1F b2F lr
  set oa := gameA T stF P E
  set mx := (simulateQ randomOracle oa).run' ∅
  set ntot := n + 2 + verifierTotal
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬MajorExtracted E (stF (stOut r)) (witKT pk hF (some (stOut r))) r
  let ε : Kind → ℝ≥0∞ := pomEps pk hF b1F b2F lr n' εc ntot N n''
  have hKε : ∀ k ∉ adaptKinds, ε k = 0 := pomEps_eq_zero pk hF b1F b2F lr n' εc ntot N n''
  let K : Finset Dom := possibleQueryKeys oa ∪ Finset.univ.image (combKey 45 dstP)
  have hK : ∀ u, combKey 45 dstP u ∈ K := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hS : AllQueriesSatisfy oa (· ∈ K) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d h => Finset.mem_union_left _ h
  let : SampleableType ((d : K) → Ans d.val) := SampleableType.piOfFintype _
  have hq'' := isKindQueryBound_gameA T stF P E hq
  have hgood := prEvent_randomOracle_le_of_fresh_bad_queries oa K hS (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound oa adaptKinds ε hKε n'' hq'') ntot
    (isTotalQueryBound_gameA T stF E hn)
    (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r)
    (pomBad pk hF b1F b2F lr T P E N)
    (fun c t hc hcard => prEvent_pomBad_le pk hF b1F b2F lr T P E hT N hn' hεc q hq K hK ntot c t
      hc hcard)
    (fun g h => pomBad_trace pk hF b1F b2F lr T P E hT N hdet cf hcf g h)
  have hsum : ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k =
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) +
        n'' .mu * stmtEpsD n'' .mu := by
    simp only [adaptKinds, ε, pomEps]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [chainEps, hitEps, stmtEpsD, hitSum, reduceCtorEq, ite_true, ite_false, zero_add,
      add_zero, mul_add, ntot]
    ring
  calc Pr{let r ← mx}[ev r]
      ≤ Pr{let r ← mx}[(ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r) ∨
          (bindFailA stF E r ∨ (deadOpenA stF E r ∨ cf r))] :=
        prEvent_mono mx _ _ fun r h => by tauto
    _ ≤ Pr{let r ← mx}[ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r] +
          (Pr{let r ← mx}[bindFailA stF E r] +
            (Pr{let r ← mx}[deadOpenA stF E r] + Pr{let r ← mx}[cf r])) :=
        (prEvent_or_le mx _ _).trans (add_le_add le_rfl ((prEvent_or_le mx _ _).trans
          (add_le_add le_rfl (prEvent_or_le mx _ _))))
    _ ≤ _ := by
        rw [← hsum]
        refine (add_le_add hgood le_rfl).trans_eq ?_
        ring
end PomUnionT

/-! ## The joint experiment and the theorem -/

section PomJointT

variable {ι β : Type} (pk : UovPk) (hF : ι → ByteArray → ByteArray) (b1F b2F : ι → ByteArray)
  (lr : Bool) (T : CrtTables) (P : OracleComp specIC (ByteArray × (ι × β)))

/-- **Lemma P's adaptive bound in the joint experiment** (the cipher table uniform). -/
theorem prEvent_accept_le_adaptive_pomfritT (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKT pk hF o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKT pk hF o c1 l).Holds w ∧ ¬witKT pk hF o c1 w) ≤ εc)
    (hdet : ∀ (E : CTable) s, @CombDetG (icPrg E.cipher) 45 T (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) N
      (GoalP (witKT pk hF (some s))))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameA T (stT pk hF b1F b2F lr) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬MajorExtracted E (stT pk hF b1F b2F lr (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n''
  have hE := fun E => prEvent_accept_le_adaptive_pomfritT_E pk hF b1F b2F lr T P E hT N hn' hεc
    (hdet E) (fun r => PostOut E r)
    (fun s g h => keysPre_of_not_postOut T (stT pk hF b1F b2F lr s) P E g h) n hn q hq
  have hdo := prEvent_joint_deadOpen_le_A T (stT pk hF b1F b2F lr) P (pomfritParams lr)
    (fun _ => rfl) q hq
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA (stT pk hF b1F b2F lr) E r)
    (fun E r => deadOpenA (stT pk hF b1F b2F lr) E r) (fun E r => PostOut E r) _ hE).trans ?_
  gcongr
  · exact (prEvent_joint_bindFail_le_A T (stT pk hF b1F b2F lr) P qE hqE).trans
      (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T (stT pk hF b1F b2F lr) P qE hqE q hq

/-- The per-chain step of Lemma P for the family (`pomfritT_extract_major_chain`). -/
theorem combDetG_pomfritT (E : CTable) (s : ι) :
    @CombDetG (icPrg E.cipher) 45 CrtGen.tables (stT pk hF b1F b2F lr s)
      (sysKT pk hF (some s)) (witKT pk hF (some s)) (2 ^ 57)
      (GoalP (witKT pk hF (some s))) := by
  classical
  let _ : HasPrg := icPrg E.cipher
  intro ch known acc l c1 hch1 hv A hA hAS hkos hQS hcb hP
  subst hch1
  exact PomFRIT.pomfritT_extract_major_chain pk (stT pk hF b1F b2F lr s) lr rfl ch
    (tgtOf (hF s ch.chal1)) l hv hA hAS hkos hP.1 hQS hcb preB admissible deltaBlocks
    deltaBlocks_injOn acc hP.2

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Lemma P, adaptive form, every term explicit.** For the issuer's key `pk`, a prover that
outputs a proof and the index `s` of the statement it proves: the target function `hF s` (any
function of `chal1`; in the one-more game the answer of `H_T`) and the binders `b1F s`, `b2F s`.
The verifier accepts and **no fully alive tree of the widest prefix group has a candidate
`(r, σ)` with `P(σ) = h(chal1) ⊕ r`** (`MajorExtracted`) with probability at most the bound of
`pomfritRedeem_accept_le_adaptive` with the `H₂³` term `(Q₃+1)·2⁵⁷·2⁻¹²⁸` (Lemma P's `2⁻⁷¹` per
query) in place of `(Q₃+1)·2·2⁻¹²⁸`. -/
theorem pomfritT_accept_le_major (labelRows : Bool) (P : OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (stT pk hF b1F b2F labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬MajorExtracted E (stT pk hF b1F b2F labelRows (stOut r))
          (witKT pk hF (some (stOut r))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 ^ 57 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 + stmtBindEpsD q := by
  classical
  have h := prEvent_accept_le_adaptive_pomfritT pk hF b1F b2F labelRows CrtGen.tables P
    liftInvOk_tables (2 ^ 57) (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun E s => combDetG_pomfritT pk hF b1F b2F labelRows E s)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q 45 rfl, stmtEpsD_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKT pk hF b1F b2F labelRows none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
      (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((2 ^ 57 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45 +
          stmtBindEpsD q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

end PomJointT

end VoleMole.ROM.IC
